%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:14 EST 2020

% Result     : Theorem 3.54s
% Output     : Refutation 3.66s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 579 expanded)
%              Number of leaves         :   25 ( 164 expanded)
%              Depth                    :   23
%              Number of atoms          :  256 (1077 expanded)
%              Number of equality atoms :   59 ( 314 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3919,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3918,f795])).

fof(f795,plain,(
    r1_tarski(k3_subset_1(sK0,sK2),sK0) ),
    inference(superposition,[],[f84,f789])).

fof(f789,plain,(
    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f88,f46])).

fof(f46,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_tarski(X1,X2)
          <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_tarski(X1,X2)
            <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f26])).

fof(f26,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f70,f60])).

fof(f60,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f84,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f54,f60])).

fof(f54,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f3918,plain,(
    ~ r1_tarski(k3_subset_1(sK0,sK2),sK0) ),
    inference(subsumption_resolution,[],[f3916,f1056])).

fof(f1056,plain,(
    r1_xboole_0(k3_subset_1(sK0,sK2),sK1) ),
    inference(subsumption_resolution,[],[f1051,f803])).

fof(f803,plain,(
    ! [X3] :
      ( r1_xboole_0(k3_subset_1(sK0,sK2),X3)
      | ~ r1_tarski(X3,sK2) ) ),
    inference(superposition,[],[f573,f789])).

fof(f573,plain,(
    ! [X6,X8,X7] :
      ( r1_xboole_0(k5_xboole_0(X8,k3_xboole_0(X8,X7)),X6)
      | ~ r1_tarski(X6,X7) ) ),
    inference(resolution,[],[f469,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f469,plain,(
    ! [X10,X8,X9] :
      ( r1_xboole_0(X10,k5_xboole_0(X9,k3_xboole_0(X9,X8)))
      | ~ r1_tarski(X10,X8) ) ),
    inference(forward_demodulation,[],[f464,f218])).

fof(f218,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f82,f212])).

fof(f212,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(resolution,[],[f145,f50])).

fof(f50,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f145,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(resolution,[],[f66,f52])).

fof(f52,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f82,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f51,f60])).

fof(f51,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f464,plain,(
    ! [X10,X8,X9] :
      ( ~ r1_tarski(X10,k5_xboole_0(X8,k1_xboole_0))
      | r1_xboole_0(X10,k5_xboole_0(X9,k3_xboole_0(X9,X8))) ) ),
    inference(superposition,[],[f90,f213])).

fof(f213,plain,(
    ! [X2,X1] : k1_xboole_0 = k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(resolution,[],[f145,f103])).

fof(f103,plain,(
    ! [X0,X1] : r1_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(resolution,[],[f83,f69])).

fof(f83,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f53,f60])).

fof(f53,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
      | r1_xboole_0(X0,X2) ) ),
    inference(definition_unfolding,[],[f78,f60])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f1051,plain,
    ( r1_xboole_0(k3_subset_1(sK0,sK2),sK1)
    | r1_tarski(sK1,sK2) ),
    inference(resolution,[],[f933,f44])).

fof(f44,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f933,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k3_subset_1(sK0,sK1))
      | r1_xboole_0(X0,sK1) ) ),
    inference(superposition,[],[f90,f790])).

fof(f790,plain,(
    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f88,f47])).

fof(f47,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f29])).

fof(f3916,plain,
    ( ~ r1_xboole_0(k3_subset_1(sK0,sK2),sK1)
    | ~ r1_tarski(k3_subset_1(sK0,sK2),sK0) ),
    inference(resolution,[],[f3894,f3425])).

fof(f3425,plain,(
    ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) ),
    inference(resolution,[],[f3424,f45])).

fof(f45,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f29])).

fof(f3424,plain,(
    r1_tarski(sK1,sK2) ),
    inference(subsumption_resolution,[],[f3419,f144])).

fof(f144,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f142,f93])).

fof(f93,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
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

fof(f142,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f137,f49])).

fof(f49,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f137,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f65,f47])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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

fof(f3419,plain,
    ( ~ r1_tarski(sK1,sK0)
    | r1_tarski(sK1,sK2) ),
    inference(resolution,[],[f3388,f1059])).

fof(f1059,plain,(
    r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) ),
    inference(resolution,[],[f1056,f69])).

fof(f3388,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,k3_subset_1(sK0,sK2))
      | ~ r1_tarski(X0,sK0)
      | r1_tarski(X0,sK2) ) ),
    inference(superposition,[],[f92,f3380])).

fof(f3380,plain,(
    sK0 = k3_tarski(k1_enumset1(sK2,sK2,k3_subset_1(sK0,sK2))) ),
    inference(backward_demodulation,[],[f893,f3377])).

fof(f3377,plain,(
    sK0 = k5_xboole_0(sK2,k3_subset_1(sK0,sK2)) ),
    inference(backward_demodulation,[],[f804,f3376])).

fof(f3376,plain,(
    sK0 = k3_tarski(k1_enumset1(sK0,sK0,sK2)) ),
    inference(forward_demodulation,[],[f3323,f218])).

fof(f3323,plain,(
    k3_tarski(k1_enumset1(sK0,sK0,sK2)) = k5_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f661,f645])).

fof(f645,plain,(
    k1_xboole_0 = k5_xboole_0(sK2,k3_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f638,f99])).

fof(f99,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f75,f48])).

fof(f48,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(f638,plain,(
    v1_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK0,sK2))) ),
    inference(forward_demodulation,[],[f631,f56])).

fof(f56,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f631,plain,(
    v1_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,sK0))) ),
    inference(resolution,[],[f169,f83])).

fof(f169,plain,(
    ! [X2] :
      ( ~ r1_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,X2)),sK0)
      | v1_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,X2))) ) ),
    inference(resolution,[],[f160,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1)
      | ~ r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f160,plain,(
    ! [X0] : r1_tarski(k5_xboole_0(sK2,k3_xboole_0(sK2,X0)),sK0) ),
    inference(resolution,[],[f158,f84])).

fof(f158,plain,(
    ! [X9] :
      ( ~ r1_tarski(X9,sK2)
      | r1_tarski(X9,sK0) ) ),
    inference(resolution,[],[f79,f143])).

fof(f143,plain,(
    r1_tarski(sK2,sK0) ),
    inference(resolution,[],[f141,f93])).

fof(f141,plain,(
    r2_hidden(sK2,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f136,f49])).

fof(f136,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f65,f46])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f661,plain,(
    ! [X0,X1] : k3_tarski(k1_enumset1(X1,X1,X0)) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0))) ),
    inference(superposition,[],[f86,f56])).

fof(f86,plain,(
    ! [X0,X1] : k3_tarski(k1_enumset1(X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f59,f81,f60])).

fof(f81,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f58,f57])).

fof(f57,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f58,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f59,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f804,plain,(
    k5_xboole_0(sK2,k3_subset_1(sK0,sK2)) = k3_tarski(k1_enumset1(sK0,sK0,sK2)) ),
    inference(forward_demodulation,[],[f796,f85])).

fof(f85,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f55,f57,f57])).

fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f796,plain,(
    k3_tarski(k1_enumset1(sK2,sK2,sK0)) = k5_xboole_0(sK2,k3_subset_1(sK0,sK2)) ),
    inference(superposition,[],[f86,f789])).

fof(f893,plain,(
    k5_xboole_0(sK2,k3_subset_1(sK0,sK2)) = k3_tarski(k1_enumset1(sK2,sK2,k3_subset_1(sK0,sK2))) ),
    inference(forward_demodulation,[],[f871,f218])).

fof(f871,plain,(
    k3_tarski(k1_enumset1(sK2,sK2,k3_subset_1(sK0,sK2))) = k5_xboole_0(sK2,k5_xboole_0(k3_subset_1(sK0,sK2),k1_xboole_0)) ),
    inference(superposition,[],[f86,f801])).

fof(f801,plain,(
    k1_xboole_0 = k3_xboole_0(k3_subset_1(sK0,sK2),sK2) ),
    inference(superposition,[],[f216,f789])).

fof(f216,plain,(
    ! [X6,X7] : k1_xboole_0 = k3_xboole_0(k5_xboole_0(X6,k3_xboole_0(X6,X7)),X7) ),
    inference(resolution,[],[f145,f83])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2)))
      | ~ r1_xboole_0(X0,X2)
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f80,f81])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

fof(f3894,plain,(
    ! [X11] :
      ( r1_tarski(X11,k3_subset_1(sK0,sK1))
      | ~ r1_xboole_0(X11,sK1)
      | ~ r1_tarski(X11,sK0) ) ),
    inference(superposition,[],[f998,f3375])).

fof(f3375,plain,(
    sK0 = k3_tarski(k1_enumset1(sK1,sK1,k3_subset_1(sK0,sK1))) ),
    inference(backward_demodulation,[],[f1034,f3372])).

fof(f3372,plain,(
    sK0 = k5_xboole_0(sK1,k3_subset_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f940,f3371])).

fof(f3371,plain,(
    sK0 = k3_tarski(k1_enumset1(sK0,sK0,sK1)) ),
    inference(forward_demodulation,[],[f3322,f218])).

fof(f3322,plain,(
    k3_tarski(k1_enumset1(sK0,sK0,sK1)) = k5_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f661,f2958])).

fof(f2958,plain,(
    k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f2911,f99])).

fof(f2911,plain,(
    v1_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f2879,f56])).

fof(f2879,plain,(
    v1_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))) ),
    inference(resolution,[],[f148,f1574])).

fof(f1574,plain,(
    ! [X1] : r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,sK0)),sK1) ),
    inference(resolution,[],[f1558,f90])).

fof(f1558,plain,(
    ! [X35] : r1_tarski(k5_xboole_0(X35,k3_xboole_0(X35,sK0)),k5_xboole_0(X35,k3_xboole_0(X35,sK1))) ),
    inference(resolution,[],[f89,f144])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k5_xboole_0(X2,k3_xboole_0(X2,X1)),k5_xboole_0(X2,k3_xboole_0(X2,X0))) ) ),
    inference(definition_unfolding,[],[f76,f60,f60])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_xboole_1)).

fof(f148,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)
      | v1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(resolution,[],[f68,f84])).

fof(f940,plain,(
    k5_xboole_0(sK1,k3_subset_1(sK0,sK1)) = k3_tarski(k1_enumset1(sK0,sK0,sK1)) ),
    inference(forward_demodulation,[],[f932,f85])).

fof(f932,plain,(
    k3_tarski(k1_enumset1(sK1,sK1,sK0)) = k5_xboole_0(sK1,k3_subset_1(sK0,sK1)) ),
    inference(superposition,[],[f86,f790])).

fof(f1034,plain,(
    k5_xboole_0(sK1,k3_subset_1(sK0,sK1)) = k3_tarski(k1_enumset1(sK1,sK1,k3_subset_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f1012,f218])).

fof(f1012,plain,(
    k3_tarski(k1_enumset1(sK1,sK1,k3_subset_1(sK0,sK1))) = k5_xboole_0(sK1,k5_xboole_0(k3_subset_1(sK0,sK1),k1_xboole_0)) ),
    inference(superposition,[],[f86,f937])).

fof(f937,plain,(
    k1_xboole_0 = k3_xboole_0(k3_subset_1(sK0,sK1),sK1) ),
    inference(superposition,[],[f216,f790])).

fof(f998,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k3_tarski(k1_enumset1(X1,X1,X0)))
      | ~ r1_xboole_0(X2,X1)
      | r1_tarski(X2,X0) ) ),
    inference(superposition,[],[f92,f85])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:34:35 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.53  % (25012)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.53  % (24996)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.54  % (25004)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.56  % (24991)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.56  % (24993)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.56  % (24984)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.57  % (24985)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.57  % (24992)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.58  % (25005)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.58  % (24983)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.58  % (24997)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.59  % (24986)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.59  % (25006)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.59  % (25007)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.59  % (24989)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.59  % (25009)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.60  % (25008)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.60  % (25001)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.60  % (24988)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.59/0.60  % (25000)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.59/0.60  % (24999)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.59/0.61  % (24987)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.59/0.61  % (24990)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.95/0.62  % (24998)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.95/0.62  % (25011)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.95/0.62  % (25003)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.95/0.63  % (24994)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.95/0.63  % (24995)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.95/0.63  % (25002)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.95/0.64  % (25010)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 3.54/0.83  % (24989)Refutation found. Thanks to Tanya!
% 3.54/0.83  % SZS status Theorem for theBenchmark
% 3.54/0.83  % SZS output start Proof for theBenchmark
% 3.54/0.83  fof(f3919,plain,(
% 3.54/0.83    $false),
% 3.54/0.83    inference(subsumption_resolution,[],[f3918,f795])).
% 3.54/0.83  fof(f795,plain,(
% 3.54/0.83    r1_tarski(k3_subset_1(sK0,sK2),sK0)),
% 3.54/0.83    inference(superposition,[],[f84,f789])).
% 3.54/0.83  fof(f789,plain,(
% 3.54/0.83    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))),
% 3.54/0.83    inference(resolution,[],[f88,f46])).
% 3.54/0.83  fof(f46,plain,(
% 3.54/0.83    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 3.54/0.83    inference(cnf_transformation,[],[f29])).
% 3.54/0.83  fof(f29,plain,(
% 3.54/0.83    ? [X0,X1] : (? [X2] : ((r1_tarski(X1,X2) <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.54/0.83    inference(ennf_transformation,[],[f27])).
% 3.54/0.83  fof(f27,negated_conjecture,(
% 3.54/0.83    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 3.54/0.83    inference(negated_conjecture,[],[f26])).
% 3.54/0.83  fof(f26,conjecture,(
% 3.54/0.83    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 3.54/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).
% 3.54/0.83  fof(f88,plain,(
% 3.54/0.83    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)) )),
% 3.54/0.83    inference(definition_unfolding,[],[f70,f60])).
% 3.54/0.83  fof(f60,plain,(
% 3.54/0.83    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.54/0.83    inference(cnf_transformation,[],[f6])).
% 3.54/0.83  fof(f6,axiom,(
% 3.54/0.83    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.54/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 3.54/0.83  fof(f70,plain,(
% 3.54/0.83    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 3.54/0.83    inference(cnf_transformation,[],[f36])).
% 3.54/0.83  fof(f36,plain,(
% 3.54/0.83    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.54/0.83    inference(ennf_transformation,[],[f24])).
% 3.54/0.83  fof(f24,axiom,(
% 3.54/0.83    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 3.54/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 3.54/0.83  fof(f84,plain,(
% 3.54/0.83    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 3.54/0.83    inference(definition_unfolding,[],[f54,f60])).
% 3.54/0.83  fof(f54,plain,(
% 3.54/0.83    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.54/0.83    inference(cnf_transformation,[],[f10])).
% 3.54/0.83  fof(f10,axiom,(
% 3.54/0.83    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.54/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 3.54/0.83  fof(f3918,plain,(
% 3.54/0.83    ~r1_tarski(k3_subset_1(sK0,sK2),sK0)),
% 3.54/0.83    inference(subsumption_resolution,[],[f3916,f1056])).
% 3.54/0.83  fof(f1056,plain,(
% 3.54/0.83    r1_xboole_0(k3_subset_1(sK0,sK2),sK1)),
% 3.54/0.83    inference(subsumption_resolution,[],[f1051,f803])).
% 3.54/0.83  fof(f803,plain,(
% 3.54/0.83    ( ! [X3] : (r1_xboole_0(k3_subset_1(sK0,sK2),X3) | ~r1_tarski(X3,sK2)) )),
% 3.54/0.83    inference(superposition,[],[f573,f789])).
% 3.54/0.83  fof(f573,plain,(
% 3.54/0.83    ( ! [X6,X8,X7] : (r1_xboole_0(k5_xboole_0(X8,k3_xboole_0(X8,X7)),X6) | ~r1_tarski(X6,X7)) )),
% 3.54/0.83    inference(resolution,[],[f469,f69])).
% 3.54/0.83  fof(f69,plain,(
% 3.54/0.83    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 3.54/0.83    inference(cnf_transformation,[],[f35])).
% 3.54/0.83  fof(f35,plain,(
% 3.54/0.83    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 3.54/0.83    inference(ennf_transformation,[],[f3])).
% 3.54/0.83  fof(f3,axiom,(
% 3.54/0.83    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 3.54/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 3.54/0.83  fof(f469,plain,(
% 3.54/0.83    ( ! [X10,X8,X9] : (r1_xboole_0(X10,k5_xboole_0(X9,k3_xboole_0(X9,X8))) | ~r1_tarski(X10,X8)) )),
% 3.54/0.83    inference(forward_demodulation,[],[f464,f218])).
% 3.54/0.83  fof(f218,plain,(
% 3.54/0.83    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.54/0.83    inference(backward_demodulation,[],[f82,f212])).
% 3.54/0.84  fof(f212,plain,(
% 3.54/0.84    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 3.54/0.84    inference(resolution,[],[f145,f50])).
% 3.54/0.84  fof(f50,plain,(
% 3.54/0.84    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 3.54/0.84    inference(cnf_transformation,[],[f13])).
% 3.54/0.84  fof(f13,axiom,(
% 3.54/0.84    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 3.54/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 3.54/0.84  fof(f145,plain,(
% 3.54/0.84    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 3.54/0.84    inference(resolution,[],[f66,f52])).
% 3.66/0.84  fof(f52,plain,(
% 3.66/0.84    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 3.66/0.84    inference(cnf_transformation,[],[f30])).
% 3.66/0.84  fof(f30,plain,(
% 3.66/0.84    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 3.66/0.84    inference(ennf_transformation,[],[f5])).
% 3.66/0.84  fof(f5,axiom,(
% 3.66/0.84    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 3.66/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 3.66/0.84  fof(f66,plain,(
% 3.66/0.84    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 3.66/0.84    inference(cnf_transformation,[],[f32])).
% 3.66/0.84  fof(f32,plain,(
% 3.66/0.84    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.66/0.84    inference(ennf_transformation,[],[f28])).
% 3.66/0.84  fof(f28,plain,(
% 3.66/0.84    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.66/0.84    inference(rectify,[],[f4])).
% 3.66/0.84  fof(f4,axiom,(
% 3.66/0.84    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.66/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 3.66/0.84  fof(f82,plain,(
% 3.66/0.84    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 3.66/0.84    inference(definition_unfolding,[],[f51,f60])).
% 3.66/0.84  fof(f51,plain,(
% 3.66/0.84    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.66/0.84    inference(cnf_transformation,[],[f12])).
% 3.66/0.84  fof(f12,axiom,(
% 3.66/0.84    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.66/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 3.66/0.84  fof(f464,plain,(
% 3.66/0.84    ( ! [X10,X8,X9] : (~r1_tarski(X10,k5_xboole_0(X8,k1_xboole_0)) | r1_xboole_0(X10,k5_xboole_0(X9,k3_xboole_0(X9,X8)))) )),
% 3.66/0.84    inference(superposition,[],[f90,f213])).
% 3.66/0.84  fof(f213,plain,(
% 3.66/0.84    ( ! [X2,X1] : (k1_xboole_0 = k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) )),
% 3.66/0.84    inference(resolution,[],[f145,f103])).
% 3.66/0.84  fof(f103,plain,(
% 3.66/0.84    ( ! [X0,X1] : (r1_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 3.66/0.84    inference(resolution,[],[f83,f69])).
% 3.66/0.84  fof(f83,plain,(
% 3.66/0.84    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 3.66/0.84    inference(definition_unfolding,[],[f53,f60])).
% 3.66/0.84  fof(f53,plain,(
% 3.66/0.84    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 3.66/0.84    inference(cnf_transformation,[],[f16])).
% 3.66/0.84  fof(f16,axiom,(
% 3.66/0.84    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 3.66/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 3.66/0.84  fof(f90,plain,(
% 3.66/0.84    ( ! [X2,X0,X1] : (~r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) | r1_xboole_0(X0,X2)) )),
% 3.66/0.84    inference(definition_unfolding,[],[f78,f60])).
% 3.66/0.84  fof(f78,plain,(
% 3.66/0.84    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 3.66/0.84    inference(cnf_transformation,[],[f39])).
% 3.66/0.84  fof(f39,plain,(
% 3.66/0.84    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 3.66/0.84    inference(ennf_transformation,[],[f7])).
% 3.66/0.84  fof(f7,axiom,(
% 3.66/0.84    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 3.66/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
% 3.66/0.84  fof(f1051,plain,(
% 3.66/0.84    r1_xboole_0(k3_subset_1(sK0,sK2),sK1) | r1_tarski(sK1,sK2)),
% 3.66/0.84    inference(resolution,[],[f933,f44])).
% 3.66/0.84  fof(f44,plain,(
% 3.66/0.84    r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,sK2)),
% 3.66/0.84    inference(cnf_transformation,[],[f29])).
% 3.66/0.84  fof(f933,plain,(
% 3.66/0.84    ( ! [X0] : (~r1_tarski(X0,k3_subset_1(sK0,sK1)) | r1_xboole_0(X0,sK1)) )),
% 3.66/0.84    inference(superposition,[],[f90,f790])).
% 3.66/0.84  fof(f790,plain,(
% 3.66/0.84    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 3.66/0.84    inference(resolution,[],[f88,f47])).
% 3.66/0.84  fof(f47,plain,(
% 3.66/0.84    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 3.66/0.84    inference(cnf_transformation,[],[f29])).
% 3.66/0.84  fof(f3916,plain,(
% 3.66/0.84    ~r1_xboole_0(k3_subset_1(sK0,sK2),sK1) | ~r1_tarski(k3_subset_1(sK0,sK2),sK0)),
% 3.66/0.84    inference(resolution,[],[f3894,f3425])).
% 3.66/0.84  fof(f3425,plain,(
% 3.66/0.84    ~r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))),
% 3.66/0.84    inference(resolution,[],[f3424,f45])).
% 3.66/0.84  fof(f45,plain,(
% 3.66/0.84    ~r1_tarski(sK1,sK2) | ~r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))),
% 3.66/0.84    inference(cnf_transformation,[],[f29])).
% 3.66/0.84  fof(f3424,plain,(
% 3.66/0.84    r1_tarski(sK1,sK2)),
% 3.66/0.84    inference(subsumption_resolution,[],[f3419,f144])).
% 3.66/0.84  fof(f144,plain,(
% 3.66/0.84    r1_tarski(sK1,sK0)),
% 3.66/0.84    inference(resolution,[],[f142,f93])).
% 3.66/0.84  fof(f93,plain,(
% 3.66/0.84    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 3.66/0.84    inference(equality_resolution,[],[f72])).
% 3.66/0.84  fof(f72,plain,(
% 3.66/0.84    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 3.66/0.84    inference(cnf_transformation,[],[f21])).
% 3.66/0.84  fof(f21,axiom,(
% 3.66/0.84    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 3.66/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 3.66/0.84  fof(f142,plain,(
% 3.66/0.84    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 3.66/0.84    inference(subsumption_resolution,[],[f137,f49])).
% 3.66/0.84  fof(f49,plain,(
% 3.66/0.84    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 3.66/0.84    inference(cnf_transformation,[],[f25])).
% 3.66/0.84  fof(f25,axiom,(
% 3.66/0.84    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 3.66/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 3.66/0.84  fof(f137,plain,(
% 3.66/0.84    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 3.66/0.84    inference(resolution,[],[f65,f47])).
% 3.66/0.84  fof(f65,plain,(
% 3.66/0.84    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 3.66/0.84    inference(cnf_transformation,[],[f31])).
% 3.66/0.84  fof(f31,plain,(
% 3.66/0.84    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 3.66/0.84    inference(ennf_transformation,[],[f23])).
% 3.66/0.84  fof(f23,axiom,(
% 3.66/0.84    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 3.66/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 3.66/0.84  fof(f3419,plain,(
% 3.66/0.84    ~r1_tarski(sK1,sK0) | r1_tarski(sK1,sK2)),
% 3.66/0.84    inference(resolution,[],[f3388,f1059])).
% 3.66/0.84  fof(f1059,plain,(
% 3.66/0.84    r1_xboole_0(sK1,k3_subset_1(sK0,sK2))),
% 3.66/0.84    inference(resolution,[],[f1056,f69])).
% 3.66/0.84  fof(f3388,plain,(
% 3.66/0.84    ( ! [X0] : (~r1_xboole_0(X0,k3_subset_1(sK0,sK2)) | ~r1_tarski(X0,sK0) | r1_tarski(X0,sK2)) )),
% 3.66/0.84    inference(superposition,[],[f92,f3380])).
% 3.66/0.84  fof(f3380,plain,(
% 3.66/0.84    sK0 = k3_tarski(k1_enumset1(sK2,sK2,k3_subset_1(sK0,sK2)))),
% 3.66/0.84    inference(backward_demodulation,[],[f893,f3377])).
% 3.66/0.84  fof(f3377,plain,(
% 3.66/0.84    sK0 = k5_xboole_0(sK2,k3_subset_1(sK0,sK2))),
% 3.66/0.84    inference(backward_demodulation,[],[f804,f3376])).
% 3.66/0.84  fof(f3376,plain,(
% 3.66/0.84    sK0 = k3_tarski(k1_enumset1(sK0,sK0,sK2))),
% 3.66/0.84    inference(forward_demodulation,[],[f3323,f218])).
% 3.66/0.84  fof(f3323,plain,(
% 3.66/0.84    k3_tarski(k1_enumset1(sK0,sK0,sK2)) = k5_xboole_0(sK0,k1_xboole_0)),
% 3.66/0.84    inference(superposition,[],[f661,f645])).
% 3.66/0.84  fof(f645,plain,(
% 3.66/0.84    k1_xboole_0 = k5_xboole_0(sK2,k3_xboole_0(sK0,sK2))),
% 3.66/0.84    inference(resolution,[],[f638,f99])).
% 3.66/0.84  fof(f99,plain,(
% 3.66/0.84    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 3.66/0.84    inference(resolution,[],[f75,f48])).
% 3.66/0.84  fof(f48,plain,(
% 3.66/0.84    v1_xboole_0(k1_xboole_0)),
% 3.66/0.84    inference(cnf_transformation,[],[f2])).
% 3.66/0.84  fof(f2,axiom,(
% 3.66/0.84    v1_xboole_0(k1_xboole_0)),
% 3.66/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 3.66/0.84  fof(f75,plain,(
% 3.66/0.84    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 3.66/0.84    inference(cnf_transformation,[],[f37])).
% 3.66/0.84  fof(f37,plain,(
% 3.66/0.84    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 3.66/0.84    inference(ennf_transformation,[],[f17])).
% 3.66/0.84  fof(f17,axiom,(
% 3.66/0.84    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 3.66/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).
% 3.66/0.84  fof(f638,plain,(
% 3.66/0.84    v1_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK0,sK2)))),
% 3.66/0.84    inference(forward_demodulation,[],[f631,f56])).
% 3.66/0.84  fof(f56,plain,(
% 3.66/0.84    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.66/0.84    inference(cnf_transformation,[],[f1])).
% 3.66/0.84  fof(f1,axiom,(
% 3.66/0.84    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.66/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 3.66/0.84  fof(f631,plain,(
% 3.66/0.84    v1_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,sK0)))),
% 3.66/0.84    inference(resolution,[],[f169,f83])).
% 3.66/0.84  fof(f169,plain,(
% 3.66/0.84    ( ! [X2] : (~r1_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,X2)),sK0) | v1_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,X2)))) )),
% 3.66/0.84    inference(resolution,[],[f160,f68])).
% 3.66/0.84  fof(f68,plain,(
% 3.66/0.84    ( ! [X0,X1] : (~r1_tarski(X1,X0) | v1_xboole_0(X1) | ~r1_xboole_0(X1,X0)) )),
% 3.66/0.84    inference(cnf_transformation,[],[f34])).
% 3.66/0.84  fof(f34,plain,(
% 3.66/0.84    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 3.66/0.84    inference(flattening,[],[f33])).
% 3.66/0.84  fof(f33,plain,(
% 3.66/0.84    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 3.66/0.84    inference(ennf_transformation,[],[f14])).
% 3.66/0.84  fof(f14,axiom,(
% 3.66/0.84    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 3.66/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).
% 3.66/0.84  fof(f160,plain,(
% 3.66/0.84    ( ! [X0] : (r1_tarski(k5_xboole_0(sK2,k3_xboole_0(sK2,X0)),sK0)) )),
% 3.66/0.84    inference(resolution,[],[f158,f84])).
% 3.66/0.84  fof(f158,plain,(
% 3.66/0.84    ( ! [X9] : (~r1_tarski(X9,sK2) | r1_tarski(X9,sK0)) )),
% 3.66/0.84    inference(resolution,[],[f79,f143])).
% 3.66/0.84  fof(f143,plain,(
% 3.66/0.84    r1_tarski(sK2,sK0)),
% 3.66/0.84    inference(resolution,[],[f141,f93])).
% 3.66/0.84  fof(f141,plain,(
% 3.66/0.84    r2_hidden(sK2,k1_zfmisc_1(sK0))),
% 3.66/0.84    inference(subsumption_resolution,[],[f136,f49])).
% 3.66/0.84  fof(f136,plain,(
% 3.66/0.84    r2_hidden(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 3.66/0.84    inference(resolution,[],[f65,f46])).
% 3.66/0.84  fof(f79,plain,(
% 3.66/0.84    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1) | r1_tarski(X0,X2)) )),
% 3.66/0.84    inference(cnf_transformation,[],[f41])).
% 3.66/0.84  fof(f41,plain,(
% 3.66/0.84    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.66/0.84    inference(flattening,[],[f40])).
% 3.66/0.84  fof(f40,plain,(
% 3.66/0.84    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.66/0.84    inference(ennf_transformation,[],[f8])).
% 3.66/0.84  fof(f8,axiom,(
% 3.66/0.84    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.66/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 3.66/0.84  fof(f661,plain,(
% 3.66/0.84    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X1,X1,X0)) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) )),
% 3.66/0.84    inference(superposition,[],[f86,f56])).
% 3.66/0.84  fof(f86,plain,(
% 3.66/0.84    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 3.66/0.84    inference(definition_unfolding,[],[f59,f81,f60])).
% 3.66/0.84  fof(f81,plain,(
% 3.66/0.84    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 3.66/0.84    inference(definition_unfolding,[],[f58,f57])).
% 3.66/0.84  fof(f57,plain,(
% 3.66/0.84    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.66/0.84    inference(cnf_transformation,[],[f20])).
% 3.66/0.84  fof(f20,axiom,(
% 3.66/0.84    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.66/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 3.66/0.84  fof(f58,plain,(
% 3.66/0.84    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.66/0.84    inference(cnf_transformation,[],[f22])).
% 3.66/0.84  fof(f22,axiom,(
% 3.66/0.84    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.66/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 3.66/0.84  fof(f59,plain,(
% 3.66/0.84    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.66/0.84    inference(cnf_transformation,[],[f18])).
% 3.66/0.84  fof(f18,axiom,(
% 3.66/0.84    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.66/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 3.66/0.84  fof(f804,plain,(
% 3.66/0.84    k5_xboole_0(sK2,k3_subset_1(sK0,sK2)) = k3_tarski(k1_enumset1(sK0,sK0,sK2))),
% 3.66/0.84    inference(forward_demodulation,[],[f796,f85])).
% 3.66/0.84  fof(f85,plain,(
% 3.66/0.84    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 3.66/0.84    inference(definition_unfolding,[],[f55,f57,f57])).
% 3.66/0.84  fof(f55,plain,(
% 3.66/0.84    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.66/0.84    inference(cnf_transformation,[],[f19])).
% 3.66/0.84  fof(f19,axiom,(
% 3.66/0.84    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.66/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 3.66/0.84  fof(f796,plain,(
% 3.66/0.84    k3_tarski(k1_enumset1(sK2,sK2,sK0)) = k5_xboole_0(sK2,k3_subset_1(sK0,sK2))),
% 3.66/0.84    inference(superposition,[],[f86,f789])).
% 3.66/0.84  fof(f893,plain,(
% 3.66/0.84    k5_xboole_0(sK2,k3_subset_1(sK0,sK2)) = k3_tarski(k1_enumset1(sK2,sK2,k3_subset_1(sK0,sK2)))),
% 3.66/0.84    inference(forward_demodulation,[],[f871,f218])).
% 3.66/0.84  fof(f871,plain,(
% 3.66/0.84    k3_tarski(k1_enumset1(sK2,sK2,k3_subset_1(sK0,sK2))) = k5_xboole_0(sK2,k5_xboole_0(k3_subset_1(sK0,sK2),k1_xboole_0))),
% 3.66/0.84    inference(superposition,[],[f86,f801])).
% 3.66/0.84  fof(f801,plain,(
% 3.66/0.84    k1_xboole_0 = k3_xboole_0(k3_subset_1(sK0,sK2),sK2)),
% 3.66/0.84    inference(superposition,[],[f216,f789])).
% 3.66/0.84  fof(f216,plain,(
% 3.66/0.84    ( ! [X6,X7] : (k1_xboole_0 = k3_xboole_0(k5_xboole_0(X6,k3_xboole_0(X6,X7)),X7)) )),
% 3.66/0.84    inference(resolution,[],[f145,f83])).
% 3.66/0.84  fof(f92,plain,(
% 3.66/0.84    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2))) | ~r1_xboole_0(X0,X2) | r1_tarski(X0,X1)) )),
% 3.66/0.84    inference(definition_unfolding,[],[f80,f81])).
% 3.66/0.84  fof(f80,plain,(
% 3.66/0.84    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | r1_tarski(X0,X1)) )),
% 3.66/0.84    inference(cnf_transformation,[],[f43])).
% 3.66/0.84  fof(f43,plain,(
% 3.66/0.84    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 3.66/0.84    inference(flattening,[],[f42])).
% 3.66/0.84  fof(f42,plain,(
% 3.66/0.84    ! [X0,X1,X2] : (r1_tarski(X0,X1) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 3.66/0.84    inference(ennf_transformation,[],[f15])).
% 3.66/0.84  fof(f15,axiom,(
% 3.66/0.84    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 3.66/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).
% 3.66/0.84  fof(f3894,plain,(
% 3.66/0.84    ( ! [X11] : (r1_tarski(X11,k3_subset_1(sK0,sK1)) | ~r1_xboole_0(X11,sK1) | ~r1_tarski(X11,sK0)) )),
% 3.66/0.84    inference(superposition,[],[f998,f3375])).
% 3.66/0.84  fof(f3375,plain,(
% 3.66/0.84    sK0 = k3_tarski(k1_enumset1(sK1,sK1,k3_subset_1(sK0,sK1)))),
% 3.66/0.84    inference(backward_demodulation,[],[f1034,f3372])).
% 3.66/0.84  fof(f3372,plain,(
% 3.66/0.84    sK0 = k5_xboole_0(sK1,k3_subset_1(sK0,sK1))),
% 3.66/0.84    inference(backward_demodulation,[],[f940,f3371])).
% 3.66/0.84  fof(f3371,plain,(
% 3.66/0.84    sK0 = k3_tarski(k1_enumset1(sK0,sK0,sK1))),
% 3.66/0.84    inference(forward_demodulation,[],[f3322,f218])).
% 3.66/0.84  fof(f3322,plain,(
% 3.66/0.84    k3_tarski(k1_enumset1(sK0,sK0,sK1)) = k5_xboole_0(sK0,k1_xboole_0)),
% 3.66/0.84    inference(superposition,[],[f661,f2958])).
% 3.66/0.84  fof(f2958,plain,(
% 3.66/0.84    k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),
% 3.66/0.84    inference(resolution,[],[f2911,f99])).
% 3.66/0.84  fof(f2911,plain,(
% 3.66/0.84    v1_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))),
% 3.66/0.84    inference(forward_demodulation,[],[f2879,f56])).
% 3.66/0.84  fof(f2879,plain,(
% 3.66/0.84    v1_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))),
% 3.66/0.84    inference(resolution,[],[f148,f1574])).
% 3.66/0.84  fof(f1574,plain,(
% 3.66/0.84    ( ! [X1] : (r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,sK0)),sK1)) )),
% 3.66/0.84    inference(resolution,[],[f1558,f90])).
% 3.66/0.84  fof(f1558,plain,(
% 3.66/0.84    ( ! [X35] : (r1_tarski(k5_xboole_0(X35,k3_xboole_0(X35,sK0)),k5_xboole_0(X35,k3_xboole_0(X35,sK1)))) )),
% 3.66/0.84    inference(resolution,[],[f89,f144])).
% 3.66/0.84  fof(f89,plain,(
% 3.66/0.84    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k5_xboole_0(X2,k3_xboole_0(X2,X1)),k5_xboole_0(X2,k3_xboole_0(X2,X0)))) )),
% 3.66/0.84    inference(definition_unfolding,[],[f76,f60,f60])).
% 3.66/0.84  fof(f76,plain,(
% 3.66/0.84    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))) )),
% 3.66/0.84    inference(cnf_transformation,[],[f38])).
% 3.66/0.84  fof(f38,plain,(
% 3.66/0.84    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1))),
% 3.66/0.84    inference(ennf_transformation,[],[f9])).
% 3.66/0.84  fof(f9,axiom,(
% 3.66/0.84    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)))),
% 3.66/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_xboole_1)).
% 3.66/0.84  fof(f148,plain,(
% 3.66/0.84    ( ! [X0,X1] : (~r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) | v1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 3.66/0.84    inference(resolution,[],[f68,f84])).
% 3.66/0.84  fof(f940,plain,(
% 3.66/0.84    k5_xboole_0(sK1,k3_subset_1(sK0,sK1)) = k3_tarski(k1_enumset1(sK0,sK0,sK1))),
% 3.66/0.84    inference(forward_demodulation,[],[f932,f85])).
% 3.66/0.84  fof(f932,plain,(
% 3.66/0.84    k3_tarski(k1_enumset1(sK1,sK1,sK0)) = k5_xboole_0(sK1,k3_subset_1(sK0,sK1))),
% 3.66/0.84    inference(superposition,[],[f86,f790])).
% 3.66/0.84  fof(f1034,plain,(
% 3.66/0.84    k5_xboole_0(sK1,k3_subset_1(sK0,sK1)) = k3_tarski(k1_enumset1(sK1,sK1,k3_subset_1(sK0,sK1)))),
% 3.66/0.84    inference(forward_demodulation,[],[f1012,f218])).
% 3.66/0.84  fof(f1012,plain,(
% 3.66/0.84    k3_tarski(k1_enumset1(sK1,sK1,k3_subset_1(sK0,sK1))) = k5_xboole_0(sK1,k5_xboole_0(k3_subset_1(sK0,sK1),k1_xboole_0))),
% 3.66/0.84    inference(superposition,[],[f86,f937])).
% 3.66/0.84  fof(f937,plain,(
% 3.66/0.84    k1_xboole_0 = k3_xboole_0(k3_subset_1(sK0,sK1),sK1)),
% 3.66/0.84    inference(superposition,[],[f216,f790])).
% 3.66/0.84  fof(f998,plain,(
% 3.66/0.84    ( ! [X2,X0,X1] : (~r1_tarski(X2,k3_tarski(k1_enumset1(X1,X1,X0))) | ~r1_xboole_0(X2,X1) | r1_tarski(X2,X0)) )),
% 3.66/0.84    inference(superposition,[],[f92,f85])).
% 3.66/0.84  % SZS output end Proof for theBenchmark
% 3.66/0.84  % (24989)------------------------------
% 3.66/0.84  % (24989)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.66/0.84  % (24989)Termination reason: Refutation
% 3.66/0.84  
% 3.66/0.84  % (24989)Memory used [KB]: 7931
% 3.66/0.84  % (24989)Time elapsed: 0.336 s
% 3.66/0.84  % (24989)------------------------------
% 3.66/0.84  % (24989)------------------------------
% 3.66/0.85  % (24982)Success in time 0.48 s
%------------------------------------------------------------------------------
