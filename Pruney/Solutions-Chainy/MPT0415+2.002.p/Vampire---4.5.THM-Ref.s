%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:21 EST 2020

% Result     : Theorem 2.20s
% Output     : Refutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :  112 (1910 expanded)
%              Number of leaves         :   16 ( 567 expanded)
%              Depth                    :   32
%              Number of atoms          :  209 (2941 expanded)
%              Number of equality atoms :   67 (1591 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1408,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1404,f32])).

fof(f32,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k7_setfam_1(X0,X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k7_setfam_1(X0,X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ~ ( k1_xboole_0 = k7_setfam_1(X0,X1)
            & k1_xboole_0 != X1 ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ~ ( k1_xboole_0 = k7_setfam_1(X0,X1)
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_setfam_1)).

fof(f1404,plain,(
    k1_xboole_0 = sK1 ),
    inference(resolution,[],[f1403,f36])).

fof(f36,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f1403,plain,(
    ! [X0] : ~ r2_hidden(X0,sK1) ),
    inference(forward_demodulation,[],[f1402,f292])).

fof(f292,plain,(
    sK1 = k3_subset_1(sK1,k5_xboole_0(sK1,sK1)) ),
    inference(forward_demodulation,[],[f283,f167])).

fof(f167,plain,(
    sK1 = k6_subset_1(sK1,k5_xboole_0(sK1,sK1)) ),
    inference(backward_demodulation,[],[f75,f156])).

fof(f156,plain,(
    k6_subset_1(sK1,k1_zfmisc_1(sK0)) = k5_xboole_0(sK1,sK1) ),
    inference(superposition,[],[f57,f75])).

fof(f57,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k5_xboole_0(X0,k6_subset_1(X0,k6_subset_1(X0,X1))) ),
    inference(definition_unfolding,[],[f40,f38,f54])).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(definition_unfolding,[],[f41,f38,f38])).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f75,plain,(
    sK1 = k6_subset_1(sK1,k6_subset_1(sK1,k1_zfmisc_1(sK0))) ),
    inference(resolution,[],[f60,f66])).

fof(f66,plain,(
    r1_tarski(sK1,k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f52,f31])).

fof(f31,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_subset_1(X0,k6_subset_1(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f44,f54])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f283,plain,(
    k6_subset_1(sK1,k5_xboole_0(sK1,sK1)) = k3_subset_1(sK1,k5_xboole_0(sK1,sK1)) ),
    inference(resolution,[],[f61,f185])).

fof(f185,plain,(
    m1_subset_1(k5_xboole_0(sK1,sK1),k1_zfmisc_1(sK1)) ),
    inference(superposition,[],[f37,f157])).

fof(f157,plain,(
    k6_subset_1(sK1,sK1) = k5_xboole_0(sK1,sK1) ),
    inference(superposition,[],[f57,f80])).

fof(f80,plain,(
    sK1 = k6_subset_1(sK1,k6_subset_1(sK1,sK1)) ),
    inference(resolution,[],[f78,f60])).

fof(f78,plain,(
    r1_tarski(sK1,sK1) ),
    inference(superposition,[],[f67,f75])).

fof(f67,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(resolution,[],[f52,f37])).

fof(f37,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f45,f38])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f1402,plain,(
    ! [X0] : ~ r2_hidden(X0,k3_subset_1(sK1,k5_xboole_0(sK1,sK1))) ),
    inference(forward_demodulation,[],[f1401,f157])).

fof(f1401,plain,(
    ! [X0] : ~ r2_hidden(X0,k3_subset_1(sK1,k6_subset_1(sK1,sK1))) ),
    inference(resolution,[],[f1400,f302])).

fof(f302,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_subset_1(X0,k6_subset_1(X0,X1))) ) ),
    inference(backward_demodulation,[],[f59,f287])).

fof(f287,plain,(
    ! [X4,X3] : k6_subset_1(X3,k6_subset_1(X3,X4)) = k3_subset_1(X3,k6_subset_1(X3,X4)) ),
    inference(resolution,[],[f61,f37])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k6_subset_1(X0,k6_subset_1(X0,X1))) ) ),
    inference(definition_unfolding,[],[f42,f54])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f1400,plain,(
    r1_xboole_0(sK1,sK1) ),
    inference(resolution,[],[f1364,f1135])).

fof(f1135,plain,
    ( r2_hidden(sK3(sK1,sK1),sK1)
    | r1_xboole_0(sK1,sK1) ),
    inference(forward_demodulation,[],[f1120,f292])).

fof(f1120,plain,
    ( r2_hidden(sK3(sK1,sK1),k3_subset_1(sK1,k5_xboole_0(sK1,sK1)))
    | r1_xboole_0(sK1,sK1) ),
    inference(superposition,[],[f301,f157])).

fof(f301,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),k3_subset_1(X0,k6_subset_1(X0,X1)))
      | r1_xboole_0(X0,X1) ) ),
    inference(backward_demodulation,[],[f58,f287])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK3(X0,X1),k6_subset_1(X0,k6_subset_1(X0,X1))) ) ),
    inference(definition_unfolding,[],[f43,f54])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1364,plain,(
    ~ r2_hidden(sK3(sK1,sK1),sK1) ),
    inference(backward_demodulation,[],[f1254,f1340])).

fof(f1340,plain,(
    sK3(sK1,sK1) = k3_subset_1(sK0,k3_subset_1(sK0,sK3(sK1,sK1))) ),
    inference(subsumption_resolution,[],[f1336,f32])).

fof(f1336,plain,
    ( sK3(sK1,sK1) = k3_subset_1(sK0,k3_subset_1(sK0,sK3(sK1,sK1)))
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f1181,f36])).

fof(f1181,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | sK3(sK1,sK1) = k3_subset_1(sK0,k3_subset_1(sK0,sK3(sK1,sK1))) ) ),
    inference(backward_demodulation,[],[f1175,f1180])).

fof(f1180,plain,(
    k3_subset_1(sK0,sK3(sK1,sK1)) = k6_subset_1(sK0,sK3(sK1,sK1)) ),
    inference(subsumption_resolution,[],[f1176,f32])).

fof(f1176,plain,
    ( k3_subset_1(sK0,sK3(sK1,sK1)) = k6_subset_1(sK0,sK3(sK1,sK1))
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f1172,f36])).

fof(f1172,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | k3_subset_1(sK0,sK3(sK1,sK1)) = k6_subset_1(sK0,sK3(sK1,sK1)) ) ),
    inference(forward_demodulation,[],[f1171,f292])).

fof(f1171,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k3_subset_1(sK1,k5_xboole_0(sK1,sK1)))
      | k3_subset_1(sK0,sK3(sK1,sK1)) = k6_subset_1(sK0,sK3(sK1,sK1)) ) ),
    inference(forward_demodulation,[],[f1170,f157])).

fof(f1170,plain,(
    ! [X0] :
      ( k3_subset_1(sK0,sK3(sK1,sK1)) = k6_subset_1(sK0,sK3(sK1,sK1))
      | ~ r2_hidden(X0,k3_subset_1(sK1,k6_subset_1(sK1,sK1))) ) ),
    inference(resolution,[],[f1147,f302])).

fof(f1147,plain,
    ( r1_xboole_0(sK1,sK1)
    | k3_subset_1(sK0,sK3(sK1,sK1)) = k6_subset_1(sK0,sK3(sK1,sK1)) ),
    inference(resolution,[],[f1145,f61])).

fof(f1145,plain,
    ( m1_subset_1(sK3(sK1,sK1),k1_zfmisc_1(sK0))
    | r1_xboole_0(sK1,sK1) ),
    inference(resolution,[],[f1142,f31])).

fof(f1142,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
      | r1_xboole_0(sK1,sK1)
      | m1_subset_1(sK3(sK1,sK1),X0) ) ),
    inference(resolution,[],[f1135,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f1175,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | sK3(sK1,sK1) = k3_subset_1(sK0,k6_subset_1(sK0,sK3(sK1,sK1))) ) ),
    inference(forward_demodulation,[],[f1174,f292])).

fof(f1174,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k3_subset_1(sK1,k5_xboole_0(sK1,sK1)))
      | sK3(sK1,sK1) = k3_subset_1(sK0,k6_subset_1(sK0,sK3(sK1,sK1))) ) ),
    inference(forward_demodulation,[],[f1173,f157])).

fof(f1173,plain,(
    ! [X0] :
      ( sK3(sK1,sK1) = k3_subset_1(sK0,k6_subset_1(sK0,sK3(sK1,sK1)))
      | ~ r2_hidden(X0,k3_subset_1(sK1,k6_subset_1(sK1,sK1))) ) ),
    inference(resolution,[],[f1151,f302])).

fof(f1151,plain,
    ( r1_xboole_0(sK1,sK1)
    | sK3(sK1,sK1) = k3_subset_1(sK0,k6_subset_1(sK0,sK3(sK1,sK1))) ),
    inference(forward_demodulation,[],[f1150,f287])).

fof(f1150,plain,
    ( sK3(sK1,sK1) = k6_subset_1(sK0,k6_subset_1(sK0,sK3(sK1,sK1)))
    | r1_xboole_0(sK1,sK1) ),
    inference(forward_demodulation,[],[f1149,f483])).

fof(f483,plain,(
    ! [X2,X3] : k3_subset_1(X2,k6_subset_1(X2,X3)) = k6_subset_1(X3,k6_subset_1(X3,X2)) ),
    inference(superposition,[],[f287,f56])).

fof(f56,plain,(
    ! [X0,X1] : k6_subset_1(X0,k6_subset_1(X0,X1)) = k6_subset_1(X1,k6_subset_1(X1,X0)) ),
    inference(definition_unfolding,[],[f39,f54,f54])).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f1149,plain,
    ( r1_xboole_0(sK1,sK1)
    | sK3(sK1,sK1) = k3_subset_1(sK3(sK1,sK1),k6_subset_1(sK3(sK1,sK1),sK0)) ),
    inference(resolution,[],[f1148,f303])).

fof(f303,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_subset_1(X0,k6_subset_1(X0,X1)) = X0 ) ),
    inference(backward_demodulation,[],[f60,f287])).

fof(f1148,plain,
    ( r1_tarski(sK3(sK1,sK1),sK0)
    | r1_xboole_0(sK1,sK1) ),
    inference(resolution,[],[f1145,f52])).

fof(f1254,plain,(
    ~ r2_hidden(k3_subset_1(sK0,k3_subset_1(sK0,sK3(sK1,sK1))),sK1) ),
    inference(superposition,[],[f1242,f1180])).

fof(f1242,plain,(
    ! [X0] : ~ r2_hidden(k3_subset_1(sK0,k6_subset_1(sK0,X0)),sK1) ),
    inference(superposition,[],[f1240,f753])).

fof(f753,plain,(
    ! [X2,X3] : k3_subset_1(X2,k6_subset_1(X2,X3)) = k3_subset_1(X3,k6_subset_1(X3,X2)) ),
    inference(superposition,[],[f483,f287])).

fof(f1240,plain,(
    ! [X0] : ~ r2_hidden(k3_subset_1(X0,k6_subset_1(X0,sK0)),sK1) ),
    inference(subsumption_resolution,[],[f1236,f37])).

fof(f1236,plain,(
    ! [X0] :
      ( ~ r2_hidden(k3_subset_1(X0,k6_subset_1(X0,sK0)),sK1)
      | ~ m1_subset_1(k6_subset_1(sK0,X0),k1_zfmisc_1(sK0)) ) ),
    inference(superposition,[],[f1233,f753])).

fof(f1233,plain,(
    ! [X23] :
      ( ~ r2_hidden(k3_subset_1(sK0,X23),sK1)
      | ~ m1_subset_1(X23,k1_zfmisc_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f1232,f73])).

fof(f73,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f72,f55])).

fof(f55,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(X0,k6_subset_1(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f35,f54])).

fof(f35,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f72,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k6_subset_1(X1,k6_subset_1(X1,k1_xboole_0))) ),
    inference(resolution,[],[f59,f34])).

fof(f34,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f1232,plain,(
    ! [X23] :
      ( r2_hidden(X23,k1_xboole_0)
      | ~ m1_subset_1(X23,k1_zfmisc_1(sK0))
      | ~ r2_hidden(k3_subset_1(sK0,X23),sK1) ) ),
    inference(forward_demodulation,[],[f1230,f33])).

fof(f33,plain,(
    k1_xboole_0 = k7_setfam_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f1230,plain,(
    ! [X23] :
      ( ~ m1_subset_1(X23,k1_zfmisc_1(sK0))
      | ~ r2_hidden(k3_subset_1(sK0,X23),sK1)
      | r2_hidden(X23,k7_setfam_1(sK0,sK1)) ) ),
    inference(resolution,[],[f65,f31])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ r2_hidden(k3_subset_1(X0,X3),X1)
      | r2_hidden(X3,k7_setfam_1(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f63,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ r2_hidden(k3_subset_1(X0,X3),X1)
      | r2_hidden(X3,k7_setfam_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ r2_hidden(k3_subset_1(X0,X3),X1)
      | r2_hidden(X3,X2)
      | k7_setfam_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_setfam_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:14:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.57  % (16196)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.58  % (16212)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.58  % (16204)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.58  % (16203)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.59  % (16213)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.59  % (16220)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.59  % (16213)Refutation not found, incomplete strategy% (16213)------------------------------
% 0.21/0.59  % (16213)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.60  % (16197)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.60  % (16194)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.60  % (16213)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.60  
% 0.21/0.60  % (16213)Memory used [KB]: 10746
% 0.21/0.60  % (16213)Time elapsed: 0.142 s
% 0.21/0.60  % (16213)------------------------------
% 0.21/0.60  % (16213)------------------------------
% 0.21/0.60  % (16193)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.61  % (16199)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.90/0.61  % (16195)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.90/0.62  % (16192)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.90/0.62  % (16214)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.90/0.62  % (16217)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.90/0.62  % (16219)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.90/0.62  % (16191)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.90/0.63  % (16206)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 2.08/0.63  % (16198)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 2.08/0.64  % (16209)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 2.08/0.64  % (16218)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 2.08/0.64  % (16211)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 2.08/0.64  % (16215)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 2.08/0.64  % (16202)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 2.08/0.64  % (16210)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 2.08/0.64  % (16201)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 2.08/0.65  % (16207)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 2.08/0.65  % (16208)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 2.08/0.65  % (16205)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 2.08/0.65  % (16208)Refutation not found, incomplete strategy% (16208)------------------------------
% 2.08/0.65  % (16208)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.08/0.65  % (16208)Termination reason: Refutation not found, incomplete strategy
% 2.08/0.65  
% 2.08/0.65  % (16208)Memory used [KB]: 10618
% 2.08/0.65  % (16208)Time elapsed: 0.202 s
% 2.08/0.65  % (16208)------------------------------
% 2.08/0.65  % (16208)------------------------------
% 2.20/0.66  % (16216)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 2.20/0.67  % (16200)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 2.20/0.71  % (16197)Refutation found. Thanks to Tanya!
% 2.20/0.71  % SZS status Theorem for theBenchmark
% 2.20/0.71  % SZS output start Proof for theBenchmark
% 2.20/0.71  fof(f1408,plain,(
% 2.20/0.71    $false),
% 2.20/0.71    inference(subsumption_resolution,[],[f1404,f32])).
% 2.20/0.71  fof(f32,plain,(
% 2.20/0.71    k1_xboole_0 != sK1),
% 2.20/0.71    inference(cnf_transformation,[],[f21])).
% 2.20/0.71  fof(f21,plain,(
% 2.20/0.71    ? [X0,X1] : (k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.20/0.71    inference(flattening,[],[f20])).
% 2.20/0.71  fof(f20,plain,(
% 2.20/0.71    ? [X0,X1] : ((k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.20/0.71    inference(ennf_transformation,[],[f17])).
% 2.20/0.71  fof(f17,negated_conjecture,(
% 2.20/0.71    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ~(k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1))),
% 2.20/0.71    inference(negated_conjecture,[],[f16])).
% 2.20/0.71  fof(f16,conjecture,(
% 2.20/0.71    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ~(k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1))),
% 2.20/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_setfam_1)).
% 2.20/0.71  fof(f1404,plain,(
% 2.20/0.71    k1_xboole_0 = sK1),
% 2.20/0.71    inference(resolution,[],[f1403,f36])).
% 2.20/0.71  fof(f36,plain,(
% 2.20/0.71    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 2.20/0.71    inference(cnf_transformation,[],[f22])).
% 2.20/0.71  fof(f22,plain,(
% 2.20/0.71    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.20/0.71    inference(ennf_transformation,[],[f3])).
% 2.20/0.71  fof(f3,axiom,(
% 2.20/0.71    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.20/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 2.20/0.71  fof(f1403,plain,(
% 2.20/0.71    ( ! [X0] : (~r2_hidden(X0,sK1)) )),
% 2.20/0.71    inference(forward_demodulation,[],[f1402,f292])).
% 2.20/0.71  fof(f292,plain,(
% 2.20/0.71    sK1 = k3_subset_1(sK1,k5_xboole_0(sK1,sK1))),
% 2.20/0.71    inference(forward_demodulation,[],[f283,f167])).
% 2.20/0.71  fof(f167,plain,(
% 2.20/0.71    sK1 = k6_subset_1(sK1,k5_xboole_0(sK1,sK1))),
% 2.20/0.71    inference(backward_demodulation,[],[f75,f156])).
% 2.20/0.71  fof(f156,plain,(
% 2.20/0.71    k6_subset_1(sK1,k1_zfmisc_1(sK0)) = k5_xboole_0(sK1,sK1)),
% 2.20/0.71    inference(superposition,[],[f57,f75])).
% 2.20/0.71  fof(f57,plain,(
% 2.20/0.71    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k5_xboole_0(X0,k6_subset_1(X0,k6_subset_1(X0,X1)))) )),
% 2.20/0.71    inference(definition_unfolding,[],[f40,f38,f54])).
% 2.20/0.71  fof(f54,plain,(
% 2.20/0.71    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,X1))) )),
% 2.20/0.71    inference(definition_unfolding,[],[f41,f38,f38])).
% 2.20/0.71  fof(f41,plain,(
% 2.20/0.71    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.20/0.71    inference(cnf_transformation,[],[f7])).
% 2.20/0.71  fof(f7,axiom,(
% 2.20/0.71    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.20/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.20/0.71  fof(f38,plain,(
% 2.20/0.71    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 2.20/0.71    inference(cnf_transformation,[],[f11])).
% 2.20/0.71  fof(f11,axiom,(
% 2.20/0.71    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 2.20/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 2.20/0.71  fof(f40,plain,(
% 2.20/0.71    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.20/0.71    inference(cnf_transformation,[],[f4])).
% 2.20/0.71  fof(f4,axiom,(
% 2.20/0.71    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.20/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.20/0.71  fof(f75,plain,(
% 2.20/0.71    sK1 = k6_subset_1(sK1,k6_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 2.20/0.71    inference(resolution,[],[f60,f66])).
% 2.20/0.71  fof(f66,plain,(
% 2.20/0.71    r1_tarski(sK1,k1_zfmisc_1(sK0))),
% 2.20/0.71    inference(resolution,[],[f52,f31])).
% 2.20/0.71  fof(f31,plain,(
% 2.20/0.71    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 2.20/0.71    inference(cnf_transformation,[],[f21])).
% 2.20/0.71  fof(f52,plain,(
% 2.20/0.71    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.20/0.71    inference(cnf_transformation,[],[f28])).
% 2.20/0.71  fof(f28,plain,(
% 2.20/0.71    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 2.20/0.71    inference(ennf_transformation,[],[f19])).
% 2.20/0.71  fof(f19,plain,(
% 2.20/0.71    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 2.20/0.71    inference(unused_predicate_definition_removal,[],[f14])).
% 2.20/0.71  fof(f14,axiom,(
% 2.20/0.71    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.20/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 2.20/0.71  fof(f60,plain,(
% 2.20/0.71    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_subset_1(X0,k6_subset_1(X0,X1)) = X0) )),
% 2.20/0.71    inference(definition_unfolding,[],[f44,f54])).
% 2.20/0.71  fof(f44,plain,(
% 2.20/0.71    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 2.20/0.71    inference(cnf_transformation,[],[f24])).
% 2.20/0.71  fof(f24,plain,(
% 2.20/0.71    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.20/0.71    inference(ennf_transformation,[],[f5])).
% 2.20/0.71  fof(f5,axiom,(
% 2.20/0.71    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.20/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.20/0.71  fof(f283,plain,(
% 2.20/0.71    k6_subset_1(sK1,k5_xboole_0(sK1,sK1)) = k3_subset_1(sK1,k5_xboole_0(sK1,sK1))),
% 2.20/0.71    inference(resolution,[],[f61,f185])).
% 2.20/0.71  fof(f185,plain,(
% 2.20/0.71    m1_subset_1(k5_xboole_0(sK1,sK1),k1_zfmisc_1(sK1))),
% 2.20/0.71    inference(superposition,[],[f37,f157])).
% 2.20/0.71  fof(f157,plain,(
% 2.20/0.71    k6_subset_1(sK1,sK1) = k5_xboole_0(sK1,sK1)),
% 2.20/0.71    inference(superposition,[],[f57,f80])).
% 2.20/0.71  fof(f80,plain,(
% 2.20/0.71    sK1 = k6_subset_1(sK1,k6_subset_1(sK1,sK1))),
% 2.20/0.71    inference(resolution,[],[f78,f60])).
% 2.20/0.71  fof(f78,plain,(
% 2.20/0.71    r1_tarski(sK1,sK1)),
% 2.20/0.71    inference(superposition,[],[f67,f75])).
% 2.20/0.71  fof(f67,plain,(
% 2.20/0.71    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 2.20/0.71    inference(resolution,[],[f52,f37])).
% 2.20/0.71  fof(f37,plain,(
% 2.20/0.71    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 2.20/0.71    inference(cnf_transformation,[],[f10])).
% 2.20/0.71  fof(f10,axiom,(
% 2.20/0.71    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 2.20/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).
% 2.20/0.71  fof(f61,plain,(
% 2.20/0.71    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k6_subset_1(X0,X1)) )),
% 2.20/0.71    inference(definition_unfolding,[],[f45,f38])).
% 2.20/0.71  fof(f45,plain,(
% 2.20/0.71    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 2.20/0.71    inference(cnf_transformation,[],[f25])).
% 2.20/0.71  fof(f25,plain,(
% 2.20/0.71    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.20/0.71    inference(ennf_transformation,[],[f9])).
% 2.20/0.71  fof(f9,axiom,(
% 2.20/0.71    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.20/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 2.20/0.71  fof(f1402,plain,(
% 2.20/0.71    ( ! [X0] : (~r2_hidden(X0,k3_subset_1(sK1,k5_xboole_0(sK1,sK1)))) )),
% 2.20/0.71    inference(forward_demodulation,[],[f1401,f157])).
% 2.20/0.71  fof(f1401,plain,(
% 2.20/0.71    ( ! [X0] : (~r2_hidden(X0,k3_subset_1(sK1,k6_subset_1(sK1,sK1)))) )),
% 2.20/0.71    inference(resolution,[],[f1400,f302])).
% 2.20/0.71  fof(f302,plain,(
% 2.20/0.71    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_subset_1(X0,k6_subset_1(X0,X1)))) )),
% 2.20/0.71    inference(backward_demodulation,[],[f59,f287])).
% 2.20/0.71  fof(f287,plain,(
% 2.20/0.71    ( ! [X4,X3] : (k6_subset_1(X3,k6_subset_1(X3,X4)) = k3_subset_1(X3,k6_subset_1(X3,X4))) )),
% 2.20/0.71    inference(resolution,[],[f61,f37])).
% 2.20/0.71  fof(f59,plain,(
% 2.20/0.71    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k6_subset_1(X0,k6_subset_1(X0,X1)))) )),
% 2.20/0.71    inference(definition_unfolding,[],[f42,f54])).
% 2.20/0.71  fof(f42,plain,(
% 2.20/0.71    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 2.20/0.71    inference(cnf_transformation,[],[f23])).
% 2.20/0.71  fof(f23,plain,(
% 2.20/0.71    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.20/0.71    inference(ennf_transformation,[],[f18])).
% 2.20/0.71  fof(f18,plain,(
% 2.20/0.71    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.20/0.71    inference(rectify,[],[f2])).
% 2.20/0.71  fof(f2,axiom,(
% 2.20/0.71    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.20/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 2.20/0.71  fof(f1400,plain,(
% 2.20/0.71    r1_xboole_0(sK1,sK1)),
% 2.20/0.71    inference(resolution,[],[f1364,f1135])).
% 2.20/0.71  fof(f1135,plain,(
% 2.20/0.71    r2_hidden(sK3(sK1,sK1),sK1) | r1_xboole_0(sK1,sK1)),
% 2.20/0.71    inference(forward_demodulation,[],[f1120,f292])).
% 2.20/0.71  fof(f1120,plain,(
% 2.20/0.71    r2_hidden(sK3(sK1,sK1),k3_subset_1(sK1,k5_xboole_0(sK1,sK1))) | r1_xboole_0(sK1,sK1)),
% 2.20/0.71    inference(superposition,[],[f301,f157])).
% 2.20/0.71  fof(f301,plain,(
% 2.20/0.71    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),k3_subset_1(X0,k6_subset_1(X0,X1))) | r1_xboole_0(X0,X1)) )),
% 2.20/0.71    inference(backward_demodulation,[],[f58,f287])).
% 2.20/0.71  fof(f58,plain,(
% 2.20/0.71    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK3(X0,X1),k6_subset_1(X0,k6_subset_1(X0,X1)))) )),
% 2.20/0.71    inference(definition_unfolding,[],[f43,f54])).
% 2.20/0.71  fof(f43,plain,(
% 2.20/0.71    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))) )),
% 2.20/0.71    inference(cnf_transformation,[],[f23])).
% 2.20/0.71  fof(f1364,plain,(
% 2.20/0.71    ~r2_hidden(sK3(sK1,sK1),sK1)),
% 2.20/0.71    inference(backward_demodulation,[],[f1254,f1340])).
% 2.20/0.71  fof(f1340,plain,(
% 2.20/0.71    sK3(sK1,sK1) = k3_subset_1(sK0,k3_subset_1(sK0,sK3(sK1,sK1)))),
% 2.20/0.71    inference(subsumption_resolution,[],[f1336,f32])).
% 2.20/0.71  fof(f1336,plain,(
% 2.20/0.71    sK3(sK1,sK1) = k3_subset_1(sK0,k3_subset_1(sK0,sK3(sK1,sK1))) | k1_xboole_0 = sK1),
% 2.20/0.71    inference(resolution,[],[f1181,f36])).
% 2.20/0.71  fof(f1181,plain,(
% 2.20/0.71    ( ! [X0] : (~r2_hidden(X0,sK1) | sK3(sK1,sK1) = k3_subset_1(sK0,k3_subset_1(sK0,sK3(sK1,sK1)))) )),
% 2.20/0.71    inference(backward_demodulation,[],[f1175,f1180])).
% 2.20/0.71  fof(f1180,plain,(
% 2.20/0.71    k3_subset_1(sK0,sK3(sK1,sK1)) = k6_subset_1(sK0,sK3(sK1,sK1))),
% 2.20/0.71    inference(subsumption_resolution,[],[f1176,f32])).
% 2.20/0.71  fof(f1176,plain,(
% 2.20/0.71    k3_subset_1(sK0,sK3(sK1,sK1)) = k6_subset_1(sK0,sK3(sK1,sK1)) | k1_xboole_0 = sK1),
% 2.20/0.71    inference(resolution,[],[f1172,f36])).
% 2.20/0.71  fof(f1172,plain,(
% 2.20/0.71    ( ! [X0] : (~r2_hidden(X0,sK1) | k3_subset_1(sK0,sK3(sK1,sK1)) = k6_subset_1(sK0,sK3(sK1,sK1))) )),
% 2.20/0.71    inference(forward_demodulation,[],[f1171,f292])).
% 2.20/0.71  fof(f1171,plain,(
% 2.20/0.71    ( ! [X0] : (~r2_hidden(X0,k3_subset_1(sK1,k5_xboole_0(sK1,sK1))) | k3_subset_1(sK0,sK3(sK1,sK1)) = k6_subset_1(sK0,sK3(sK1,sK1))) )),
% 2.20/0.71    inference(forward_demodulation,[],[f1170,f157])).
% 2.20/0.71  fof(f1170,plain,(
% 2.20/0.71    ( ! [X0] : (k3_subset_1(sK0,sK3(sK1,sK1)) = k6_subset_1(sK0,sK3(sK1,sK1)) | ~r2_hidden(X0,k3_subset_1(sK1,k6_subset_1(sK1,sK1)))) )),
% 2.20/0.71    inference(resolution,[],[f1147,f302])).
% 2.20/0.71  fof(f1147,plain,(
% 2.20/0.71    r1_xboole_0(sK1,sK1) | k3_subset_1(sK0,sK3(sK1,sK1)) = k6_subset_1(sK0,sK3(sK1,sK1))),
% 2.20/0.71    inference(resolution,[],[f1145,f61])).
% 2.20/0.71  fof(f1145,plain,(
% 2.20/0.71    m1_subset_1(sK3(sK1,sK1),k1_zfmisc_1(sK0)) | r1_xboole_0(sK1,sK1)),
% 2.20/0.71    inference(resolution,[],[f1142,f31])).
% 2.20/0.71  fof(f1142,plain,(
% 2.20/0.71    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(X0)) | r1_xboole_0(sK1,sK1) | m1_subset_1(sK3(sK1,sK1),X0)) )),
% 2.20/0.71    inference(resolution,[],[f1135,f53])).
% 2.20/0.71  fof(f53,plain,(
% 2.20/0.71    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 2.20/0.71    inference(cnf_transformation,[],[f30])).
% 2.20/0.71  fof(f30,plain,(
% 2.20/0.71    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.20/0.71    inference(flattening,[],[f29])).
% 2.20/0.71  fof(f29,plain,(
% 2.20/0.71    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.20/0.71    inference(ennf_transformation,[],[f15])).
% 2.20/0.71  fof(f15,axiom,(
% 2.20/0.71    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.20/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 2.20/0.71  fof(f1175,plain,(
% 2.20/0.71    ( ! [X0] : (~r2_hidden(X0,sK1) | sK3(sK1,sK1) = k3_subset_1(sK0,k6_subset_1(sK0,sK3(sK1,sK1)))) )),
% 2.20/0.71    inference(forward_demodulation,[],[f1174,f292])).
% 2.20/0.71  fof(f1174,plain,(
% 2.20/0.71    ( ! [X0] : (~r2_hidden(X0,k3_subset_1(sK1,k5_xboole_0(sK1,sK1))) | sK3(sK1,sK1) = k3_subset_1(sK0,k6_subset_1(sK0,sK3(sK1,sK1)))) )),
% 2.20/0.71    inference(forward_demodulation,[],[f1173,f157])).
% 2.20/0.71  fof(f1173,plain,(
% 2.20/0.71    ( ! [X0] : (sK3(sK1,sK1) = k3_subset_1(sK0,k6_subset_1(sK0,sK3(sK1,sK1))) | ~r2_hidden(X0,k3_subset_1(sK1,k6_subset_1(sK1,sK1)))) )),
% 2.20/0.71    inference(resolution,[],[f1151,f302])).
% 2.20/0.71  fof(f1151,plain,(
% 2.20/0.71    r1_xboole_0(sK1,sK1) | sK3(sK1,sK1) = k3_subset_1(sK0,k6_subset_1(sK0,sK3(sK1,sK1)))),
% 2.20/0.71    inference(forward_demodulation,[],[f1150,f287])).
% 2.20/0.71  fof(f1150,plain,(
% 2.20/0.71    sK3(sK1,sK1) = k6_subset_1(sK0,k6_subset_1(sK0,sK3(sK1,sK1))) | r1_xboole_0(sK1,sK1)),
% 2.20/0.71    inference(forward_demodulation,[],[f1149,f483])).
% 2.20/0.71  fof(f483,plain,(
% 2.20/0.71    ( ! [X2,X3] : (k3_subset_1(X2,k6_subset_1(X2,X3)) = k6_subset_1(X3,k6_subset_1(X3,X2))) )),
% 2.20/0.71    inference(superposition,[],[f287,f56])).
% 2.20/0.71  fof(f56,plain,(
% 2.20/0.71    ( ! [X0,X1] : (k6_subset_1(X0,k6_subset_1(X0,X1)) = k6_subset_1(X1,k6_subset_1(X1,X0))) )),
% 2.20/0.71    inference(definition_unfolding,[],[f39,f54,f54])).
% 2.20/0.71  fof(f39,plain,(
% 2.20/0.71    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.20/0.71    inference(cnf_transformation,[],[f1])).
% 2.20/0.71  fof(f1,axiom,(
% 2.20/0.71    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.20/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.20/0.71  fof(f1149,plain,(
% 2.20/0.71    r1_xboole_0(sK1,sK1) | sK3(sK1,sK1) = k3_subset_1(sK3(sK1,sK1),k6_subset_1(sK3(sK1,sK1),sK0))),
% 2.20/0.71    inference(resolution,[],[f1148,f303])).
% 2.20/0.71  fof(f303,plain,(
% 2.20/0.71    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_subset_1(X0,k6_subset_1(X0,X1)) = X0) )),
% 2.20/0.71    inference(backward_demodulation,[],[f60,f287])).
% 2.20/0.71  fof(f1148,plain,(
% 2.20/0.71    r1_tarski(sK3(sK1,sK1),sK0) | r1_xboole_0(sK1,sK1)),
% 2.20/0.71    inference(resolution,[],[f1145,f52])).
% 2.20/0.71  fof(f1254,plain,(
% 2.20/0.71    ~r2_hidden(k3_subset_1(sK0,k3_subset_1(sK0,sK3(sK1,sK1))),sK1)),
% 2.20/0.71    inference(superposition,[],[f1242,f1180])).
% 2.20/0.71  fof(f1242,plain,(
% 2.20/0.71    ( ! [X0] : (~r2_hidden(k3_subset_1(sK0,k6_subset_1(sK0,X0)),sK1)) )),
% 2.20/0.71    inference(superposition,[],[f1240,f753])).
% 2.20/0.71  fof(f753,plain,(
% 2.20/0.71    ( ! [X2,X3] : (k3_subset_1(X2,k6_subset_1(X2,X3)) = k3_subset_1(X3,k6_subset_1(X3,X2))) )),
% 2.20/0.71    inference(superposition,[],[f483,f287])).
% 2.20/0.71  fof(f1240,plain,(
% 2.20/0.71    ( ! [X0] : (~r2_hidden(k3_subset_1(X0,k6_subset_1(X0,sK0)),sK1)) )),
% 2.20/0.71    inference(subsumption_resolution,[],[f1236,f37])).
% 2.20/0.71  fof(f1236,plain,(
% 2.20/0.71    ( ! [X0] : (~r2_hidden(k3_subset_1(X0,k6_subset_1(X0,sK0)),sK1) | ~m1_subset_1(k6_subset_1(sK0,X0),k1_zfmisc_1(sK0))) )),
% 2.20/0.71    inference(superposition,[],[f1233,f753])).
% 2.20/0.71  fof(f1233,plain,(
% 2.20/0.71    ( ! [X23] : (~r2_hidden(k3_subset_1(sK0,X23),sK1) | ~m1_subset_1(X23,k1_zfmisc_1(sK0))) )),
% 2.20/0.71    inference(subsumption_resolution,[],[f1232,f73])).
% 2.20/0.71  fof(f73,plain,(
% 2.20/0.71    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 2.20/0.71    inference(forward_demodulation,[],[f72,f55])).
% 2.20/0.71  fof(f55,plain,(
% 2.20/0.71    ( ! [X0] : (k1_xboole_0 = k6_subset_1(X0,k6_subset_1(X0,k1_xboole_0))) )),
% 2.20/0.71    inference(definition_unfolding,[],[f35,f54])).
% 2.20/0.71  fof(f35,plain,(
% 2.20/0.71    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 2.20/0.71    inference(cnf_transformation,[],[f6])).
% 2.20/0.71  fof(f6,axiom,(
% 2.20/0.71    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 2.20/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 2.20/0.71  fof(f72,plain,(
% 2.20/0.71    ( ! [X0,X1] : (~r2_hidden(X0,k6_subset_1(X1,k6_subset_1(X1,k1_xboole_0)))) )),
% 2.20/0.71    inference(resolution,[],[f59,f34])).
% 2.20/0.71  fof(f34,plain,(
% 2.20/0.71    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 2.20/0.71    inference(cnf_transformation,[],[f8])).
% 2.20/0.71  fof(f8,axiom,(
% 2.20/0.71    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 2.20/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 2.20/0.71  fof(f1232,plain,(
% 2.20/0.71    ( ! [X23] : (r2_hidden(X23,k1_xboole_0) | ~m1_subset_1(X23,k1_zfmisc_1(sK0)) | ~r2_hidden(k3_subset_1(sK0,X23),sK1)) )),
% 2.20/0.71    inference(forward_demodulation,[],[f1230,f33])).
% 2.20/0.71  fof(f33,plain,(
% 2.20/0.71    k1_xboole_0 = k7_setfam_1(sK0,sK1)),
% 2.20/0.71    inference(cnf_transformation,[],[f21])).
% 2.20/0.71  fof(f1230,plain,(
% 2.20/0.71    ( ! [X23] : (~m1_subset_1(X23,k1_zfmisc_1(sK0)) | ~r2_hidden(k3_subset_1(sK0,X23),sK1) | r2_hidden(X23,k7_setfam_1(sK0,sK1))) )),
% 2.20/0.71    inference(resolution,[],[f65,f31])).
% 2.20/0.71  fof(f65,plain,(
% 2.20/0.71    ( ! [X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,k7_setfam_1(X0,X1))) )),
% 2.20/0.71    inference(subsumption_resolution,[],[f63,f46])).
% 2.20/0.71  fof(f46,plain,(
% 2.20/0.71    ( ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.20/0.71    inference(cnf_transformation,[],[f26])).
% 2.20/0.71  fof(f26,plain,(
% 2.20/0.71    ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.20/0.71    inference(ennf_transformation,[],[f13])).
% 2.20/0.71  fof(f13,axiom,(
% 2.20/0.71    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.20/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).
% 2.20/0.71  fof(f63,plain,(
% 2.20/0.71    ( ! [X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,k7_setfam_1(X0,X1))) )),
% 2.20/0.71    inference(equality_resolution,[],[f49])).
% 2.20/0.72  fof(f49,plain,(
% 2.20/0.72    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2) | k7_setfam_1(X0,X1) != X2) )),
% 2.20/0.72    inference(cnf_transformation,[],[f27])).
% 2.20/0.72  fof(f27,plain,(
% 2.20/0.72    ! [X0,X1] : (! [X2] : ((k7_setfam_1(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> r2_hidden(k3_subset_1(X0,X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.20/0.72    inference(ennf_transformation,[],[f12])).
% 2.20/0.72  fof(f12,axiom,(
% 2.20/0.72    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k7_setfam_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => (r2_hidden(X3,X2) <=> r2_hidden(k3_subset_1(X0,X3),X1))))))),
% 2.20/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_setfam_1)).
% 2.20/0.72  % SZS output end Proof for theBenchmark
% 2.20/0.72  % (16197)------------------------------
% 2.20/0.72  % (16197)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.20/0.72  % (16197)Termination reason: Refutation
% 2.20/0.72  
% 2.20/0.72  % (16197)Memory used [KB]: 7036
% 2.20/0.72  % (16197)Time elapsed: 0.264 s
% 2.20/0.72  % (16197)------------------------------
% 2.20/0.72  % (16197)------------------------------
% 2.73/0.72  % (16190)Success in time 0.354 s
%------------------------------------------------------------------------------
