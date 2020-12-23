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
% DateTime   : Thu Dec  3 12:42:39 EST 2020

% Result     : Theorem 5.78s
% Output     : Refutation 5.78s
% Verified   : 
% Statistics : Number of formulae       :  141 (1207 expanded)
%              Number of leaves         :   19 ( 292 expanded)
%              Depth                    :   40
%              Number of atoms          :  257 (2718 expanded)
%              Number of equality atoms :  110 ( 925 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21556,plain,(
    $false ),
    inference(subsumption_resolution,[],[f21107,f64])).

fof(f64,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f21107,plain,(
    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) ),
    inference(backward_demodulation,[],[f34,f21104])).

fof(f21104,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f21063,f19378])).

fof(f19378,plain,(
    k1_xboole_0 != k4_xboole_0(sK1,sK3) ),
    inference(trivial_inequality_removal,[],[f18751])).

fof(f18751,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 != k4_xboole_0(sK1,sK3) ),
    inference(backward_demodulation,[],[f77,f18750])).

fof(f18750,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK2) ),
    inference(subsumption_resolution,[],[f18614,f4175])).

fof(f4175,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f4173,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f4173,plain,(
    r2_hidden(sK5(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f4172,f34])).

fof(f4172,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | r2_hidden(sK5(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f4168,f1173])).

fof(f1173,plain,(
    ! [X7] : k3_xboole_0(X7,X7) = X7 ),
    inference(resolution,[],[f1137,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f1137,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(subsumption_resolution,[],[f1128,f34])).

fof(f1128,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f1121,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X1,X2)
      | ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
        & ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_tarski(X1,X2)
        & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
          | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(f1121,plain,(
    ! [X0] : r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0)) ),
    inference(forward_demodulation,[],[f1113,f424])).

fof(f424,plain,(
    ! [X2] : k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X2) = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k3_xboole_0(X2,X2)) ),
    inference(forward_demodulation,[],[f406,f73])).

fof(f73,plain,(
    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(resolution,[],[f33,f45])).

fof(f33,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
       => ( ( r1_tarski(X1,X3)
            & r1_tarski(X0,X2) )
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(f406,plain,(
    ! [X2] : k2_zfmisc_1(k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)),X2) = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k3_xboole_0(X2,X2)) ),
    inference(superposition,[],[f194,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t122_zfmisc_1)).

fof(f194,plain,(
    ! [X2,X1] : k3_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X1),k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),X2)) = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k3_xboole_0(X1,X2)) ),
    inference(superposition,[],[f62,f73])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f1113,plain,(
    ! [X0] : r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k3_xboole_0(X0,X0))) ),
    inference(superposition,[],[f1081,f36])).

fof(f36,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f1081,plain,(
    ! [X6,X5] : r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X5),k2_zfmisc_1(k2_xboole_0(k2_zfmisc_1(sK0,sK1),X6),k3_xboole_0(X5,X5))) ),
    inference(resolution,[],[f750,f41])).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f750,plain,(
    ! [X23,X22] :
      ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),X23)
      | r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X22),k2_zfmisc_1(X23,k3_xboole_0(X22,X22))) ) ),
    inference(superposition,[],[f55,f424])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(f4168,plain,
    ( r2_hidden(sK5(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f984,f73])).

fof(f984,plain,(
    ! [X4] :
      ( r2_hidden(sK5(k2_zfmisc_1(sK2,sK3),X4),k3_xboole_0(X4,k2_zfmisc_1(sK2,sK3)))
      | k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(sK0,sK1),X4) ) ),
    inference(superposition,[],[f286,f42])).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f286,plain,(
    ! [X2] :
      ( r2_hidden(sK5(k2_zfmisc_1(sK2,sK3),X2),k3_xboole_0(k2_zfmisc_1(sK2,sK3),X2))
      | k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(sK0,sK1),X2) ) ),
    inference(resolution,[],[f121,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f121,plain,(
    ! [X5] :
      ( r1_xboole_0(k2_zfmisc_1(sK0,sK1),X5)
      | r2_hidden(sK5(k2_zfmisc_1(sK2,sK3),X5),k3_xboole_0(k2_zfmisc_1(sK2,sK3),X5)) ) ),
    inference(resolution,[],[f69,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f69,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(k2_zfmisc_1(sK2,sK3),X0)
      | r1_xboole_0(k2_zfmisc_1(sK0,sK1),X0) ) ),
    inference(resolution,[],[f33,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f18614,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | k1_xboole_0 = k4_xboole_0(sK0,sK2) ),
    inference(superposition,[],[f18580,f13825])).

fof(f13825,plain,(
    ! [X7] :
      ( k1_xboole_0 = k4_xboole_0(sK0,sK2)
      | sK1 = k3_xboole_0(sK1,X7) ) ),
    inference(resolution,[],[f13726,f45])).

fof(f13726,plain,(
    ! [X157] :
      ( r1_tarski(sK1,X157)
      | k1_xboole_0 = k4_xboole_0(sK0,sK2) ) ),
    inference(trivial_inequality_removal,[],[f13698])).

fof(f13698,plain,(
    ! [X157] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(sK1,X157)
      | k1_xboole_0 = k4_xboole_0(sK0,sK2) ) ),
    inference(superposition,[],[f1311,f13287])).

fof(f13287,plain,(
    ! [X4] :
      ( k1_xboole_0 = k4_xboole_0(sK1,X4)
      | k1_xboole_0 = k4_xboole_0(sK0,sK2) ) ),
    inference(superposition,[],[f8310,f1299])).

fof(f1299,plain,(
    ! [X12,X11] : k4_xboole_0(X11,X12) = k3_xboole_0(k4_xboole_0(X11,X12),X11) ),
    inference(resolution,[],[f1174,f45])).

fof(f1174,plain,(
    ! [X8,X9] : r1_tarski(k4_xboole_0(X8,X9),X8) ),
    inference(resolution,[],[f1137,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f8310,plain,(
    ! [X15,X16] :
      ( k1_xboole_0 = k4_xboole_0(sK1,X15)
      | k1_xboole_0 = k3_xboole_0(k4_xboole_0(sK0,sK2),X16) ) ),
    inference(resolution,[],[f8080,f47])).

fof(f8080,plain,(
    ! [X364,X365] :
      ( r1_xboole_0(k4_xboole_0(sK0,sK2),X364)
      | k1_xboole_0 = k4_xboole_0(sK1,X365) ) ),
    inference(trivial_inequality_removal,[],[f7974])).

fof(f7974,plain,(
    ! [X364,X365] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_xboole_0(k4_xboole_0(sK0,sK2),X364)
      | k1_xboole_0 = k4_xboole_0(sK1,X365) ) ),
    inference(superposition,[],[f1411,f5815])).

fof(f5815,plain,(
    ! [X10,X11] :
      ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),X10)
      | k1_xboole_0 = k4_xboole_0(sK1,X11) ) ),
    inference(resolution,[],[f5516,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f5516,plain,(
    ! [X33,X34] :
      ( r1_tarski(sK1,X34)
      | k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),X33) ) ),
    inference(subsumption_resolution,[],[f5499,f35])).

fof(f35,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f5499,plain,(
    ! [X33,X34] :
      ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(k4_xboole_0(k4_xboole_0(sK0,sK2),X33),X34))
      | k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),X33)
      | r1_tarski(sK1,X34) ) ),
    inference(superposition,[],[f61,f5417])).

fof(f5417,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(k4_xboole_0(sK0,sK2),X0),sK1) ),
    inference(superposition,[],[f5367,f3500])).

fof(f3500,plain,(
    ! [X14,X15,X16] : k4_xboole_0(k4_xboole_0(X14,X15),X16) = k3_xboole_0(X14,k4_xboole_0(k4_xboole_0(X14,X15),X16)) ),
    inference(superposition,[],[f1445,f42])).

fof(f1445,plain,(
    ! [X17,X15,X16] : k4_xboole_0(k4_xboole_0(X15,X16),X17) = k3_xboole_0(k4_xboole_0(k4_xboole_0(X15,X16),X17),X15) ),
    inference(resolution,[],[f1300,f45])).

fof(f1300,plain,(
    ! [X14,X15,X13] : r1_tarski(k4_xboole_0(k4_xboole_0(X13,X14),X15),X13) ),
    inference(resolution,[],[f1174,f57])).

fof(f5367,plain,(
    ! [X6,X5] : k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(sK0,k4_xboole_0(k4_xboole_0(X5,sK2),X6)),sK1) ),
    inference(superposition,[],[f3635,f53])).

fof(f3635,plain,(
    ! [X21,X22,X20] : k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k4_xboole_0(k4_xboole_0(X20,sK2),X21),X22)) ),
    inference(subsumption_resolution,[],[f3578,f91])).

fof(f91,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f90,f38])).

fof(f38,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f90,plain,(
    ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f84,f83])).

fof(f83,plain,(
    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(sK2,sK3)) ),
    inference(resolution,[],[f81,f47])).

fof(f81,plain,(
    r1_xboole_0(k1_xboole_0,k2_zfmisc_1(sK2,sK3)) ),
    inference(superposition,[],[f40,f72])).

fof(f72,plain,(
    k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(resolution,[],[f33,f48])).

fof(f40,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f84,plain,(
    ! [X1] : ~ r2_hidden(X1,k3_xboole_0(k1_xboole_0,k2_zfmisc_1(sK2,sK3))) ),
    inference(resolution,[],[f81,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3578,plain,(
    ! [X21,X22,X20] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k4_xboole_0(k4_xboole_0(X20,sK2),X21),X22)) ) ),
    inference(superposition,[],[f992,f1827])).

fof(f1827,plain,(
    ! [X26,X24,X23,X25,X22] : k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(k4_xboole_0(k4_xboole_0(X22,X23),X24),X25),k2_zfmisc_1(X23,X26)) ),
    inference(forward_demodulation,[],[f1812,f64])).

fof(f1812,plain,(
    ! [X26,X24,X23,X25,X22] : k2_zfmisc_1(k1_xboole_0,k3_xboole_0(X25,X26)) = k3_xboole_0(k2_zfmisc_1(k4_xboole_0(k4_xboole_0(X22,X23),X24),X25),k2_zfmisc_1(X23,X26)) ),
    inference(superposition,[],[f62,f1476])).

fof(f1476,plain,(
    ! [X6,X4,X5] : k1_xboole_0 = k3_xboole_0(k4_xboole_0(k4_xboole_0(X4,X5),X6),X5) ),
    inference(resolution,[],[f1301,f47])).

fof(f1301,plain,(
    ! [X17,X18,X16] : r1_xboole_0(k4_xboole_0(k4_xboole_0(X16,X17),X18),X17) ),
    inference(resolution,[],[f1174,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f992,plain,(
    ! [X4] :
      ( ~ v1_xboole_0(k3_xboole_0(X4,k2_zfmisc_1(sK2,sK3)))
      | k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(sK0,sK1),X4) ) ),
    inference(superposition,[],[f979,f42])).

fof(f979,plain,(
    ! [X1] :
      ( ~ v1_xboole_0(k3_xboole_0(k2_zfmisc_1(sK2,sK3),X1))
      | k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(sK0,sK1),X1) ) ),
    inference(resolution,[],[f286,f39])).

fof(f1411,plain,(
    ! [X10,X9] :
      ( k1_xboole_0 != k4_xboole_0(X9,k1_xboole_0)
      | r1_xboole_0(X9,X10) ) ),
    inference(resolution,[],[f1238,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f1238,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X3,k1_xboole_0)
      | r1_xboole_0(X3,X2) ) ),
    inference(superposition,[],[f58,f1172])).

fof(f1172,plain,(
    ! [X6] : k1_xboole_0 = k4_xboole_0(X6,X6) ),
    inference(resolution,[],[f1137,f48])).

fof(f1311,plain,(
    ! [X10,X9] :
      ( k1_xboole_0 != k4_xboole_0(X9,k1_xboole_0)
      | r1_tarski(X9,X10) ) ),
    inference(resolution,[],[f1237,f49])).

fof(f1237,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k1_xboole_0)
      | r1_tarski(X1,X0) ) ),
    inference(superposition,[],[f57,f1172])).

fof(f18580,plain,(
    ! [X0,X1] : v1_xboole_0(k2_zfmisc_1(sK0,k3_xboole_0(sK1,k4_xboole_0(k4_xboole_0(X0,sK3),X1)))) ),
    inference(subsumption_resolution,[],[f18565,f90])).

fof(f18565,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,k4_xboole_0(k4_xboole_0(X0,sK3),X1))),k1_xboole_0)
      | v1_xboole_0(k2_zfmisc_1(sK0,k3_xboole_0(sK1,k4_xboole_0(k4_xboole_0(X0,sK3),X1)))) ) ),
    inference(superposition,[],[f5895,f1915])).

fof(f1915,plain,(
    ! [X30,X28,X31,X29,X27] : k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(X30,X27),k2_zfmisc_1(X31,k4_xboole_0(k4_xboole_0(X28,X27),X29))) ),
    inference(forward_demodulation,[],[f1899,f63])).

fof(f63,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f1899,plain,(
    ! [X30,X28,X31,X29,X27] : k2_zfmisc_1(k3_xboole_0(X30,X31),k1_xboole_0) = k3_xboole_0(k2_zfmisc_1(X30,X27),k2_zfmisc_1(X31,k4_xboole_0(k4_xboole_0(X28,X27),X29))) ),
    inference(superposition,[],[f62,f1804])).

fof(f1804,plain,(
    ! [X10,X11,X9] : k1_xboole_0 = k3_xboole_0(X10,k4_xboole_0(k4_xboole_0(X9,X10),X11)) ),
    inference(superposition,[],[f1476,f42])).

fof(f5895,plain,(
    ! [X0] :
      ( r2_hidden(sK5(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,X0)),k3_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,X0)))
      | v1_xboole_0(k2_zfmisc_1(sK0,k3_xboole_0(sK1,X0))) ) ),
    inference(resolution,[],[f1042,f38])).

fof(f1042,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X2,k2_zfmisc_1(sK0,k3_xboole_0(sK1,X1)))
      | r2_hidden(sK5(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,X1)),k3_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,X1))) ) ),
    inference(superposition,[],[f287,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f287,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X4,k3_xboole_0(k2_zfmisc_1(sK0,sK1),X3))
      | r2_hidden(sK5(k2_zfmisc_1(sK2,sK3),X3),k3_xboole_0(k2_zfmisc_1(sK2,sK3),X3)) ) ),
    inference(resolution,[],[f121,f43])).

fof(f77,plain,
    ( k1_xboole_0 != k4_xboole_0(sK1,sK3)
    | k1_xboole_0 != k4_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f68,f49])).

fof(f68,plain,
    ( ~ r1_tarski(sK0,sK2)
    | k1_xboole_0 != k4_xboole_0(sK1,sK3) ),
    inference(resolution,[],[f32,f49])).

fof(f32,plain,
    ( ~ r1_tarski(sK1,sK3)
    | ~ r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f21063,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK3)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f20920,f1299])).

fof(f20920,plain,(
    ! [X11] :
      ( k1_xboole_0 = k3_xboole_0(k4_xboole_0(sK1,sK3),X11)
      | k1_xboole_0 = sK0 ) ),
    inference(resolution,[],[f20767,f47])).

fof(f20767,plain,(
    ! [X221] :
      ( r1_xboole_0(k4_xboole_0(sK1,sK3),X221)
      | k1_xboole_0 = sK0 ) ),
    inference(trivial_inequality_removal,[],[f20737])).

fof(f20737,plain,(
    ! [X221] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_xboole_0(k4_xboole_0(sK1,sK3),X221)
      | k1_xboole_0 = sK0 ) ),
    inference(superposition,[],[f1411,f20377])).

fof(f20377,plain,(
    ! [X6] :
      ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK3),X6)
      | k1_xboole_0 = sK0 ) ),
    inference(trivial_inequality_removal,[],[f20358])).

fof(f20358,plain,(
    ! [X6] :
      ( k1_xboole_0 != k1_xboole_0
      | k1_xboole_0 = sK0
      | k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK3),X6) ) ),
    inference(superposition,[],[f50,f20342])).

fof(f20342,plain,(
    ! [X2] : k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(k4_xboole_0(sK1,sK3),X2)) ),
    inference(resolution,[],[f18617,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f18617,plain,(
    ! [X14] : v1_xboole_0(k2_zfmisc_1(sK0,k4_xboole_0(k4_xboole_0(sK1,sK3),X14))) ),
    inference(superposition,[],[f18580,f3500])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f34,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:54:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (18176)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (18161)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.47  % (18172)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.47  % (18176)Refutation not found, incomplete strategy% (18176)------------------------------
% 0.21/0.47  % (18176)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (18176)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (18176)Memory used [KB]: 10618
% 0.21/0.47  % (18176)Time elapsed: 0.064 s
% 0.21/0.47  % (18176)------------------------------
% 0.21/0.47  % (18176)------------------------------
% 0.21/0.48  % (18168)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (18170)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (18166)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.49  % (18167)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.49  % (18158)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  % (18155)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (18156)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (18156)Refutation not found, incomplete strategy% (18156)------------------------------
% 0.21/0.50  % (18156)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (18156)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (18156)Memory used [KB]: 10618
% 0.21/0.50  % (18156)Time elapsed: 0.083 s
% 0.21/0.50  % (18156)------------------------------
% 0.21/0.50  % (18156)------------------------------
% 0.21/0.50  % (18169)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.50  % (18159)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (18171)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.51  % (18162)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.51  % (18160)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.51  % (18173)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.51  % (18164)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.51  % (18163)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.52  % (18174)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.52  % (18175)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.52  % (18165)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 4.20/0.92  % (18168)Time limit reached!
% 4.20/0.92  % (18168)------------------------------
% 4.20/0.92  % (18168)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.20/0.92  % (18168)Termination reason: Time limit
% 4.20/0.92  
% 4.20/0.92  % (18168)Memory used [KB]: 11385
% 4.20/0.92  % (18168)Time elapsed: 0.501 s
% 4.20/0.92  % (18168)------------------------------
% 4.20/0.92  % (18168)------------------------------
% 4.54/0.93  % (18161)Time limit reached!
% 4.54/0.93  % (18161)------------------------------
% 4.54/0.93  % (18161)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.54/0.93  % (18161)Termination reason: Time limit
% 4.54/0.93  
% 4.54/0.93  % (18161)Memory used [KB]: 9338
% 4.54/0.93  % (18161)Time elapsed: 0.511 s
% 4.54/0.93  % (18161)------------------------------
% 4.54/0.93  % (18161)------------------------------
% 4.54/0.93  % (18166)Time limit reached!
% 4.54/0.93  % (18166)------------------------------
% 4.54/0.93  % (18166)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.54/0.93  % (18166)Termination reason: Time limit
% 4.54/0.93  
% 4.54/0.93  % (18166)Memory used [KB]: 10362
% 4.54/0.93  % (18166)Time elapsed: 0.525 s
% 4.54/0.93  % (18166)------------------------------
% 4.54/0.93  % (18166)------------------------------
% 4.65/0.94  % (18155)Time limit reached!
% 4.65/0.94  % (18155)------------------------------
% 4.65/0.94  % (18155)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.65/0.94  % (18155)Termination reason: Time limit
% 4.65/0.94  % (18155)Termination phase: Saturation
% 4.65/0.94  
% 4.65/0.94  % (18155)Memory used [KB]: 14456
% 4.65/0.94  % (18155)Time elapsed: 0.505 s
% 4.65/0.94  % (18155)------------------------------
% 4.65/0.94  % (18155)------------------------------
% 5.22/1.01  % (18164)Time limit reached!
% 5.22/1.01  % (18164)------------------------------
% 5.22/1.01  % (18164)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.22/1.01  % (18164)Termination reason: Time limit
% 5.22/1.01  
% 5.22/1.01  % (18164)Memory used [KB]: 10746
% 5.22/1.01  % (18164)Time elapsed: 0.607 s
% 5.22/1.01  % (18164)------------------------------
% 5.22/1.01  % (18164)------------------------------
% 5.78/1.11  % (18169)Refutation found. Thanks to Tanya!
% 5.78/1.11  % SZS status Theorem for theBenchmark
% 5.78/1.11  % SZS output start Proof for theBenchmark
% 5.78/1.11  fof(f21556,plain,(
% 5.78/1.11    $false),
% 5.78/1.11    inference(subsumption_resolution,[],[f21107,f64])).
% 5.78/1.11  fof(f64,plain,(
% 5.78/1.11    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 5.78/1.11    inference(equality_resolution,[],[f51])).
% 5.78/1.11  fof(f51,plain,(
% 5.78/1.11    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 5.78/1.11    inference(cnf_transformation,[],[f14])).
% 5.78/1.11  fof(f14,axiom,(
% 5.78/1.11    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 5.78/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 5.78/1.11  fof(f21107,plain,(
% 5.78/1.11    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)),
% 5.78/1.11    inference(backward_demodulation,[],[f34,f21104])).
% 5.78/1.11  fof(f21104,plain,(
% 5.78/1.11    k1_xboole_0 = sK0),
% 5.78/1.11    inference(subsumption_resolution,[],[f21063,f19378])).
% 5.78/1.11  fof(f19378,plain,(
% 5.78/1.11    k1_xboole_0 != k4_xboole_0(sK1,sK3)),
% 5.78/1.11    inference(trivial_inequality_removal,[],[f18751])).
% 5.78/1.11  fof(f18751,plain,(
% 5.78/1.11    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 != k4_xboole_0(sK1,sK3)),
% 5.78/1.11    inference(backward_demodulation,[],[f77,f18750])).
% 5.78/1.11  fof(f18750,plain,(
% 5.78/1.11    k1_xboole_0 = k4_xboole_0(sK0,sK2)),
% 5.78/1.11    inference(subsumption_resolution,[],[f18614,f4175])).
% 5.78/1.11  fof(f4175,plain,(
% 5.78/1.11    ~v1_xboole_0(k2_zfmisc_1(sK0,sK1))),
% 5.78/1.11    inference(resolution,[],[f4173,f39])).
% 5.78/1.11  fof(f39,plain,(
% 5.78/1.11    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 5.78/1.11    inference(cnf_transformation,[],[f2])).
% 5.78/1.11  fof(f2,axiom,(
% 5.78/1.11    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 5.78/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 5.78/1.11  fof(f4173,plain,(
% 5.78/1.11    r2_hidden(sK5(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))),
% 5.78/1.11    inference(subsumption_resolution,[],[f4172,f34])).
% 5.78/1.11  fof(f4172,plain,(
% 5.78/1.11    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | r2_hidden(sK5(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))),
% 5.78/1.11    inference(forward_demodulation,[],[f4168,f1173])).
% 5.78/1.11  fof(f1173,plain,(
% 5.78/1.11    ( ! [X7] : (k3_xboole_0(X7,X7) = X7) )),
% 5.78/1.11    inference(resolution,[],[f1137,f45])).
% 5.78/1.11  fof(f45,plain,(
% 5.78/1.11    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 5.78/1.11    inference(cnf_transformation,[],[f26])).
% 5.78/1.11  fof(f26,plain,(
% 5.78/1.11    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 5.78/1.11    inference(ennf_transformation,[],[f9])).
% 5.78/1.11  fof(f9,axiom,(
% 5.78/1.11    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 5.78/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 5.78/1.11  fof(f1137,plain,(
% 5.78/1.11    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 5.78/1.11    inference(subsumption_resolution,[],[f1128,f34])).
% 5.78/1.11  fof(f1128,plain,(
% 5.78/1.11    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | r1_tarski(X0,X0)) )),
% 5.78/1.11    inference(resolution,[],[f1121,f61])).
% 5.78/1.11  fof(f61,plain,(
% 5.78/1.11    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(X1,X2)) )),
% 5.78/1.11    inference(cnf_transformation,[],[f31])).
% 5.78/1.11  fof(f31,plain,(
% 5.78/1.11    ! [X0,X1,X2] : (r1_tarski(X1,X2) | (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) & ~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) | k1_xboole_0 = X0)),
% 5.78/1.11    inference(ennf_transformation,[],[f15])).
% 5.78/1.11  fof(f15,axiom,(
% 5.78/1.11    ! [X0,X1,X2] : ~(~r1_tarski(X1,X2) & (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) & k1_xboole_0 != X0)),
% 5.78/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_zfmisc_1)).
% 5.78/1.11  fof(f1121,plain,(
% 5.78/1.11    ( ! [X0] : (r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0))) )),
% 5.78/1.11    inference(forward_demodulation,[],[f1113,f424])).
% 5.78/1.11  fof(f424,plain,(
% 5.78/1.11    ( ! [X2] : (k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X2) = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k3_xboole_0(X2,X2))) )),
% 5.78/1.11    inference(forward_demodulation,[],[f406,f73])).
% 5.78/1.11  fof(f73,plain,(
% 5.78/1.11    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 5.78/1.11    inference(resolution,[],[f33,f45])).
% 5.78/1.11  fof(f33,plain,(
% 5.78/1.11    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 5.78/1.11    inference(cnf_transformation,[],[f23])).
% 5.78/1.11  fof(f23,plain,(
% 5.78/1.11    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 5.78/1.11    inference(flattening,[],[f22])).
% 5.78/1.11  fof(f22,plain,(
% 5.78/1.11    ? [X0,X1,X2,X3] : (((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1)) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 5.78/1.11    inference(ennf_transformation,[],[f20])).
% 5.78/1.11  fof(f20,negated_conjecture,(
% 5.78/1.11    ~! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 5.78/1.11    inference(negated_conjecture,[],[f19])).
% 5.78/1.11  fof(f19,conjecture,(
% 5.78/1.11    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 5.78/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).
% 5.78/1.11  fof(f406,plain,(
% 5.78/1.11    ( ! [X2] : (k2_zfmisc_1(k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)),X2) = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k3_xboole_0(X2,X2))) )),
% 5.78/1.11    inference(superposition,[],[f194,f53])).
% 5.78/1.11  fof(f53,plain,(
% 5.78/1.11    ( ! [X2,X0,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 5.78/1.11    inference(cnf_transformation,[],[f17])).
% 5.78/1.11  fof(f17,axiom,(
% 5.78/1.11    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 5.78/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t122_zfmisc_1)).
% 5.78/1.11  fof(f194,plain,(
% 5.78/1.11    ( ! [X2,X1] : (k3_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X1),k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),X2)) = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k3_xboole_0(X1,X2))) )),
% 5.78/1.11    inference(superposition,[],[f62,f73])).
% 5.78/1.11  fof(f62,plain,(
% 5.78/1.11    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 5.78/1.11    inference(cnf_transformation,[],[f18])).
% 5.78/1.11  fof(f18,axiom,(
% 5.78/1.11    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 5.78/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 5.78/1.11  fof(f1113,plain,(
% 5.78/1.11    ( ! [X0] : (r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k3_xboole_0(X0,X0)))) )),
% 5.78/1.11    inference(superposition,[],[f1081,f36])).
% 5.78/1.11  fof(f36,plain,(
% 5.78/1.11    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 5.78/1.11    inference(cnf_transformation,[],[f8])).
% 5.78/1.11  fof(f8,axiom,(
% 5.78/1.11    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 5.78/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 5.78/1.11  fof(f1081,plain,(
% 5.78/1.11    ( ! [X6,X5] : (r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X5),k2_zfmisc_1(k2_xboole_0(k2_zfmisc_1(sK0,sK1),X6),k3_xboole_0(X5,X5)))) )),
% 5.78/1.11    inference(resolution,[],[f750,f41])).
% 5.78/1.11  fof(f41,plain,(
% 5.78/1.11    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 5.78/1.11    inference(cnf_transformation,[],[f13])).
% 5.78/1.11  fof(f13,axiom,(
% 5.78/1.11    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 5.78/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 5.78/1.11  fof(f750,plain,(
% 5.78/1.11    ( ! [X23,X22] : (~r1_tarski(k2_zfmisc_1(sK0,sK1),X23) | r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X22),k2_zfmisc_1(X23,k3_xboole_0(X22,X22)))) )),
% 5.78/1.11    inference(superposition,[],[f55,f424])).
% 5.78/1.11  fof(f55,plain,(
% 5.78/1.11    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 5.78/1.11    inference(cnf_transformation,[],[f27])).
% 5.78/1.11  fof(f27,plain,(
% 5.78/1.11    ! [X0,X1,X2] : ((r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X1))),
% 5.78/1.11    inference(ennf_transformation,[],[f16])).
% 5.78/1.11  fof(f16,axiom,(
% 5.78/1.11    ! [X0,X1,X2] : (r1_tarski(X0,X1) => (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))))),
% 5.78/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).
% 5.78/1.11  fof(f4168,plain,(
% 5.78/1.11    r2_hidden(sK5(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)) | k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1))),
% 5.78/1.11    inference(superposition,[],[f984,f73])).
% 5.78/1.11  fof(f984,plain,(
% 5.78/1.11    ( ! [X4] : (r2_hidden(sK5(k2_zfmisc_1(sK2,sK3),X4),k3_xboole_0(X4,k2_zfmisc_1(sK2,sK3))) | k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(sK0,sK1),X4)) )),
% 5.78/1.11    inference(superposition,[],[f286,f42])).
% 5.78/1.11  fof(f42,plain,(
% 5.78/1.11    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 5.78/1.11    inference(cnf_transformation,[],[f1])).
% 5.78/1.11  fof(f1,axiom,(
% 5.78/1.11    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 5.78/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 5.78/1.11  fof(f286,plain,(
% 5.78/1.11    ( ! [X2] : (r2_hidden(sK5(k2_zfmisc_1(sK2,sK3),X2),k3_xboole_0(k2_zfmisc_1(sK2,sK3),X2)) | k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(sK0,sK1),X2)) )),
% 5.78/1.11    inference(resolution,[],[f121,f47])).
% 5.78/1.11  fof(f47,plain,(
% 5.78/1.11    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 5.78/1.11    inference(cnf_transformation,[],[f3])).
% 5.78/1.11  fof(f3,axiom,(
% 5.78/1.11    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 5.78/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 5.78/1.11  fof(f121,plain,(
% 5.78/1.11    ( ! [X5] : (r1_xboole_0(k2_zfmisc_1(sK0,sK1),X5) | r2_hidden(sK5(k2_zfmisc_1(sK2,sK3),X5),k3_xboole_0(k2_zfmisc_1(sK2,sK3),X5))) )),
% 5.78/1.11    inference(resolution,[],[f69,f44])).
% 5.78/1.11  fof(f44,plain,(
% 5.78/1.11    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1))) )),
% 5.78/1.11    inference(cnf_transformation,[],[f25])).
% 5.78/1.11  fof(f25,plain,(
% 5.78/1.11    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 5.78/1.11    inference(ennf_transformation,[],[f21])).
% 5.78/1.11  fof(f21,plain,(
% 5.78/1.11    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 5.78/1.11    inference(rectify,[],[f5])).
% 5.78/1.11  fof(f5,axiom,(
% 5.78/1.11    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 5.78/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 5.78/1.11  fof(f69,plain,(
% 5.78/1.11    ( ! [X0] : (~r1_xboole_0(k2_zfmisc_1(sK2,sK3),X0) | r1_xboole_0(k2_zfmisc_1(sK0,sK1),X0)) )),
% 5.78/1.11    inference(resolution,[],[f33,f59])).
% 5.78/1.11  fof(f59,plain,(
% 5.78/1.11    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2)) )),
% 5.78/1.11    inference(cnf_transformation,[],[f30])).
% 5.78/1.11  fof(f30,plain,(
% 5.78/1.11    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 5.78/1.11    inference(flattening,[],[f29])).
% 5.78/1.11  fof(f29,plain,(
% 5.78/1.11    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 5.78/1.11    inference(ennf_transformation,[],[f11])).
% 5.78/1.11  fof(f11,axiom,(
% 5.78/1.11    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 5.78/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 5.78/1.11  fof(f18614,plain,(
% 5.78/1.11    v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | k1_xboole_0 = k4_xboole_0(sK0,sK2)),
% 5.78/1.11    inference(superposition,[],[f18580,f13825])).
% 5.78/1.11  fof(f13825,plain,(
% 5.78/1.11    ( ! [X7] : (k1_xboole_0 = k4_xboole_0(sK0,sK2) | sK1 = k3_xboole_0(sK1,X7)) )),
% 5.78/1.11    inference(resolution,[],[f13726,f45])).
% 5.78/1.11  fof(f13726,plain,(
% 5.78/1.11    ( ! [X157] : (r1_tarski(sK1,X157) | k1_xboole_0 = k4_xboole_0(sK0,sK2)) )),
% 5.78/1.11    inference(trivial_inequality_removal,[],[f13698])).
% 5.78/1.11  fof(f13698,plain,(
% 5.78/1.11    ( ! [X157] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(sK1,X157) | k1_xboole_0 = k4_xboole_0(sK0,sK2)) )),
% 5.78/1.11    inference(superposition,[],[f1311,f13287])).
% 5.78/1.11  fof(f13287,plain,(
% 5.78/1.11    ( ! [X4] : (k1_xboole_0 = k4_xboole_0(sK1,X4) | k1_xboole_0 = k4_xboole_0(sK0,sK2)) )),
% 5.78/1.11    inference(superposition,[],[f8310,f1299])).
% 5.78/1.11  fof(f1299,plain,(
% 5.78/1.11    ( ! [X12,X11] : (k4_xboole_0(X11,X12) = k3_xboole_0(k4_xboole_0(X11,X12),X11)) )),
% 5.78/1.11    inference(resolution,[],[f1174,f45])).
% 5.78/1.11  fof(f1174,plain,(
% 5.78/1.11    ( ! [X8,X9] : (r1_tarski(k4_xboole_0(X8,X9),X8)) )),
% 5.78/1.11    inference(resolution,[],[f1137,f57])).
% 5.78/1.11  fof(f57,plain,(
% 5.78/1.11    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_tarski(X0,X1)) )),
% 5.78/1.11    inference(cnf_transformation,[],[f28])).
% 5.78/1.11  fof(f28,plain,(
% 5.78/1.11    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 5.78/1.11    inference(ennf_transformation,[],[f7])).
% 5.78/1.11  fof(f7,axiom,(
% 5.78/1.11    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 5.78/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).
% 5.78/1.11  fof(f8310,plain,(
% 5.78/1.11    ( ! [X15,X16] : (k1_xboole_0 = k4_xboole_0(sK1,X15) | k1_xboole_0 = k3_xboole_0(k4_xboole_0(sK0,sK2),X16)) )),
% 5.78/1.11    inference(resolution,[],[f8080,f47])).
% 5.78/1.11  fof(f8080,plain,(
% 5.78/1.11    ( ! [X364,X365] : (r1_xboole_0(k4_xboole_0(sK0,sK2),X364) | k1_xboole_0 = k4_xboole_0(sK1,X365)) )),
% 5.78/1.11    inference(trivial_inequality_removal,[],[f7974])).
% 5.78/1.11  fof(f7974,plain,(
% 5.78/1.11    ( ! [X364,X365] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k4_xboole_0(sK0,sK2),X364) | k1_xboole_0 = k4_xboole_0(sK1,X365)) )),
% 5.78/1.11    inference(superposition,[],[f1411,f5815])).
% 5.78/1.11  fof(f5815,plain,(
% 5.78/1.11    ( ! [X10,X11] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),X10) | k1_xboole_0 = k4_xboole_0(sK1,X11)) )),
% 5.78/1.11    inference(resolution,[],[f5516,f48])).
% 5.78/1.11  fof(f48,plain,(
% 5.78/1.11    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 5.78/1.11    inference(cnf_transformation,[],[f6])).
% 5.78/1.11  fof(f6,axiom,(
% 5.78/1.11    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 5.78/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 5.78/1.11  fof(f5516,plain,(
% 5.78/1.11    ( ! [X33,X34] : (r1_tarski(sK1,X34) | k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),X33)) )),
% 5.78/1.11    inference(subsumption_resolution,[],[f5499,f35])).
% 5.78/1.11  fof(f35,plain,(
% 5.78/1.11    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 5.78/1.11    inference(cnf_transformation,[],[f10])).
% 5.78/1.11  fof(f10,axiom,(
% 5.78/1.11    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 5.78/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 5.78/1.11  fof(f5499,plain,(
% 5.78/1.11    ( ! [X33,X34] : (~r1_tarski(k1_xboole_0,k2_zfmisc_1(k4_xboole_0(k4_xboole_0(sK0,sK2),X33),X34)) | k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),X33) | r1_tarski(sK1,X34)) )),
% 5.78/1.11    inference(superposition,[],[f61,f5417])).
% 5.78/1.11  fof(f5417,plain,(
% 5.78/1.11    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(k4_xboole_0(sK0,sK2),X0),sK1)) )),
% 5.78/1.11    inference(superposition,[],[f5367,f3500])).
% 5.78/1.11  fof(f3500,plain,(
% 5.78/1.11    ( ! [X14,X15,X16] : (k4_xboole_0(k4_xboole_0(X14,X15),X16) = k3_xboole_0(X14,k4_xboole_0(k4_xboole_0(X14,X15),X16))) )),
% 5.78/1.11    inference(superposition,[],[f1445,f42])).
% 5.78/1.11  fof(f1445,plain,(
% 5.78/1.11    ( ! [X17,X15,X16] : (k4_xboole_0(k4_xboole_0(X15,X16),X17) = k3_xboole_0(k4_xboole_0(k4_xboole_0(X15,X16),X17),X15)) )),
% 5.78/1.11    inference(resolution,[],[f1300,f45])).
% 5.78/1.11  fof(f1300,plain,(
% 5.78/1.11    ( ! [X14,X15,X13] : (r1_tarski(k4_xboole_0(k4_xboole_0(X13,X14),X15),X13)) )),
% 5.78/1.11    inference(resolution,[],[f1174,f57])).
% 5.78/1.11  fof(f5367,plain,(
% 5.78/1.11    ( ! [X6,X5] : (k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(sK0,k4_xboole_0(k4_xboole_0(X5,sK2),X6)),sK1)) )),
% 5.78/1.11    inference(superposition,[],[f3635,f53])).
% 5.78/1.11  fof(f3635,plain,(
% 5.78/1.11    ( ! [X21,X22,X20] : (k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k4_xboole_0(k4_xboole_0(X20,sK2),X21),X22))) )),
% 5.78/1.11    inference(subsumption_resolution,[],[f3578,f91])).
% 5.78/1.11  fof(f91,plain,(
% 5.78/1.11    v1_xboole_0(k1_xboole_0)),
% 5.78/1.11    inference(resolution,[],[f90,f38])).
% 5.78/1.11  fof(f38,plain,(
% 5.78/1.11    ( ! [X0] : (r2_hidden(sK4(X0),X0) | v1_xboole_0(X0)) )),
% 5.78/1.11    inference(cnf_transformation,[],[f2])).
% 5.78/1.11  fof(f90,plain,(
% 5.78/1.11    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) )),
% 5.78/1.11    inference(forward_demodulation,[],[f84,f83])).
% 5.78/1.11  fof(f83,plain,(
% 5.78/1.11    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(sK2,sK3))),
% 5.78/1.11    inference(resolution,[],[f81,f47])).
% 5.78/1.11  fof(f81,plain,(
% 5.78/1.11    r1_xboole_0(k1_xboole_0,k2_zfmisc_1(sK2,sK3))),
% 5.78/1.11    inference(superposition,[],[f40,f72])).
% 5.78/1.11  fof(f72,plain,(
% 5.78/1.11    k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 5.78/1.11    inference(resolution,[],[f33,f48])).
% 5.78/1.11  fof(f40,plain,(
% 5.78/1.11    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 5.78/1.11    inference(cnf_transformation,[],[f12])).
% 5.78/1.12  fof(f12,axiom,(
% 5.78/1.12    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 5.78/1.12    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 5.78/1.12  fof(f84,plain,(
% 5.78/1.12    ( ! [X1] : (~r2_hidden(X1,k3_xboole_0(k1_xboole_0,k2_zfmisc_1(sK2,sK3)))) )),
% 5.78/1.12    inference(resolution,[],[f81,f43])).
% 5.78/1.12  fof(f43,plain,(
% 5.78/1.12    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 5.78/1.12    inference(cnf_transformation,[],[f25])).
% 5.78/1.12  fof(f3578,plain,(
% 5.78/1.12    ( ! [X21,X22,X20] : (~v1_xboole_0(k1_xboole_0) | k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k4_xboole_0(k4_xboole_0(X20,sK2),X21),X22))) )),
% 5.78/1.12    inference(superposition,[],[f992,f1827])).
% 5.78/1.12  fof(f1827,plain,(
% 5.78/1.12    ( ! [X26,X24,X23,X25,X22] : (k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(k4_xboole_0(k4_xboole_0(X22,X23),X24),X25),k2_zfmisc_1(X23,X26))) )),
% 5.78/1.12    inference(forward_demodulation,[],[f1812,f64])).
% 5.78/1.12  fof(f1812,plain,(
% 5.78/1.12    ( ! [X26,X24,X23,X25,X22] : (k2_zfmisc_1(k1_xboole_0,k3_xboole_0(X25,X26)) = k3_xboole_0(k2_zfmisc_1(k4_xboole_0(k4_xboole_0(X22,X23),X24),X25),k2_zfmisc_1(X23,X26))) )),
% 5.78/1.12    inference(superposition,[],[f62,f1476])).
% 5.78/1.12  fof(f1476,plain,(
% 5.78/1.12    ( ! [X6,X4,X5] : (k1_xboole_0 = k3_xboole_0(k4_xboole_0(k4_xboole_0(X4,X5),X6),X5)) )),
% 5.78/1.12    inference(resolution,[],[f1301,f47])).
% 5.78/1.12  fof(f1301,plain,(
% 5.78/1.12    ( ! [X17,X18,X16] : (r1_xboole_0(k4_xboole_0(k4_xboole_0(X16,X17),X18),X17)) )),
% 5.78/1.12    inference(resolution,[],[f1174,f58])).
% 5.78/1.12  fof(f58,plain,(
% 5.78/1.12    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 5.78/1.12    inference(cnf_transformation,[],[f28])).
% 5.78/1.12  fof(f992,plain,(
% 5.78/1.12    ( ! [X4] : (~v1_xboole_0(k3_xboole_0(X4,k2_zfmisc_1(sK2,sK3))) | k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(sK0,sK1),X4)) )),
% 5.78/1.12    inference(superposition,[],[f979,f42])).
% 5.78/1.12  fof(f979,plain,(
% 5.78/1.12    ( ! [X1] : (~v1_xboole_0(k3_xboole_0(k2_zfmisc_1(sK2,sK3),X1)) | k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(sK0,sK1),X1)) )),
% 5.78/1.12    inference(resolution,[],[f286,f39])).
% 5.78/1.12  fof(f1411,plain,(
% 5.78/1.12    ( ! [X10,X9] : (k1_xboole_0 != k4_xboole_0(X9,k1_xboole_0) | r1_xboole_0(X9,X10)) )),
% 5.78/1.12    inference(resolution,[],[f1238,f49])).
% 5.78/1.12  fof(f49,plain,(
% 5.78/1.12    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 5.78/1.12    inference(cnf_transformation,[],[f6])).
% 5.78/1.12  fof(f1238,plain,(
% 5.78/1.12    ( ! [X2,X3] : (~r1_tarski(X3,k1_xboole_0) | r1_xboole_0(X3,X2)) )),
% 5.78/1.12    inference(superposition,[],[f58,f1172])).
% 5.78/1.12  fof(f1172,plain,(
% 5.78/1.12    ( ! [X6] : (k1_xboole_0 = k4_xboole_0(X6,X6)) )),
% 5.78/1.12    inference(resolution,[],[f1137,f48])).
% 5.78/1.12  fof(f1311,plain,(
% 5.78/1.12    ( ! [X10,X9] : (k1_xboole_0 != k4_xboole_0(X9,k1_xboole_0) | r1_tarski(X9,X10)) )),
% 5.78/1.12    inference(resolution,[],[f1237,f49])).
% 5.78/1.12  fof(f1237,plain,(
% 5.78/1.12    ( ! [X0,X1] : (~r1_tarski(X1,k1_xboole_0) | r1_tarski(X1,X0)) )),
% 5.78/1.12    inference(superposition,[],[f57,f1172])).
% 5.78/1.12  fof(f18580,plain,(
% 5.78/1.12    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(sK0,k3_xboole_0(sK1,k4_xboole_0(k4_xboole_0(X0,sK3),X1))))) )),
% 5.78/1.12    inference(subsumption_resolution,[],[f18565,f90])).
% 5.78/1.12  fof(f18565,plain,(
% 5.78/1.12    ( ! [X0,X1] : (r2_hidden(sK5(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,k4_xboole_0(k4_xboole_0(X0,sK3),X1))),k1_xboole_0) | v1_xboole_0(k2_zfmisc_1(sK0,k3_xboole_0(sK1,k4_xboole_0(k4_xboole_0(X0,sK3),X1))))) )),
% 5.78/1.12    inference(superposition,[],[f5895,f1915])).
% 5.78/1.12  fof(f1915,plain,(
% 5.78/1.12    ( ! [X30,X28,X31,X29,X27] : (k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(X30,X27),k2_zfmisc_1(X31,k4_xboole_0(k4_xboole_0(X28,X27),X29)))) )),
% 5.78/1.12    inference(forward_demodulation,[],[f1899,f63])).
% 5.78/1.12  fof(f63,plain,(
% 5.78/1.12    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 5.78/1.12    inference(equality_resolution,[],[f52])).
% 5.78/1.12  fof(f52,plain,(
% 5.78/1.12    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 5.78/1.12    inference(cnf_transformation,[],[f14])).
% 5.78/1.12  fof(f1899,plain,(
% 5.78/1.12    ( ! [X30,X28,X31,X29,X27] : (k2_zfmisc_1(k3_xboole_0(X30,X31),k1_xboole_0) = k3_xboole_0(k2_zfmisc_1(X30,X27),k2_zfmisc_1(X31,k4_xboole_0(k4_xboole_0(X28,X27),X29)))) )),
% 5.78/1.12    inference(superposition,[],[f62,f1804])).
% 5.78/1.12  fof(f1804,plain,(
% 5.78/1.12    ( ! [X10,X11,X9] : (k1_xboole_0 = k3_xboole_0(X10,k4_xboole_0(k4_xboole_0(X9,X10),X11))) )),
% 5.78/1.12    inference(superposition,[],[f1476,f42])).
% 5.78/1.12  fof(f5895,plain,(
% 5.78/1.12    ( ! [X0] : (r2_hidden(sK5(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,X0)),k3_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,X0))) | v1_xboole_0(k2_zfmisc_1(sK0,k3_xboole_0(sK1,X0)))) )),
% 5.78/1.12    inference(resolution,[],[f1042,f38])).
% 5.78/1.12  fof(f1042,plain,(
% 5.78/1.12    ( ! [X2,X1] : (~r2_hidden(X2,k2_zfmisc_1(sK0,k3_xboole_0(sK1,X1))) | r2_hidden(sK5(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,X1)),k3_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,X1)))) )),
% 5.78/1.12    inference(superposition,[],[f287,f54])).
% 5.78/1.12  fof(f54,plain,(
% 5.78/1.12    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 5.78/1.12    inference(cnf_transformation,[],[f17])).
% 5.78/1.12  fof(f287,plain,(
% 5.78/1.12    ( ! [X4,X3] : (~r2_hidden(X4,k3_xboole_0(k2_zfmisc_1(sK0,sK1),X3)) | r2_hidden(sK5(k2_zfmisc_1(sK2,sK3),X3),k3_xboole_0(k2_zfmisc_1(sK2,sK3),X3))) )),
% 5.78/1.12    inference(resolution,[],[f121,f43])).
% 5.78/1.12  fof(f77,plain,(
% 5.78/1.12    k1_xboole_0 != k4_xboole_0(sK1,sK3) | k1_xboole_0 != k4_xboole_0(sK0,sK2)),
% 5.78/1.12    inference(resolution,[],[f68,f49])).
% 5.78/1.12  fof(f68,plain,(
% 5.78/1.12    ~r1_tarski(sK0,sK2) | k1_xboole_0 != k4_xboole_0(sK1,sK3)),
% 5.78/1.12    inference(resolution,[],[f32,f49])).
% 5.78/1.12  fof(f32,plain,(
% 5.78/1.12    ~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)),
% 5.78/1.12    inference(cnf_transformation,[],[f23])).
% 5.78/1.12  fof(f21063,plain,(
% 5.78/1.12    k1_xboole_0 = k4_xboole_0(sK1,sK3) | k1_xboole_0 = sK0),
% 5.78/1.12    inference(superposition,[],[f20920,f1299])).
% 5.78/1.12  fof(f20920,plain,(
% 5.78/1.12    ( ! [X11] : (k1_xboole_0 = k3_xboole_0(k4_xboole_0(sK1,sK3),X11) | k1_xboole_0 = sK0) )),
% 5.78/1.12    inference(resolution,[],[f20767,f47])).
% 5.78/1.12  fof(f20767,plain,(
% 5.78/1.12    ( ! [X221] : (r1_xboole_0(k4_xboole_0(sK1,sK3),X221) | k1_xboole_0 = sK0) )),
% 5.78/1.12    inference(trivial_inequality_removal,[],[f20737])).
% 5.78/1.12  fof(f20737,plain,(
% 5.78/1.12    ( ! [X221] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k4_xboole_0(sK1,sK3),X221) | k1_xboole_0 = sK0) )),
% 5.78/1.12    inference(superposition,[],[f1411,f20377])).
% 5.78/1.12  fof(f20377,plain,(
% 5.78/1.12    ( ! [X6] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK3),X6) | k1_xboole_0 = sK0) )),
% 5.78/1.12    inference(trivial_inequality_removal,[],[f20358])).
% 5.78/1.12  fof(f20358,plain,(
% 5.78/1.12    ( ! [X6] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK3),X6)) )),
% 5.78/1.12    inference(superposition,[],[f50,f20342])).
% 5.78/1.12  fof(f20342,plain,(
% 5.78/1.12    ( ! [X2] : (k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(k4_xboole_0(sK1,sK3),X2))) )),
% 5.78/1.12    inference(resolution,[],[f18617,f37])).
% 5.78/1.12  fof(f37,plain,(
% 5.78/1.12    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 5.78/1.12    inference(cnf_transformation,[],[f24])).
% 5.78/1.12  fof(f24,plain,(
% 5.78/1.12    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 5.78/1.12    inference(ennf_transformation,[],[f4])).
% 5.78/1.12  fof(f4,axiom,(
% 5.78/1.12    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 5.78/1.12    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 5.78/1.12  fof(f18617,plain,(
% 5.78/1.12    ( ! [X14] : (v1_xboole_0(k2_zfmisc_1(sK0,k4_xboole_0(k4_xboole_0(sK1,sK3),X14)))) )),
% 5.78/1.12    inference(superposition,[],[f18580,f3500])).
% 5.78/1.12  fof(f50,plain,(
% 5.78/1.12    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 5.78/1.12    inference(cnf_transformation,[],[f14])).
% 5.78/1.12  fof(f34,plain,(
% 5.78/1.12    k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 5.78/1.12    inference(cnf_transformation,[],[f23])).
% 5.78/1.12  % SZS output end Proof for theBenchmark
% 5.78/1.12  % (18169)------------------------------
% 5.78/1.12  % (18169)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.78/1.12  % (18169)Termination reason: Refutation
% 5.78/1.12  
% 5.78/1.12  % (18169)Memory used [KB]: 10234
% 5.78/1.12  % (18169)Time elapsed: 0.663 s
% 5.78/1.12  % (18169)------------------------------
% 5.78/1.12  % (18169)------------------------------
% 5.78/1.12  % (18150)Success in time 0.762 s
%------------------------------------------------------------------------------
