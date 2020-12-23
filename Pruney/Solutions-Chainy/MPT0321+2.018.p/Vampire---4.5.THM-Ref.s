%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:31 EST 2020

% Result     : Theorem 6.76s
% Output     : Refutation 7.14s
% Verified   : 
% Statistics : Number of formulae       :  170 (2967 expanded)
%              Number of leaves         :   15 ( 681 expanded)
%              Depth                    :   58
%              Number of atoms          :  317 (7005 expanded)
%              Number of equality atoms :  147 (2339 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12670,plain,(
    $false ),
    inference(subsumption_resolution,[],[f12669,f6696])).

fof(f6696,plain,(
    r1_tarski(sK1,sK3) ),
    inference(duplicate_literal_removal,[],[f6689])).

fof(f6689,plain,
    ( r1_tarski(sK1,sK3)
    | r1_tarski(sK1,sK3) ),
    inference(resolution,[],[f6265,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f6265,plain,(
    ! [X19] :
      ( ~ r2_hidden(sK5(X19,sK3),sK1)
      | r1_tarski(X19,sK3) ) ),
    inference(resolution,[],[f6235,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f6235,plain,(
    ! [X28] :
      ( r2_hidden(X28,sK3)
      | ~ r2_hidden(X28,sK1) ) ),
    inference(subsumption_resolution,[],[f6144,f125])).

fof(f125,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,k1_xboole_0)
      | r2_hidden(X3,X2) ) ),
    inference(superposition,[],[f70,f121])).

fof(f121,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f120,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f120,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(factoring,[],[f116])).

fof(f116,plain,(
    ! [X2,X3] :
      ( r1_tarski(k1_xboole_0,X2)
      | r1_tarski(k1_xboole_0,X3) ) ),
    inference(resolution,[],[f114,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK7(X0),X0) ) ),
    inference(resolution,[],[f42,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(sK7(X1),X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK7(k1_xboole_0),X0)
      | r1_tarski(k1_xboole_0,X1) ) ),
    inference(superposition,[],[f81,f35])).

fof(f35,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f81,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(sK7(X2),k4_xboole_0(X3,X2))
      | r1_tarski(X2,X4) ) ),
    inference(resolution,[],[f67,f74])).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f70,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k3_xboole_0(X0,X1))
      | r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f6144,plain,(
    ! [X28] :
      ( r2_hidden(X28,k1_xboole_0)
      | r2_hidden(X28,sK3)
      | ~ r2_hidden(X28,sK1) ) ),
    inference(superposition,[],[f66,f6120])).

fof(f6120,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK3) ),
    inference(subsumption_resolution,[],[f6115,f33])).

fof(f33,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
       => ( ( X1 = X3
            & X0 = X2 )
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(f6115,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK3)
    | k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f6108])).

fof(f6108,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k4_xboole_0(sK1,sK3)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f44,f6069])).

fof(f6069,plain,(
    k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)) ),
    inference(superposition,[],[f5953,f809])).

fof(f809,plain,(
    ! [X2,X3] : k4_xboole_0(X2,X3) = k3_xboole_0(X2,k4_xboole_0(X2,X3)) ),
    inference(superposition,[],[f804,f39])).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f804,plain,(
    ! [X2,X3] : k4_xboole_0(X2,X3) = k3_xboole_0(k4_xboole_0(X2,X3),X2) ),
    inference(resolution,[],[f800,f40])).

fof(f800,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(duplicate_literal_removal,[],[f788])).

fof(f788,plain,(
    ! [X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X0)
      | r1_tarski(k4_xboole_0(X0,X1),X0) ) ),
    inference(resolution,[],[f87,f43])).

fof(f87,plain,(
    ! [X8,X7,X9] :
      ( r2_hidden(sK5(k4_xboole_0(X7,X8),X9),X7)
      | r1_tarski(k4_xboole_0(X7,X8),X9) ) ),
    inference(resolution,[],[f68,f42])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5953,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(sK0,k3_xboole_0(sK1,k4_xboole_0(X0,sK3))) ),
    inference(superposition,[],[f648,f1406])).

fof(f1406,plain,(
    ! [X12,X13] : k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X12,k4_xboole_0(X13,sK3))) ),
    inference(superposition,[],[f1314,f32])).

fof(f32,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f1314,plain,(
    ! [X12,X10,X11,X9] : k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(X11,X9),k2_zfmisc_1(X12,k4_xboole_0(X10,X9))) ),
    inference(forward_demodulation,[],[f1282,f64])).

fof(f64,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f1282,plain,(
    ! [X12,X10,X11,X9] : k3_xboole_0(k2_zfmisc_1(X11,X9),k2_zfmisc_1(X12,k4_xboole_0(X10,X9))) = k2_zfmisc_1(k3_xboole_0(X11,X12),k1_xboole_0) ),
    inference(superposition,[],[f63,f1265])).

fof(f1265,plain,(
    ! [X0,X1] : k1_xboole_0 = k3_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(resolution,[],[f1262,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f1262,plain,(
    ! [X4,X3] : v1_xboole_0(k3_xboole_0(X4,k4_xboole_0(X3,X4))) ),
    inference(forward_demodulation,[],[f1261,f39])).

fof(f1261,plain,(
    ! [X4,X3] : v1_xboole_0(k3_xboole_0(k4_xboole_0(X3,X4),X4)) ),
    inference(duplicate_literal_removal,[],[f1246])).

fof(f1246,plain,(
    ! [X4,X3] :
      ( v1_xboole_0(k3_xboole_0(k4_xboole_0(X3,X4),X4))
      | v1_xboole_0(k3_xboole_0(k4_xboole_0(X3,X4),X4)) ) ),
    inference(resolution,[],[f209,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(k3_xboole_0(X0,X1)),X0)
      | v1_xboole_0(k3_xboole_0(X0,X1)) ) ),
    inference(resolution,[],[f71,f37])).

fof(f37,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ? [X1] : r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
     => v1_xboole_0(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f71,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k3_xboole_0(X0,X1))
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f209,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(k3_xboole_0(X0,X1)),k4_xboole_0(X2,X1))
      | v1_xboole_0(k3_xboole_0(X0,X1)) ) ),
    inference(resolution,[],[f89,f67])).

fof(f89,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(k3_xboole_0(X0,X1)),X1)
      | v1_xboole_0(k3_xboole_0(X0,X1)) ) ),
    inference(resolution,[],[f70,f37])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f648,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) = k2_zfmisc_1(X0,k3_xboole_0(X1,X2)) ),
    inference(superposition,[],[f63,f38])).

fof(f38,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k4_xboole_0(X0,X1))
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f12669,plain,(
    ~ r1_tarski(sK1,sK3) ),
    inference(subsumption_resolution,[],[f12668,f11985])).

fof(f11985,plain,(
    sK1 != sK3 ),
    inference(trivial_inequality_removal,[],[f11319])).

fof(f11319,plain,
    ( sK0 != sK0
    | sK1 != sK3 ),
    inference(backward_demodulation,[],[f31,f11318])).

fof(f11318,plain,(
    sK0 = sK2 ),
    inference(subsumption_resolution,[],[f11317,f7847])).

fof(f7847,plain,(
    r1_tarski(sK0,sK2) ),
    inference(duplicate_literal_removal,[],[f7840])).

fof(f7840,plain,
    ( r1_tarski(sK0,sK2)
    | r1_tarski(sK0,sK2) ),
    inference(resolution,[],[f7396,f42])).

fof(f7396,plain,(
    ! [X23] :
      ( ~ r2_hidden(sK5(X23,sK2),sK0)
      | r1_tarski(X23,sK2) ) ),
    inference(resolution,[],[f7363,f43])).

fof(f7363,plain,(
    ! [X28] :
      ( r2_hidden(X28,sK2)
      | ~ r2_hidden(X28,sK0) ) ),
    inference(subsumption_resolution,[],[f7272,f125])).

fof(f7272,plain,(
    ! [X28] :
      ( r2_hidden(X28,k1_xboole_0)
      | r2_hidden(X28,sK2)
      | ~ r2_hidden(X28,sK0) ) ),
    inference(superposition,[],[f66,f7243])).

fof(f7243,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK2) ),
    inference(subsumption_resolution,[],[f7238,f34])).

fof(f34,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f22])).

fof(f7238,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = k4_xboole_0(sK0,sK2) ),
    inference(trivial_inequality_removal,[],[f7229])).

fof(f7229,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = k4_xboole_0(sK0,sK2) ),
    inference(superposition,[],[f44,f7183])).

fof(f7183,plain,(
    k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1) ),
    inference(superposition,[],[f6378,f809])).

fof(f6378,plain,(
    ! [X11] : k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(sK0,k4_xboole_0(X11,sK2)),sK1) ),
    inference(superposition,[],[f653,f1318])).

fof(f1318,plain,(
    ! [X12,X13] : k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k4_xboole_0(X12,sK2),X13)) ),
    inference(superposition,[],[f1313,f32])).

fof(f1313,plain,(
    ! [X6,X8,X7,X5] : k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(X5,X7),k2_zfmisc_1(k4_xboole_0(X6,X5),X8)) ),
    inference(forward_demodulation,[],[f1281,f65])).

fof(f65,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f1281,plain,(
    ! [X6,X8,X7,X5] : k3_xboole_0(k2_zfmisc_1(X5,X7),k2_zfmisc_1(k4_xboole_0(X6,X5),X8)) = k2_zfmisc_1(k1_xboole_0,k3_xboole_0(X7,X8)) ),
    inference(superposition,[],[f63,f1265])).

fof(f653,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) = k2_zfmisc_1(k3_xboole_0(X1,X2),X0) ),
    inference(superposition,[],[f63,f38])).

fof(f11317,plain,
    ( sK0 = sK2
    | ~ r1_tarski(sK0,sK2) ),
    inference(duplicate_literal_removal,[],[f11316])).

fof(f11316,plain,
    ( sK0 = sK2
    | sK0 = sK2
    | ~ r1_tarski(sK0,sK2) ),
    inference(resolution,[],[f11309,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f11309,plain,
    ( ~ r2_xboole_0(sK0,sK2)
    | sK0 = sK2 ),
    inference(resolution,[],[f11059,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1),X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ~ r2_hidden(X2,X0)
              & r2_hidden(X2,X1) )
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_0)).

fof(f11059,plain,
    ( r2_hidden(sK6(sK0,sK2),sK0)
    | sK0 = sK2 ),
    inference(resolution,[],[f11041,f7848])).

fof(f7848,plain,
    ( r2_hidden(sK6(sK0,sK2),sK2)
    | sK0 = sK2 ),
    inference(resolution,[],[f7847,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_hidden(sK6(X0,X1),X1) ) ),
    inference(resolution,[],[f41,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | r2_hidden(sK6(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f11041,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | r2_hidden(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f10967,f125])).

fof(f10967,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_xboole_0)
      | r2_hidden(X0,sK0)
      | ~ r2_hidden(X0,sK2) ) ),
    inference(superposition,[],[f66,f10936])).

fof(f10936,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,sK0) ),
    inference(subsumption_resolution,[],[f10935,f34])).

fof(f10935,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = k4_xboole_0(sK2,sK0) ),
    inference(trivial_inequality_removal,[],[f10926])).

fof(f10926,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = k4_xboole_0(sK2,sK0) ),
    inference(superposition,[],[f44,f10893])).

fof(f10893,plain,(
    k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK2,sK0),sK1) ),
    inference(superposition,[],[f10799,f6863])).

fof(f6863,plain,(
    sK1 = k3_xboole_0(sK3,sK1) ),
    inference(superposition,[],[f981,f6698])).

fof(f6698,plain,(
    sK1 = k3_xboole_0(sK1,sK3) ),
    inference(resolution,[],[f6696,f40])).

fof(f981,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,k3_xboole_0(X2,X3)) ),
    inference(superposition,[],[f956,f39])).

fof(f956,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(k3_xboole_0(X2,X3),X3) ),
    inference(resolution,[],[f952,f40])).

fof(f952,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X1) ),
    inference(duplicate_literal_removal,[],[f935])).

fof(f935,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X1),X1)
      | r1_tarski(k3_xboole_0(X0,X1),X1) ) ),
    inference(resolution,[],[f92,f43])).

fof(f92,plain,(
    ! [X8,X7,X9] :
      ( r2_hidden(sK5(k3_xboole_0(X7,X8),X9),X8)
      | r1_tarski(k3_xboole_0(X7,X8),X9) ) ),
    inference(resolution,[],[f70,f42])).

fof(f10799,plain,(
    ! [X2] : k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK2,sK0),k3_xboole_0(sK3,X2)) ),
    inference(forward_demodulation,[],[f10790,f121])).

fof(f10790,plain,(
    ! [X2] : k2_zfmisc_1(k4_xboole_0(sK2,sK0),k3_xboole_0(sK3,X2)) = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(k4_xboole_0(sK2,sK0),X2)) ),
    inference(superposition,[],[f648,f10761])).

fof(f10761,plain,(
    k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK2,sK0),sK3) ),
    inference(superposition,[],[f10741,f809])).

fof(f10741,plain,(
    ! [X5] : k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(sK2,k4_xboole_0(X5,sK0)),sK3) ),
    inference(forward_demodulation,[],[f10712,f65])).

fof(f10712,plain,(
    ! [X5] : k2_zfmisc_1(k1_xboole_0,sK1) = k2_zfmisc_1(k3_xboole_0(sK2,k4_xboole_0(X5,sK0)),sK3) ),
    inference(superposition,[],[f10413,f3984])).

fof(f3984,plain,(
    ! [X10,X9] : k1_xboole_0 = k3_xboole_0(k4_xboole_0(X9,X10),X10) ),
    inference(subsumption_resolution,[],[f3945,f36])).

fof(f3945,plain,(
    ! [X10,X9] :
      ( v1_xboole_0(k3_xboole_0(k4_xboole_0(X9,X10),X10))
      | k1_xboole_0 = k3_xboole_0(k4_xboole_0(X9,X10),X10) ) ),
    inference(resolution,[],[f311,f462])).

fof(f462,plain,(
    ! [X4,X5] :
      ( r2_hidden(sK7(k3_xboole_0(X4,X5)),X4)
      | k1_xboole_0 = k3_xboole_0(X4,X5) ) ),
    inference(resolution,[],[f453,f71])).

fof(f453,plain,(
    ! [X2] :
      ( r2_hidden(sK7(X2),X2)
      | k1_xboole_0 = X2 ) ),
    inference(resolution,[],[f448,f50])).

fof(f448,plain,(
    ! [X3] :
      ( r2_hidden(sK6(k1_xboole_0,X3),X3)
      | k1_xboole_0 = X3 ) ),
    inference(resolution,[],[f108,f120])).

fof(f311,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK7(k3_xboole_0(X0,X1)),k4_xboole_0(X2,X1))
      | v1_xboole_0(k3_xboole_0(X0,X1)) ) ),
    inference(resolution,[],[f91,f67])).

fof(f91,plain,(
    ! [X6,X5] :
      ( r2_hidden(sK7(k3_xboole_0(X5,X6)),X6)
      | v1_xboole_0(k3_xboole_0(X5,X6)) ) ),
    inference(resolution,[],[f70,f72])).

fof(f72,plain,(
    ! [X0] :
      ( r2_hidden(sK7(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f50,f37])).

fof(f10413,plain,(
    ! [X0] : k2_zfmisc_1(k3_xboole_0(sK2,X0),sK3) = k2_zfmisc_1(k3_xboole_0(X0,sK0),sK1) ),
    inference(superposition,[],[f6953,f39])).

fof(f6953,plain,(
    ! [X9] : k2_zfmisc_1(k3_xboole_0(X9,sK2),sK3) = k2_zfmisc_1(k3_xboole_0(X9,sK0),sK1) ),
    inference(backward_demodulation,[],[f6374,f6891])).

fof(f6891,plain,(
    ! [X2,X3] : k2_zfmisc_1(k3_xboole_0(X2,X3),sK1) = k3_xboole_0(k2_zfmisc_1(X2,sK3),k2_zfmisc_1(X3,sK1)) ),
    inference(superposition,[],[f63,f6863])).

fof(f6374,plain,(
    ! [X9] : k2_zfmisc_1(k3_xboole_0(X9,sK2),sK3) = k3_xboole_0(k2_zfmisc_1(X9,sK3),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f653,f32])).

fof(f31,plain,
    ( sK1 != sK3
    | sK0 != sK2 ),
    inference(cnf_transformation,[],[f22])).

fof(f12668,plain,
    ( sK1 = sK3
    | ~ r1_tarski(sK1,sK3) ),
    inference(resolution,[],[f12661,f41])).

fof(f12661,plain,(
    ~ r2_xboole_0(sK1,sK3) ),
    inference(resolution,[],[f12641,f48])).

fof(f12641,plain,(
    r2_hidden(sK6(sK1,sK3),sK1) ),
    inference(subsumption_resolution,[],[f12537,f11985])).

fof(f12537,plain,
    ( r2_hidden(sK6(sK1,sK3),sK1)
    | sK1 = sK3 ),
    inference(resolution,[],[f12519,f6697])).

fof(f6697,plain,
    ( r2_hidden(sK6(sK1,sK3),sK3)
    | sK1 = sK3 ),
    inference(resolution,[],[f6696,f108])).

fof(f12519,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3)
      | r2_hidden(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f12447,f125])).

fof(f12447,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_xboole_0)
      | r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,sK3) ) ),
    inference(superposition,[],[f66,f12368])).

fof(f12368,plain,(
    k1_xboole_0 = k4_xboole_0(sK3,sK1) ),
    inference(subsumption_resolution,[],[f12367,f33])).

fof(f12367,plain,
    ( k1_xboole_0 = k4_xboole_0(sK3,sK1)
    | k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f12358])).

fof(f12358,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k4_xboole_0(sK3,sK1)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f44,f12326])).

fof(f12326,plain,(
    k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK3,sK1)) ),
    inference(superposition,[],[f12300,f809])).

fof(f12300,plain,(
    ! [X5] : k1_xboole_0 = k2_zfmisc_1(sK0,k3_xboole_0(sK3,k4_xboole_0(X5,sK1))) ),
    inference(forward_demodulation,[],[f12274,f64])).

fof(f12274,plain,(
    ! [X5] : k2_zfmisc_1(sK0,k1_xboole_0) = k2_zfmisc_1(sK0,k3_xboole_0(sK3,k4_xboole_0(X5,sK1))) ),
    inference(superposition,[],[f11895,f3984])).

fof(f11895,plain,(
    ! [X0] : k2_zfmisc_1(sK0,k3_xboole_0(X0,sK1)) = k2_zfmisc_1(sK0,k3_xboole_0(sK3,X0)) ),
    inference(backward_demodulation,[],[f10591,f11318])).

fof(f10591,plain,(
    ! [X0] : k2_zfmisc_1(sK2,k3_xboole_0(sK3,X0)) = k2_zfmisc_1(sK0,k3_xboole_0(X0,sK1)) ),
    inference(superposition,[],[f7945,f39])).

fof(f7945,plain,(
    ! [X9] : k2_zfmisc_1(sK2,k3_xboole_0(X9,sK3)) = k2_zfmisc_1(sK0,k3_xboole_0(X9,sK1)) ),
    inference(backward_demodulation,[],[f5952,f7918])).

fof(f7918,plain,(
    ! [X31,X32] : k3_xboole_0(k2_zfmisc_1(sK2,X31),k2_zfmisc_1(sK0,X32)) = k2_zfmisc_1(sK0,k3_xboole_0(X31,X32)) ),
    inference(superposition,[],[f649,f7849])).

fof(f7849,plain,(
    sK0 = k3_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f7847,f40])).

fof(f649,plain,(
    ! [X6,X4,X5,X3] : k3_xboole_0(k2_zfmisc_1(X3,X5),k2_zfmisc_1(X4,X6)) = k2_zfmisc_1(k3_xboole_0(X4,X3),k3_xboole_0(X5,X6)) ),
    inference(superposition,[],[f63,f39])).

fof(f5952,plain,(
    ! [X9] : k2_zfmisc_1(sK2,k3_xboole_0(X9,sK3)) = k3_xboole_0(k2_zfmisc_1(sK2,X9),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f648,f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:03:32 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.45  % (9069)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.49  % (9093)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.49  % (9085)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.49  % (9077)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (9085)Refutation not found, incomplete strategy% (9085)------------------------------
% 0.21/0.50  % (9085)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (9072)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.22/0.52  % (9070)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.22/0.52  % (9066)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.22/0.52  % (9068)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.22/0.52  % (9085)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.52  
% 1.22/0.52  % (9085)Memory used [KB]: 10746
% 1.22/0.52  % (9085)Time elapsed: 0.115 s
% 1.22/0.52  % (9085)------------------------------
% 1.22/0.52  % (9085)------------------------------
% 1.22/0.52  % (9080)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.22/0.52  % (9071)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.22/0.52  % (9067)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.22/0.53  % (9065)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.22/0.53  % (9079)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.22/0.53  % (9065)Refutation not found, incomplete strategy% (9065)------------------------------
% 1.22/0.53  % (9065)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.53  % (9065)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.53  
% 1.22/0.53  % (9065)Memory used [KB]: 1663
% 1.22/0.53  % (9065)Time elapsed: 0.125 s
% 1.22/0.53  % (9065)------------------------------
% 1.22/0.53  % (9065)------------------------------
% 1.22/0.53  % (9073)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.22/0.53  % (9074)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.35/0.53  % (9076)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.35/0.53  % (9073)Refutation not found, incomplete strategy% (9073)------------------------------
% 1.35/0.53  % (9073)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.53  % (9073)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.53  
% 1.35/0.53  % (9073)Memory used [KB]: 10746
% 1.35/0.53  % (9073)Time elapsed: 0.125 s
% 1.35/0.53  % (9073)------------------------------
% 1.35/0.53  % (9073)------------------------------
% 1.35/0.53  % (9087)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.35/0.53  % (9084)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.35/0.53  % (9067)Refutation not found, incomplete strategy% (9067)------------------------------
% 1.35/0.53  % (9067)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.53  % (9067)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.53  
% 1.35/0.53  % (9067)Memory used [KB]: 10746
% 1.35/0.53  % (9067)Time elapsed: 0.120 s
% 1.35/0.53  % (9067)------------------------------
% 1.35/0.53  % (9067)------------------------------
% 1.35/0.53  % (9087)Refutation not found, incomplete strategy% (9087)------------------------------
% 1.35/0.53  % (9087)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.53  % (9087)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.53  
% 1.35/0.53  % (9087)Memory used [KB]: 10746
% 1.35/0.53  % (9087)Time elapsed: 0.086 s
% 1.35/0.53  % (9087)------------------------------
% 1.35/0.53  % (9087)------------------------------
% 1.35/0.54  % (9092)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.35/0.54  % (9089)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.35/0.54  % (9090)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.35/0.54  % (9081)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.35/0.54  % (9083)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.35/0.54  % (9075)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.35/0.54  % (9086)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.35/0.54  % (9094)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.35/0.54  % (9078)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.35/0.55  % (9091)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.35/0.55  % (9086)Refutation not found, incomplete strategy% (9086)------------------------------
% 1.35/0.55  % (9086)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.55  % (9086)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.55  
% 1.35/0.55  % (9086)Memory used [KB]: 1791
% 1.35/0.55  % (9086)Time elapsed: 0.147 s
% 1.35/0.55  % (9086)------------------------------
% 1.35/0.55  % (9086)------------------------------
% 1.35/0.56  % (9082)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.35/0.56  % (9082)Refutation not found, incomplete strategy% (9082)------------------------------
% 1.35/0.56  % (9082)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.56  % (9082)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.56  
% 1.35/0.56  % (9082)Memory used [KB]: 10618
% 1.35/0.56  % (9082)Time elapsed: 0.160 s
% 1.35/0.56  % (9082)------------------------------
% 1.35/0.56  % (9082)------------------------------
% 1.35/0.56  % (9088)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.35/0.56  % (9088)Refutation not found, incomplete strategy% (9088)------------------------------
% 1.35/0.56  % (9088)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.56  % (9088)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.56  
% 1.35/0.56  % (9088)Memory used [KB]: 1791
% 1.35/0.56  % (9088)Time elapsed: 0.134 s
% 1.35/0.56  % (9088)------------------------------
% 1.35/0.56  % (9088)------------------------------
% 1.95/0.66  % (9136)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 1.95/0.66  % (9140)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 1.95/0.66  % (9153)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 1.95/0.67  % (9143)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 1.95/0.67  % (9136)Refutation not found, incomplete strategy% (9136)------------------------------
% 1.95/0.67  % (9136)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.95/0.67  % (9146)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 1.95/0.68  % (9159)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 1.95/0.68  % (9136)Termination reason: Refutation not found, incomplete strategy
% 1.95/0.68  
% 1.95/0.68  % (9136)Memory used [KB]: 6140
% 1.95/0.68  % (9136)Time elapsed: 0.125 s
% 1.95/0.68  % (9136)------------------------------
% 1.95/0.68  % (9136)------------------------------
% 1.95/0.69  % (9145)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.36/0.69  % (9157)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 2.81/0.80  % (9070)Time limit reached!
% 2.81/0.80  % (9070)------------------------------
% 2.81/0.80  % (9070)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.81/0.80  % (9070)Termination reason: Time limit
% 2.81/0.80  % (9070)Termination phase: Saturation
% 2.81/0.80  
% 2.81/0.80  % (9070)Memory used [KB]: 8955
% 2.81/0.80  % (9070)Time elapsed: 0.400 s
% 2.81/0.80  % (9070)------------------------------
% 2.81/0.80  % (9070)------------------------------
% 3.03/0.81  % (9231)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 3.17/0.92  % (9077)Time limit reached!
% 3.17/0.92  % (9077)------------------------------
% 3.17/0.92  % (9077)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.17/0.92  % (9077)Termination reason: Time limit
% 3.17/0.92  
% 3.17/0.92  % (9077)Memory used [KB]: 8699
% 3.17/0.92  % (9077)Time elapsed: 0.524 s
% 3.17/0.92  % (9077)------------------------------
% 3.17/0.92  % (9077)------------------------------
% 3.17/0.92  % (9075)Time limit reached!
% 3.17/0.92  % (9075)------------------------------
% 3.17/0.92  % (9075)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.17/0.92  % (9075)Termination reason: Time limit
% 3.17/0.92  
% 3.17/0.92  % (9075)Memory used [KB]: 19061
% 3.17/0.92  % (9075)Time elapsed: 0.520 s
% 3.17/0.92  % (9075)------------------------------
% 3.17/0.92  % (9075)------------------------------
% 3.71/0.93  % (9066)Time limit reached!
% 3.71/0.93  % (9066)------------------------------
% 3.71/0.93  % (9066)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.71/0.93  % (9066)Termination reason: Time limit
% 3.71/0.93  
% 3.71/0.93  % (9066)Memory used [KB]: 8699
% 3.71/0.93  % (9066)Time elapsed: 0.516 s
% 3.71/0.93  % (9066)------------------------------
% 3.71/0.93  % (9066)------------------------------
% 3.71/0.94  % (9265)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 3.71/0.98  % (9146)Time limit reached!
% 3.71/0.98  % (9146)------------------------------
% 3.71/0.98  % (9146)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.71/0.98  % (9146)Termination reason: Time limit
% 3.71/0.98  
% 3.71/0.98  % (9146)Memory used [KB]: 13688
% 3.71/0.98  % (9146)Time elapsed: 0.418 s
% 3.71/0.98  % (9146)------------------------------
% 3.71/0.98  % (9146)------------------------------
% 3.71/0.98  % (9145)Time limit reached!
% 3.71/0.98  % (9145)------------------------------
% 3.71/0.98  % (9145)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.71/0.99  % (9145)Termination reason: Time limit
% 3.71/0.99  
% 3.71/0.99  % (9145)Memory used [KB]: 7547
% 3.71/0.99  % (9145)Time elapsed: 0.423 s
% 3.71/0.99  % (9145)------------------------------
% 3.71/0.99  % (9145)------------------------------
% 4.28/1.00  % (9093)Time limit reached!
% 4.28/1.00  % (9093)------------------------------
% 4.28/1.00  % (9093)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.28/1.00  % (9081)Time limit reached!
% 4.28/1.00  % (9081)------------------------------
% 4.28/1.00  % (9081)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.28/1.01  % (9081)Termination reason: Time limit
% 4.28/1.01  % (9081)Termination phase: Saturation
% 4.28/1.01  
% 4.28/1.01  % (9081)Memory used [KB]: 16247
% 4.28/1.01  % (9081)Time elapsed: 0.600 s
% 4.28/1.01  % (9081)------------------------------
% 4.28/1.01  % (9081)------------------------------
% 4.28/1.01  % (9093)Termination reason: Time limit
% 4.28/1.01  
% 4.28/1.01  % (9093)Memory used [KB]: 9083
% 4.28/1.01  % (9093)Time elapsed: 0.616 s
% 4.28/1.01  % (9093)------------------------------
% 4.28/1.01  % (9093)------------------------------
% 4.28/1.03  % (9072)Time limit reached!
% 4.28/1.03  % (9072)------------------------------
% 4.28/1.03  % (9072)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.28/1.03  % (9072)Termination reason: Time limit
% 4.28/1.03  
% 4.28/1.03  % (9072)Memory used [KB]: 11257
% 4.28/1.03  % (9072)Time elapsed: 0.609 s
% 4.28/1.03  % (9072)------------------------------
% 4.28/1.03  % (9072)------------------------------
% 4.28/1.04  % (9311)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 4.28/1.05  % (9300)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 4.28/1.06  % (9300)Refutation not found, incomplete strategy% (9300)------------------------------
% 4.28/1.06  % (9300)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.61/1.07  % (9300)Termination reason: Refutation not found, incomplete strategy
% 4.61/1.07  
% 4.61/1.07  % (9300)Memory used [KB]: 6268
% 4.61/1.07  % (9300)Time elapsed: 0.124 s
% 4.61/1.07  % (9300)------------------------------
% 4.61/1.07  % (9300)------------------------------
% 4.61/1.07  % (9311)Refutation not found, incomplete strategy% (9311)------------------------------
% 4.61/1.07  % (9311)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.61/1.07  % (9311)Termination reason: Refutation not found, incomplete strategy
% 4.61/1.07  
% 4.61/1.07  % (9311)Memory used [KB]: 1791
% 4.61/1.07  % (9311)Time elapsed: 0.106 s
% 4.61/1.07  % (9311)------------------------------
% 4.61/1.07  % (9311)------------------------------
% 4.61/1.07  % (9313)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 5.90/1.11  % (9333)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 5.90/1.11  % (9333)Refutation not found, incomplete strategy% (9333)------------------------------
% 5.90/1.11  % (9333)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.90/1.11  % (9333)Termination reason: Refutation not found, incomplete strategy
% 5.90/1.11  
% 5.90/1.11  % (9333)Memory used [KB]: 1663
% 5.90/1.11  % (9333)Time elapsed: 0.113 s
% 5.90/1.11  % (9333)------------------------------
% 5.90/1.11  % (9333)------------------------------
% 5.90/1.12  % (9337)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 5.90/1.12  % (9339)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 5.90/1.12  % (9339)Refutation not found, incomplete strategy% (9339)------------------------------
% 5.90/1.12  % (9339)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.90/1.12  % (9339)Termination reason: Refutation not found, incomplete strategy
% 5.90/1.12  
% 5.90/1.12  % (9339)Memory used [KB]: 6268
% 5.90/1.12  % (9339)Time elapsed: 0.085 s
% 5.90/1.12  % (9339)------------------------------
% 5.90/1.12  % (9339)------------------------------
% 5.90/1.13  % (9340)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 6.12/1.15  % (9341)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 6.12/1.17  % (9342)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 6.12/1.21  % (9343)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_1 on theBenchmark
% 6.12/1.21  % (9344)ott+1_128_add=large:afr=on:amm=sco:anc=none:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1.1:nicw=on:sas=z3:sac=on:sp=reverse_arity_44 on theBenchmark
% 6.76/1.25  % (9345)lrs+10_3:1_av=off:bsr=on:cond=on:er=known:gs=on:lcm=reverse:nm=32:nwc=4:stl=30:sp=occurrence:urr=on:updr=off_73 on theBenchmark
% 6.76/1.28  % (9071)Refutation found. Thanks to Tanya!
% 6.76/1.28  % SZS status Theorem for theBenchmark
% 6.76/1.28  % SZS output start Proof for theBenchmark
% 6.76/1.28  fof(f12670,plain,(
% 6.76/1.28    $false),
% 6.76/1.28    inference(subsumption_resolution,[],[f12669,f6696])).
% 6.76/1.28  fof(f6696,plain,(
% 6.76/1.28    r1_tarski(sK1,sK3)),
% 6.76/1.28    inference(duplicate_literal_removal,[],[f6689])).
% 6.76/1.28  fof(f6689,plain,(
% 6.76/1.28    r1_tarski(sK1,sK3) | r1_tarski(sK1,sK3)),
% 6.76/1.28    inference(resolution,[],[f6265,f42])).
% 6.76/1.28  fof(f42,plain,(
% 6.76/1.28    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 6.76/1.28    inference(cnf_transformation,[],[f28])).
% 6.76/1.28  fof(f28,plain,(
% 6.76/1.28    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 6.76/1.28    inference(ennf_transformation,[],[f19])).
% 6.76/1.28  fof(f19,plain,(
% 6.76/1.28    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 6.76/1.28    inference(unused_predicate_definition_removal,[],[f3])).
% 6.76/1.28  fof(f3,axiom,(
% 6.76/1.28    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 6.76/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 6.76/1.28  fof(f6265,plain,(
% 6.76/1.28    ( ! [X19] : (~r2_hidden(sK5(X19,sK3),sK1) | r1_tarski(X19,sK3)) )),
% 6.76/1.28    inference(resolution,[],[f6235,f43])).
% 6.76/1.28  fof(f43,plain,(
% 6.76/1.28    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 6.76/1.28    inference(cnf_transformation,[],[f28])).
% 6.76/1.28  fof(f6235,plain,(
% 6.76/1.28    ( ! [X28] : (r2_hidden(X28,sK3) | ~r2_hidden(X28,sK1)) )),
% 6.76/1.28    inference(subsumption_resolution,[],[f6144,f125])).
% 6.76/1.28  fof(f125,plain,(
% 6.76/1.28    ( ! [X2,X3] : (~r2_hidden(X3,k1_xboole_0) | r2_hidden(X3,X2)) )),
% 6.76/1.28    inference(superposition,[],[f70,f121])).
% 6.76/1.28  fof(f121,plain,(
% 6.76/1.28    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 6.76/1.28    inference(resolution,[],[f120,f40])).
% 6.76/1.28  fof(f40,plain,(
% 6.76/1.28    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 6.76/1.28    inference(cnf_transformation,[],[f25])).
% 6.76/1.28  fof(f25,plain,(
% 6.76/1.28    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 6.76/1.28    inference(ennf_transformation,[],[f10])).
% 6.76/1.28  fof(f10,axiom,(
% 6.76/1.28    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 6.76/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 6.76/1.28  fof(f120,plain,(
% 6.76/1.28    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 6.76/1.28    inference(factoring,[],[f116])).
% 6.76/1.28  fof(f116,plain,(
% 6.76/1.28    ( ! [X2,X3] : (r1_tarski(k1_xboole_0,X2) | r1_tarski(k1_xboole_0,X3)) )),
% 6.76/1.28    inference(resolution,[],[f114,f74])).
% 6.76/1.28  fof(f74,plain,(
% 6.76/1.28    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK7(X0),X0)) )),
% 6.76/1.28    inference(resolution,[],[f42,f50])).
% 6.76/1.28  fof(f50,plain,(
% 6.76/1.28    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r2_hidden(sK7(X1),X1)) )),
% 6.76/1.28    inference(cnf_transformation,[],[f30])).
% 6.76/1.28  fof(f30,plain,(
% 6.76/1.28    ! [X0,X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 6.76/1.28    inference(ennf_transformation,[],[f14])).
% 6.76/1.28  fof(f14,axiom,(
% 6.76/1.28    ! [X0,X1] : ~(! [X2] : ~(! [X3] : ~(r2_hidden(X3,X2) & r2_hidden(X3,X1)) & r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 6.76/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).
% 6.76/1.28  fof(f114,plain,(
% 6.76/1.28    ( ! [X0,X1] : (~r2_hidden(sK7(k1_xboole_0),X0) | r1_tarski(k1_xboole_0,X1)) )),
% 6.76/1.28    inference(superposition,[],[f81,f35])).
% 6.76/1.28  fof(f35,plain,(
% 6.76/1.28    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 6.76/1.28    inference(cnf_transformation,[],[f11])).
% 6.76/1.28  fof(f11,axiom,(
% 6.76/1.28    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 6.76/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 6.76/1.28  fof(f81,plain,(
% 6.76/1.28    ( ! [X4,X2,X3] : (~r2_hidden(sK7(X2),k4_xboole_0(X3,X2)) | r1_tarski(X2,X4)) )),
% 6.76/1.28    inference(resolution,[],[f67,f74])).
% 6.76/1.28  fof(f67,plain,(
% 6.76/1.28    ( ! [X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,k4_xboole_0(X0,X1))) )),
% 6.76/1.28    inference(equality_resolution,[],[f55])).
% 6.76/1.28  fof(f55,plain,(
% 6.76/1.28    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 6.76/1.28    inference(cnf_transformation,[],[f5])).
% 6.76/1.28  fof(f5,axiom,(
% 6.76/1.28    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 6.76/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 6.76/1.28  fof(f70,plain,(
% 6.76/1.28    ( ! [X0,X3,X1] : (~r2_hidden(X3,k3_xboole_0(X0,X1)) | r2_hidden(X3,X1)) )),
% 6.76/1.28    inference(equality_resolution,[],[f61])).
% 6.76/1.28  fof(f61,plain,(
% 6.76/1.28    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 6.76/1.28    inference(cnf_transformation,[],[f4])).
% 6.76/1.28  fof(f4,axiom,(
% 6.76/1.28    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 6.76/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 6.76/1.28  fof(f6144,plain,(
% 6.76/1.28    ( ! [X28] : (r2_hidden(X28,k1_xboole_0) | r2_hidden(X28,sK3) | ~r2_hidden(X28,sK1)) )),
% 6.76/1.28    inference(superposition,[],[f66,f6120])).
% 6.76/1.28  fof(f6120,plain,(
% 6.76/1.28    k1_xboole_0 = k4_xboole_0(sK1,sK3)),
% 6.76/1.28    inference(subsumption_resolution,[],[f6115,f33])).
% 6.76/1.28  fof(f33,plain,(
% 6.76/1.28    k1_xboole_0 != sK0),
% 6.76/1.28    inference(cnf_transformation,[],[f22])).
% 6.76/1.28  fof(f22,plain,(
% 6.76/1.28    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 6.76/1.28    inference(flattening,[],[f21])).
% 6.76/1.28  fof(f21,plain,(
% 6.76/1.28    ? [X0,X1,X2,X3] : (((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 6.76/1.28    inference(ennf_transformation,[],[f16])).
% 6.76/1.28  fof(f16,negated_conjecture,(
% 6.76/1.28    ~! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 6.76/1.28    inference(negated_conjecture,[],[f15])).
% 6.76/1.28  fof(f15,conjecture,(
% 6.76/1.28    ! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 6.76/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).
% 6.76/1.28  fof(f6115,plain,(
% 6.76/1.28    k1_xboole_0 = k4_xboole_0(sK1,sK3) | k1_xboole_0 = sK0),
% 6.76/1.28    inference(trivial_inequality_removal,[],[f6108])).
% 6.76/1.28  fof(f6108,plain,(
% 6.76/1.28    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k4_xboole_0(sK1,sK3) | k1_xboole_0 = sK0),
% 6.76/1.28    inference(superposition,[],[f44,f6069])).
% 6.76/1.28  fof(f6069,plain,(
% 6.76/1.28    k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3))),
% 6.76/1.28    inference(superposition,[],[f5953,f809])).
% 6.76/1.28  fof(f809,plain,(
% 6.76/1.28    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k3_xboole_0(X2,k4_xboole_0(X2,X3))) )),
% 6.76/1.28    inference(superposition,[],[f804,f39])).
% 6.76/1.28  fof(f39,plain,(
% 6.76/1.28    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 6.76/1.28    inference(cnf_transformation,[],[f1])).
% 6.76/1.28  fof(f1,axiom,(
% 6.76/1.28    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 6.76/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 6.76/1.28  fof(f804,plain,(
% 6.76/1.28    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k3_xboole_0(k4_xboole_0(X2,X3),X2)) )),
% 6.76/1.28    inference(resolution,[],[f800,f40])).
% 6.76/1.28  fof(f800,plain,(
% 6.76/1.28    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 6.76/1.28    inference(duplicate_literal_removal,[],[f788])).
% 6.76/1.28  fof(f788,plain,(
% 6.76/1.28    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0) | r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 6.76/1.28    inference(resolution,[],[f87,f43])).
% 6.76/1.28  fof(f87,plain,(
% 6.76/1.28    ( ! [X8,X7,X9] : (r2_hidden(sK5(k4_xboole_0(X7,X8),X9),X7) | r1_tarski(k4_xboole_0(X7,X8),X9)) )),
% 6.76/1.28    inference(resolution,[],[f68,f42])).
% 6.76/1.28  fof(f68,plain,(
% 6.76/1.28    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | r2_hidden(X3,X0)) )),
% 6.76/1.28    inference(equality_resolution,[],[f54])).
% 6.76/1.28  fof(f54,plain,(
% 6.76/1.28    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 6.76/1.28    inference(cnf_transformation,[],[f5])).
% 6.76/1.28  fof(f5953,plain,(
% 6.76/1.28    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(sK0,k3_xboole_0(sK1,k4_xboole_0(X0,sK3)))) )),
% 6.76/1.28    inference(superposition,[],[f648,f1406])).
% 6.76/1.28  fof(f1406,plain,(
% 6.76/1.28    ( ! [X12,X13] : (k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X12,k4_xboole_0(X13,sK3)))) )),
% 6.76/1.28    inference(superposition,[],[f1314,f32])).
% 6.76/1.28  fof(f32,plain,(
% 6.76/1.28    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3)),
% 6.76/1.28    inference(cnf_transformation,[],[f22])).
% 6.76/1.28  fof(f1314,plain,(
% 6.76/1.28    ( ! [X12,X10,X11,X9] : (k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(X11,X9),k2_zfmisc_1(X12,k4_xboole_0(X10,X9)))) )),
% 6.76/1.28    inference(forward_demodulation,[],[f1282,f64])).
% 6.76/1.28  fof(f64,plain,(
% 6.76/1.28    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 6.76/1.28    inference(equality_resolution,[],[f46])).
% 6.76/1.28  fof(f46,plain,(
% 6.76/1.28    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 6.76/1.28    inference(cnf_transformation,[],[f12])).
% 6.76/1.28  fof(f12,axiom,(
% 6.76/1.28    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 6.76/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 6.76/1.28  fof(f1282,plain,(
% 6.76/1.28    ( ! [X12,X10,X11,X9] : (k3_xboole_0(k2_zfmisc_1(X11,X9),k2_zfmisc_1(X12,k4_xboole_0(X10,X9))) = k2_zfmisc_1(k3_xboole_0(X11,X12),k1_xboole_0)) )),
% 6.76/1.28    inference(superposition,[],[f63,f1265])).
% 6.76/1.28  fof(f1265,plain,(
% 6.76/1.28    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 6.76/1.28    inference(resolution,[],[f1262,f36])).
% 6.76/1.28  fof(f36,plain,(
% 6.76/1.28    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 6.76/1.28    inference(cnf_transformation,[],[f23])).
% 6.76/1.28  fof(f23,plain,(
% 6.76/1.28    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 6.76/1.28    inference(ennf_transformation,[],[f8])).
% 6.76/1.28  fof(f8,axiom,(
% 6.76/1.28    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 6.76/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 6.76/1.28  fof(f1262,plain,(
% 6.76/1.28    ( ! [X4,X3] : (v1_xboole_0(k3_xboole_0(X4,k4_xboole_0(X3,X4)))) )),
% 6.76/1.28    inference(forward_demodulation,[],[f1261,f39])).
% 6.76/1.28  fof(f1261,plain,(
% 6.76/1.28    ( ! [X4,X3] : (v1_xboole_0(k3_xboole_0(k4_xboole_0(X3,X4),X4))) )),
% 6.76/1.28    inference(duplicate_literal_removal,[],[f1246])).
% 6.76/1.28  fof(f1246,plain,(
% 6.76/1.28    ( ! [X4,X3] : (v1_xboole_0(k3_xboole_0(k4_xboole_0(X3,X4),X4)) | v1_xboole_0(k3_xboole_0(k4_xboole_0(X3,X4),X4))) )),
% 6.76/1.28    inference(resolution,[],[f209,f96])).
% 6.76/1.28  fof(f96,plain,(
% 6.76/1.28    ( ! [X0,X1] : (r2_hidden(sK4(k3_xboole_0(X0,X1)),X0) | v1_xboole_0(k3_xboole_0(X0,X1))) )),
% 6.76/1.28    inference(resolution,[],[f71,f37])).
% 6.76/1.28  fof(f37,plain,(
% 6.76/1.28    ( ! [X0] : (r2_hidden(sK4(X0),X0) | v1_xboole_0(X0)) )),
% 6.76/1.28    inference(cnf_transformation,[],[f24])).
% 6.76/1.28  fof(f24,plain,(
% 6.76/1.28    ! [X0] : (v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0))),
% 6.76/1.28    inference(ennf_transformation,[],[f20])).
% 6.76/1.28  fof(f20,plain,(
% 6.76/1.28    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) => v1_xboole_0(X0))),
% 6.76/1.28    inference(unused_predicate_definition_removal,[],[f2])).
% 6.76/1.28  fof(f2,axiom,(
% 6.76/1.28    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 6.76/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 6.76/1.28  fof(f71,plain,(
% 6.76/1.28    ( ! [X0,X3,X1] : (~r2_hidden(X3,k3_xboole_0(X0,X1)) | r2_hidden(X3,X0)) )),
% 6.76/1.28    inference(equality_resolution,[],[f60])).
% 6.76/1.28  fof(f60,plain,(
% 6.76/1.28    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 6.76/1.28    inference(cnf_transformation,[],[f4])).
% 6.76/1.28  fof(f209,plain,(
% 6.76/1.28    ( ! [X2,X0,X1] : (~r2_hidden(sK4(k3_xboole_0(X0,X1)),k4_xboole_0(X2,X1)) | v1_xboole_0(k3_xboole_0(X0,X1))) )),
% 6.76/1.28    inference(resolution,[],[f89,f67])).
% 6.76/1.28  fof(f89,plain,(
% 6.76/1.28    ( ! [X0,X1] : (r2_hidden(sK4(k3_xboole_0(X0,X1)),X1) | v1_xboole_0(k3_xboole_0(X0,X1))) )),
% 6.76/1.28    inference(resolution,[],[f70,f37])).
% 6.76/1.28  fof(f63,plain,(
% 6.76/1.28    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 6.76/1.28    inference(cnf_transformation,[],[f13])).
% 6.76/1.28  fof(f13,axiom,(
% 6.76/1.28    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 6.76/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 6.76/1.28  fof(f648,plain,(
% 6.76/1.28    ( ! [X2,X0,X1] : (k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) = k2_zfmisc_1(X0,k3_xboole_0(X1,X2))) )),
% 6.76/1.28    inference(superposition,[],[f63,f38])).
% 6.76/1.28  fof(f38,plain,(
% 6.76/1.28    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 6.76/1.28    inference(cnf_transformation,[],[f17])).
% 6.76/1.28  fof(f17,plain,(
% 6.76/1.28    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 6.76/1.28    inference(rectify,[],[f7])).
% 6.76/1.28  fof(f7,axiom,(
% 6.76/1.28    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 6.76/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 6.76/1.28  fof(f44,plain,(
% 6.76/1.28    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 6.76/1.28    inference(cnf_transformation,[],[f12])).
% 6.76/1.28  fof(f66,plain,(
% 6.76/1.28    ( ! [X0,X3,X1] : (r2_hidden(X3,k4_xboole_0(X0,X1)) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) )),
% 6.76/1.28    inference(equality_resolution,[],[f56])).
% 6.76/1.28  fof(f56,plain,(
% 6.76/1.28    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 6.76/1.28    inference(cnf_transformation,[],[f5])).
% 6.76/1.28  fof(f12669,plain,(
% 6.76/1.28    ~r1_tarski(sK1,sK3)),
% 6.76/1.28    inference(subsumption_resolution,[],[f12668,f11985])).
% 6.76/1.28  fof(f11985,plain,(
% 6.76/1.28    sK1 != sK3),
% 6.76/1.28    inference(trivial_inequality_removal,[],[f11319])).
% 6.76/1.28  fof(f11319,plain,(
% 6.76/1.28    sK0 != sK0 | sK1 != sK3),
% 6.76/1.28    inference(backward_demodulation,[],[f31,f11318])).
% 6.76/1.28  fof(f11318,plain,(
% 6.76/1.28    sK0 = sK2),
% 6.76/1.28    inference(subsumption_resolution,[],[f11317,f7847])).
% 6.76/1.28  fof(f7847,plain,(
% 6.76/1.28    r1_tarski(sK0,sK2)),
% 6.76/1.28    inference(duplicate_literal_removal,[],[f7840])).
% 6.76/1.28  fof(f7840,plain,(
% 6.76/1.28    r1_tarski(sK0,sK2) | r1_tarski(sK0,sK2)),
% 6.76/1.28    inference(resolution,[],[f7396,f42])).
% 6.76/1.28  fof(f7396,plain,(
% 6.76/1.28    ( ! [X23] : (~r2_hidden(sK5(X23,sK2),sK0) | r1_tarski(X23,sK2)) )),
% 6.76/1.28    inference(resolution,[],[f7363,f43])).
% 6.76/1.28  fof(f7363,plain,(
% 6.76/1.28    ( ! [X28] : (r2_hidden(X28,sK2) | ~r2_hidden(X28,sK0)) )),
% 6.76/1.28    inference(subsumption_resolution,[],[f7272,f125])).
% 6.76/1.28  fof(f7272,plain,(
% 6.76/1.28    ( ! [X28] : (r2_hidden(X28,k1_xboole_0) | r2_hidden(X28,sK2) | ~r2_hidden(X28,sK0)) )),
% 6.76/1.28    inference(superposition,[],[f66,f7243])).
% 6.76/1.28  fof(f7243,plain,(
% 6.76/1.28    k1_xboole_0 = k4_xboole_0(sK0,sK2)),
% 6.76/1.28    inference(subsumption_resolution,[],[f7238,f34])).
% 6.76/1.28  fof(f34,plain,(
% 6.76/1.28    k1_xboole_0 != sK1),
% 6.76/1.28    inference(cnf_transformation,[],[f22])).
% 6.76/1.28  fof(f7238,plain,(
% 6.76/1.28    k1_xboole_0 = sK1 | k1_xboole_0 = k4_xboole_0(sK0,sK2)),
% 6.76/1.28    inference(trivial_inequality_removal,[],[f7229])).
% 6.76/1.28  fof(f7229,plain,(
% 6.76/1.28    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK1 | k1_xboole_0 = k4_xboole_0(sK0,sK2)),
% 6.76/1.28    inference(superposition,[],[f44,f7183])).
% 6.76/1.28  fof(f7183,plain,(
% 6.76/1.28    k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1)),
% 6.76/1.28    inference(superposition,[],[f6378,f809])).
% 6.76/1.28  fof(f6378,plain,(
% 6.76/1.28    ( ! [X11] : (k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(sK0,k4_xboole_0(X11,sK2)),sK1)) )),
% 6.76/1.28    inference(superposition,[],[f653,f1318])).
% 6.76/1.28  fof(f1318,plain,(
% 6.76/1.28    ( ! [X12,X13] : (k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k4_xboole_0(X12,sK2),X13))) )),
% 6.76/1.28    inference(superposition,[],[f1313,f32])).
% 6.76/1.28  fof(f1313,plain,(
% 6.76/1.28    ( ! [X6,X8,X7,X5] : (k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(X5,X7),k2_zfmisc_1(k4_xboole_0(X6,X5),X8))) )),
% 6.76/1.28    inference(forward_demodulation,[],[f1281,f65])).
% 6.76/1.28  fof(f65,plain,(
% 6.76/1.28    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 6.76/1.28    inference(equality_resolution,[],[f45])).
% 6.76/1.28  fof(f45,plain,(
% 6.76/1.28    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 6.76/1.28    inference(cnf_transformation,[],[f12])).
% 6.76/1.28  fof(f1281,plain,(
% 6.76/1.28    ( ! [X6,X8,X7,X5] : (k3_xboole_0(k2_zfmisc_1(X5,X7),k2_zfmisc_1(k4_xboole_0(X6,X5),X8)) = k2_zfmisc_1(k1_xboole_0,k3_xboole_0(X7,X8))) )),
% 6.76/1.28    inference(superposition,[],[f63,f1265])).
% 6.76/1.28  fof(f653,plain,(
% 6.76/1.28    ( ! [X2,X0,X1] : (k3_xboole_0(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) = k2_zfmisc_1(k3_xboole_0(X1,X2),X0)) )),
% 6.76/1.28    inference(superposition,[],[f63,f38])).
% 6.76/1.28  fof(f11317,plain,(
% 6.76/1.28    sK0 = sK2 | ~r1_tarski(sK0,sK2)),
% 6.76/1.28    inference(duplicate_literal_removal,[],[f11316])).
% 6.76/1.28  fof(f11316,plain,(
% 6.76/1.28    sK0 = sK2 | sK0 = sK2 | ~r1_tarski(sK0,sK2)),
% 6.76/1.28    inference(resolution,[],[f11309,f41])).
% 6.76/1.28  fof(f41,plain,(
% 6.76/1.28    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 6.76/1.28    inference(cnf_transformation,[],[f27])).
% 6.76/1.28  fof(f27,plain,(
% 6.76/1.28    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 6.76/1.28    inference(flattening,[],[f26])).
% 6.76/1.28  fof(f26,plain,(
% 6.76/1.28    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 6.76/1.28    inference(ennf_transformation,[],[f18])).
% 6.76/1.28  fof(f18,plain,(
% 6.76/1.28    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 6.76/1.28    inference(unused_predicate_definition_removal,[],[f6])).
% 6.76/1.28  fof(f6,axiom,(
% 6.76/1.28    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 6.76/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 6.76/1.28  fof(f11309,plain,(
% 6.76/1.28    ~r2_xboole_0(sK0,sK2) | sK0 = sK2),
% 6.76/1.28    inference(resolution,[],[f11059,f48])).
% 6.76/1.28  fof(f48,plain,(
% 6.76/1.28    ( ! [X0,X1] : (~r2_hidden(sK6(X0,X1),X0) | ~r2_xboole_0(X0,X1)) )),
% 6.76/1.28    inference(cnf_transformation,[],[f29])).
% 6.76/1.28  fof(f29,plain,(
% 6.76/1.28    ! [X0,X1] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) | ~r2_xboole_0(X0,X1))),
% 6.76/1.28    inference(ennf_transformation,[],[f9])).
% 6.76/1.28  fof(f9,axiom,(
% 6.76/1.28    ! [X0,X1] : ~(! [X2] : ~(~r2_hidden(X2,X0) & r2_hidden(X2,X1)) & r2_xboole_0(X0,X1))),
% 6.76/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_0)).
% 6.76/1.28  fof(f11059,plain,(
% 6.76/1.28    r2_hidden(sK6(sK0,sK2),sK0) | sK0 = sK2),
% 6.76/1.28    inference(resolution,[],[f11041,f7848])).
% 6.76/1.28  fof(f7848,plain,(
% 6.76/1.28    r2_hidden(sK6(sK0,sK2),sK2) | sK0 = sK2),
% 6.76/1.28    inference(resolution,[],[f7847,f108])).
% 6.76/1.28  fof(f108,plain,(
% 6.76/1.28    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_hidden(sK6(X0,X1),X1)) )),
% 6.76/1.28    inference(resolution,[],[f41,f47])).
% 6.76/1.28  fof(f47,plain,(
% 6.76/1.28    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | r2_hidden(sK6(X0,X1),X1)) )),
% 6.76/1.28    inference(cnf_transformation,[],[f29])).
% 6.76/1.28  fof(f11041,plain,(
% 6.76/1.28    ( ! [X0] : (~r2_hidden(X0,sK2) | r2_hidden(X0,sK0)) )),
% 6.76/1.28    inference(subsumption_resolution,[],[f10967,f125])).
% 6.76/1.28  fof(f10967,plain,(
% 6.76/1.28    ( ! [X0] : (r2_hidden(X0,k1_xboole_0) | r2_hidden(X0,sK0) | ~r2_hidden(X0,sK2)) )),
% 6.76/1.28    inference(superposition,[],[f66,f10936])).
% 6.76/1.28  fof(f10936,plain,(
% 6.76/1.28    k1_xboole_0 = k4_xboole_0(sK2,sK0)),
% 6.76/1.28    inference(subsumption_resolution,[],[f10935,f34])).
% 6.76/1.28  fof(f10935,plain,(
% 6.76/1.28    k1_xboole_0 = sK1 | k1_xboole_0 = k4_xboole_0(sK2,sK0)),
% 6.76/1.28    inference(trivial_inequality_removal,[],[f10926])).
% 6.76/1.28  fof(f10926,plain,(
% 6.76/1.28    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK1 | k1_xboole_0 = k4_xboole_0(sK2,sK0)),
% 6.76/1.28    inference(superposition,[],[f44,f10893])).
% 6.76/1.28  fof(f10893,plain,(
% 6.76/1.28    k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK2,sK0),sK1)),
% 6.76/1.28    inference(superposition,[],[f10799,f6863])).
% 6.76/1.28  fof(f6863,plain,(
% 6.76/1.28    sK1 = k3_xboole_0(sK3,sK1)),
% 6.76/1.28    inference(superposition,[],[f981,f6698])).
% 6.76/1.28  fof(f6698,plain,(
% 6.76/1.28    sK1 = k3_xboole_0(sK1,sK3)),
% 6.76/1.28    inference(resolution,[],[f6696,f40])).
% 6.76/1.28  fof(f981,plain,(
% 6.76/1.28    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,k3_xboole_0(X2,X3))) )),
% 6.76/1.28    inference(superposition,[],[f956,f39])).
% 6.76/1.28  fof(f956,plain,(
% 6.76/1.28    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(k3_xboole_0(X2,X3),X3)) )),
% 6.76/1.28    inference(resolution,[],[f952,f40])).
% 6.76/1.28  fof(f952,plain,(
% 6.76/1.28    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X1)) )),
% 6.76/1.28    inference(duplicate_literal_removal,[],[f935])).
% 6.76/1.28  fof(f935,plain,(
% 6.76/1.28    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X1) | r1_tarski(k3_xboole_0(X0,X1),X1)) )),
% 6.76/1.28    inference(resolution,[],[f92,f43])).
% 6.76/1.28  fof(f92,plain,(
% 6.76/1.28    ( ! [X8,X7,X9] : (r2_hidden(sK5(k3_xboole_0(X7,X8),X9),X8) | r1_tarski(k3_xboole_0(X7,X8),X9)) )),
% 6.76/1.28    inference(resolution,[],[f70,f42])).
% 6.76/1.28  fof(f10799,plain,(
% 6.76/1.28    ( ! [X2] : (k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK2,sK0),k3_xboole_0(sK3,X2))) )),
% 6.76/1.28    inference(forward_demodulation,[],[f10790,f121])).
% 6.76/1.28  fof(f10790,plain,(
% 6.76/1.28    ( ! [X2] : (k2_zfmisc_1(k4_xboole_0(sK2,sK0),k3_xboole_0(sK3,X2)) = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(k4_xboole_0(sK2,sK0),X2))) )),
% 6.76/1.28    inference(superposition,[],[f648,f10761])).
% 6.76/1.28  fof(f10761,plain,(
% 6.76/1.28    k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK2,sK0),sK3)),
% 6.76/1.28    inference(superposition,[],[f10741,f809])).
% 6.76/1.28  fof(f10741,plain,(
% 6.76/1.28    ( ! [X5] : (k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(sK2,k4_xboole_0(X5,sK0)),sK3)) )),
% 6.76/1.28    inference(forward_demodulation,[],[f10712,f65])).
% 6.76/1.28  fof(f10712,plain,(
% 6.76/1.28    ( ! [X5] : (k2_zfmisc_1(k1_xboole_0,sK1) = k2_zfmisc_1(k3_xboole_0(sK2,k4_xboole_0(X5,sK0)),sK3)) )),
% 6.76/1.28    inference(superposition,[],[f10413,f3984])).
% 6.76/1.28  fof(f3984,plain,(
% 6.76/1.28    ( ! [X10,X9] : (k1_xboole_0 = k3_xboole_0(k4_xboole_0(X9,X10),X10)) )),
% 6.76/1.28    inference(subsumption_resolution,[],[f3945,f36])).
% 6.76/1.28  fof(f3945,plain,(
% 6.76/1.28    ( ! [X10,X9] : (v1_xboole_0(k3_xboole_0(k4_xboole_0(X9,X10),X10)) | k1_xboole_0 = k3_xboole_0(k4_xboole_0(X9,X10),X10)) )),
% 6.76/1.28    inference(resolution,[],[f311,f462])).
% 6.76/1.28  fof(f462,plain,(
% 6.76/1.28    ( ! [X4,X5] : (r2_hidden(sK7(k3_xboole_0(X4,X5)),X4) | k1_xboole_0 = k3_xboole_0(X4,X5)) )),
% 6.76/1.28    inference(resolution,[],[f453,f71])).
% 6.76/1.28  fof(f453,plain,(
% 6.76/1.28    ( ! [X2] : (r2_hidden(sK7(X2),X2) | k1_xboole_0 = X2) )),
% 6.76/1.28    inference(resolution,[],[f448,f50])).
% 6.76/1.28  fof(f448,plain,(
% 6.76/1.28    ( ! [X3] : (r2_hidden(sK6(k1_xboole_0,X3),X3) | k1_xboole_0 = X3) )),
% 6.76/1.28    inference(resolution,[],[f108,f120])).
% 6.76/1.28  fof(f311,plain,(
% 6.76/1.28    ( ! [X2,X0,X1] : (~r2_hidden(sK7(k3_xboole_0(X0,X1)),k4_xboole_0(X2,X1)) | v1_xboole_0(k3_xboole_0(X0,X1))) )),
% 6.76/1.28    inference(resolution,[],[f91,f67])).
% 6.76/1.28  fof(f91,plain,(
% 6.76/1.28    ( ! [X6,X5] : (r2_hidden(sK7(k3_xboole_0(X5,X6)),X6) | v1_xboole_0(k3_xboole_0(X5,X6))) )),
% 6.76/1.28    inference(resolution,[],[f70,f72])).
% 6.76/1.28  fof(f72,plain,(
% 6.76/1.28    ( ! [X0] : (r2_hidden(sK7(X0),X0) | v1_xboole_0(X0)) )),
% 6.76/1.28    inference(resolution,[],[f50,f37])).
% 6.76/1.28  fof(f10413,plain,(
% 6.76/1.28    ( ! [X0] : (k2_zfmisc_1(k3_xboole_0(sK2,X0),sK3) = k2_zfmisc_1(k3_xboole_0(X0,sK0),sK1)) )),
% 6.76/1.28    inference(superposition,[],[f6953,f39])).
% 7.14/1.28  fof(f6953,plain,(
% 7.14/1.28    ( ! [X9] : (k2_zfmisc_1(k3_xboole_0(X9,sK2),sK3) = k2_zfmisc_1(k3_xboole_0(X9,sK0),sK1)) )),
% 7.14/1.28    inference(backward_demodulation,[],[f6374,f6891])).
% 7.14/1.28  fof(f6891,plain,(
% 7.14/1.28    ( ! [X2,X3] : (k2_zfmisc_1(k3_xboole_0(X2,X3),sK1) = k3_xboole_0(k2_zfmisc_1(X2,sK3),k2_zfmisc_1(X3,sK1))) )),
% 7.14/1.28    inference(superposition,[],[f63,f6863])).
% 7.14/1.28  fof(f6374,plain,(
% 7.14/1.28    ( ! [X9] : (k2_zfmisc_1(k3_xboole_0(X9,sK2),sK3) = k3_xboole_0(k2_zfmisc_1(X9,sK3),k2_zfmisc_1(sK0,sK1))) )),
% 7.14/1.28    inference(superposition,[],[f653,f32])).
% 7.14/1.28  fof(f31,plain,(
% 7.14/1.28    sK1 != sK3 | sK0 != sK2),
% 7.14/1.28    inference(cnf_transformation,[],[f22])).
% 7.14/1.28  fof(f12668,plain,(
% 7.14/1.28    sK1 = sK3 | ~r1_tarski(sK1,sK3)),
% 7.14/1.28    inference(resolution,[],[f12661,f41])).
% 7.14/1.28  fof(f12661,plain,(
% 7.14/1.28    ~r2_xboole_0(sK1,sK3)),
% 7.14/1.28    inference(resolution,[],[f12641,f48])).
% 7.14/1.28  fof(f12641,plain,(
% 7.14/1.28    r2_hidden(sK6(sK1,sK3),sK1)),
% 7.14/1.28    inference(subsumption_resolution,[],[f12537,f11985])).
% 7.14/1.28  fof(f12537,plain,(
% 7.14/1.28    r2_hidden(sK6(sK1,sK3),sK1) | sK1 = sK3),
% 7.14/1.28    inference(resolution,[],[f12519,f6697])).
% 7.14/1.28  fof(f6697,plain,(
% 7.14/1.28    r2_hidden(sK6(sK1,sK3),sK3) | sK1 = sK3),
% 7.14/1.28    inference(resolution,[],[f6696,f108])).
% 7.14/1.28  fof(f12519,plain,(
% 7.14/1.28    ( ! [X0] : (~r2_hidden(X0,sK3) | r2_hidden(X0,sK1)) )),
% 7.14/1.28    inference(subsumption_resolution,[],[f12447,f125])).
% 7.14/1.28  fof(f12447,plain,(
% 7.14/1.28    ( ! [X0] : (r2_hidden(X0,k1_xboole_0) | r2_hidden(X0,sK1) | ~r2_hidden(X0,sK3)) )),
% 7.14/1.28    inference(superposition,[],[f66,f12368])).
% 7.14/1.28  fof(f12368,plain,(
% 7.14/1.28    k1_xboole_0 = k4_xboole_0(sK3,sK1)),
% 7.14/1.28    inference(subsumption_resolution,[],[f12367,f33])).
% 7.14/1.28  fof(f12367,plain,(
% 7.14/1.28    k1_xboole_0 = k4_xboole_0(sK3,sK1) | k1_xboole_0 = sK0),
% 7.14/1.28    inference(trivial_inequality_removal,[],[f12358])).
% 7.14/1.28  fof(f12358,plain,(
% 7.14/1.28    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k4_xboole_0(sK3,sK1) | k1_xboole_0 = sK0),
% 7.14/1.28    inference(superposition,[],[f44,f12326])).
% 7.14/1.28  fof(f12326,plain,(
% 7.14/1.28    k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK3,sK1))),
% 7.14/1.28    inference(superposition,[],[f12300,f809])).
% 7.14/1.28  fof(f12300,plain,(
% 7.14/1.28    ( ! [X5] : (k1_xboole_0 = k2_zfmisc_1(sK0,k3_xboole_0(sK3,k4_xboole_0(X5,sK1)))) )),
% 7.14/1.28    inference(forward_demodulation,[],[f12274,f64])).
% 7.14/1.28  fof(f12274,plain,(
% 7.14/1.28    ( ! [X5] : (k2_zfmisc_1(sK0,k1_xboole_0) = k2_zfmisc_1(sK0,k3_xboole_0(sK3,k4_xboole_0(X5,sK1)))) )),
% 7.14/1.28    inference(superposition,[],[f11895,f3984])).
% 7.14/1.28  fof(f11895,plain,(
% 7.14/1.28    ( ! [X0] : (k2_zfmisc_1(sK0,k3_xboole_0(X0,sK1)) = k2_zfmisc_1(sK0,k3_xboole_0(sK3,X0))) )),
% 7.14/1.28    inference(backward_demodulation,[],[f10591,f11318])).
% 7.14/1.28  fof(f10591,plain,(
% 7.14/1.28    ( ! [X0] : (k2_zfmisc_1(sK2,k3_xboole_0(sK3,X0)) = k2_zfmisc_1(sK0,k3_xboole_0(X0,sK1))) )),
% 7.14/1.28    inference(superposition,[],[f7945,f39])).
% 7.14/1.28  fof(f7945,plain,(
% 7.14/1.28    ( ! [X9] : (k2_zfmisc_1(sK2,k3_xboole_0(X9,sK3)) = k2_zfmisc_1(sK0,k3_xboole_0(X9,sK1))) )),
% 7.14/1.28    inference(backward_demodulation,[],[f5952,f7918])).
% 7.14/1.28  fof(f7918,plain,(
% 7.14/1.28    ( ! [X31,X32] : (k3_xboole_0(k2_zfmisc_1(sK2,X31),k2_zfmisc_1(sK0,X32)) = k2_zfmisc_1(sK0,k3_xboole_0(X31,X32))) )),
% 7.14/1.28    inference(superposition,[],[f649,f7849])).
% 7.14/1.28  fof(f7849,plain,(
% 7.14/1.28    sK0 = k3_xboole_0(sK0,sK2)),
% 7.14/1.28    inference(resolution,[],[f7847,f40])).
% 7.14/1.28  fof(f649,plain,(
% 7.14/1.28    ( ! [X6,X4,X5,X3] : (k3_xboole_0(k2_zfmisc_1(X3,X5),k2_zfmisc_1(X4,X6)) = k2_zfmisc_1(k3_xboole_0(X4,X3),k3_xboole_0(X5,X6))) )),
% 7.14/1.28    inference(superposition,[],[f63,f39])).
% 7.14/1.28  fof(f5952,plain,(
% 7.14/1.28    ( ! [X9] : (k2_zfmisc_1(sK2,k3_xboole_0(X9,sK3)) = k3_xboole_0(k2_zfmisc_1(sK2,X9),k2_zfmisc_1(sK0,sK1))) )),
% 7.14/1.28    inference(superposition,[],[f648,f32])).
% 7.14/1.28  % SZS output end Proof for theBenchmark
% 7.14/1.28  % (9071)------------------------------
% 7.14/1.28  % (9071)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.14/1.28  % (9071)Termination reason: Refutation
% 7.14/1.28  
% 7.14/1.28  % (9071)Memory used [KB]: 13304
% 7.14/1.28  % (9071)Time elapsed: 0.836 s
% 7.14/1.28  % (9071)------------------------------
% 7.14/1.28  % (9071)------------------------------
% 7.14/1.29  % (9061)Success in time 0.942 s
%------------------------------------------------------------------------------
