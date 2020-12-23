%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:43 EST 2020

% Result     : Theorem 2.13s
% Output     : Refutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 747 expanded)
%              Number of leaves         :   10 ( 217 expanded)
%              Depth                    :   25
%              Number of atoms          :  198 (1449 expanded)
%              Number of equality atoms :   48 ( 395 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1428,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1141,f50])).

fof(f50,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f1141,plain,(
    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) ),
    inference(backward_demodulation,[],[f19,f1138])).

fof(f1138,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f1094,f49])).

fof(f49,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f1094,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f19,f1066])).

fof(f1066,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(global_subsumption,[],[f795,f1060])).

fof(f1060,plain,
    ( ~ r1_tarski(sK0,sK2)
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f1043,f17])).

fof(f17,plain,
    ( ~ r1_tarski(sK1,sK3)
    | ~ r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
       => ( ( r1_tarski(X1,X3)
            & r1_tarski(X0,X2) )
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(f1043,plain,
    ( r1_tarski(sK1,sK3)
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f1029,f363])).

fof(f363,plain,(
    ! [X24,X21] :
      ( r2_hidden(sK6(X21,k1_xboole_0,X24),X24)
      | k1_xboole_0 = X24 ) ),
    inference(forward_demodulation,[],[f362,f270])).

fof(f270,plain,(
    ! [X8] : k1_xboole_0 = k4_xboole_0(X8,X8) ),
    inference(resolution,[],[f266,f68])).

fof(f68,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f62,f21])).

fof(f21,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f62,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k4_xboole_0(X1,X1)) ),
    inference(forward_demodulation,[],[f61,f22])).

fof(f22,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f61,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))) ),
    inference(resolution,[],[f42,f20])).

fof(f20,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f24,f23])).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f266,plain,(
    ! [X12,X11] :
      ( r2_hidden(sK6(X11,k1_xboole_0,X12),X12)
      | k4_xboole_0(X11,X11) = X12 ) ),
    inference(forward_demodulation,[],[f247,f22])).

fof(f247,plain,(
    ! [X12,X11] :
      ( r2_hidden(sK6(X11,k1_xboole_0,X12),X12)
      | k4_xboole_0(X11,k4_xboole_0(X11,k1_xboole_0)) = X12 ) ),
    inference(resolution,[],[f46,f68])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X2),X1)
      | r2_hidden(sK6(X0,X1,X2),X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f34,f23])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X2),X1)
      | r2_hidden(sK6(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f362,plain,(
    ! [X24,X21] :
      ( k4_xboole_0(X21,X21) = X24
      | r2_hidden(sK6(X21,k1_xboole_0,X24),X24) ) ),
    inference(forward_demodulation,[],[f361,f22])).

fof(f361,plain,(
    ! [X24,X21] :
      ( k4_xboole_0(X21,k4_xboole_0(X21,k1_xboole_0)) = X24
      | r2_hidden(sK6(X21,k1_xboole_0,X24),X24) ) ),
    inference(forward_demodulation,[],[f360,f270])).

fof(f360,plain,(
    ! [X24,X21,X22] :
      ( k4_xboole_0(X21,k4_xboole_0(X21,k4_xboole_0(X22,X22))) = X24
      | r2_hidden(sK6(X21,k1_xboole_0,X24),X24) ) ),
    inference(forward_demodulation,[],[f359,f22])).

fof(f359,plain,(
    ! [X24,X21,X22] :
      ( k4_xboole_0(X21,k4_xboole_0(X21,k4_xboole_0(X22,k4_xboole_0(X22,k1_xboole_0)))) = X24
      | r2_hidden(sK6(X21,k1_xboole_0,X24),X24) ) ),
    inference(forward_demodulation,[],[f358,f270])).

fof(f358,plain,(
    ! [X24,X23,X21,X22] :
      ( r2_hidden(sK6(X21,k1_xboole_0,X24),X24)
      | k4_xboole_0(X21,k4_xboole_0(X21,k4_xboole_0(X22,k4_xboole_0(X22,k4_xboole_0(X23,X23))))) = X24 ) ),
    inference(forward_demodulation,[],[f357,f270])).

fof(f357,plain,(
    ! [X24,X23,X21,X22] :
      ( r2_hidden(sK6(X21,k4_xboole_0(X22,X22),X24),X24)
      | k4_xboole_0(X21,k4_xboole_0(X21,k4_xboole_0(X22,k4_xboole_0(X22,k4_xboole_0(X23,X23))))) = X24 ) ),
    inference(forward_demodulation,[],[f298,f22])).

fof(f298,plain,(
    ! [X24,X23,X21,X22] :
      ( r2_hidden(sK6(X21,k4_xboole_0(X22,k4_xboole_0(X22,k1_xboole_0)),X24),X24)
      | k4_xboole_0(X21,k4_xboole_0(X21,k4_xboole_0(X22,k4_xboole_0(X22,k4_xboole_0(X23,X23))))) = X24 ) ),
    inference(backward_demodulation,[],[f250,f270])).

fof(f250,plain,(
    ! [X24,X23,X21,X22] :
      ( r2_hidden(sK6(X21,k4_xboole_0(X22,k4_xboole_0(X22,k4_xboole_0(X23,X23))),X24),X24)
      | k4_xboole_0(X21,k4_xboole_0(X21,k4_xboole_0(X22,k4_xboole_0(X22,k4_xboole_0(X23,X23))))) = X24 ) ),
    inference(resolution,[],[f46,f111])).

fof(f111,plain,(
    ! [X2,X0,X1] : ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X2)))) ),
    inference(resolution,[],[f110,f42])).

fof(f110,plain,(
    ! [X12,X13] : r1_xboole_0(X12,k4_xboole_0(X13,X13)) ),
    inference(resolution,[],[f88,f62])).

fof(f88,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK4(X2,X3),X3)
      | r1_xboole_0(X2,X3) ) ),
    inference(resolution,[],[f41,f52])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f36,f23])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f25,f23])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f1029,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | r1_tarski(sK1,sK3) ) ),
    inference(forward_demodulation,[],[f1027,f22])).

fof(f1027,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k4_xboole_0(sK0,k1_xboole_0))
      | r1_tarski(sK1,sK3) ) ),
    inference(superposition,[],[f1006,f270])).

fof(f1006,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,X1)))
      | r1_tarski(sK1,sK3) ) ),
    inference(resolution,[],[f1005,f42])).

fof(f1005,plain,(
    ! [X0] :
      ( r1_xboole_0(sK0,X0)
      | r1_tarski(sK1,sK3) ) ),
    inference(duplicate_literal_removal,[],[f999])).

fof(f999,plain,(
    ! [X0] :
      ( r1_xboole_0(sK0,X0)
      | r1_tarski(sK1,sK3)
      | r1_tarski(sK1,sK3) ) ),
    inference(resolution,[],[f730,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f730,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(sK1,X0),sK3)
      | r1_xboole_0(sK0,X1)
      | r1_tarski(sK1,X0) ) ),
    inference(resolution,[],[f589,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f41,f53])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f35,f23])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f589,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,sK0)
      | r2_hidden(sK5(sK1,X5),sK3)
      | r1_tarski(sK1,X5) ) ),
    inference(resolution,[],[f583,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f583,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,sK1)
      | ~ r2_hidden(X0,sK0)
      | r2_hidden(X1,sK3) ) ),
    inference(resolution,[],[f579,f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f579,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK2,sK3))
      | ~ r2_hidden(X0,sK0)
      | ~ r2_hidden(X1,sK1) ) ),
    inference(resolution,[],[f126,f18])).

fof(f18,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f14])).

fof(f126,plain,(
    ! [X12,X10,X8,X11,X9] :
      ( ~ r1_tarski(k2_zfmisc_1(X11,X9),X12)
      | ~ r2_hidden(X10,X11)
      | r2_hidden(k4_tarski(X10,X8),X12)
      | ~ r2_hidden(X8,X9) ) ),
    inference(resolution,[],[f40,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f795,plain,
    ( r1_tarski(sK0,sK2)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f781,f363])).

fof(f781,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK1)
      | r1_tarski(sK0,sK2) ) ),
    inference(forward_demodulation,[],[f779,f22])).

fof(f779,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k4_xboole_0(sK1,k1_xboole_0))
      | r1_tarski(sK0,sK2) ) ),
    inference(superposition,[],[f759,f270])).

fof(f759,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,X1)))
      | r1_tarski(sK0,sK2) ) ),
    inference(resolution,[],[f758,f42])).

fof(f758,plain,(
    ! [X0] :
      ( r1_xboole_0(sK1,X0)
      | r1_tarski(sK0,sK2) ) ),
    inference(duplicate_literal_removal,[],[f754])).

fof(f754,plain,(
    ! [X0] :
      ( r1_xboole_0(sK1,X0)
      | r1_tarski(sK0,sK2)
      | r1_tarski(sK0,sK2) ) ),
    inference(resolution,[],[f623,f28])).

fof(f623,plain,(
    ! [X4,X5] :
      ( r2_hidden(sK5(sK0,X4),sK2)
      | r1_xboole_0(sK1,X5)
      | r1_tarski(sK0,X4) ) ),
    inference(resolution,[],[f604,f27])).

fof(f604,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK0)
      | r2_hidden(X0,sK2)
      | r1_xboole_0(sK1,X1) ) ),
    inference(resolution,[],[f584,f87])).

fof(f584,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,sK1)
      | ~ r2_hidden(X2,sK0)
      | r2_hidden(X2,sK2) ) ),
    inference(resolution,[],[f579,f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f19,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:29:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.51  % (29471)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (29470)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (29476)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.52  % (29468)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (29486)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.53  % (29490)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.53  % (29488)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.53  % (29474)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.53  % (29468)Refutation not found, incomplete strategy% (29468)------------------------------
% 0.20/0.53  % (29468)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (29467)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.54  % (29480)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.54  % (29468)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (29468)Memory used [KB]: 10618
% 0.20/0.54  % (29468)Time elapsed: 0.127 s
% 0.20/0.54  % (29468)------------------------------
% 0.20/0.54  % (29468)------------------------------
% 0.20/0.54  % (29469)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.54  % (29478)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.54  % (29477)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.54  % (29481)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.54  % (29482)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.54  % (29488)Refutation not found, incomplete strategy% (29488)------------------------------
% 0.20/0.54  % (29488)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (29484)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.54  % (29488)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (29488)Memory used [KB]: 10746
% 0.20/0.54  % (29488)Time elapsed: 0.090 s
% 0.20/0.54  % (29488)------------------------------
% 0.20/0.54  % (29488)------------------------------
% 0.20/0.54  % (29466)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.54  % (29472)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.54  % (29483)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.54  % (29483)Refutation not found, incomplete strategy% (29483)------------------------------
% 0.20/0.54  % (29483)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (29489)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.55  % (29487)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.55  % (29494)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.55  % (29485)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.55  % (29492)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.55  % (29493)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.55  % (29473)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.55  % (29474)Refutation not found, incomplete strategy% (29474)------------------------------
% 0.20/0.55  % (29474)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (29474)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (29474)Memory used [KB]: 10618
% 0.20/0.55  % (29474)Time elapsed: 0.141 s
% 0.20/0.55  % (29474)------------------------------
% 0.20/0.55  % (29474)------------------------------
% 0.20/0.55  % (29475)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.55  % (29479)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.56  % (29491)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.56  % (29495)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.56  % (29483)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (29483)Memory used [KB]: 10618
% 0.20/0.56  % (29483)Time elapsed: 0.140 s
% 0.20/0.56  % (29483)------------------------------
% 0.20/0.56  % (29483)------------------------------
% 2.13/0.64  % (29472)Refutation found. Thanks to Tanya!
% 2.13/0.64  % SZS status Theorem for theBenchmark
% 2.13/0.65  % SZS output start Proof for theBenchmark
% 2.13/0.65  fof(f1428,plain,(
% 2.13/0.65    $false),
% 2.13/0.65    inference(subsumption_resolution,[],[f1141,f50])).
% 2.13/0.65  fof(f50,plain,(
% 2.13/0.65    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.13/0.65    inference(equality_resolution,[],[f30])).
% 2.13/0.65  fof(f30,plain,(
% 2.13/0.65    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 2.13/0.65    inference(cnf_transformation,[],[f9])).
% 2.13/0.65  fof(f9,axiom,(
% 2.13/0.65    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.13/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 2.13/0.65  fof(f1141,plain,(
% 2.13/0.65    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)),
% 2.13/0.65    inference(backward_demodulation,[],[f19,f1138])).
% 2.13/0.65  fof(f1138,plain,(
% 2.13/0.65    k1_xboole_0 = sK0),
% 2.13/0.65    inference(subsumption_resolution,[],[f1094,f49])).
% 2.13/0.65  fof(f49,plain,(
% 2.13/0.65    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.13/0.65    inference(equality_resolution,[],[f31])).
% 2.13/0.65  fof(f31,plain,(
% 2.13/0.65    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 2.13/0.65    inference(cnf_transformation,[],[f9])).
% 2.13/0.65  fof(f1094,plain,(
% 2.13/0.65    k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | k1_xboole_0 = sK0),
% 2.13/0.65    inference(superposition,[],[f19,f1066])).
% 2.13/0.65  fof(f1066,plain,(
% 2.13/0.65    k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 2.13/0.65    inference(global_subsumption,[],[f795,f1060])).
% 2.13/0.65  fof(f1060,plain,(
% 2.13/0.65    ~r1_tarski(sK0,sK2) | k1_xboole_0 = sK0),
% 2.13/0.65    inference(resolution,[],[f1043,f17])).
% 2.13/0.65  fof(f17,plain,(
% 2.13/0.65    ~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)),
% 2.13/0.65    inference(cnf_transformation,[],[f14])).
% 2.13/0.65  fof(f14,plain,(
% 2.13/0.65    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 2.13/0.65    inference(flattening,[],[f13])).
% 2.13/0.65  fof(f13,plain,(
% 2.13/0.65    ? [X0,X1,X2,X3] : (((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1)) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 2.13/0.65    inference(ennf_transformation,[],[f11])).
% 2.13/0.65  fof(f11,negated_conjecture,(
% 2.13/0.65    ~! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 2.13/0.65    inference(negated_conjecture,[],[f10])).
% 2.13/0.65  fof(f10,conjecture,(
% 2.13/0.65    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 2.13/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).
% 2.13/0.65  fof(f1043,plain,(
% 2.13/0.65    r1_tarski(sK1,sK3) | k1_xboole_0 = sK0),
% 2.13/0.65    inference(resolution,[],[f1029,f363])).
% 2.13/0.65  fof(f363,plain,(
% 2.13/0.65    ( ! [X24,X21] : (r2_hidden(sK6(X21,k1_xboole_0,X24),X24) | k1_xboole_0 = X24) )),
% 2.13/0.65    inference(forward_demodulation,[],[f362,f270])).
% 2.13/0.65  fof(f270,plain,(
% 2.13/0.65    ( ! [X8] : (k1_xboole_0 = k4_xboole_0(X8,X8)) )),
% 2.13/0.65    inference(resolution,[],[f266,f68])).
% 2.13/0.65  fof(f68,plain,(
% 2.13/0.65    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 2.13/0.65    inference(superposition,[],[f62,f21])).
% 2.13/0.65  fof(f21,plain,(
% 2.13/0.65    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 2.13/0.65    inference(cnf_transformation,[],[f6])).
% 2.13/0.65  fof(f6,axiom,(
% 2.13/0.65    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 2.13/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 2.13/0.65  fof(f62,plain,(
% 2.13/0.65    ( ! [X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,X1))) )),
% 2.13/0.65    inference(forward_demodulation,[],[f61,f22])).
% 2.13/0.65  fof(f22,plain,(
% 2.13/0.65    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.13/0.65    inference(cnf_transformation,[],[f4])).
% 2.13/0.65  fof(f4,axiom,(
% 2.13/0.65    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.13/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 2.13/0.65  fof(f61,plain,(
% 2.13/0.65    ( ! [X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)))) )),
% 2.13/0.65    inference(resolution,[],[f42,f20])).
% 2.13/0.65  fof(f20,plain,(
% 2.13/0.65    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 2.13/0.65    inference(cnf_transformation,[],[f7])).
% 2.13/0.65  fof(f7,axiom,(
% 2.13/0.65    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 2.13/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 2.13/0.65  fof(f42,plain,(
% 2.13/0.65    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 2.13/0.65    inference(definition_unfolding,[],[f24,f23])).
% 2.13/0.65  fof(f23,plain,(
% 2.13/0.65    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.13/0.65    inference(cnf_transformation,[],[f5])).
% 2.13/0.65  fof(f5,axiom,(
% 2.13/0.65    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.13/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.13/0.65  fof(f24,plain,(
% 2.13/0.65    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 2.13/0.65    inference(cnf_transformation,[],[f15])).
% 2.13/0.65  fof(f15,plain,(
% 2.13/0.65    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.13/0.65    inference(ennf_transformation,[],[f12])).
% 2.13/0.65  fof(f12,plain,(
% 2.13/0.65    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.13/0.65    inference(rectify,[],[f3])).
% 2.13/0.65  fof(f3,axiom,(
% 2.13/0.65    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.13/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 2.13/0.65  fof(f266,plain,(
% 2.13/0.65    ( ! [X12,X11] : (r2_hidden(sK6(X11,k1_xboole_0,X12),X12) | k4_xboole_0(X11,X11) = X12) )),
% 2.13/0.65    inference(forward_demodulation,[],[f247,f22])).
% 2.13/0.65  fof(f247,plain,(
% 2.13/0.65    ( ! [X12,X11] : (r2_hidden(sK6(X11,k1_xboole_0,X12),X12) | k4_xboole_0(X11,k4_xboole_0(X11,k1_xboole_0)) = X12) )),
% 2.13/0.65    inference(resolution,[],[f46,f68])).
% 2.13/0.65  fof(f46,plain,(
% 2.13/0.65    ( ! [X2,X0,X1] : (r2_hidden(sK6(X0,X1,X2),X1) | r2_hidden(sK6(X0,X1,X2),X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2) )),
% 2.13/0.65    inference(definition_unfolding,[],[f34,f23])).
% 2.13/0.65  fof(f34,plain,(
% 2.13/0.65    ( ! [X2,X0,X1] : (r2_hidden(sK6(X0,X1,X2),X1) | r2_hidden(sK6(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 2.13/0.65    inference(cnf_transformation,[],[f2])).
% 2.13/0.65  fof(f2,axiom,(
% 2.13/0.65    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.13/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 2.13/0.65  fof(f362,plain,(
% 2.13/0.65    ( ! [X24,X21] : (k4_xboole_0(X21,X21) = X24 | r2_hidden(sK6(X21,k1_xboole_0,X24),X24)) )),
% 2.13/0.65    inference(forward_demodulation,[],[f361,f22])).
% 2.13/0.65  fof(f361,plain,(
% 2.13/0.65    ( ! [X24,X21] : (k4_xboole_0(X21,k4_xboole_0(X21,k1_xboole_0)) = X24 | r2_hidden(sK6(X21,k1_xboole_0,X24),X24)) )),
% 2.13/0.65    inference(forward_demodulation,[],[f360,f270])).
% 2.13/0.65  fof(f360,plain,(
% 2.13/0.65    ( ! [X24,X21,X22] : (k4_xboole_0(X21,k4_xboole_0(X21,k4_xboole_0(X22,X22))) = X24 | r2_hidden(sK6(X21,k1_xboole_0,X24),X24)) )),
% 2.13/0.65    inference(forward_demodulation,[],[f359,f22])).
% 2.13/0.65  fof(f359,plain,(
% 2.13/0.65    ( ! [X24,X21,X22] : (k4_xboole_0(X21,k4_xboole_0(X21,k4_xboole_0(X22,k4_xboole_0(X22,k1_xboole_0)))) = X24 | r2_hidden(sK6(X21,k1_xboole_0,X24),X24)) )),
% 2.13/0.65    inference(forward_demodulation,[],[f358,f270])).
% 2.13/0.65  fof(f358,plain,(
% 2.13/0.65    ( ! [X24,X23,X21,X22] : (r2_hidden(sK6(X21,k1_xboole_0,X24),X24) | k4_xboole_0(X21,k4_xboole_0(X21,k4_xboole_0(X22,k4_xboole_0(X22,k4_xboole_0(X23,X23))))) = X24) )),
% 2.13/0.65    inference(forward_demodulation,[],[f357,f270])).
% 2.13/0.65  fof(f357,plain,(
% 2.13/0.65    ( ! [X24,X23,X21,X22] : (r2_hidden(sK6(X21,k4_xboole_0(X22,X22),X24),X24) | k4_xboole_0(X21,k4_xboole_0(X21,k4_xboole_0(X22,k4_xboole_0(X22,k4_xboole_0(X23,X23))))) = X24) )),
% 2.13/0.65    inference(forward_demodulation,[],[f298,f22])).
% 2.13/0.65  fof(f298,plain,(
% 2.13/0.65    ( ! [X24,X23,X21,X22] : (r2_hidden(sK6(X21,k4_xboole_0(X22,k4_xboole_0(X22,k1_xboole_0)),X24),X24) | k4_xboole_0(X21,k4_xboole_0(X21,k4_xboole_0(X22,k4_xboole_0(X22,k4_xboole_0(X23,X23))))) = X24) )),
% 2.13/0.65    inference(backward_demodulation,[],[f250,f270])).
% 2.13/0.65  fof(f250,plain,(
% 2.13/0.65    ( ! [X24,X23,X21,X22] : (r2_hidden(sK6(X21,k4_xboole_0(X22,k4_xboole_0(X22,k4_xboole_0(X23,X23))),X24),X24) | k4_xboole_0(X21,k4_xboole_0(X21,k4_xboole_0(X22,k4_xboole_0(X22,k4_xboole_0(X23,X23))))) = X24) )),
% 2.13/0.65    inference(resolution,[],[f46,f111])).
% 2.13/0.65  fof(f111,plain,(
% 2.13/0.65    ( ! [X2,X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X2))))) )),
% 2.13/0.65    inference(resolution,[],[f110,f42])).
% 2.13/0.65  fof(f110,plain,(
% 2.13/0.65    ( ! [X12,X13] : (r1_xboole_0(X12,k4_xboole_0(X13,X13))) )),
% 2.13/0.65    inference(resolution,[],[f88,f62])).
% 2.13/0.65  fof(f88,plain,(
% 2.13/0.65    ( ! [X2,X3] : (r2_hidden(sK4(X2,X3),X3) | r1_xboole_0(X2,X3)) )),
% 2.13/0.65    inference(resolution,[],[f41,f52])).
% 2.13/0.65  fof(f52,plain,(
% 2.13/0.65    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r2_hidden(X3,X1)) )),
% 2.13/0.65    inference(equality_resolution,[],[f44])).
% 2.13/0.65  fof(f44,plain,(
% 2.13/0.65    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 2.13/0.65    inference(definition_unfolding,[],[f36,f23])).
% 2.13/0.65  fof(f36,plain,(
% 2.13/0.65    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 2.13/0.65    inference(cnf_transformation,[],[f2])).
% 2.13/0.65  fof(f41,plain,(
% 2.13/0.65    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r1_xboole_0(X0,X1)) )),
% 2.13/0.65    inference(definition_unfolding,[],[f25,f23])).
% 2.13/0.65  fof(f25,plain,(
% 2.13/0.65    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))) )),
% 2.13/0.65    inference(cnf_transformation,[],[f15])).
% 2.13/0.65  fof(f1029,plain,(
% 2.13/0.65    ( ! [X1] : (~r2_hidden(X1,sK0) | r1_tarski(sK1,sK3)) )),
% 2.13/0.65    inference(forward_demodulation,[],[f1027,f22])).
% 2.13/0.65  fof(f1027,plain,(
% 2.13/0.65    ( ! [X1] : (~r2_hidden(X1,k4_xboole_0(sK0,k1_xboole_0)) | r1_tarski(sK1,sK3)) )),
% 2.13/0.65    inference(superposition,[],[f1006,f270])).
% 2.13/0.65  fof(f1006,plain,(
% 2.13/0.65    ( ! [X0,X1] : (~r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,X1))) | r1_tarski(sK1,sK3)) )),
% 2.13/0.65    inference(resolution,[],[f1005,f42])).
% 2.13/0.65  fof(f1005,plain,(
% 2.13/0.65    ( ! [X0] : (r1_xboole_0(sK0,X0) | r1_tarski(sK1,sK3)) )),
% 2.13/0.65    inference(duplicate_literal_removal,[],[f999])).
% 2.13/0.65  fof(f999,plain,(
% 2.13/0.65    ( ! [X0] : (r1_xboole_0(sK0,X0) | r1_tarski(sK1,sK3) | r1_tarski(sK1,sK3)) )),
% 2.13/0.65    inference(resolution,[],[f730,f28])).
% 2.13/0.65  fof(f28,plain,(
% 2.13/0.65    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 2.13/0.65    inference(cnf_transformation,[],[f16])).
% 2.13/0.65  fof(f16,plain,(
% 2.13/0.65    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.13/0.65    inference(ennf_transformation,[],[f1])).
% 2.13/0.65  fof(f1,axiom,(
% 2.13/0.65    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.13/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 2.13/0.65  fof(f730,plain,(
% 2.13/0.65    ( ! [X0,X1] : (r2_hidden(sK5(sK1,X0),sK3) | r1_xboole_0(sK0,X1) | r1_tarski(sK1,X0)) )),
% 2.13/0.65    inference(resolution,[],[f589,f87])).
% 2.13/0.65  fof(f87,plain,(
% 2.13/0.65    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 2.13/0.65    inference(resolution,[],[f41,f53])).
% 2.13/0.65  fof(f53,plain,(
% 2.13/0.65    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r2_hidden(X3,X0)) )),
% 2.13/0.65    inference(equality_resolution,[],[f45])).
% 2.13/0.65  fof(f45,plain,(
% 2.13/0.65    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 2.13/0.65    inference(definition_unfolding,[],[f35,f23])).
% 2.13/0.65  fof(f35,plain,(
% 2.13/0.65    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 2.13/0.65    inference(cnf_transformation,[],[f2])).
% 2.13/0.65  fof(f589,plain,(
% 2.13/0.65    ( ! [X4,X5] : (~r2_hidden(X4,sK0) | r2_hidden(sK5(sK1,X5),sK3) | r1_tarski(sK1,X5)) )),
% 2.13/0.65    inference(resolution,[],[f583,f27])).
% 2.13/0.65  fof(f27,plain,(
% 2.13/0.65    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.13/0.65    inference(cnf_transformation,[],[f16])).
% 2.13/0.65  fof(f583,plain,(
% 2.13/0.65    ( ! [X0,X1] : (~r2_hidden(X1,sK1) | ~r2_hidden(X0,sK0) | r2_hidden(X1,sK3)) )),
% 2.13/0.65    inference(resolution,[],[f579,f39])).
% 2.13/0.65  fof(f39,plain,(
% 2.13/0.65    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 2.13/0.65    inference(cnf_transformation,[],[f8])).
% 2.13/0.65  fof(f8,axiom,(
% 2.13/0.65    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 2.13/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 2.13/0.65  fof(f579,plain,(
% 2.13/0.65    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK2,sK3)) | ~r2_hidden(X0,sK0) | ~r2_hidden(X1,sK1)) )),
% 2.13/0.65    inference(resolution,[],[f126,f18])).
% 2.13/0.65  fof(f18,plain,(
% 2.13/0.65    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 2.13/0.65    inference(cnf_transformation,[],[f14])).
% 2.13/0.65  fof(f126,plain,(
% 2.13/0.65    ( ! [X12,X10,X8,X11,X9] : (~r1_tarski(k2_zfmisc_1(X11,X9),X12) | ~r2_hidden(X10,X11) | r2_hidden(k4_tarski(X10,X8),X12) | ~r2_hidden(X8,X9)) )),
% 2.13/0.65    inference(resolution,[],[f40,f26])).
% 2.13/0.65  fof(f26,plain,(
% 2.13/0.65    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.13/0.65    inference(cnf_transformation,[],[f16])).
% 2.13/0.65  fof(f40,plain,(
% 2.13/0.65    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 2.13/0.65    inference(cnf_transformation,[],[f8])).
% 2.13/0.65  fof(f795,plain,(
% 2.13/0.65    r1_tarski(sK0,sK2) | k1_xboole_0 = sK1),
% 2.13/0.65    inference(resolution,[],[f781,f363])).
% 2.13/0.65  fof(f781,plain,(
% 2.13/0.65    ( ! [X1] : (~r2_hidden(X1,sK1) | r1_tarski(sK0,sK2)) )),
% 2.13/0.65    inference(forward_demodulation,[],[f779,f22])).
% 2.13/0.65  fof(f779,plain,(
% 2.13/0.65    ( ! [X1] : (~r2_hidden(X1,k4_xboole_0(sK1,k1_xboole_0)) | r1_tarski(sK0,sK2)) )),
% 2.13/0.65    inference(superposition,[],[f759,f270])).
% 2.13/0.65  fof(f759,plain,(
% 2.13/0.65    ( ! [X0,X1] : (~r2_hidden(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,X1))) | r1_tarski(sK0,sK2)) )),
% 2.13/0.65    inference(resolution,[],[f758,f42])).
% 2.13/0.65  fof(f758,plain,(
% 2.13/0.65    ( ! [X0] : (r1_xboole_0(sK1,X0) | r1_tarski(sK0,sK2)) )),
% 2.13/0.65    inference(duplicate_literal_removal,[],[f754])).
% 2.13/0.65  fof(f754,plain,(
% 2.13/0.65    ( ! [X0] : (r1_xboole_0(sK1,X0) | r1_tarski(sK0,sK2) | r1_tarski(sK0,sK2)) )),
% 2.13/0.65    inference(resolution,[],[f623,f28])).
% 2.13/0.65  fof(f623,plain,(
% 2.13/0.65    ( ! [X4,X5] : (r2_hidden(sK5(sK0,X4),sK2) | r1_xboole_0(sK1,X5) | r1_tarski(sK0,X4)) )),
% 2.13/0.65    inference(resolution,[],[f604,f27])).
% 2.13/0.65  fof(f604,plain,(
% 2.13/0.65    ( ! [X0,X1] : (~r2_hidden(X0,sK0) | r2_hidden(X0,sK2) | r1_xboole_0(sK1,X1)) )),
% 2.13/0.65    inference(resolution,[],[f584,f87])).
% 2.13/0.65  fof(f584,plain,(
% 2.13/0.65    ( ! [X2,X3] : (~r2_hidden(X3,sK1) | ~r2_hidden(X2,sK0) | r2_hidden(X2,sK2)) )),
% 2.13/0.65    inference(resolution,[],[f579,f38])).
% 2.13/0.65  fof(f38,plain,(
% 2.13/0.65    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 2.13/0.65    inference(cnf_transformation,[],[f8])).
% 2.13/0.65  fof(f19,plain,(
% 2.13/0.65    k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 2.13/0.65    inference(cnf_transformation,[],[f14])).
% 2.13/0.65  % SZS output end Proof for theBenchmark
% 2.13/0.65  % (29472)------------------------------
% 2.13/0.65  % (29472)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.13/0.66  % (29472)Termination reason: Refutation
% 2.13/0.66  
% 2.13/0.66  % (29472)Memory used [KB]: 7291
% 2.13/0.66  % (29472)Time elapsed: 0.169 s
% 2.13/0.66  % (29472)------------------------------
% 2.13/0.66  % (29472)------------------------------
% 2.13/0.66  % (29465)Success in time 0.296 s
%------------------------------------------------------------------------------
