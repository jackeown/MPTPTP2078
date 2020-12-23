%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:09 EST 2020

% Result     : Theorem 9.49s
% Output     : Refutation 9.49s
% Verified   : 
% Statistics : Number of formulae       :  153 (1560 expanded)
%              Number of leaves         :   20 ( 522 expanded)
%              Depth                    :   23
%              Number of atoms          :  187 (1806 expanded)
%              Number of equality atoms :  169 (1477 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    8 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7600,plain,(
    $false ),
    inference(subsumption_resolution,[],[f6990,f7599])).

fof(f7599,plain,(
    ! [X37,X35,X36] : k2_zfmisc_1(X37,k4_xboole_0(X35,X36)) = k4_xboole_0(k2_zfmisc_1(X37,X35),k2_zfmisc_1(X37,X36)) ),
    inference(forward_demodulation,[],[f7598,f6818])).

fof(f6818,plain,(
    ! [X6,X4,X5,X3] : k2_zfmisc_1(X3,X4) = k4_xboole_0(k2_zfmisc_1(X3,X4),k2_zfmisc_1(X5,k4_xboole_0(X6,X4))) ),
    inference(forward_demodulation,[],[f6725,f2005])).

fof(f2005,plain,(
    ! [X8] : k4_xboole_0(X8,k1_xboole_0) = X8 ),
    inference(backward_demodulation,[],[f350,f1988])).

fof(f1988,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(unit_resulting_resolution,[],[f1807,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X0,X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_zfmisc_1(X0,X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(X0,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_zfmisc_1)).

fof(f1807,plain,(
    ! [X8,X9] : r1_tarski(k4_xboole_0(X9,X9),X8) ),
    inference(superposition,[],[f83,f970])).

fof(f970,plain,(
    ! [X8,X9] : k2_xboole_0(X8,k4_xboole_0(X9,X9)) = X8 ),
    inference(forward_demodulation,[],[f931,f350])).

fof(f931,plain,(
    ! [X8,X9] : k4_xboole_0(X8,k4_xboole_0(X9,X9)) = k2_xboole_0(X8,k4_xboole_0(X9,X9)) ),
    inference(superposition,[],[f350,f37])).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f83,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(unit_resulting_resolution,[],[f34,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f350,plain,(
    ! [X8,X9] : k4_xboole_0(X8,k4_xboole_0(X9,X9)) = X8 ),
    inference(forward_demodulation,[],[f311,f77])).

fof(f77,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(unit_resulting_resolution,[],[f34,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(forward_demodulation,[],[f40,f38])).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

fof(f311,plain,(
    ! [X8,X9] : k2_xboole_0(k4_xboole_0(X8,X9),X8) = k4_xboole_0(X8,k4_xboole_0(X9,X9)) ),
    inference(superposition,[],[f62,f38])).

fof(f62,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f48,f35])).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f48,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f6725,plain,(
    ! [X6,X4,X5,X3] : k4_xboole_0(k2_zfmisc_1(X3,X4),k1_xboole_0) = k4_xboole_0(k2_zfmisc_1(X3,X4),k2_zfmisc_1(X5,k4_xboole_0(X6,X4))) ),
    inference(superposition,[],[f57,f2100])).

fof(f2100,plain,(
    ! [X28,X26,X27,X25] : k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(X27,X25),k4_xboole_0(k2_zfmisc_1(X27,X25),k2_zfmisc_1(X28,k4_xboole_0(X26,X25)))) ),
    inference(forward_demodulation,[],[f2021,f68])).

fof(f68,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f2021,plain,(
    ! [X28,X26,X27,X25] : k4_xboole_0(k2_zfmisc_1(X27,X25),k4_xboole_0(k2_zfmisc_1(X27,X25),k2_zfmisc_1(X28,k4_xboole_0(X26,X25)))) = k2_zfmisc_1(k4_xboole_0(X27,k4_xboole_0(X27,X28)),k1_xboole_0) ),
    inference(backward_demodulation,[],[f1360,f1988])).

fof(f1360,plain,(
    ! [X28,X26,X27,X25] : k4_xboole_0(k2_zfmisc_1(X27,X25),k4_xboole_0(k2_zfmisc_1(X27,X25),k2_zfmisc_1(X28,k4_xboole_0(X26,X25)))) = k2_zfmisc_1(k4_xboole_0(X27,k4_xboole_0(X27,X28)),k4_xboole_0(X25,X25)) ),
    inference(forward_demodulation,[],[f1359,f1096])).

fof(f1096,plain,(
    ! [X10,X8,X11,X9] : k4_xboole_0(k2_zfmisc_1(X10,k4_xboole_0(X8,k4_xboole_0(X8,X9))),k4_xboole_0(k2_zfmisc_1(X10,k4_xboole_0(X8,k4_xboole_0(X8,X9))),k2_zfmisc_1(X11,k4_xboole_0(X8,X8)))) = k2_zfmisc_1(k4_xboole_0(X10,k4_xboole_0(X10,X11)),k4_xboole_0(X8,X8)) ),
    inference(backward_demodulation,[],[f877,f1092])).

fof(f1092,plain,(
    ! [X66,X64] : k4_xboole_0(X64,X64) = k4_xboole_0(X64,k2_xboole_0(X66,X64)) ),
    inference(forward_demodulation,[],[f1091,f38])).

fof(f1091,plain,(
    ! [X66,X64] : k4_xboole_0(X64,X64) = k4_xboole_0(X64,k2_xboole_0(X66,k4_xboole_0(X64,X66))) ),
    inference(forward_demodulation,[],[f1090,f970])).

fof(f1090,plain,(
    ! [X66,X64,X65] : k4_xboole_0(X64,X64) = k4_xboole_0(X64,k2_xboole_0(X66,k4_xboole_0(X64,k2_xboole_0(X66,k4_xboole_0(X65,X65))))) ),
    inference(forward_demodulation,[],[f1089,f350])).

fof(f1089,plain,(
    ! [X66,X64,X65] : k4_xboole_0(X64,k2_xboole_0(X66,k4_xboole_0(X64,k2_xboole_0(X66,k4_xboole_0(X65,X65))))) = k4_xboole_0(k4_xboole_0(X64,X64),k4_xboole_0(X66,X66)) ),
    inference(forward_demodulation,[],[f957,f350])).

fof(f957,plain,(
    ! [X66,X64,X65] : k4_xboole_0(X64,k2_xboole_0(X66,k4_xboole_0(X64,k2_xboole_0(X66,k4_xboole_0(X65,X65))))) = k4_xboole_0(k4_xboole_0(X64,X64),k4_xboole_0(X66,k4_xboole_0(X66,k4_xboole_0(X65,X65)))) ),
    inference(superposition,[],[f73,f350])).

fof(f73,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(X0,k2_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X2,X1)))) ),
    inference(forward_demodulation,[],[f72,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f72,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(X0,k2_xboole_0(X2,k4_xboole_0(k4_xboole_0(X0,X2),X1))) ),
    inference(forward_demodulation,[],[f63,f45])).

fof(f63,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(k4_xboole_0(X0,X2),X1)) ),
    inference(definition_unfolding,[],[f49,f35,f35,f35])).

fof(f49,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k4_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k4_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_xboole_1)).

fof(f877,plain,(
    ! [X10,X8,X11,X9] : k2_zfmisc_1(k4_xboole_0(X10,k4_xboole_0(X10,X11)),k4_xboole_0(X8,k2_xboole_0(X9,X8))) = k4_xboole_0(k2_zfmisc_1(X10,k4_xboole_0(X8,k4_xboole_0(X8,X9))),k4_xboole_0(k2_zfmisc_1(X10,k4_xboole_0(X8,k4_xboole_0(X8,X9))),k2_zfmisc_1(X11,k4_xboole_0(X8,X8)))) ),
    inference(forward_demodulation,[],[f876,f350])).

fof(f876,plain,(
    ! [X10,X8,X11,X9] : k2_zfmisc_1(k4_xboole_0(X10,k4_xboole_0(X10,X11)),k4_xboole_0(X8,k2_xboole_0(X9,X8))) = k4_xboole_0(k2_zfmisc_1(X10,k4_xboole_0(X8,k4_xboole_0(X8,X9))),k4_xboole_0(k2_zfmisc_1(X10,k4_xboole_0(X8,k4_xboole_0(X8,X9))),k2_zfmisc_1(X11,k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X9,X9)))))) ),
    inference(forward_demodulation,[],[f875,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f44,f35,f35])).

fof(f44,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f875,plain,(
    ! [X10,X8,X11,X9] : k4_xboole_0(k2_zfmisc_1(X10,k4_xboole_0(X8,k4_xboole_0(X8,X9))),k4_xboole_0(k2_zfmisc_1(X10,k4_xboole_0(X8,k4_xboole_0(X8,X9))),k2_zfmisc_1(X11,k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X9)))) = k2_zfmisc_1(k4_xboole_0(X10,k4_xboole_0(X10,X11)),k4_xboole_0(X8,k2_xboole_0(X9,X8))) ),
    inference(forward_demodulation,[],[f874,f38])).

fof(f874,plain,(
    ! [X10,X8,X11,X9] : k4_xboole_0(k2_zfmisc_1(X10,k4_xboole_0(X8,k4_xboole_0(X8,X9))),k4_xboole_0(k2_zfmisc_1(X10,k4_xboole_0(X8,k4_xboole_0(X8,X9))),k2_zfmisc_1(X11,k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X9)))) = k2_zfmisc_1(k4_xboole_0(X10,k4_xboole_0(X10,X11)),k4_xboole_0(X8,k2_xboole_0(X9,k4_xboole_0(X8,X9)))) ),
    inference(forward_demodulation,[],[f873,f818])).

fof(f818,plain,(
    ! [X2,X0,X3,X1] : k4_xboole_0(k2_zfmisc_1(X2,X0),k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X3,k4_xboole_0(X0,X1)))) = k2_zfmisc_1(k4_xboole_0(X2,k4_xboole_0(X2,X3)),k4_xboole_0(X0,X1)) ),
    inference(superposition,[],[f67,f57])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k4_xboole_0(k2_zfmisc_1(X0,X2),k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) ),
    inference(definition_unfolding,[],[f56,f35,f35,f35])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f873,plain,(
    ! [X10,X8,X11,X9] : k4_xboole_0(k2_zfmisc_1(X10,k4_xboole_0(X8,k4_xboole_0(X8,X9))),k4_xboole_0(k2_zfmisc_1(X10,k4_xboole_0(X8,k4_xboole_0(X8,X9))),k2_zfmisc_1(X11,k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X9)))) = k4_xboole_0(k2_zfmisc_1(X10,X8),k4_xboole_0(k2_zfmisc_1(X10,X8),k2_zfmisc_1(X11,k4_xboole_0(X8,k2_xboole_0(X9,k4_xboole_0(X8,X9)))))) ),
    inference(forward_demodulation,[],[f872,f45])).

fof(f872,plain,(
    ! [X10,X8,X11,X9] : k4_xboole_0(k2_zfmisc_1(X10,k4_xboole_0(X8,k4_xboole_0(X8,X9))),k4_xboole_0(k2_zfmisc_1(X10,k4_xboole_0(X8,k4_xboole_0(X8,X9))),k2_zfmisc_1(X11,k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X9)))) = k4_xboole_0(k2_zfmisc_1(X10,X8),k4_xboole_0(k2_zfmisc_1(X10,X8),k2_zfmisc_1(X11,k4_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X8,X9))))) ),
    inference(forward_demodulation,[],[f871,f863])).

fof(f863,plain,(
    ! [X14,X17,X15,X18,X16] : k4_xboole_0(k2_zfmisc_1(X17,k4_xboole_0(X14,k4_xboole_0(X14,X15))),k4_xboole_0(k2_zfmisc_1(X17,k4_xboole_0(X14,k4_xboole_0(X14,X15))),k2_zfmisc_1(X18,X16))) = k4_xboole_0(k2_zfmisc_1(X17,X14),k4_xboole_0(k2_zfmisc_1(X17,X14),k2_zfmisc_1(X18,k4_xboole_0(X15,k4_xboole_0(X14,X16))))) ),
    inference(forward_demodulation,[],[f862,f310])).

fof(f310,plain,(
    ! [X6,X7,X5] : k4_xboole_0(X5,k4_xboole_0(X6,X7)) = k4_xboole_0(X5,k4_xboole_0(X6,k4_xboole_0(X6,k4_xboole_0(X5,X7)))) ),
    inference(superposition,[],[f62,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(definition_unfolding,[],[f47,f35])).

fof(f47,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l36_xboole_1)).

fof(f862,plain,(
    ! [X14,X17,X15,X18,X16] : k4_xboole_0(k2_zfmisc_1(X17,k4_xboole_0(X14,k4_xboole_0(X14,X15))),k4_xboole_0(k2_zfmisc_1(X17,k4_xboole_0(X14,k4_xboole_0(X14,X15))),k2_zfmisc_1(X18,X16))) = k4_xboole_0(k2_zfmisc_1(X17,X14),k4_xboole_0(k2_zfmisc_1(X17,X14),k2_zfmisc_1(X18,k4_xboole_0(X15,k4_xboole_0(X14,k4_xboole_0(X14,k4_xboole_0(X15,X16))))))) ),
    inference(forward_demodulation,[],[f861,f67])).

fof(f861,plain,(
    ! [X14,X17,X15,X18,X16] : k4_xboole_0(k2_zfmisc_1(X17,k4_xboole_0(X14,k4_xboole_0(X14,X15))),k4_xboole_0(k2_zfmisc_1(X17,k4_xboole_0(X14,k4_xboole_0(X14,X15))),k2_zfmisc_1(X18,X16))) = k2_zfmisc_1(k4_xboole_0(X17,k4_xboole_0(X17,X18)),k4_xboole_0(X14,k4_xboole_0(X14,k4_xboole_0(X15,k4_xboole_0(X14,k4_xboole_0(X14,k4_xboole_0(X15,X16))))))) ),
    inference(forward_demodulation,[],[f812,f59])).

fof(f812,plain,(
    ! [X14,X17,X15,X18,X16] : k4_xboole_0(k2_zfmisc_1(X17,k4_xboole_0(X14,k4_xboole_0(X14,X15))),k4_xboole_0(k2_zfmisc_1(X17,k4_xboole_0(X14,k4_xboole_0(X14,X15))),k2_zfmisc_1(X18,X16))) = k2_zfmisc_1(k4_xboole_0(X17,k4_xboole_0(X17,X18)),k4_xboole_0(k4_xboole_0(X14,k4_xboole_0(X14,X15)),k4_xboole_0(X14,k4_xboole_0(X14,k4_xboole_0(X15,X16))))) ),
    inference(superposition,[],[f67,f59])).

fof(f871,plain,(
    ! [X10,X8,X11,X9] : k4_xboole_0(k2_zfmisc_1(X10,k4_xboole_0(X8,k4_xboole_0(X8,X9))),k4_xboole_0(k2_zfmisc_1(X10,k4_xboole_0(X8,k4_xboole_0(X8,X9))),k2_zfmisc_1(X11,k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X9)))) = k4_xboole_0(k2_zfmisc_1(X10,k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X8,X9)))),k4_xboole_0(k2_zfmisc_1(X10,k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X8,X9)))),k2_zfmisc_1(X11,X9))) ),
    inference(forward_demodulation,[],[f819,f860])).

fof(f860,plain,(
    ! [X12,X10,X13,X11,X9] : k4_xboole_0(k2_zfmisc_1(X12,k4_xboole_0(X9,X10)),k4_xboole_0(k2_zfmisc_1(X12,k4_xboole_0(X9,X10)),k2_zfmisc_1(X13,X11))) = k2_zfmisc_1(k4_xboole_0(X12,k4_xboole_0(X12,X13)),k4_xboole_0(X9,k2_xboole_0(X10,k4_xboole_0(X9,k2_xboole_0(X10,X11))))) ),
    inference(forward_demodulation,[],[f811,f45])).

fof(f811,plain,(
    ! [X12,X10,X13,X11,X9] : k4_xboole_0(k2_zfmisc_1(X12,k4_xboole_0(X9,X10)),k4_xboole_0(k2_zfmisc_1(X12,k4_xboole_0(X9,X10)),k2_zfmisc_1(X13,X11))) = k2_zfmisc_1(k4_xboole_0(X12,k4_xboole_0(X12,X13)),k4_xboole_0(k4_xboole_0(X9,X10),k4_xboole_0(X9,k2_xboole_0(X10,X11)))) ),
    inference(superposition,[],[f67,f45])).

fof(f819,plain,(
    ! [X10,X8,X11,X9] : k4_xboole_0(k2_zfmisc_1(X10,k4_xboole_0(X8,k4_xboole_0(X8,X9))),k4_xboole_0(k2_zfmisc_1(X10,k4_xboole_0(X8,k4_xboole_0(X8,X9))),k2_zfmisc_1(X11,k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X9)))) = k2_zfmisc_1(k4_xboole_0(X10,k4_xboole_0(X10,X11)),k4_xboole_0(X8,k2_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),k4_xboole_0(X8,k2_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X9))))) ),
    inference(superposition,[],[f67,f73])).

fof(f1359,plain,(
    ! [X28,X26,X27,X25] : k4_xboole_0(k2_zfmisc_1(X27,X25),k4_xboole_0(k2_zfmisc_1(X27,X25),k2_zfmisc_1(X28,k4_xboole_0(X26,X25)))) = k4_xboole_0(k2_zfmisc_1(X27,k4_xboole_0(X25,k4_xboole_0(X25,X26))),k4_xboole_0(k2_zfmisc_1(X27,k4_xboole_0(X25,k4_xboole_0(X25,X26))),k2_zfmisc_1(X28,k4_xboole_0(X25,X25)))) ),
    inference(forward_demodulation,[],[f1358,f350])).

fof(f1358,plain,(
    ! [X28,X26,X27,X25] : k4_xboole_0(k2_zfmisc_1(X27,X25),k4_xboole_0(k2_zfmisc_1(X27,X25),k2_zfmisc_1(X28,k4_xboole_0(X26,X25)))) = k4_xboole_0(k2_zfmisc_1(X27,k4_xboole_0(X25,k4_xboole_0(X25,X26))),k4_xboole_0(k2_zfmisc_1(X27,k4_xboole_0(X25,k4_xboole_0(X25,X26))),k2_zfmisc_1(X28,k4_xboole_0(X25,k4_xboole_0(X25,k4_xboole_0(X26,X26)))))) ),
    inference(forward_demodulation,[],[f1357,f59])).

fof(f1357,plain,(
    ! [X28,X26,X27,X25] : k4_xboole_0(k2_zfmisc_1(X27,k4_xboole_0(X25,k4_xboole_0(X25,X26))),k4_xboole_0(k2_zfmisc_1(X27,k4_xboole_0(X25,k4_xboole_0(X25,X26))),k2_zfmisc_1(X28,k4_xboole_0(k4_xboole_0(X25,k4_xboole_0(X25,X26)),X26)))) = k4_xboole_0(k2_zfmisc_1(X27,X25),k4_xboole_0(k2_zfmisc_1(X27,X25),k2_zfmisc_1(X28,k4_xboole_0(X26,X25)))) ),
    inference(forward_demodulation,[],[f1356,f1101])).

fof(f1101,plain,(
    ! [X14,X15] : k4_xboole_0(X14,X15) = k4_xboole_0(X14,k4_xboole_0(X15,k4_xboole_0(X15,X14))) ),
    inference(forward_demodulation,[],[f1097,f970])).

fof(f1097,plain,(
    ! [X14,X15] : k4_xboole_0(X14,k4_xboole_0(X15,k4_xboole_0(X15,X14))) = k4_xboole_0(X14,k2_xboole_0(X15,k4_xboole_0(X14,X14))) ),
    inference(backward_demodulation,[],[f940,f1092])).

fof(f940,plain,(
    ! [X14,X15] : k4_xboole_0(X14,k2_xboole_0(X15,k4_xboole_0(X14,k2_xboole_0(X15,X14)))) = k4_xboole_0(X14,k4_xboole_0(X15,k4_xboole_0(X15,X14))) ),
    inference(superposition,[],[f73,f350])).

fof(f1356,plain,(
    ! [X28,X26,X27,X25] : k4_xboole_0(k2_zfmisc_1(X27,k4_xboole_0(X25,k4_xboole_0(X25,X26))),k4_xboole_0(k2_zfmisc_1(X27,k4_xboole_0(X25,k4_xboole_0(X25,X26))),k2_zfmisc_1(X28,k4_xboole_0(k4_xboole_0(X25,k4_xboole_0(X25,X26)),X26)))) = k4_xboole_0(k2_zfmisc_1(X27,X25),k4_xboole_0(k2_zfmisc_1(X27,X25),k2_zfmisc_1(X28,k4_xboole_0(X26,k4_xboole_0(X25,k4_xboole_0(X25,X26)))))) ),
    inference(forward_demodulation,[],[f1154,f67])).

fof(f1154,plain,(
    ! [X28,X26,X27,X25] : k4_xboole_0(k2_zfmisc_1(X27,k4_xboole_0(X25,k4_xboole_0(X25,X26))),k4_xboole_0(k2_zfmisc_1(X27,k4_xboole_0(X25,k4_xboole_0(X25,X26))),k2_zfmisc_1(X28,k4_xboole_0(k4_xboole_0(X25,k4_xboole_0(X25,X26)),X26)))) = k2_zfmisc_1(k4_xboole_0(X27,k4_xboole_0(X27,X28)),k4_xboole_0(X25,k4_xboole_0(X25,k4_xboole_0(X26,k4_xboole_0(X25,k4_xboole_0(X25,X26)))))) ),
    inference(superposition,[],[f67,f974])).

fof(f974,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(backward_demodulation,[],[f73,f971])).

fof(f971,plain,(
    ! [X12,X13,X11] : k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X12,X13))) = k4_xboole_0(X11,k2_xboole_0(X13,k4_xboole_0(X11,k2_xboole_0(X13,X12)))) ),
    inference(backward_demodulation,[],[f712,f970])).

fof(f712,plain,(
    ! [X12,X13,X11] : k4_xboole_0(X11,k2_xboole_0(X13,k4_xboole_0(X11,k2_xboole_0(X13,X12)))) = k2_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X12,X13))),k4_xboole_0(X11,X11)) ),
    inference(forward_demodulation,[],[f711,f59])).

fof(f711,plain,(
    ! [X12,X13,X11] : k4_xboole_0(X11,k2_xboole_0(X13,k4_xboole_0(X11,k2_xboole_0(X13,X12)))) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),X13),k4_xboole_0(X11,X11)) ),
    inference(forward_demodulation,[],[f710,f350])).

fof(f710,plain,(
    ! [X12,X13,X11] : k4_xboole_0(X11,k2_xboole_0(X13,k4_xboole_0(X11,k2_xboole_0(X13,X12)))) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),X13),k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X12,X12)))) ),
    inference(forward_demodulation,[],[f600,f59])).

fof(f600,plain,(
    ! [X12,X13,X11] : k2_xboole_0(k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),X13),k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),X12)) = k4_xboole_0(X11,k2_xboole_0(X13,k4_xboole_0(X11,k2_xboole_0(X13,X12)))) ),
    inference(superposition,[],[f73,f61])).

fof(f57,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f36,f35])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f7598,plain,(
    ! [X37,X35,X36] : k4_xboole_0(k2_zfmisc_1(X37,k4_xboole_0(X35,X36)),k2_zfmisc_1(X37,k4_xboole_0(X35,k4_xboole_0(X35,X36)))) = k4_xboole_0(k2_zfmisc_1(X37,X35),k2_zfmisc_1(X37,X36)) ),
    inference(forward_demodulation,[],[f7534,f474])).

fof(f474,plain,(
    ! [X17,X15,X16] : k4_xboole_0(k2_zfmisc_1(X15,X16),k2_zfmisc_1(X15,X17)) = k4_xboole_0(k2_zfmisc_1(X15,X16),k2_zfmisc_1(X15,k4_xboole_0(X16,k4_xboole_0(X16,X17)))) ),
    inference(superposition,[],[f57,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k2_zfmisc_1(X2,X0),k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) ),
    inference(definition_unfolding,[],[f53,f35,f35])).

fof(f53,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t122_zfmisc_1)).

fof(f7534,plain,(
    ! [X37,X35,X36] : k4_xboole_0(k2_zfmisc_1(X37,k4_xboole_0(X35,X36)),k2_zfmisc_1(X37,k4_xboole_0(X35,k4_xboole_0(X35,X36)))) = k4_xboole_0(k2_zfmisc_1(X37,X35),k2_zfmisc_1(X37,k4_xboole_0(X35,k4_xboole_0(X35,X36)))) ),
    inference(superposition,[],[f150,f125])).

fof(f125,plain,(
    ! [X4,X3] : k2_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X3,k4_xboole_0(X3,X4))) = X3 ),
    inference(superposition,[],[f58,f57])).

fof(f58,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f39,f35])).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f150,plain,(
    ! [X6,X7,X5] : k4_xboole_0(k2_zfmisc_1(X5,X6),k2_zfmisc_1(X5,X7)) = k4_xboole_0(k2_zfmisc_1(X5,k2_xboole_0(X6,X7)),k2_zfmisc_1(X5,X7)) ),
    inference(superposition,[],[f37,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(f6990,plain,(
    k2_zfmisc_1(sK2,k4_xboole_0(sK0,sK1)) != k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)) ),
    inference(subsumption_resolution,[],[f32,f6989])).

fof(f6989,plain,(
    ! [X37,X35,X36] : k2_zfmisc_1(k4_xboole_0(X35,X36),X37) = k4_xboole_0(k2_zfmisc_1(X35,X37),k2_zfmisc_1(X36,X37)) ),
    inference(forward_demodulation,[],[f6988,f6495])).

fof(f6495,plain,(
    ! [X6,X4,X5,X3] : k2_zfmisc_1(X3,X4) = k4_xboole_0(k2_zfmisc_1(X3,X4),k2_zfmisc_1(k4_xboole_0(X5,X3),X6)) ),
    inference(forward_demodulation,[],[f6402,f2005])).

fof(f6402,plain,(
    ! [X6,X4,X5,X3] : k4_xboole_0(k2_zfmisc_1(X3,X4),k2_zfmisc_1(k4_xboole_0(X5,X3),X6)) = k4_xboole_0(k2_zfmisc_1(X3,X4),k1_xboole_0) ),
    inference(superposition,[],[f57,f2099])).

fof(f2099,plain,(
    ! [X24,X23,X21,X22] : k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(X21,X23),k4_xboole_0(k2_zfmisc_1(X21,X23),k2_zfmisc_1(k4_xboole_0(X22,X21),X24))) ),
    inference(forward_demodulation,[],[f2020,f69])).

fof(f69,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f2020,plain,(
    ! [X24,X23,X21,X22] : k4_xboole_0(k2_zfmisc_1(X21,X23),k4_xboole_0(k2_zfmisc_1(X21,X23),k2_zfmisc_1(k4_xboole_0(X22,X21),X24))) = k2_zfmisc_1(k1_xboole_0,k4_xboole_0(X23,k4_xboole_0(X23,X24))) ),
    inference(backward_demodulation,[],[f1355,f1988])).

fof(f1355,plain,(
    ! [X24,X23,X21,X22] : k4_xboole_0(k2_zfmisc_1(X21,X23),k4_xboole_0(k2_zfmisc_1(X21,X23),k2_zfmisc_1(k4_xboole_0(X22,X21),X24))) = k2_zfmisc_1(k4_xboole_0(X21,X21),k4_xboole_0(X23,k4_xboole_0(X23,X24))) ),
    inference(forward_demodulation,[],[f1354,f1095])).

fof(f1095,plain,(
    ! [X10,X8,X11,X9] : k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X10),k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X10),k2_zfmisc_1(k4_xboole_0(X8,X8),X11))) = k2_zfmisc_1(k4_xboole_0(X8,X8),k4_xboole_0(X10,k4_xboole_0(X10,X11))) ),
    inference(backward_demodulation,[],[f853,f1092])).

fof(f853,plain,(
    ! [X10,X8,X11,X9] : k2_zfmisc_1(k4_xboole_0(X8,k2_xboole_0(X9,X8)),k4_xboole_0(X10,k4_xboole_0(X10,X11))) = k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X10),k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X10),k2_zfmisc_1(k4_xboole_0(X8,X8),X11))) ),
    inference(forward_demodulation,[],[f852,f350])).

fof(f852,plain,(
    ! [X10,X8,X11,X9] : k2_zfmisc_1(k4_xboole_0(X8,k2_xboole_0(X9,X8)),k4_xboole_0(X10,k4_xboole_0(X10,X11))) = k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X10),k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X10),k2_zfmisc_1(k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X9,X9))),X11))) ),
    inference(forward_demodulation,[],[f851,f59])).

fof(f851,plain,(
    ! [X10,X8,X11,X9] : k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X10),k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X10),k2_zfmisc_1(k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X9),X11))) = k2_zfmisc_1(k4_xboole_0(X8,k2_xboole_0(X9,X8)),k4_xboole_0(X10,k4_xboole_0(X10,X11))) ),
    inference(forward_demodulation,[],[f850,f38])).

fof(f850,plain,(
    ! [X10,X8,X11,X9] : k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X10),k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X10),k2_zfmisc_1(k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X9),X11))) = k2_zfmisc_1(k4_xboole_0(X8,k2_xboole_0(X9,k4_xboole_0(X8,X9))),k4_xboole_0(X10,k4_xboole_0(X10,X11))) ),
    inference(forward_demodulation,[],[f849,f803])).

fof(f803,plain,(
    ! [X2,X0,X3,X1] : k4_xboole_0(k2_zfmisc_1(X0,X2),k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(k4_xboole_0(X0,X1),X3))) = k2_zfmisc_1(k4_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(superposition,[],[f67,f57])).

fof(f849,plain,(
    ! [X10,X8,X11,X9] : k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X10),k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X10),k2_zfmisc_1(k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X9),X11))) = k4_xboole_0(k2_zfmisc_1(X8,X10),k4_xboole_0(k2_zfmisc_1(X8,X10),k2_zfmisc_1(k4_xboole_0(X8,k2_xboole_0(X9,k4_xboole_0(X8,X9))),X11))) ),
    inference(forward_demodulation,[],[f848,f45])).

fof(f848,plain,(
    ! [X10,X8,X11,X9] : k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X10),k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X10),k2_zfmisc_1(k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X9),X11))) = k4_xboole_0(k2_zfmisc_1(X8,X10),k4_xboole_0(k2_zfmisc_1(X8,X10),k2_zfmisc_1(k4_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X8,X9)),X11))) ),
    inference(forward_demodulation,[],[f847,f839])).

fof(f839,plain,(
    ! [X14,X17,X15,X18,X16] : k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X14,k4_xboole_0(X14,X15)),X17),k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X14,k4_xboole_0(X14,X15)),X17),k2_zfmisc_1(X16,X18))) = k4_xboole_0(k2_zfmisc_1(X14,X17),k4_xboole_0(k2_zfmisc_1(X14,X17),k2_zfmisc_1(k4_xboole_0(X15,k4_xboole_0(X14,X16)),X18))) ),
    inference(forward_demodulation,[],[f838,f310])).

fof(f838,plain,(
    ! [X14,X17,X15,X18,X16] : k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X14,k4_xboole_0(X14,X15)),X17),k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X14,k4_xboole_0(X14,X15)),X17),k2_zfmisc_1(X16,X18))) = k4_xboole_0(k2_zfmisc_1(X14,X17),k4_xboole_0(k2_zfmisc_1(X14,X17),k2_zfmisc_1(k4_xboole_0(X15,k4_xboole_0(X14,k4_xboole_0(X14,k4_xboole_0(X15,X16)))),X18))) ),
    inference(forward_demodulation,[],[f837,f67])).

fof(f837,plain,(
    ! [X14,X17,X15,X18,X16] : k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X14,k4_xboole_0(X14,X15)),X17),k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X14,k4_xboole_0(X14,X15)),X17),k2_zfmisc_1(X16,X18))) = k2_zfmisc_1(k4_xboole_0(X14,k4_xboole_0(X14,k4_xboole_0(X15,k4_xboole_0(X14,k4_xboole_0(X14,k4_xboole_0(X15,X16)))))),k4_xboole_0(X17,k4_xboole_0(X17,X18))) ),
    inference(forward_demodulation,[],[f797,f59])).

fof(f797,plain,(
    ! [X14,X17,X15,X18,X16] : k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X14,k4_xboole_0(X14,X15)),X17),k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X14,k4_xboole_0(X14,X15)),X17),k2_zfmisc_1(X16,X18))) = k2_zfmisc_1(k4_xboole_0(k4_xboole_0(X14,k4_xboole_0(X14,X15)),k4_xboole_0(X14,k4_xboole_0(X14,k4_xboole_0(X15,X16)))),k4_xboole_0(X17,k4_xboole_0(X17,X18))) ),
    inference(superposition,[],[f67,f59])).

fof(f847,plain,(
    ! [X10,X8,X11,X9] : k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X10),k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X10),k2_zfmisc_1(k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X9),X11))) = k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X8,X9))),X10),k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X8,X9))),X10),k2_zfmisc_1(X9,X11))) ),
    inference(forward_demodulation,[],[f804,f836])).

fof(f836,plain,(
    ! [X12,X10,X13,X11,X9] : k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X9,X10),X12),k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X9,X10),X12),k2_zfmisc_1(X11,X13))) = k2_zfmisc_1(k4_xboole_0(X9,k2_xboole_0(X10,k4_xboole_0(X9,k2_xboole_0(X10,X11)))),k4_xboole_0(X12,k4_xboole_0(X12,X13))) ),
    inference(forward_demodulation,[],[f796,f45])).

fof(f796,plain,(
    ! [X12,X10,X13,X11,X9] : k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X9,X10),X12),k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X9,X10),X12),k2_zfmisc_1(X11,X13))) = k2_zfmisc_1(k4_xboole_0(k4_xboole_0(X9,X10),k4_xboole_0(X9,k2_xboole_0(X10,X11))),k4_xboole_0(X12,k4_xboole_0(X12,X13))) ),
    inference(superposition,[],[f67,f45])).

fof(f804,plain,(
    ! [X10,X8,X11,X9] : k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X10),k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X10),k2_zfmisc_1(k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X9),X11))) = k2_zfmisc_1(k4_xboole_0(X8,k2_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),k4_xboole_0(X8,k2_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X9)))),k4_xboole_0(X10,k4_xboole_0(X10,X11))) ),
    inference(superposition,[],[f67,f73])).

fof(f1354,plain,(
    ! [X24,X23,X21,X22] : k4_xboole_0(k2_zfmisc_1(X21,X23),k4_xboole_0(k2_zfmisc_1(X21,X23),k2_zfmisc_1(k4_xboole_0(X22,X21),X24))) = k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X21,k4_xboole_0(X21,X22)),X23),k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X21,k4_xboole_0(X21,X22)),X23),k2_zfmisc_1(k4_xboole_0(X21,X21),X24))) ),
    inference(forward_demodulation,[],[f1353,f350])).

fof(f1353,plain,(
    ! [X24,X23,X21,X22] : k4_xboole_0(k2_zfmisc_1(X21,X23),k4_xboole_0(k2_zfmisc_1(X21,X23),k2_zfmisc_1(k4_xboole_0(X22,X21),X24))) = k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X21,k4_xboole_0(X21,X22)),X23),k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X21,k4_xboole_0(X21,X22)),X23),k2_zfmisc_1(k4_xboole_0(X21,k4_xboole_0(X21,k4_xboole_0(X22,X22))),X24))) ),
    inference(forward_demodulation,[],[f1352,f59])).

fof(f1352,plain,(
    ! [X24,X23,X21,X22] : k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X21,k4_xboole_0(X21,X22)),X23),k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X21,k4_xboole_0(X21,X22)),X23),k2_zfmisc_1(k4_xboole_0(k4_xboole_0(X21,k4_xboole_0(X21,X22)),X22),X24))) = k4_xboole_0(k2_zfmisc_1(X21,X23),k4_xboole_0(k2_zfmisc_1(X21,X23),k2_zfmisc_1(k4_xboole_0(X22,X21),X24))) ),
    inference(forward_demodulation,[],[f1351,f1101])).

fof(f1351,plain,(
    ! [X24,X23,X21,X22] : k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X21,k4_xboole_0(X21,X22)),X23),k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X21,k4_xboole_0(X21,X22)),X23),k2_zfmisc_1(k4_xboole_0(k4_xboole_0(X21,k4_xboole_0(X21,X22)),X22),X24))) = k4_xboole_0(k2_zfmisc_1(X21,X23),k4_xboole_0(k2_zfmisc_1(X21,X23),k2_zfmisc_1(k4_xboole_0(X22,k4_xboole_0(X21,k4_xboole_0(X21,X22))),X24))) ),
    inference(forward_demodulation,[],[f1153,f67])).

fof(f1153,plain,(
    ! [X24,X23,X21,X22] : k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X21,k4_xboole_0(X21,X22)),X23),k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X21,k4_xboole_0(X21,X22)),X23),k2_zfmisc_1(k4_xboole_0(k4_xboole_0(X21,k4_xboole_0(X21,X22)),X22),X24))) = k2_zfmisc_1(k4_xboole_0(X21,k4_xboole_0(X21,k4_xboole_0(X22,k4_xboole_0(X21,k4_xboole_0(X21,X22))))),k4_xboole_0(X23,k4_xboole_0(X23,X24))) ),
    inference(superposition,[],[f67,f974])).

fof(f6988,plain,(
    ! [X37,X35,X36] : k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X35,X36),X37),k2_zfmisc_1(k4_xboole_0(X35,k4_xboole_0(X35,X36)),X37)) = k4_xboole_0(k2_zfmisc_1(X35,X37),k2_zfmisc_1(X36,X37)) ),
    inference(forward_demodulation,[],[f6925,f530])).

fof(f530,plain,(
    ! [X19,X17,X18] : k4_xboole_0(k2_zfmisc_1(X17,X18),k2_zfmisc_1(X19,X18)) = k4_xboole_0(k2_zfmisc_1(X17,X18),k2_zfmisc_1(k4_xboole_0(X17,k4_xboole_0(X17,X19)),X18)) ),
    inference(superposition,[],[f57,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) ),
    inference(definition_unfolding,[],[f52,f35,f35])).

fof(f52,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f6925,plain,(
    ! [X37,X35,X36] : k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X35,X36),X37),k2_zfmisc_1(k4_xboole_0(X35,k4_xboole_0(X35,X36)),X37)) = k4_xboole_0(k2_zfmisc_1(X35,X37),k2_zfmisc_1(k4_xboole_0(X35,k4_xboole_0(X35,X36)),X37)) ),
    inference(superposition,[],[f138,f125])).

fof(f138,plain,(
    ! [X4,X5,X3] : k4_xboole_0(k2_zfmisc_1(X3,X4),k2_zfmisc_1(X5,X4)) = k4_xboole_0(k2_zfmisc_1(k2_xboole_0(X3,X5),X4),k2_zfmisc_1(X5,X4)) ),
    inference(superposition,[],[f37,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f32,plain,
    ( k2_zfmisc_1(sK2,k4_xboole_0(sK0,sK1)) != k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))
    | k2_zfmisc_1(k4_xboole_0(sK0,sK1),sK2) != k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( k2_zfmisc_1(sK2,k4_xboole_0(sK0,sK1)) != k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))
    | k2_zfmisc_1(k4_xboole_0(sK0,sK1),sK2) != k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f28])).

fof(f28,plain,
    ( ? [X0,X1,X2] :
        ( k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) != k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        | k2_zfmisc_1(k4_xboole_0(X0,X1),X2) != k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
   => ( k2_zfmisc_1(sK2,k4_xboole_0(sK0,sK1)) != k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))
      | k2_zfmisc_1(k4_xboole_0(sK0,sK1),sK2) != k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) != k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      | k2_zfmisc_1(k4_xboole_0(X0,X1),X2) != k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:50:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (1688)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (1711)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.51  % (1688)Refutation not found, incomplete strategy% (1688)------------------------------
% 0.21/0.51  % (1688)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (1688)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (1688)Memory used [KB]: 1663
% 0.21/0.51  % (1688)Time elapsed: 0.094 s
% 0.21/0.51  % (1688)------------------------------
% 0.21/0.51  % (1688)------------------------------
% 0.21/0.51  % (1713)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.51  % (1693)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (1690)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (1695)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (1689)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (1711)Refutation not found, incomplete strategy% (1711)------------------------------
% 0.21/0.52  % (1711)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (1711)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (1711)Memory used [KB]: 1663
% 0.21/0.52  % (1711)Time elapsed: 0.099 s
% 0.21/0.52  % (1711)------------------------------
% 0.21/0.52  % (1711)------------------------------
% 0.21/0.52  % (1705)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.52  % (1697)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (1697)Refutation not found, incomplete strategy% (1697)------------------------------
% 0.21/0.52  % (1697)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (1705)Refutation not found, incomplete strategy% (1705)------------------------------
% 0.21/0.52  % (1705)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (1697)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (1697)Memory used [KB]: 10618
% 0.21/0.52  % (1697)Time elapsed: 0.099 s
% 0.21/0.52  % (1697)------------------------------
% 0.21/0.52  % (1697)------------------------------
% 0.21/0.52  % (1700)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (1705)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (1705)Memory used [KB]: 10618
% 0.21/0.52  % (1705)Time elapsed: 0.106 s
% 0.21/0.52  % (1705)------------------------------
% 0.21/0.52  % (1705)------------------------------
% 0.21/0.52  % (1699)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (1713)Refutation not found, incomplete strategy% (1713)------------------------------
% 0.21/0.52  % (1713)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (1713)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (1713)Memory used [KB]: 6268
% 0.21/0.52  % (1713)Time elapsed: 0.101 s
% 0.21/0.52  % (1713)------------------------------
% 0.21/0.52  % (1713)------------------------------
% 0.21/0.52  % (1694)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (1710)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (1717)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  % (1710)Refutation not found, incomplete strategy% (1710)------------------------------
% 0.21/0.53  % (1710)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (1710)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (1710)Memory used [KB]: 10746
% 0.21/0.53  % (1710)Time elapsed: 0.082 s
% 0.21/0.53  % (1710)------------------------------
% 0.21/0.53  % (1710)------------------------------
% 0.21/0.53  % (1701)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  % (1702)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (1709)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (1690)Refutation not found, incomplete strategy% (1690)------------------------------
% 0.21/0.54  % (1690)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (1690)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (1690)Memory used [KB]: 10746
% 0.21/0.54  % (1690)Time elapsed: 0.117 s
% 0.21/0.54  % (1690)------------------------------
% 0.21/0.54  % (1690)------------------------------
% 0.21/0.54  % (1709)Refutation not found, incomplete strategy% (1709)------------------------------
% 0.21/0.54  % (1709)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (1709)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (1709)Memory used [KB]: 1663
% 0.21/0.54  % (1709)Time elapsed: 0.123 s
% 0.21/0.54  % (1709)------------------------------
% 0.21/0.54  % (1709)------------------------------
% 0.21/0.54  % (1692)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (1715)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (1714)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (1692)Refutation not found, incomplete strategy% (1692)------------------------------
% 0.21/0.54  % (1692)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (1692)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (1692)Memory used [KB]: 6140
% 0.21/0.54  % (1692)Time elapsed: 0.127 s
% 0.21/0.54  % (1692)------------------------------
% 0.21/0.54  % (1692)------------------------------
% 0.21/0.54  % (1706)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (1698)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (1691)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (1716)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (1712)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (1698)Refutation not found, incomplete strategy% (1698)------------------------------
% 0.21/0.55  % (1698)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (1698)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (1698)Memory used [KB]: 10618
% 0.21/0.55  % (1698)Time elapsed: 0.132 s
% 0.21/0.55  % (1698)------------------------------
% 0.21/0.55  % (1698)------------------------------
% 0.21/0.55  % (1703)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (1714)Refutation not found, incomplete strategy% (1714)------------------------------
% 0.21/0.55  % (1714)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (1703)Refutation not found, incomplete strategy% (1703)------------------------------
% 0.21/0.55  % (1703)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (1703)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (1703)Memory used [KB]: 6140
% 0.21/0.55  % (1703)Time elapsed: 0.002 s
% 0.21/0.55  % (1703)------------------------------
% 0.21/0.55  % (1703)------------------------------
% 0.21/0.55  % (1714)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (1714)Memory used [KB]: 10746
% 0.21/0.55  % (1714)Time elapsed: 0.130 s
% 0.21/0.55  % (1714)------------------------------
% 0.21/0.55  % (1714)------------------------------
% 0.21/0.55  % (1708)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (1704)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (1708)Refutation not found, incomplete strategy% (1708)------------------------------
% 0.21/0.55  % (1708)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (1708)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (1708)Memory used [KB]: 10746
% 0.21/0.55  % (1708)Time elapsed: 0.140 s
% 0.21/0.55  % (1708)------------------------------
% 0.21/0.55  % (1708)------------------------------
% 0.21/0.55  % (1707)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.56  % (1696)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.56  % (1696)Refutation not found, incomplete strategy% (1696)------------------------------
% 0.21/0.56  % (1696)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (1696)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (1696)Memory used [KB]: 10746
% 0.21/0.56  % (1696)Time elapsed: 0.151 s
% 0.21/0.56  % (1696)------------------------------
% 0.21/0.56  % (1696)------------------------------
% 1.85/0.61  % (1772)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 1.85/0.62  % (1773)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.11/0.64  % (1766)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.11/0.64  % (1766)Refutation not found, incomplete strategy% (1766)------------------------------
% 2.11/0.64  % (1766)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.11/0.64  % (1775)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.11/0.64  % (1769)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.11/0.64  % (1766)Termination reason: Refutation not found, incomplete strategy
% 2.11/0.64  
% 2.11/0.64  % (1766)Memory used [KB]: 6140
% 2.11/0.64  % (1766)Time elapsed: 0.097 s
% 2.11/0.64  % (1766)------------------------------
% 2.11/0.64  % (1766)------------------------------
% 2.11/0.66  % (1779)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.11/0.67  % (1785)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 2.11/0.67  % (1783)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 2.11/0.68  % (1789)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 2.11/0.68  % (1792)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 2.11/0.68  % (1792)Refutation not found, incomplete strategy% (1792)------------------------------
% 2.11/0.68  % (1792)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.11/0.68  % (1792)Termination reason: Refutation not found, incomplete strategy
% 2.11/0.68  
% 2.11/0.68  % (1792)Memory used [KB]: 1791
% 2.11/0.68  % (1792)Time elapsed: 0.104 s
% 2.11/0.68  % (1792)------------------------------
% 2.11/0.68  % (1792)------------------------------
% 2.11/0.68  % (1788)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 2.11/0.68  % (1806)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 2.11/0.69  % (1790)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 2.11/0.69  % (1788)Refutation not found, incomplete strategy% (1788)------------------------------
% 2.11/0.69  % (1788)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.11/0.69  % (1788)Termination reason: Refutation not found, incomplete strategy
% 2.11/0.69  
% 2.11/0.69  % (1788)Memory used [KB]: 1791
% 2.11/0.69  % (1788)Time elapsed: 0.097 s
% 2.11/0.69  % (1788)------------------------------
% 2.11/0.69  % (1788)------------------------------
% 2.11/0.69  % (1790)Refutation not found, incomplete strategy% (1790)------------------------------
% 2.11/0.69  % (1790)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.11/0.69  % (1790)Termination reason: Refutation not found, incomplete strategy
% 2.11/0.69  
% 2.11/0.69  % (1790)Memory used [KB]: 6268
% 2.11/0.69  % (1790)Time elapsed: 0.095 s
% 2.11/0.69  % (1790)------------------------------
% 2.11/0.69  % (1790)------------------------------
% 2.11/0.70  % (1797)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 2.11/0.70  % (1806)Refutation not found, incomplete strategy% (1806)------------------------------
% 2.11/0.70  % (1806)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.11/0.70  % (1806)Termination reason: Refutation not found, incomplete strategy
% 2.11/0.70  
% 2.11/0.70  % (1806)Memory used [KB]: 1663
% 2.11/0.70  % (1806)Time elapsed: 0.116 s
% 2.11/0.70  % (1806)------------------------------
% 2.11/0.70  % (1806)------------------------------
% 2.64/0.75  % (1863)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 3.07/0.81  % (1883)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 3.07/0.81  % (1883)Refutation not found, incomplete strategy% (1883)------------------------------
% 3.07/0.81  % (1883)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.07/0.81  % (1883)Termination reason: Refutation not found, incomplete strategy
% 3.07/0.81  
% 3.07/0.81  % (1883)Memory used [KB]: 6268
% 3.07/0.81  % (1883)Time elapsed: 0.104 s
% 3.07/0.81  % (1883)------------------------------
% 3.07/0.81  % (1883)------------------------------
% 3.07/0.82  % (1884)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 3.07/0.82  % (1693)Time limit reached!
% 3.07/0.82  % (1693)------------------------------
% 3.07/0.82  % (1693)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.07/0.82  % (1693)Termination reason: Time limit
% 3.07/0.82  
% 3.07/0.82  % (1693)Memory used [KB]: 9210
% 3.07/0.82  % (1693)Time elapsed: 0.408 s
% 3.07/0.82  % (1693)------------------------------
% 3.07/0.82  % (1693)------------------------------
% 3.07/0.82  % (1886)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 3.07/0.82  % (1886)Refutation not found, incomplete strategy% (1886)------------------------------
% 3.07/0.82  % (1886)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.07/0.82  % (1886)Termination reason: Refutation not found, incomplete strategy
% 3.07/0.82  
% 3.07/0.82  % (1886)Memory used [KB]: 6140
% 3.07/0.82  % (1886)Time elapsed: 0.110 s
% 3.07/0.82  % (1886)------------------------------
% 3.07/0.82  % (1886)------------------------------
% 3.07/0.84  % (1893)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 3.90/0.92  % (1700)Time limit reached!
% 3.90/0.92  % (1700)------------------------------
% 3.90/0.92  % (1700)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.90/0.92  % (1700)Termination reason: Time limit
% 3.90/0.92  
% 3.90/0.92  % (1700)Memory used [KB]: 10106
% 3.90/0.92  % (1700)Time elapsed: 0.507 s
% 3.90/0.92  % (1700)------------------------------
% 3.90/0.92  % (1700)------------------------------
% 4.16/0.93  % (1689)Time limit reached!
% 4.16/0.93  % (1689)------------------------------
% 4.16/0.93  % (1689)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.22/0.94  % (1689)Termination reason: Time limit
% 4.22/0.94  
% 4.22/0.94  % (1689)Memory used [KB]: 8955
% 4.22/0.94  % (1689)Time elapsed: 0.508 s
% 4.22/0.94  % (1689)------------------------------
% 4.22/0.94  % (1689)------------------------------
% 4.22/0.95  % (1922)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_1 on theBenchmark
% 4.22/0.95  % (1929)lrs+10_3:1_av=off:bsr=on:cond=on:er=known:gs=on:lcm=reverse:nm=32:nwc=4:stl=30:sp=occurrence:urr=on:updr=off_73 on theBenchmark
% 4.22/0.97  % (1927)ott+1_128_add=large:afr=on:amm=sco:anc=none:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1.1:nicw=on:sas=z3:sac=on:sp=reverse_arity_44 on theBenchmark
% 4.22/0.97  % (1773)Time limit reached!
% 4.22/0.97  % (1773)------------------------------
% 4.22/0.97  % (1773)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.22/0.98  % (1775)Time limit reached!
% 4.22/0.98  % (1775)------------------------------
% 4.22/0.98  % (1775)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.22/0.98  % (1775)Termination reason: Time limit
% 4.22/0.98  % (1775)Termination phase: Saturation
% 4.22/0.98  
% 4.22/0.98  % (1775)Memory used [KB]: 17014
% 4.22/0.98  % (1775)Time elapsed: 0.400 s
% 4.22/0.98  % (1775)------------------------------
% 4.22/0.98  % (1775)------------------------------
% 4.22/0.99  % (1773)Termination reason: Time limit
% 4.22/0.99  % (1773)Termination phase: Saturation
% 4.22/0.99  
% 4.22/0.99  % (1773)Memory used [KB]: 9083
% 4.22/0.99  % (1773)Time elapsed: 0.400 s
% 4.22/0.99  % (1773)------------------------------
% 4.22/0.99  % (1773)------------------------------
% 4.66/1.01  % (1716)Time limit reached!
% 4.66/1.01  % (1716)------------------------------
% 4.66/1.01  % (1716)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.66/1.01  % (1716)Termination reason: Time limit
% 4.66/1.01  % (1716)Termination phase: Saturation
% 4.66/1.01  
% 4.66/1.01  % (1716)Memory used [KB]: 9978
% 4.66/1.01  % (1716)Time elapsed: 0.600 s
% 4.66/1.01  % (1716)------------------------------
% 4.66/1.01  % (1716)------------------------------
% 4.66/1.03  % (1695)Time limit reached!
% 4.66/1.03  % (1695)------------------------------
% 4.66/1.03  % (1695)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.66/1.03  % (1704)Time limit reached!
% 4.66/1.03  % (1704)------------------------------
% 4.66/1.03  % (1704)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.66/1.03  % (1704)Termination reason: Time limit
% 4.66/1.03  % (1704)Termination phase: Saturation
% 4.66/1.03  
% 4.66/1.03  % (1704)Memory used [KB]: 18038
% 4.66/1.03  % (1704)Time elapsed: 0.600 s
% 4.66/1.03  % (1704)------------------------------
% 4.66/1.03  % (1704)------------------------------
% 4.66/1.04  % (1695)Termination reason: Time limit
% 4.66/1.04  
% 4.66/1.04  % (1695)Memory used [KB]: 12920
% 4.66/1.04  % (1695)Time elapsed: 0.620 s
% 4.66/1.04  % (1695)------------------------------
% 4.66/1.04  % (1695)------------------------------
% 4.66/1.06  % (1986)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_275 on theBenchmark
% 4.66/1.06  % (1987)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_117 on theBenchmark
% 5.01/1.10  % (1797)Time limit reached!
% 5.01/1.10  % (1797)------------------------------
% 5.01/1.10  % (1797)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.01/1.10  % (1797)Termination reason: Time limit
% 5.01/1.10  % (1797)Termination phase: Saturation
% 5.01/1.10  
% 5.01/1.10  % (1797)Memory used [KB]: 6140
% 5.01/1.10  % (1797)Time elapsed: 0.500 s
% 5.01/1.10  % (1797)------------------------------
% 5.01/1.10  % (1797)------------------------------
% 5.01/1.11  % (1988)ott+10_8:1_av=off:bd=preordered:bsr=on:cond=fast:fsr=off:gs=on:gsem=off:lcm=predicate:nm=0:nwc=1.2:sp=reverse_arity:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 5.01/1.12  % (1990)lrs+1011_10_av=off:bce=on:cond=on:fsr=off:fde=unused:gs=on:nm=2:nwc=1.1:stl=30:sd=4:ss=axioms:s2a=on:st=1.5:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 5.01/1.12  % (1884)Time limit reached!
% 5.01/1.12  % (1884)------------------------------
% 5.01/1.12  % (1884)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.01/1.12  % (1884)Termination reason: Time limit
% 5.01/1.12  % (1884)Termination phase: Saturation
% 5.01/1.12  
% 5.01/1.12  % (1884)Memory used [KB]: 5117
% 5.01/1.12  % (1884)Time elapsed: 0.400 s
% 5.01/1.12  % (1884)------------------------------
% 5.01/1.12  % (1884)------------------------------
% 5.01/1.12  % (1990)Refutation not found, incomplete strategy% (1990)------------------------------
% 5.01/1.12  % (1990)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.01/1.12  % (1990)Termination reason: Refutation not found, incomplete strategy
% 5.01/1.12  
% 5.01/1.12  % (1990)Memory used [KB]: 6140
% 5.01/1.12  % (1990)Time elapsed: 0.071 s
% 5.01/1.12  % (1990)------------------------------
% 5.01/1.12  % (1990)------------------------------
% 5.01/1.13  % (1989)dis+3_24_av=off:bd=off:bs=unit_only:fsr=off:fde=unused:gs=on:irw=on:lma=on:nm=0:nwc=1.1:sos=on:uhcvi=on_180 on theBenchmark
% 5.01/1.13  % (1991)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_34 on theBenchmark
% 5.01/1.13  % (1989)Refutation not found, incomplete strategy% (1989)------------------------------
% 5.01/1.13  % (1989)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.01/1.13  % (1989)Termination reason: Refutation not found, incomplete strategy
% 5.01/1.13  
% 5.01/1.13  % (1989)Memory used [KB]: 6140
% 5.01/1.13  % (1989)Time elapsed: 0.102 s
% 5.01/1.13  % (1989)------------------------------
% 5.01/1.13  % (1989)------------------------------
% 5.01/1.13  % (1991)Refutation not found, incomplete strategy% (1991)------------------------------
% 5.01/1.13  % (1991)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.01/1.13  % (1991)Termination reason: Refutation not found, incomplete strategy
% 5.01/1.13  
% 5.01/1.13  % (1991)Memory used [KB]: 10746
% 5.01/1.13  % (1991)Time elapsed: 0.036 s
% 5.01/1.13  % (1991)------------------------------
% 5.01/1.13  % (1991)------------------------------
% 6.92/1.26  % (1922)Time limit reached!
% 6.92/1.26  % (1922)------------------------------
% 6.92/1.26  % (1922)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.92/1.27  % (1922)Termination reason: Time limit
% 6.92/1.27  
% 6.92/1.27  % (1922)Memory used [KB]: 4989
% 6.92/1.27  % (1922)Time elapsed: 0.429 s
% 6.92/1.27  % (1922)------------------------------
% 6.92/1.27  % (1922)------------------------------
% 8.19/1.44  % (1988)Time limit reached!
% 8.19/1.44  % (1988)------------------------------
% 8.19/1.44  % (1988)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.19/1.44  % (1988)Termination reason: Time limit
% 8.19/1.44  
% 8.19/1.44  % (1988)Memory used [KB]: 11897
% 8.19/1.44  % (1988)Time elapsed: 0.422 s
% 8.19/1.44  % (1988)------------------------------
% 8.19/1.44  % (1988)------------------------------
% 9.49/1.59  % (1929)Refutation found. Thanks to Tanya!
% 9.49/1.59  % SZS status Theorem for theBenchmark
% 9.49/1.59  % SZS output start Proof for theBenchmark
% 9.49/1.59  fof(f7600,plain,(
% 9.49/1.59    $false),
% 9.49/1.59    inference(subsumption_resolution,[],[f6990,f7599])).
% 9.49/1.59  fof(f7599,plain,(
% 9.49/1.59    ( ! [X37,X35,X36] : (k2_zfmisc_1(X37,k4_xboole_0(X35,X36)) = k4_xboole_0(k2_zfmisc_1(X37,X35),k2_zfmisc_1(X37,X36))) )),
% 9.49/1.59    inference(forward_demodulation,[],[f7598,f6818])).
% 9.49/1.59  fof(f6818,plain,(
% 9.49/1.59    ( ! [X6,X4,X5,X3] : (k2_zfmisc_1(X3,X4) = k4_xboole_0(k2_zfmisc_1(X3,X4),k2_zfmisc_1(X5,k4_xboole_0(X6,X4)))) )),
% 9.49/1.59    inference(forward_demodulation,[],[f6725,f2005])).
% 9.49/1.59  fof(f2005,plain,(
% 9.49/1.59    ( ! [X8] : (k4_xboole_0(X8,k1_xboole_0) = X8) )),
% 9.49/1.59    inference(backward_demodulation,[],[f350,f1988])).
% 9.49/1.59  fof(f1988,plain,(
% 9.49/1.59    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 9.49/1.59    inference(unit_resulting_resolution,[],[f1807,f33])).
% 9.49/1.59  fof(f33,plain,(
% 9.49/1.59    ( ! [X0] : (~r1_tarski(X0,k2_zfmisc_1(X0,X0)) | k1_xboole_0 = X0) )),
% 9.49/1.59    inference(cnf_transformation,[],[f24])).
% 9.49/1.59  fof(f24,plain,(
% 9.49/1.59    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k2_zfmisc_1(X0,X0)))),
% 9.49/1.59    inference(ennf_transformation,[],[f17])).
% 9.49/1.59  fof(f17,axiom,(
% 9.49/1.59    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(X0,X0)) => k1_xboole_0 = X0)),
% 9.49/1.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_zfmisc_1)).
% 9.49/1.59  fof(f1807,plain,(
% 9.49/1.59    ( ! [X8,X9] : (r1_tarski(k4_xboole_0(X9,X9),X8)) )),
% 9.49/1.59    inference(superposition,[],[f83,f970])).
% 9.49/1.59  fof(f970,plain,(
% 9.49/1.59    ( ! [X8,X9] : (k2_xboole_0(X8,k4_xboole_0(X9,X9)) = X8) )),
% 9.49/1.59    inference(forward_demodulation,[],[f931,f350])).
% 9.49/1.59  fof(f931,plain,(
% 9.49/1.59    ( ! [X8,X9] : (k4_xboole_0(X8,k4_xboole_0(X9,X9)) = k2_xboole_0(X8,k4_xboole_0(X9,X9))) )),
% 9.49/1.59    inference(superposition,[],[f350,f37])).
% 9.49/1.59  fof(f37,plain,(
% 9.49/1.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 9.49/1.59    inference(cnf_transformation,[],[f6])).
% 9.49/1.59  fof(f6,axiom,(
% 9.49/1.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 9.49/1.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 9.49/1.59  fof(f83,plain,(
% 9.49/1.59    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 9.49/1.59    inference(unit_resulting_resolution,[],[f34,f55])).
% 9.49/1.59  fof(f55,plain,(
% 9.49/1.59    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 9.49/1.59    inference(cnf_transformation,[],[f27])).
% 9.49/1.59  fof(f27,plain,(
% 9.49/1.59    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 9.49/1.59    inference(ennf_transformation,[],[f8])).
% 9.49/1.59  fof(f8,axiom,(
% 9.49/1.59    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 9.49/1.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 9.49/1.59  fof(f34,plain,(
% 9.49/1.59    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 9.49/1.59    inference(cnf_transformation,[],[f4])).
% 9.49/1.59  fof(f4,axiom,(
% 9.49/1.59    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 9.49/1.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 9.49/1.59  fof(f350,plain,(
% 9.49/1.59    ( ! [X8,X9] : (k4_xboole_0(X8,k4_xboole_0(X9,X9)) = X8) )),
% 9.49/1.59    inference(forward_demodulation,[],[f311,f77])).
% 9.49/1.59  fof(f77,plain,(
% 9.49/1.59    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0) )),
% 9.49/1.59    inference(unit_resulting_resolution,[],[f34,f70])).
% 9.49/1.59  fof(f70,plain,(
% 9.49/1.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 9.49/1.59    inference(forward_demodulation,[],[f40,f38])).
% 9.49/1.59  fof(f38,plain,(
% 9.49/1.59    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 9.49/1.59    inference(cnf_transformation,[],[f5])).
% 9.49/1.59  fof(f5,axiom,(
% 9.49/1.59    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 9.49/1.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 9.49/1.59  fof(f40,plain,(
% 9.49/1.59    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1)) )),
% 9.49/1.59    inference(cnf_transformation,[],[f25])).
% 9.49/1.59  fof(f25,plain,(
% 9.49/1.59    ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 9.49/1.59    inference(ennf_transformation,[],[f9])).
% 9.49/1.59  fof(f9,axiom,(
% 9.49/1.59    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1)),
% 9.49/1.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).
% 9.49/1.59  fof(f311,plain,(
% 9.49/1.59    ( ! [X8,X9] : (k2_xboole_0(k4_xboole_0(X8,X9),X8) = k4_xboole_0(X8,k4_xboole_0(X9,X9))) )),
% 9.49/1.59    inference(superposition,[],[f62,f38])).
% 9.49/1.59  fof(f62,plain,(
% 9.49/1.59    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 9.49/1.59    inference(definition_unfolding,[],[f48,f35])).
% 9.49/1.59  fof(f35,plain,(
% 9.49/1.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 9.49/1.59    inference(cnf_transformation,[],[f11])).
% 9.49/1.59  fof(f11,axiom,(
% 9.49/1.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 9.49/1.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 9.49/1.59  fof(f48,plain,(
% 9.49/1.59    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 9.49/1.59    inference(cnf_transformation,[],[f14])).
% 9.49/1.59  fof(f14,axiom,(
% 9.49/1.59    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 9.49/1.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).
% 9.49/1.59  fof(f6725,plain,(
% 9.49/1.59    ( ! [X6,X4,X5,X3] : (k4_xboole_0(k2_zfmisc_1(X3,X4),k1_xboole_0) = k4_xboole_0(k2_zfmisc_1(X3,X4),k2_zfmisc_1(X5,k4_xboole_0(X6,X4)))) )),
% 9.49/1.59    inference(superposition,[],[f57,f2100])).
% 9.49/1.59  fof(f2100,plain,(
% 9.49/1.59    ( ! [X28,X26,X27,X25] : (k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(X27,X25),k4_xboole_0(k2_zfmisc_1(X27,X25),k2_zfmisc_1(X28,k4_xboole_0(X26,X25))))) )),
% 9.49/1.59    inference(forward_demodulation,[],[f2021,f68])).
% 9.49/1.59  fof(f68,plain,(
% 9.49/1.59    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 9.49/1.59    inference(equality_resolution,[],[f43])).
% 9.49/1.59  fof(f43,plain,(
% 9.49/1.59    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 9.49/1.59    inference(cnf_transformation,[],[f31])).
% 9.49/1.59  fof(f31,plain,(
% 9.49/1.59    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 9.49/1.59    inference(flattening,[],[f30])).
% 9.49/1.59  fof(f30,plain,(
% 9.49/1.59    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 9.49/1.59    inference(nnf_transformation,[],[f16])).
% 9.49/1.59  fof(f16,axiom,(
% 9.49/1.59    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 9.49/1.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 9.49/1.59  fof(f2021,plain,(
% 9.49/1.59    ( ! [X28,X26,X27,X25] : (k4_xboole_0(k2_zfmisc_1(X27,X25),k4_xboole_0(k2_zfmisc_1(X27,X25),k2_zfmisc_1(X28,k4_xboole_0(X26,X25)))) = k2_zfmisc_1(k4_xboole_0(X27,k4_xboole_0(X27,X28)),k1_xboole_0)) )),
% 9.49/1.59    inference(backward_demodulation,[],[f1360,f1988])).
% 9.49/1.59  fof(f1360,plain,(
% 9.49/1.59    ( ! [X28,X26,X27,X25] : (k4_xboole_0(k2_zfmisc_1(X27,X25),k4_xboole_0(k2_zfmisc_1(X27,X25),k2_zfmisc_1(X28,k4_xboole_0(X26,X25)))) = k2_zfmisc_1(k4_xboole_0(X27,k4_xboole_0(X27,X28)),k4_xboole_0(X25,X25))) )),
% 9.49/1.59    inference(forward_demodulation,[],[f1359,f1096])).
% 9.49/1.59  fof(f1096,plain,(
% 9.49/1.59    ( ! [X10,X8,X11,X9] : (k4_xboole_0(k2_zfmisc_1(X10,k4_xboole_0(X8,k4_xboole_0(X8,X9))),k4_xboole_0(k2_zfmisc_1(X10,k4_xboole_0(X8,k4_xboole_0(X8,X9))),k2_zfmisc_1(X11,k4_xboole_0(X8,X8)))) = k2_zfmisc_1(k4_xboole_0(X10,k4_xboole_0(X10,X11)),k4_xboole_0(X8,X8))) )),
% 9.49/1.59    inference(backward_demodulation,[],[f877,f1092])).
% 9.49/1.59  fof(f1092,plain,(
% 9.49/1.59    ( ! [X66,X64] : (k4_xboole_0(X64,X64) = k4_xboole_0(X64,k2_xboole_0(X66,X64))) )),
% 9.49/1.59    inference(forward_demodulation,[],[f1091,f38])).
% 9.49/1.59  fof(f1091,plain,(
% 9.49/1.59    ( ! [X66,X64] : (k4_xboole_0(X64,X64) = k4_xboole_0(X64,k2_xboole_0(X66,k4_xboole_0(X64,X66)))) )),
% 9.49/1.59    inference(forward_demodulation,[],[f1090,f970])).
% 9.49/1.59  fof(f1090,plain,(
% 9.49/1.59    ( ! [X66,X64,X65] : (k4_xboole_0(X64,X64) = k4_xboole_0(X64,k2_xboole_0(X66,k4_xboole_0(X64,k2_xboole_0(X66,k4_xboole_0(X65,X65)))))) )),
% 9.49/1.59    inference(forward_demodulation,[],[f1089,f350])).
% 9.49/1.59  fof(f1089,plain,(
% 9.49/1.59    ( ! [X66,X64,X65] : (k4_xboole_0(X64,k2_xboole_0(X66,k4_xboole_0(X64,k2_xboole_0(X66,k4_xboole_0(X65,X65))))) = k4_xboole_0(k4_xboole_0(X64,X64),k4_xboole_0(X66,X66))) )),
% 9.49/1.59    inference(forward_demodulation,[],[f957,f350])).
% 9.49/1.59  fof(f957,plain,(
% 9.49/1.59    ( ! [X66,X64,X65] : (k4_xboole_0(X64,k2_xboole_0(X66,k4_xboole_0(X64,k2_xboole_0(X66,k4_xboole_0(X65,X65))))) = k4_xboole_0(k4_xboole_0(X64,X64),k4_xboole_0(X66,k4_xboole_0(X66,k4_xboole_0(X65,X65))))) )),
% 9.49/1.59    inference(superposition,[],[f73,f350])).
% 9.49/1.59  fof(f73,plain,(
% 9.49/1.59    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(X0,k2_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X2,X1))))) )),
% 9.49/1.59    inference(forward_demodulation,[],[f72,f45])).
% 9.49/1.59  fof(f45,plain,(
% 9.49/1.59    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 9.49/1.59    inference(cnf_transformation,[],[f7])).
% 9.49/1.59  fof(f7,axiom,(
% 9.49/1.59    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 9.49/1.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 9.49/1.59  fof(f72,plain,(
% 9.49/1.59    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(X0,k2_xboole_0(X2,k4_xboole_0(k4_xboole_0(X0,X2),X1)))) )),
% 9.49/1.59    inference(forward_demodulation,[],[f63,f45])).
% 9.49/1.59  fof(f63,plain,(
% 9.49/1.59    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(k4_xboole_0(X0,X2),X1))) )),
% 9.49/1.59    inference(definition_unfolding,[],[f49,f35,f35,f35])).
% 9.49/1.59  fof(f49,plain,(
% 9.49/1.59    ( ! [X2,X0,X1] : (k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k4_xboole_0(X0,X2),X1)) )),
% 9.49/1.59    inference(cnf_transformation,[],[f2])).
% 9.49/1.59  fof(f2,axiom,(
% 9.49/1.59    ! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k4_xboole_0(X0,X2),X1)),
% 9.49/1.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_xboole_1)).
% 9.49/1.59  fof(f877,plain,(
% 9.49/1.59    ( ! [X10,X8,X11,X9] : (k2_zfmisc_1(k4_xboole_0(X10,k4_xboole_0(X10,X11)),k4_xboole_0(X8,k2_xboole_0(X9,X8))) = k4_xboole_0(k2_zfmisc_1(X10,k4_xboole_0(X8,k4_xboole_0(X8,X9))),k4_xboole_0(k2_zfmisc_1(X10,k4_xboole_0(X8,k4_xboole_0(X8,X9))),k2_zfmisc_1(X11,k4_xboole_0(X8,X8))))) )),
% 9.49/1.59    inference(forward_demodulation,[],[f876,f350])).
% 9.49/1.59  fof(f876,plain,(
% 9.49/1.59    ( ! [X10,X8,X11,X9] : (k2_zfmisc_1(k4_xboole_0(X10,k4_xboole_0(X10,X11)),k4_xboole_0(X8,k2_xboole_0(X9,X8))) = k4_xboole_0(k2_zfmisc_1(X10,k4_xboole_0(X8,k4_xboole_0(X8,X9))),k4_xboole_0(k2_zfmisc_1(X10,k4_xboole_0(X8,k4_xboole_0(X8,X9))),k2_zfmisc_1(X11,k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X9,X9))))))) )),
% 9.49/1.59    inference(forward_demodulation,[],[f875,f59])).
% 9.49/1.59  fof(f59,plain,(
% 9.49/1.59    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 9.49/1.59    inference(definition_unfolding,[],[f44,f35,f35])).
% 9.49/1.59  fof(f44,plain,(
% 9.49/1.59    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 9.49/1.59    inference(cnf_transformation,[],[f12])).
% 9.49/1.59  fof(f12,axiom,(
% 9.49/1.59    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 9.49/1.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 9.49/1.59  fof(f875,plain,(
% 9.49/1.59    ( ! [X10,X8,X11,X9] : (k4_xboole_0(k2_zfmisc_1(X10,k4_xboole_0(X8,k4_xboole_0(X8,X9))),k4_xboole_0(k2_zfmisc_1(X10,k4_xboole_0(X8,k4_xboole_0(X8,X9))),k2_zfmisc_1(X11,k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X9)))) = k2_zfmisc_1(k4_xboole_0(X10,k4_xboole_0(X10,X11)),k4_xboole_0(X8,k2_xboole_0(X9,X8)))) )),
% 9.49/1.59    inference(forward_demodulation,[],[f874,f38])).
% 9.49/1.59  fof(f874,plain,(
% 9.49/1.59    ( ! [X10,X8,X11,X9] : (k4_xboole_0(k2_zfmisc_1(X10,k4_xboole_0(X8,k4_xboole_0(X8,X9))),k4_xboole_0(k2_zfmisc_1(X10,k4_xboole_0(X8,k4_xboole_0(X8,X9))),k2_zfmisc_1(X11,k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X9)))) = k2_zfmisc_1(k4_xboole_0(X10,k4_xboole_0(X10,X11)),k4_xboole_0(X8,k2_xboole_0(X9,k4_xboole_0(X8,X9))))) )),
% 9.49/1.59    inference(forward_demodulation,[],[f873,f818])).
% 9.49/1.59  fof(f818,plain,(
% 9.49/1.59    ( ! [X2,X0,X3,X1] : (k4_xboole_0(k2_zfmisc_1(X2,X0),k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X3,k4_xboole_0(X0,X1)))) = k2_zfmisc_1(k4_xboole_0(X2,k4_xboole_0(X2,X3)),k4_xboole_0(X0,X1))) )),
% 9.49/1.59    inference(superposition,[],[f67,f57])).
% 9.49/1.59  fof(f67,plain,(
% 9.49/1.59    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k4_xboole_0(k2_zfmisc_1(X0,X2),k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))) )),
% 9.49/1.59    inference(definition_unfolding,[],[f56,f35,f35,f35])).
% 9.49/1.59  fof(f56,plain,(
% 9.49/1.59    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 9.49/1.59    inference(cnf_transformation,[],[f20])).
% 9.49/1.59  fof(f20,axiom,(
% 9.49/1.59    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 9.49/1.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 9.49/1.59  fof(f873,plain,(
% 9.49/1.59    ( ! [X10,X8,X11,X9] : (k4_xboole_0(k2_zfmisc_1(X10,k4_xboole_0(X8,k4_xboole_0(X8,X9))),k4_xboole_0(k2_zfmisc_1(X10,k4_xboole_0(X8,k4_xboole_0(X8,X9))),k2_zfmisc_1(X11,k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X9)))) = k4_xboole_0(k2_zfmisc_1(X10,X8),k4_xboole_0(k2_zfmisc_1(X10,X8),k2_zfmisc_1(X11,k4_xboole_0(X8,k2_xboole_0(X9,k4_xboole_0(X8,X9))))))) )),
% 9.49/1.59    inference(forward_demodulation,[],[f872,f45])).
% 9.49/1.59  fof(f872,plain,(
% 9.49/1.59    ( ! [X10,X8,X11,X9] : (k4_xboole_0(k2_zfmisc_1(X10,k4_xboole_0(X8,k4_xboole_0(X8,X9))),k4_xboole_0(k2_zfmisc_1(X10,k4_xboole_0(X8,k4_xboole_0(X8,X9))),k2_zfmisc_1(X11,k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X9)))) = k4_xboole_0(k2_zfmisc_1(X10,X8),k4_xboole_0(k2_zfmisc_1(X10,X8),k2_zfmisc_1(X11,k4_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X8,X9)))))) )),
% 9.49/1.59    inference(forward_demodulation,[],[f871,f863])).
% 9.49/1.59  fof(f863,plain,(
% 9.49/1.59    ( ! [X14,X17,X15,X18,X16] : (k4_xboole_0(k2_zfmisc_1(X17,k4_xboole_0(X14,k4_xboole_0(X14,X15))),k4_xboole_0(k2_zfmisc_1(X17,k4_xboole_0(X14,k4_xboole_0(X14,X15))),k2_zfmisc_1(X18,X16))) = k4_xboole_0(k2_zfmisc_1(X17,X14),k4_xboole_0(k2_zfmisc_1(X17,X14),k2_zfmisc_1(X18,k4_xboole_0(X15,k4_xboole_0(X14,X16)))))) )),
% 9.49/1.59    inference(forward_demodulation,[],[f862,f310])).
% 9.49/1.59  fof(f310,plain,(
% 9.49/1.59    ( ! [X6,X7,X5] : (k4_xboole_0(X5,k4_xboole_0(X6,X7)) = k4_xboole_0(X5,k4_xboole_0(X6,k4_xboole_0(X6,k4_xboole_0(X5,X7))))) )),
% 9.49/1.59    inference(superposition,[],[f62,f61])).
% 9.49/1.59  fof(f61,plain,(
% 9.49/1.59    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) )),
% 9.49/1.59    inference(definition_unfolding,[],[f47,f35])).
% 9.49/1.59  fof(f47,plain,(
% 9.49/1.59    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) )),
% 9.49/1.59    inference(cnf_transformation,[],[f1])).
% 9.49/1.59  fof(f1,axiom,(
% 9.49/1.59    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 9.49/1.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l36_xboole_1)).
% 9.49/1.59  fof(f862,plain,(
% 9.49/1.59    ( ! [X14,X17,X15,X18,X16] : (k4_xboole_0(k2_zfmisc_1(X17,k4_xboole_0(X14,k4_xboole_0(X14,X15))),k4_xboole_0(k2_zfmisc_1(X17,k4_xboole_0(X14,k4_xboole_0(X14,X15))),k2_zfmisc_1(X18,X16))) = k4_xboole_0(k2_zfmisc_1(X17,X14),k4_xboole_0(k2_zfmisc_1(X17,X14),k2_zfmisc_1(X18,k4_xboole_0(X15,k4_xboole_0(X14,k4_xboole_0(X14,k4_xboole_0(X15,X16)))))))) )),
% 9.49/1.59    inference(forward_demodulation,[],[f861,f67])).
% 9.49/1.59  fof(f861,plain,(
% 9.49/1.59    ( ! [X14,X17,X15,X18,X16] : (k4_xboole_0(k2_zfmisc_1(X17,k4_xboole_0(X14,k4_xboole_0(X14,X15))),k4_xboole_0(k2_zfmisc_1(X17,k4_xboole_0(X14,k4_xboole_0(X14,X15))),k2_zfmisc_1(X18,X16))) = k2_zfmisc_1(k4_xboole_0(X17,k4_xboole_0(X17,X18)),k4_xboole_0(X14,k4_xboole_0(X14,k4_xboole_0(X15,k4_xboole_0(X14,k4_xboole_0(X14,k4_xboole_0(X15,X16)))))))) )),
% 9.49/1.59    inference(forward_demodulation,[],[f812,f59])).
% 9.49/1.59  fof(f812,plain,(
% 9.49/1.59    ( ! [X14,X17,X15,X18,X16] : (k4_xboole_0(k2_zfmisc_1(X17,k4_xboole_0(X14,k4_xboole_0(X14,X15))),k4_xboole_0(k2_zfmisc_1(X17,k4_xboole_0(X14,k4_xboole_0(X14,X15))),k2_zfmisc_1(X18,X16))) = k2_zfmisc_1(k4_xboole_0(X17,k4_xboole_0(X17,X18)),k4_xboole_0(k4_xboole_0(X14,k4_xboole_0(X14,X15)),k4_xboole_0(X14,k4_xboole_0(X14,k4_xboole_0(X15,X16)))))) )),
% 9.49/1.59    inference(superposition,[],[f67,f59])).
% 9.49/1.59  fof(f871,plain,(
% 9.49/1.59    ( ! [X10,X8,X11,X9] : (k4_xboole_0(k2_zfmisc_1(X10,k4_xboole_0(X8,k4_xboole_0(X8,X9))),k4_xboole_0(k2_zfmisc_1(X10,k4_xboole_0(X8,k4_xboole_0(X8,X9))),k2_zfmisc_1(X11,k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X9)))) = k4_xboole_0(k2_zfmisc_1(X10,k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X8,X9)))),k4_xboole_0(k2_zfmisc_1(X10,k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X8,X9)))),k2_zfmisc_1(X11,X9)))) )),
% 9.49/1.59    inference(forward_demodulation,[],[f819,f860])).
% 9.49/1.59  fof(f860,plain,(
% 9.49/1.59    ( ! [X12,X10,X13,X11,X9] : (k4_xboole_0(k2_zfmisc_1(X12,k4_xboole_0(X9,X10)),k4_xboole_0(k2_zfmisc_1(X12,k4_xboole_0(X9,X10)),k2_zfmisc_1(X13,X11))) = k2_zfmisc_1(k4_xboole_0(X12,k4_xboole_0(X12,X13)),k4_xboole_0(X9,k2_xboole_0(X10,k4_xboole_0(X9,k2_xboole_0(X10,X11)))))) )),
% 9.49/1.59    inference(forward_demodulation,[],[f811,f45])).
% 9.49/1.59  fof(f811,plain,(
% 9.49/1.59    ( ! [X12,X10,X13,X11,X9] : (k4_xboole_0(k2_zfmisc_1(X12,k4_xboole_0(X9,X10)),k4_xboole_0(k2_zfmisc_1(X12,k4_xboole_0(X9,X10)),k2_zfmisc_1(X13,X11))) = k2_zfmisc_1(k4_xboole_0(X12,k4_xboole_0(X12,X13)),k4_xboole_0(k4_xboole_0(X9,X10),k4_xboole_0(X9,k2_xboole_0(X10,X11))))) )),
% 9.49/1.59    inference(superposition,[],[f67,f45])).
% 9.49/1.59  fof(f819,plain,(
% 9.49/1.59    ( ! [X10,X8,X11,X9] : (k4_xboole_0(k2_zfmisc_1(X10,k4_xboole_0(X8,k4_xboole_0(X8,X9))),k4_xboole_0(k2_zfmisc_1(X10,k4_xboole_0(X8,k4_xboole_0(X8,X9))),k2_zfmisc_1(X11,k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X9)))) = k2_zfmisc_1(k4_xboole_0(X10,k4_xboole_0(X10,X11)),k4_xboole_0(X8,k2_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),k4_xboole_0(X8,k2_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X9)))))) )),
% 9.49/1.59    inference(superposition,[],[f67,f73])).
% 9.49/1.59  fof(f1359,plain,(
% 9.49/1.59    ( ! [X28,X26,X27,X25] : (k4_xboole_0(k2_zfmisc_1(X27,X25),k4_xboole_0(k2_zfmisc_1(X27,X25),k2_zfmisc_1(X28,k4_xboole_0(X26,X25)))) = k4_xboole_0(k2_zfmisc_1(X27,k4_xboole_0(X25,k4_xboole_0(X25,X26))),k4_xboole_0(k2_zfmisc_1(X27,k4_xboole_0(X25,k4_xboole_0(X25,X26))),k2_zfmisc_1(X28,k4_xboole_0(X25,X25))))) )),
% 9.49/1.59    inference(forward_demodulation,[],[f1358,f350])).
% 9.49/1.59  fof(f1358,plain,(
% 9.49/1.59    ( ! [X28,X26,X27,X25] : (k4_xboole_0(k2_zfmisc_1(X27,X25),k4_xboole_0(k2_zfmisc_1(X27,X25),k2_zfmisc_1(X28,k4_xboole_0(X26,X25)))) = k4_xboole_0(k2_zfmisc_1(X27,k4_xboole_0(X25,k4_xboole_0(X25,X26))),k4_xboole_0(k2_zfmisc_1(X27,k4_xboole_0(X25,k4_xboole_0(X25,X26))),k2_zfmisc_1(X28,k4_xboole_0(X25,k4_xboole_0(X25,k4_xboole_0(X26,X26))))))) )),
% 9.49/1.59    inference(forward_demodulation,[],[f1357,f59])).
% 9.49/1.59  fof(f1357,plain,(
% 9.49/1.59    ( ! [X28,X26,X27,X25] : (k4_xboole_0(k2_zfmisc_1(X27,k4_xboole_0(X25,k4_xboole_0(X25,X26))),k4_xboole_0(k2_zfmisc_1(X27,k4_xboole_0(X25,k4_xboole_0(X25,X26))),k2_zfmisc_1(X28,k4_xboole_0(k4_xboole_0(X25,k4_xboole_0(X25,X26)),X26)))) = k4_xboole_0(k2_zfmisc_1(X27,X25),k4_xboole_0(k2_zfmisc_1(X27,X25),k2_zfmisc_1(X28,k4_xboole_0(X26,X25))))) )),
% 9.49/1.59    inference(forward_demodulation,[],[f1356,f1101])).
% 9.49/1.59  fof(f1101,plain,(
% 9.49/1.59    ( ! [X14,X15] : (k4_xboole_0(X14,X15) = k4_xboole_0(X14,k4_xboole_0(X15,k4_xboole_0(X15,X14)))) )),
% 9.49/1.59    inference(forward_demodulation,[],[f1097,f970])).
% 9.49/1.59  fof(f1097,plain,(
% 9.49/1.59    ( ! [X14,X15] : (k4_xboole_0(X14,k4_xboole_0(X15,k4_xboole_0(X15,X14))) = k4_xboole_0(X14,k2_xboole_0(X15,k4_xboole_0(X14,X14)))) )),
% 9.49/1.59    inference(backward_demodulation,[],[f940,f1092])).
% 9.49/1.59  fof(f940,plain,(
% 9.49/1.59    ( ! [X14,X15] : (k4_xboole_0(X14,k2_xboole_0(X15,k4_xboole_0(X14,k2_xboole_0(X15,X14)))) = k4_xboole_0(X14,k4_xboole_0(X15,k4_xboole_0(X15,X14)))) )),
% 9.49/1.59    inference(superposition,[],[f73,f350])).
% 9.49/1.59  fof(f1356,plain,(
% 9.49/1.59    ( ! [X28,X26,X27,X25] : (k4_xboole_0(k2_zfmisc_1(X27,k4_xboole_0(X25,k4_xboole_0(X25,X26))),k4_xboole_0(k2_zfmisc_1(X27,k4_xboole_0(X25,k4_xboole_0(X25,X26))),k2_zfmisc_1(X28,k4_xboole_0(k4_xboole_0(X25,k4_xboole_0(X25,X26)),X26)))) = k4_xboole_0(k2_zfmisc_1(X27,X25),k4_xboole_0(k2_zfmisc_1(X27,X25),k2_zfmisc_1(X28,k4_xboole_0(X26,k4_xboole_0(X25,k4_xboole_0(X25,X26))))))) )),
% 9.49/1.59    inference(forward_demodulation,[],[f1154,f67])).
% 9.49/1.59  fof(f1154,plain,(
% 9.49/1.59    ( ! [X28,X26,X27,X25] : (k4_xboole_0(k2_zfmisc_1(X27,k4_xboole_0(X25,k4_xboole_0(X25,X26))),k4_xboole_0(k2_zfmisc_1(X27,k4_xboole_0(X25,k4_xboole_0(X25,X26))),k2_zfmisc_1(X28,k4_xboole_0(k4_xboole_0(X25,k4_xboole_0(X25,X26)),X26)))) = k2_zfmisc_1(k4_xboole_0(X27,k4_xboole_0(X27,X28)),k4_xboole_0(X25,k4_xboole_0(X25,k4_xboole_0(X26,k4_xboole_0(X25,k4_xboole_0(X25,X26))))))) )),
% 9.49/1.59    inference(superposition,[],[f67,f974])).
% 9.49/1.59  fof(f974,plain,(
% 9.49/1.59    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X1)))) )),
% 9.49/1.59    inference(backward_demodulation,[],[f73,f971])).
% 9.49/1.59  fof(f971,plain,(
% 9.49/1.59    ( ! [X12,X13,X11] : (k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X12,X13))) = k4_xboole_0(X11,k2_xboole_0(X13,k4_xboole_0(X11,k2_xboole_0(X13,X12))))) )),
% 9.49/1.59    inference(backward_demodulation,[],[f712,f970])).
% 9.49/1.59  fof(f712,plain,(
% 9.49/1.59    ( ! [X12,X13,X11] : (k4_xboole_0(X11,k2_xboole_0(X13,k4_xboole_0(X11,k2_xboole_0(X13,X12)))) = k2_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X12,X13))),k4_xboole_0(X11,X11))) )),
% 9.49/1.59    inference(forward_demodulation,[],[f711,f59])).
% 9.49/1.59  fof(f711,plain,(
% 9.49/1.59    ( ! [X12,X13,X11] : (k4_xboole_0(X11,k2_xboole_0(X13,k4_xboole_0(X11,k2_xboole_0(X13,X12)))) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),X13),k4_xboole_0(X11,X11))) )),
% 9.49/1.59    inference(forward_demodulation,[],[f710,f350])).
% 9.49/1.59  fof(f710,plain,(
% 9.49/1.59    ( ! [X12,X13,X11] : (k4_xboole_0(X11,k2_xboole_0(X13,k4_xboole_0(X11,k2_xboole_0(X13,X12)))) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),X13),k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X12,X12))))) )),
% 9.49/1.59    inference(forward_demodulation,[],[f600,f59])).
% 9.49/1.59  fof(f600,plain,(
% 9.49/1.59    ( ! [X12,X13,X11] : (k2_xboole_0(k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),X13),k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),X12)) = k4_xboole_0(X11,k2_xboole_0(X13,k4_xboole_0(X11,k2_xboole_0(X13,X12))))) )),
% 9.49/1.59    inference(superposition,[],[f73,f61])).
% 9.49/1.59  fof(f57,plain,(
% 9.49/1.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 9.49/1.59    inference(definition_unfolding,[],[f36,f35])).
% 9.49/1.59  fof(f36,plain,(
% 9.49/1.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 9.49/1.59    inference(cnf_transformation,[],[f10])).
% 9.49/1.59  fof(f10,axiom,(
% 9.49/1.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 9.49/1.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 9.49/1.59  fof(f7598,plain,(
% 9.49/1.59    ( ! [X37,X35,X36] : (k4_xboole_0(k2_zfmisc_1(X37,k4_xboole_0(X35,X36)),k2_zfmisc_1(X37,k4_xboole_0(X35,k4_xboole_0(X35,X36)))) = k4_xboole_0(k2_zfmisc_1(X37,X35),k2_zfmisc_1(X37,X36))) )),
% 9.49/1.59    inference(forward_demodulation,[],[f7534,f474])).
% 9.49/1.59  fof(f474,plain,(
% 9.49/1.59    ( ! [X17,X15,X16] : (k4_xboole_0(k2_zfmisc_1(X15,X16),k2_zfmisc_1(X15,X17)) = k4_xboole_0(k2_zfmisc_1(X15,X16),k2_zfmisc_1(X15,k4_xboole_0(X16,k4_xboole_0(X16,X17))))) )),
% 9.49/1.59    inference(superposition,[],[f57,f64])).
% 9.49/1.59  fof(f64,plain,(
% 9.49/1.59    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k2_zfmisc_1(X2,X0),k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)))) )),
% 9.49/1.59    inference(definition_unfolding,[],[f53,f35,f35])).
% 9.49/1.59  fof(f53,plain,(
% 9.49/1.59    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 9.49/1.59    inference(cnf_transformation,[],[f19])).
% 9.49/1.59  fof(f19,axiom,(
% 9.49/1.59    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 9.49/1.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t122_zfmisc_1)).
% 9.49/1.59  fof(f7534,plain,(
% 9.49/1.59    ( ! [X37,X35,X36] : (k4_xboole_0(k2_zfmisc_1(X37,k4_xboole_0(X35,X36)),k2_zfmisc_1(X37,k4_xboole_0(X35,k4_xboole_0(X35,X36)))) = k4_xboole_0(k2_zfmisc_1(X37,X35),k2_zfmisc_1(X37,k4_xboole_0(X35,k4_xboole_0(X35,X36))))) )),
% 9.49/1.59    inference(superposition,[],[f150,f125])).
% 9.49/1.59  fof(f125,plain,(
% 9.49/1.59    ( ! [X4,X3] : (k2_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X3,k4_xboole_0(X3,X4))) = X3) )),
% 9.49/1.59    inference(superposition,[],[f58,f57])).
% 9.49/1.59  fof(f58,plain,(
% 9.49/1.59    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 9.49/1.59    inference(definition_unfolding,[],[f39,f35])).
% 9.49/1.59  fof(f39,plain,(
% 9.49/1.59    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 9.49/1.59    inference(cnf_transformation,[],[f13])).
% 9.49/1.59  fof(f13,axiom,(
% 9.49/1.59    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 9.49/1.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 9.49/1.59  fof(f150,plain,(
% 9.49/1.59    ( ! [X6,X7,X5] : (k4_xboole_0(k2_zfmisc_1(X5,X6),k2_zfmisc_1(X5,X7)) = k4_xboole_0(k2_zfmisc_1(X5,k2_xboole_0(X6,X7)),k2_zfmisc_1(X5,X7))) )),
% 9.49/1.59    inference(superposition,[],[f37,f51])).
% 9.49/1.59  fof(f51,plain,(
% 9.49/1.59    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 9.49/1.59    inference(cnf_transformation,[],[f18])).
% 9.49/1.59  fof(f18,axiom,(
% 9.49/1.59    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 9.49/1.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).
% 9.49/1.59  fof(f6990,plain,(
% 9.49/1.59    k2_zfmisc_1(sK2,k4_xboole_0(sK0,sK1)) != k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))),
% 9.49/1.59    inference(subsumption_resolution,[],[f32,f6989])).
% 9.49/1.59  fof(f6989,plain,(
% 9.49/1.59    ( ! [X37,X35,X36] : (k2_zfmisc_1(k4_xboole_0(X35,X36),X37) = k4_xboole_0(k2_zfmisc_1(X35,X37),k2_zfmisc_1(X36,X37))) )),
% 9.49/1.59    inference(forward_demodulation,[],[f6988,f6495])).
% 9.49/1.59  fof(f6495,plain,(
% 9.49/1.59    ( ! [X6,X4,X5,X3] : (k2_zfmisc_1(X3,X4) = k4_xboole_0(k2_zfmisc_1(X3,X4),k2_zfmisc_1(k4_xboole_0(X5,X3),X6))) )),
% 9.49/1.59    inference(forward_demodulation,[],[f6402,f2005])).
% 9.49/1.59  fof(f6402,plain,(
% 9.49/1.59    ( ! [X6,X4,X5,X3] : (k4_xboole_0(k2_zfmisc_1(X3,X4),k2_zfmisc_1(k4_xboole_0(X5,X3),X6)) = k4_xboole_0(k2_zfmisc_1(X3,X4),k1_xboole_0)) )),
% 9.49/1.59    inference(superposition,[],[f57,f2099])).
% 9.49/1.59  fof(f2099,plain,(
% 9.49/1.59    ( ! [X24,X23,X21,X22] : (k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(X21,X23),k4_xboole_0(k2_zfmisc_1(X21,X23),k2_zfmisc_1(k4_xboole_0(X22,X21),X24)))) )),
% 9.49/1.59    inference(forward_demodulation,[],[f2020,f69])).
% 9.49/1.59  fof(f69,plain,(
% 9.49/1.59    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 9.49/1.59    inference(equality_resolution,[],[f42])).
% 9.49/1.59  fof(f42,plain,(
% 9.49/1.59    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 9.49/1.59    inference(cnf_transformation,[],[f31])).
% 9.49/1.59  fof(f2020,plain,(
% 9.49/1.59    ( ! [X24,X23,X21,X22] : (k4_xboole_0(k2_zfmisc_1(X21,X23),k4_xboole_0(k2_zfmisc_1(X21,X23),k2_zfmisc_1(k4_xboole_0(X22,X21),X24))) = k2_zfmisc_1(k1_xboole_0,k4_xboole_0(X23,k4_xboole_0(X23,X24)))) )),
% 9.49/1.59    inference(backward_demodulation,[],[f1355,f1988])).
% 9.49/1.59  fof(f1355,plain,(
% 9.49/1.59    ( ! [X24,X23,X21,X22] : (k4_xboole_0(k2_zfmisc_1(X21,X23),k4_xboole_0(k2_zfmisc_1(X21,X23),k2_zfmisc_1(k4_xboole_0(X22,X21),X24))) = k2_zfmisc_1(k4_xboole_0(X21,X21),k4_xboole_0(X23,k4_xboole_0(X23,X24)))) )),
% 9.49/1.59    inference(forward_demodulation,[],[f1354,f1095])).
% 9.49/1.59  fof(f1095,plain,(
% 9.49/1.59    ( ! [X10,X8,X11,X9] : (k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X10),k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X10),k2_zfmisc_1(k4_xboole_0(X8,X8),X11))) = k2_zfmisc_1(k4_xboole_0(X8,X8),k4_xboole_0(X10,k4_xboole_0(X10,X11)))) )),
% 9.49/1.59    inference(backward_demodulation,[],[f853,f1092])).
% 9.49/1.59  fof(f853,plain,(
% 9.49/1.59    ( ! [X10,X8,X11,X9] : (k2_zfmisc_1(k4_xboole_0(X8,k2_xboole_0(X9,X8)),k4_xboole_0(X10,k4_xboole_0(X10,X11))) = k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X10),k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X10),k2_zfmisc_1(k4_xboole_0(X8,X8),X11)))) )),
% 9.49/1.59    inference(forward_demodulation,[],[f852,f350])).
% 9.49/1.59  fof(f852,plain,(
% 9.49/1.59    ( ! [X10,X8,X11,X9] : (k2_zfmisc_1(k4_xboole_0(X8,k2_xboole_0(X9,X8)),k4_xboole_0(X10,k4_xboole_0(X10,X11))) = k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X10),k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X10),k2_zfmisc_1(k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X9,X9))),X11)))) )),
% 9.49/1.59    inference(forward_demodulation,[],[f851,f59])).
% 9.49/1.59  fof(f851,plain,(
% 9.49/1.59    ( ! [X10,X8,X11,X9] : (k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X10),k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X10),k2_zfmisc_1(k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X9),X11))) = k2_zfmisc_1(k4_xboole_0(X8,k2_xboole_0(X9,X8)),k4_xboole_0(X10,k4_xboole_0(X10,X11)))) )),
% 9.49/1.59    inference(forward_demodulation,[],[f850,f38])).
% 9.49/1.59  fof(f850,plain,(
% 9.49/1.59    ( ! [X10,X8,X11,X9] : (k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X10),k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X10),k2_zfmisc_1(k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X9),X11))) = k2_zfmisc_1(k4_xboole_0(X8,k2_xboole_0(X9,k4_xboole_0(X8,X9))),k4_xboole_0(X10,k4_xboole_0(X10,X11)))) )),
% 9.49/1.59    inference(forward_demodulation,[],[f849,f803])).
% 9.49/1.59  fof(f803,plain,(
% 9.49/1.59    ( ! [X2,X0,X3,X1] : (k4_xboole_0(k2_zfmisc_1(X0,X2),k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(k4_xboole_0(X0,X1),X3))) = k2_zfmisc_1(k4_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X2,X3)))) )),
% 9.49/1.59    inference(superposition,[],[f67,f57])).
% 9.49/1.59  fof(f849,plain,(
% 9.49/1.59    ( ! [X10,X8,X11,X9] : (k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X10),k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X10),k2_zfmisc_1(k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X9),X11))) = k4_xboole_0(k2_zfmisc_1(X8,X10),k4_xboole_0(k2_zfmisc_1(X8,X10),k2_zfmisc_1(k4_xboole_0(X8,k2_xboole_0(X9,k4_xboole_0(X8,X9))),X11)))) )),
% 9.49/1.59    inference(forward_demodulation,[],[f848,f45])).
% 9.49/1.59  fof(f848,plain,(
% 9.49/1.59    ( ! [X10,X8,X11,X9] : (k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X10),k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X10),k2_zfmisc_1(k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X9),X11))) = k4_xboole_0(k2_zfmisc_1(X8,X10),k4_xboole_0(k2_zfmisc_1(X8,X10),k2_zfmisc_1(k4_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X8,X9)),X11)))) )),
% 9.49/1.59    inference(forward_demodulation,[],[f847,f839])).
% 9.49/1.59  fof(f839,plain,(
% 9.49/1.59    ( ! [X14,X17,X15,X18,X16] : (k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X14,k4_xboole_0(X14,X15)),X17),k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X14,k4_xboole_0(X14,X15)),X17),k2_zfmisc_1(X16,X18))) = k4_xboole_0(k2_zfmisc_1(X14,X17),k4_xboole_0(k2_zfmisc_1(X14,X17),k2_zfmisc_1(k4_xboole_0(X15,k4_xboole_0(X14,X16)),X18)))) )),
% 9.49/1.59    inference(forward_demodulation,[],[f838,f310])).
% 9.49/1.59  fof(f838,plain,(
% 9.49/1.59    ( ! [X14,X17,X15,X18,X16] : (k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X14,k4_xboole_0(X14,X15)),X17),k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X14,k4_xboole_0(X14,X15)),X17),k2_zfmisc_1(X16,X18))) = k4_xboole_0(k2_zfmisc_1(X14,X17),k4_xboole_0(k2_zfmisc_1(X14,X17),k2_zfmisc_1(k4_xboole_0(X15,k4_xboole_0(X14,k4_xboole_0(X14,k4_xboole_0(X15,X16)))),X18)))) )),
% 9.49/1.59    inference(forward_demodulation,[],[f837,f67])).
% 9.49/1.59  fof(f837,plain,(
% 9.49/1.59    ( ! [X14,X17,X15,X18,X16] : (k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X14,k4_xboole_0(X14,X15)),X17),k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X14,k4_xboole_0(X14,X15)),X17),k2_zfmisc_1(X16,X18))) = k2_zfmisc_1(k4_xboole_0(X14,k4_xboole_0(X14,k4_xboole_0(X15,k4_xboole_0(X14,k4_xboole_0(X14,k4_xboole_0(X15,X16)))))),k4_xboole_0(X17,k4_xboole_0(X17,X18)))) )),
% 9.49/1.59    inference(forward_demodulation,[],[f797,f59])).
% 9.49/1.59  fof(f797,plain,(
% 9.49/1.59    ( ! [X14,X17,X15,X18,X16] : (k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X14,k4_xboole_0(X14,X15)),X17),k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X14,k4_xboole_0(X14,X15)),X17),k2_zfmisc_1(X16,X18))) = k2_zfmisc_1(k4_xboole_0(k4_xboole_0(X14,k4_xboole_0(X14,X15)),k4_xboole_0(X14,k4_xboole_0(X14,k4_xboole_0(X15,X16)))),k4_xboole_0(X17,k4_xboole_0(X17,X18)))) )),
% 9.49/1.59    inference(superposition,[],[f67,f59])).
% 9.49/1.59  fof(f847,plain,(
% 9.49/1.59    ( ! [X10,X8,X11,X9] : (k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X10),k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X10),k2_zfmisc_1(k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X9),X11))) = k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X8,X9))),X10),k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X8,X9))),X10),k2_zfmisc_1(X9,X11)))) )),
% 9.49/1.59    inference(forward_demodulation,[],[f804,f836])).
% 9.49/1.59  fof(f836,plain,(
% 9.49/1.59    ( ! [X12,X10,X13,X11,X9] : (k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X9,X10),X12),k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X9,X10),X12),k2_zfmisc_1(X11,X13))) = k2_zfmisc_1(k4_xboole_0(X9,k2_xboole_0(X10,k4_xboole_0(X9,k2_xboole_0(X10,X11)))),k4_xboole_0(X12,k4_xboole_0(X12,X13)))) )),
% 9.49/1.59    inference(forward_demodulation,[],[f796,f45])).
% 9.49/1.59  fof(f796,plain,(
% 9.49/1.59    ( ! [X12,X10,X13,X11,X9] : (k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X9,X10),X12),k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X9,X10),X12),k2_zfmisc_1(X11,X13))) = k2_zfmisc_1(k4_xboole_0(k4_xboole_0(X9,X10),k4_xboole_0(X9,k2_xboole_0(X10,X11))),k4_xboole_0(X12,k4_xboole_0(X12,X13)))) )),
% 9.49/1.59    inference(superposition,[],[f67,f45])).
% 9.49/1.59  fof(f804,plain,(
% 9.49/1.59    ( ! [X10,X8,X11,X9] : (k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X10),k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X10),k2_zfmisc_1(k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X9),X11))) = k2_zfmisc_1(k4_xboole_0(X8,k2_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),k4_xboole_0(X8,k2_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X9)))),k4_xboole_0(X10,k4_xboole_0(X10,X11)))) )),
% 9.49/1.59    inference(superposition,[],[f67,f73])).
% 9.49/1.59  fof(f1354,plain,(
% 9.49/1.59    ( ! [X24,X23,X21,X22] : (k4_xboole_0(k2_zfmisc_1(X21,X23),k4_xboole_0(k2_zfmisc_1(X21,X23),k2_zfmisc_1(k4_xboole_0(X22,X21),X24))) = k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X21,k4_xboole_0(X21,X22)),X23),k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X21,k4_xboole_0(X21,X22)),X23),k2_zfmisc_1(k4_xboole_0(X21,X21),X24)))) )),
% 9.49/1.59    inference(forward_demodulation,[],[f1353,f350])).
% 9.49/1.59  fof(f1353,plain,(
% 9.49/1.59    ( ! [X24,X23,X21,X22] : (k4_xboole_0(k2_zfmisc_1(X21,X23),k4_xboole_0(k2_zfmisc_1(X21,X23),k2_zfmisc_1(k4_xboole_0(X22,X21),X24))) = k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X21,k4_xboole_0(X21,X22)),X23),k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X21,k4_xboole_0(X21,X22)),X23),k2_zfmisc_1(k4_xboole_0(X21,k4_xboole_0(X21,k4_xboole_0(X22,X22))),X24)))) )),
% 9.49/1.59    inference(forward_demodulation,[],[f1352,f59])).
% 9.49/1.59  fof(f1352,plain,(
% 9.49/1.59    ( ! [X24,X23,X21,X22] : (k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X21,k4_xboole_0(X21,X22)),X23),k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X21,k4_xboole_0(X21,X22)),X23),k2_zfmisc_1(k4_xboole_0(k4_xboole_0(X21,k4_xboole_0(X21,X22)),X22),X24))) = k4_xboole_0(k2_zfmisc_1(X21,X23),k4_xboole_0(k2_zfmisc_1(X21,X23),k2_zfmisc_1(k4_xboole_0(X22,X21),X24)))) )),
% 9.49/1.59    inference(forward_demodulation,[],[f1351,f1101])).
% 9.49/1.59  fof(f1351,plain,(
% 9.49/1.59    ( ! [X24,X23,X21,X22] : (k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X21,k4_xboole_0(X21,X22)),X23),k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X21,k4_xboole_0(X21,X22)),X23),k2_zfmisc_1(k4_xboole_0(k4_xboole_0(X21,k4_xboole_0(X21,X22)),X22),X24))) = k4_xboole_0(k2_zfmisc_1(X21,X23),k4_xboole_0(k2_zfmisc_1(X21,X23),k2_zfmisc_1(k4_xboole_0(X22,k4_xboole_0(X21,k4_xboole_0(X21,X22))),X24)))) )),
% 9.49/1.59    inference(forward_demodulation,[],[f1153,f67])).
% 9.49/1.59  fof(f1153,plain,(
% 9.49/1.59    ( ! [X24,X23,X21,X22] : (k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X21,k4_xboole_0(X21,X22)),X23),k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X21,k4_xboole_0(X21,X22)),X23),k2_zfmisc_1(k4_xboole_0(k4_xboole_0(X21,k4_xboole_0(X21,X22)),X22),X24))) = k2_zfmisc_1(k4_xboole_0(X21,k4_xboole_0(X21,k4_xboole_0(X22,k4_xboole_0(X21,k4_xboole_0(X21,X22))))),k4_xboole_0(X23,k4_xboole_0(X23,X24)))) )),
% 9.49/1.59    inference(superposition,[],[f67,f974])).
% 9.49/1.59  fof(f6988,plain,(
% 9.49/1.59    ( ! [X37,X35,X36] : (k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X35,X36),X37),k2_zfmisc_1(k4_xboole_0(X35,k4_xboole_0(X35,X36)),X37)) = k4_xboole_0(k2_zfmisc_1(X35,X37),k2_zfmisc_1(X36,X37))) )),
% 9.49/1.59    inference(forward_demodulation,[],[f6925,f530])).
% 9.49/1.59  fof(f530,plain,(
% 9.49/1.59    ( ! [X19,X17,X18] : (k4_xboole_0(k2_zfmisc_1(X17,X18),k2_zfmisc_1(X19,X18)) = k4_xboole_0(k2_zfmisc_1(X17,X18),k2_zfmisc_1(k4_xboole_0(X17,k4_xboole_0(X17,X19)),X18))) )),
% 9.49/1.59    inference(superposition,[],[f57,f65])).
% 9.49/1.59  fof(f65,plain,(
% 9.49/1.59    ( ! [X2,X0,X1] : (k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))) )),
% 9.49/1.59    inference(definition_unfolding,[],[f52,f35,f35])).
% 9.49/1.59  fof(f52,plain,(
% 9.49/1.59    ( ! [X2,X0,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 9.49/1.59    inference(cnf_transformation,[],[f19])).
% 9.49/1.59  fof(f6925,plain,(
% 9.49/1.59    ( ! [X37,X35,X36] : (k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X35,X36),X37),k2_zfmisc_1(k4_xboole_0(X35,k4_xboole_0(X35,X36)),X37)) = k4_xboole_0(k2_zfmisc_1(X35,X37),k2_zfmisc_1(k4_xboole_0(X35,k4_xboole_0(X35,X36)),X37))) )),
% 9.49/1.59    inference(superposition,[],[f138,f125])).
% 9.49/1.59  fof(f138,plain,(
% 9.49/1.59    ( ! [X4,X5,X3] : (k4_xboole_0(k2_zfmisc_1(X3,X4),k2_zfmisc_1(X5,X4)) = k4_xboole_0(k2_zfmisc_1(k2_xboole_0(X3,X5),X4),k2_zfmisc_1(X5,X4))) )),
% 9.49/1.59    inference(superposition,[],[f37,f50])).
% 9.49/1.59  fof(f50,plain,(
% 9.49/1.59    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 9.49/1.59    inference(cnf_transformation,[],[f18])).
% 9.49/1.59  fof(f32,plain,(
% 9.49/1.59    k2_zfmisc_1(sK2,k4_xboole_0(sK0,sK1)) != k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)) | k2_zfmisc_1(k4_xboole_0(sK0,sK1),sK2) != k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))),
% 9.49/1.59    inference(cnf_transformation,[],[f29])).
% 9.49/1.59  fof(f29,plain,(
% 9.49/1.59    k2_zfmisc_1(sK2,k4_xboole_0(sK0,sK1)) != k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)) | k2_zfmisc_1(k4_xboole_0(sK0,sK1),sK2) != k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))),
% 9.49/1.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f28])).
% 9.49/1.59  fof(f28,plain,(
% 9.49/1.59    ? [X0,X1,X2] : (k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) != k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) | k2_zfmisc_1(k4_xboole_0(X0,X1),X2) != k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) => (k2_zfmisc_1(sK2,k4_xboole_0(sK0,sK1)) != k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)) | k2_zfmisc_1(k4_xboole_0(sK0,sK1),sK2) != k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),
% 9.49/1.59    introduced(choice_axiom,[])).
% 9.49/1.59  fof(f23,plain,(
% 9.49/1.59    ? [X0,X1,X2] : (k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) != k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) | k2_zfmisc_1(k4_xboole_0(X0,X1),X2) != k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 9.49/1.59    inference(ennf_transformation,[],[f22])).
% 9.49/1.59  fof(f22,negated_conjecture,(
% 9.49/1.59    ~! [X0,X1,X2] : (k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 9.49/1.59    inference(negated_conjecture,[],[f21])).
% 9.49/1.59  fof(f21,conjecture,(
% 9.49/1.59    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 9.49/1.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_zfmisc_1)).
% 9.49/1.59  % SZS output end Proof for theBenchmark
% 9.49/1.59  % (1929)------------------------------
% 9.49/1.59  % (1929)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.49/1.59  % (1929)Termination reason: Refutation
% 9.49/1.59  
% 9.49/1.59  % (1929)Memory used [KB]: 13944
% 9.49/1.59  % (1929)Time elapsed: 0.746 s
% 9.49/1.59  % (1929)------------------------------
% 9.49/1.59  % (1929)------------------------------
% 9.49/1.59  % (1686)Success in time 1.232 s
%------------------------------------------------------------------------------
