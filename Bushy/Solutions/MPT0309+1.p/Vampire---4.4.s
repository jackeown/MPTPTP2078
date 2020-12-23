%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : zfmisc_1__t121_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:59 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   13 (  16 expanded)
%              Number of leaves         :    3 (   5 expanded)
%              Depth                    :    7
%              Number of atoms          :   14 (  19 expanded)
%              Number of equality atoms :   13 (  18 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f47,plain,(
    $false ),
    inference(subsumption_resolution,[],[f46,f15])).

fof(f15,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k2_xboole_0(X0,X1))
      & k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k2_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t121_zfmisc_1.p',t120_zfmisc_1)).

fof(f46,plain,(
    k2_xboole_0(k2_zfmisc_1(sK0,k2_xboole_0(sK2,sK3)),k2_zfmisc_1(sK1,k2_xboole_0(sK2,sK3))) != k2_zfmisc_1(k2_xboole_0(sK0,sK1),k2_xboole_0(sK2,sK3)) ),
    inference(forward_demodulation,[],[f45,f16])).

fof(f16,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f45,plain,(
    k2_xboole_0(k2_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK3)),k2_zfmisc_1(sK1,k2_xboole_0(sK2,sK3))) != k2_zfmisc_1(k2_xboole_0(sK0,sK1),k2_xboole_0(sK2,sK3)) ),
    inference(forward_demodulation,[],[f38,f16])).

fof(f38,plain,(
    k2_xboole_0(k2_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK3)),k2_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK1,sK3))) != k2_zfmisc_1(k2_xboole_0(sK0,sK1),k2_xboole_0(sK2,sK3)) ),
    inference(superposition,[],[f11,f14])).

fof(f14,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t121_zfmisc_1.p',t4_xboole_1)).

fof(f11,plain,(
    k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK3)),k2_zfmisc_1(sK1,sK2)),k2_zfmisc_1(sK1,sK3)) != k2_zfmisc_1(k2_xboole_0(sK0,sK1),k2_xboole_0(sK2,sK3)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] : k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X3)),k2_zfmisc_1(X1,X2)),k2_zfmisc_1(X1,X3)) != k2_zfmisc_1(k2_xboole_0(X0,X1),k2_xboole_0(X2,X3)) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X3)),k2_zfmisc_1(X1,X2)),k2_zfmisc_1(X1,X3)) = k2_zfmisc_1(k2_xboole_0(X0,X1),k2_xboole_0(X2,X3)) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X3)),k2_zfmisc_1(X1,X2)),k2_zfmisc_1(X1,X3)) = k2_zfmisc_1(k2_xboole_0(X0,X1),k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t121_zfmisc_1.p',t121_zfmisc_1)).
%------------------------------------------------------------------------------
