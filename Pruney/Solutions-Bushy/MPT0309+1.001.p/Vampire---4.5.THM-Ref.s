%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0309+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:43 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   16 (  19 expanded)
%              Number of leaves         :    4 (   6 expanded)
%              Depth                    :    9
%              Number of atoms          :   18 (  23 expanded)
%              Number of equality atoms :   17 (  22 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f48,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f47])).

fof(f47,plain,(
    k2_zfmisc_1(k2_xboole_0(sK0,sK1),k2_xboole_0(sK2,sK3)) != k2_zfmisc_1(k2_xboole_0(sK0,sK1),k2_xboole_0(sK2,sK3)) ),
    inference(superposition,[],[f46,f10])).

fof(f10,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(f46,plain,(
    k2_zfmisc_1(k2_xboole_0(sK0,sK1),k2_xboole_0(sK2,sK3)) != k2_xboole_0(k2_zfmisc_1(sK0,k2_xboole_0(sK2,sK3)),k2_zfmisc_1(sK1,k2_xboole_0(sK2,sK3))) ),
    inference(forward_demodulation,[],[f45,f11])).

fof(f11,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f45,plain,(
    k2_zfmisc_1(k2_xboole_0(sK0,sK1),k2_xboole_0(sK2,sK3)) != k2_xboole_0(k2_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK3)),k2_zfmisc_1(sK1,k2_xboole_0(sK2,sK3))) ),
    inference(forward_demodulation,[],[f43,f11])).

fof(f43,plain,(
    k2_zfmisc_1(k2_xboole_0(sK0,sK1),k2_xboole_0(sK2,sK3)) != k2_xboole_0(k2_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK3)),k2_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK1,sK3))) ),
    inference(superposition,[],[f8,f9])).

fof(f9,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f8,plain,(
    k2_zfmisc_1(k2_xboole_0(sK0,sK1),k2_xboole_0(sK2,sK3)) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK3)),k2_zfmisc_1(sK1,sK2)),k2_zfmisc_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    k2_zfmisc_1(k2_xboole_0(sK0,sK1),k2_xboole_0(sK2,sK3)) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK3)),k2_zfmisc_1(sK1,sK2)),k2_zfmisc_1(sK1,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f5,f6])).

fof(f6,plain,
    ( ? [X0,X1,X2,X3] : k2_zfmisc_1(k2_xboole_0(X0,X1),k2_xboole_0(X2,X3)) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X3)),k2_zfmisc_1(X1,X2)),k2_zfmisc_1(X1,X3))
   => k2_zfmisc_1(k2_xboole_0(sK0,sK1),k2_xboole_0(sK2,sK3)) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK3)),k2_zfmisc_1(sK1,sK2)),k2_zfmisc_1(sK1,sK3)) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1,X2,X3] : k2_zfmisc_1(k2_xboole_0(X0,X1),k2_xboole_0(X2,X3)) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X3)),k2_zfmisc_1(X1,X2)),k2_zfmisc_1(X1,X3)) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X3)),k2_zfmisc_1(X1,X2)),k2_zfmisc_1(X1,X3)) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X3)),k2_zfmisc_1(X1,X2)),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_zfmisc_1)).

%------------------------------------------------------------------------------
