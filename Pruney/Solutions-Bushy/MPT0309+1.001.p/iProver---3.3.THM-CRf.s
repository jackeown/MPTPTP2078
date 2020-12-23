%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0309+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:58 EST 2020

% Result     : Theorem 0.82s
% Output     : CNFRefutation 0.82s
% Verified   : 
% Statistics : Number of formulae       :   19 (  23 expanded)
%              Number of clauses        :    8 (   9 expanded)
%              Number of leaves         :    4 (   6 expanded)
%              Depth                    :    9
%              Number of atoms          :   21 (  27 expanded)
%              Number of equality atoms :   20 (  26 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,conjecture,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X3)),k2_zfmisc_1(X1,X2)),k2_zfmisc_1(X1,X3)) = k2_zfmisc_1(k2_xboole_0(X0,X1),k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X3)),k2_zfmisc_1(X1,X2)),k2_zfmisc_1(X1,X3)) = k2_zfmisc_1(k2_xboole_0(X0,X1),k2_xboole_0(X2,X3)) ),
    inference(negated_conjecture,[],[f3])).

fof(f5,plain,(
    ? [X0,X1,X2,X3] : k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X3)),k2_zfmisc_1(X1,X2)),k2_zfmisc_1(X1,X3)) != k2_zfmisc_1(k2_xboole_0(X0,X1),k2_xboole_0(X2,X3)) ),
    inference(ennf_transformation,[],[f4])).

fof(f6,plain,
    ( ? [X0,X1,X2,X3] : k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X3)),k2_zfmisc_1(X1,X2)),k2_zfmisc_1(X1,X3)) != k2_zfmisc_1(k2_xboole_0(X0,X1),k2_xboole_0(X2,X3))
   => k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK3)),k2_zfmisc_1(sK1,sK2)),k2_zfmisc_1(sK1,sK3)) != k2_zfmisc_1(k2_xboole_0(sK0,sK1),k2_xboole_0(sK2,sK3)) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK3)),k2_zfmisc_1(sK1,sK2)),k2_zfmisc_1(sK1,sK3)) != k2_zfmisc_1(k2_xboole_0(sK0,sK1),k2_xboole_0(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f5,f6])).

fof(f11,plain,(
    k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK3)),k2_zfmisc_1(sK1,sK2)),k2_zfmisc_1(sK1,sK3)) != k2_zfmisc_1(k2_xboole_0(sK0,sK1),k2_xboole_0(sK2,sK3)) ),
    inference(cnf_transformation,[],[f7])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k2_xboole_0(X0,X1))
      & k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k2_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f8,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

cnf(c_2,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

cnf(c_3,negated_conjecture,
    ( k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK3)),k2_zfmisc_1(sK1,sK2)),k2_zfmisc_1(sK1,sK3)) != k2_zfmisc_1(k2_xboole_0(sK0,sK1),k2_xboole_0(sK2,sK3)) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_0,plain,
    ( k2_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) = k2_zfmisc_1(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

cnf(c_18,plain,
    ( k2_xboole_0(k2_xboole_0(k2_zfmisc_1(sK0,k2_xboole_0(sK2,sK3)),k2_zfmisc_1(sK1,sK2)),k2_zfmisc_1(sK1,sK3)) != k2_zfmisc_1(k2_xboole_0(sK0,sK1),k2_xboole_0(sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_3,c_0])).

cnf(c_19,plain,
    ( k2_xboole_0(k2_zfmisc_1(sK0,k2_xboole_0(sK2,sK3)),k2_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK1,sK3))) != k2_zfmisc_1(k2_xboole_0(sK0,sK1),k2_xboole_0(sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_2,c_18])).

cnf(c_1,plain,
    ( k2_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f8])).

cnf(c_20,plain,
    ( k2_zfmisc_1(k2_xboole_0(sK0,sK1),k2_xboole_0(sK2,sK3)) != k2_zfmisc_1(k2_xboole_0(sK0,sK1),k2_xboole_0(sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_19,c_0,c_1])).

cnf(c_21,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_20])).


%------------------------------------------------------------------------------
