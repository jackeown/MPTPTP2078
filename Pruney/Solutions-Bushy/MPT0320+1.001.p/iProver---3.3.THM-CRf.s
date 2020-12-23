%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0320+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:00 EST 2020

% Result     : Theorem 0.57s
% Output     : CNFRefutation 0.57s
% Verified   : 
% Statistics : Number of formulae       :   20 (  23 expanded)
%              Number of clauses        :    8 (   8 expanded)
%              Number of leaves         :    4 (   6 expanded)
%              Depth                    :    9
%              Number of atoms          :   33 (  37 expanded)
%              Number of equality atoms :   32 (  36 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X2,k1_tarski(X1))) = k2_zfmisc_1(X2,k2_tarski(X0,X1))
      & k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2)) = k2_zfmisc_1(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k2_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X2,k1_tarski(X1))) = k2_zfmisc_1(X2,k2_tarski(X0,X1))
        & k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2)) = k2_zfmisc_1(k2_tarski(X0,X1),X2) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X2,k1_tarski(X1))) != k2_zfmisc_1(X2,k2_tarski(X0,X1))
      | k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2)) != k2_zfmisc_1(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f6,plain,
    ( ? [X0,X1,X2] :
        ( k2_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X2,k1_tarski(X1))) != k2_zfmisc_1(X2,k2_tarski(X0,X1))
        | k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2)) != k2_zfmisc_1(k2_tarski(X0,X1),X2) )
   => ( k2_xboole_0(k2_zfmisc_1(sK2,k1_tarski(sK0)),k2_zfmisc_1(sK2,k1_tarski(sK1))) != k2_zfmisc_1(sK2,k2_tarski(sK0,sK1))
      | k2_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK2)) != k2_zfmisc_1(k2_tarski(sK0,sK1),sK2) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,
    ( k2_xboole_0(k2_zfmisc_1(sK2,k1_tarski(sK0)),k2_zfmisc_1(sK2,k1_tarski(sK1))) != k2_zfmisc_1(sK2,k2_tarski(sK0,sK1))
    | k2_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK2)) != k2_zfmisc_1(k2_tarski(sK0,sK1),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f6])).

fof(f11,plain,
    ( k2_xboole_0(k2_zfmisc_1(sK2,k1_tarski(sK0)),k2_zfmisc_1(sK2,k1_tarski(sK1))) != k2_zfmisc_1(sK2,k2_tarski(sK0,sK1))
    | k2_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK2)) != k2_zfmisc_1(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f12,plain,
    ( k2_xboole_0(k2_zfmisc_1(sK2,k1_tarski(sK0)),k2_zfmisc_1(sK2,k1_tarski(sK1))) != k2_zfmisc_1(sK2,k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))
    | k2_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK2)) != k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2) ),
    inference(definition_unfolding,[],[f11,f10,f10])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k2_xboole_0(X0,X1))
      & k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k2_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f9,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

cnf(c_2,negated_conjecture,
    ( k2_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK2)) != k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2)
    | k2_xboole_0(k2_zfmisc_1(sK2,k1_tarski(sK0)),k2_zfmisc_1(sK2,k1_tarski(sK1))) != k2_zfmisc_1(sK2,k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_10,negated_conjecture,
    ( k2_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK2)) != k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2)
    | k2_xboole_0(k2_zfmisc_1(sK2,k1_tarski(sK0)),k2_zfmisc_1(sK2,k1_tarski(sK1))) != k2_zfmisc_1(sK2,k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1,plain,
    ( k2_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f8])).

cnf(c_11,plain,
    ( k2_xboole_0(k2_zfmisc_1(X0_34,X1_34),k2_zfmisc_1(X2_34,X1_34)) = k2_zfmisc_1(k2_xboole_0(X0_34,X2_34),X1_34) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_0,plain,
    ( k2_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) = k2_zfmisc_1(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

cnf(c_12,plain,
    ( k2_xboole_0(k2_zfmisc_1(X0_34,X1_34),k2_zfmisc_1(X0_34,X2_34)) = k2_zfmisc_1(X0_34,k2_xboole_0(X1_34,X2_34)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_26,plain,
    ( k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2) != k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2)
    | k2_zfmisc_1(sK2,k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) != k2_zfmisc_1(sK2,k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) ),
    inference(demodulation,[status(thm)],[c_10,c_11,c_12])).

cnf(c_27,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_26])).


%------------------------------------------------------------------------------
