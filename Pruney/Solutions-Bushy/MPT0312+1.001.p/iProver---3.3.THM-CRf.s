%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0312+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:58 EST 2020

% Result     : Theorem 1.08s
% Output     : CNFRefutation 1.08s
% Verified   : 
% Statistics : Number of formulae       :   31 (  47 expanded)
%              Number of clauses        :   15 (  16 expanded)
%              Number of leaves         :    5 (  10 expanded)
%              Depth                    :   12
%              Number of atoms          :   54 ( 104 expanded)
%              Number of equality atoms :   31 (  49 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f4,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_tarski(X2,X3)
          & r1_tarski(X0,X1) )
       => k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(X0,X2) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f7,plain,(
    ? [X0,X1,X2,X3] :
      ( k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) != k2_zfmisc_1(X0,X2)
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f8,plain,(
    ? [X0,X1,X2,X3] :
      ( k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) != k2_zfmisc_1(X0,X2)
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f7])).

fof(f9,plain,
    ( ? [X0,X1,X2,X3] :
        ( k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) != k2_zfmisc_1(X0,X2)
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
   => ( k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)) != k2_zfmisc_1(sK0,sK2)
      & r1_tarski(sK2,sK3)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,
    ( k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)) != k2_zfmisc_1(sK0,sK2)
    & r1_tarski(sK2,sK3)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f9])).

fof(f14,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) = k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X2,X0,X3,X1] : k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) = k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) ),
    inference(cnf_transformation,[],[f2])).

fof(f16,plain,(
    k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)) != k2_zfmisc_1(sK0,sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f15,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f10])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f13])).

cnf(c_5,negated_conjecture,
    ( r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_46,plain,
    ( k3_xboole_0(X0,X1) = X0
    | sK1 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_5])).

cnf(c_47,plain,
    ( k3_xboole_0(sK0,sK1) = sK0 ),
    inference(unflattening,[status(thm)],[c_46])).

cnf(c_1,plain,
    ( k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_70,plain,
    ( k3_xboole_0(k2_zfmisc_1(sK0,X0),k2_zfmisc_1(sK1,X1)) = k2_zfmisc_1(sK0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_47,c_1])).

cnf(c_3,negated_conjecture,
    ( k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)) != k2_zfmisc_1(sK0,sK2) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_84,plain,
    ( k2_zfmisc_1(sK0,k3_xboole_0(sK3,sK2)) != k2_zfmisc_1(sK0,sK2) ),
    inference(demodulation,[status(thm)],[c_70,c_3])).

cnf(c_4,negated_conjecture,
    ( r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_41,plain,
    ( k3_xboole_0(X0,X1) = X0
    | sK2 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_4])).

cnf(c_42,plain,
    ( k3_xboole_0(sK2,sK3) = sK2 ),
    inference(unflattening,[status(thm)],[c_41])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_63,plain,
    ( k3_xboole_0(sK3,sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_42,c_0])).

cnf(c_85,plain,
    ( k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(sK0,sK2) ),
    inference(light_normalisation,[status(thm)],[c_84,c_63])).

cnf(c_86,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_85])).


%------------------------------------------------------------------------------
