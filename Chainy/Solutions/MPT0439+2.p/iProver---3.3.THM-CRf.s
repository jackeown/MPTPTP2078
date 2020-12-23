%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0439+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:40 EST 2020

% Result     : Theorem 15.55s
% Output     : CNFRefutation 15.55s
% Verified   : 
% Statistics : Number of formulae       :   24 (  31 expanded)
%              Number of clauses        :    7 (   7 expanded)
%              Number of leaves         :    5 (   8 expanded)
%              Depth                    :    7
%              Number of atoms          :   42 (  56 expanded)
%              Number of equality atoms :   17 (  25 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f655,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1110,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f655])).

fof(f2535,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1110])).

fof(f86,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f720,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f86])).

fof(f1637,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f720])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1662,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f2625,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f1637,f1662])).

fof(f656,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f657,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    inference(negated_conjecture,[],[f656])).

fof(f1111,plain,(
    ? [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) != X0
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f657])).

fof(f1505,plain,
    ( ? [X0] :
        ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) != X0
        & v1_relat_1(X0) )
   => ( k3_xboole_0(sK135,k2_zfmisc_1(k1_relat_1(sK135),k2_relat_1(sK135))) != sK135
      & v1_relat_1(sK135) ) ),
    introduced(choice_axiom,[])).

fof(f1506,plain,
    ( k3_xboole_0(sK135,k2_zfmisc_1(k1_relat_1(sK135),k2_relat_1(sK135))) != sK135
    & v1_relat_1(sK135) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK135])],[f1111,f1505])).

fof(f2537,plain,(
    k3_xboole_0(sK135,k2_zfmisc_1(k1_relat_1(sK135),k2_relat_1(sK135))) != sK135 ),
    inference(cnf_transformation,[],[f1506])).

fof(f3043,plain,(
    k4_xboole_0(sK135,k4_xboole_0(sK135,k2_zfmisc_1(k1_relat_1(sK135),k2_relat_1(sK135)))) != sK135 ),
    inference(definition_unfolding,[],[f2537,f1662])).

fof(f2536,plain,(
    v1_relat_1(sK135) ),
    inference(cnf_transformation,[],[f1506])).

cnf(c_1014,plain,
    ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f2535])).

cnf(c_48673,plain,
    ( r1_tarski(sK135,k2_zfmisc_1(k1_relat_1(sK135),k2_relat_1(sK135)))
    | ~ v1_relat_1(sK135) ),
    inference(instantiation,[status(thm)],[c_1014])).

cnf(c_130,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f2625])).

cnf(c_44518,plain,
    ( ~ r1_tarski(sK135,k2_zfmisc_1(k1_relat_1(sK135),k2_relat_1(sK135)))
    | k4_xboole_0(sK135,k4_xboole_0(sK135,k2_zfmisc_1(k1_relat_1(sK135),k2_relat_1(sK135)))) = sK135 ),
    inference(instantiation,[status(thm)],[c_130])).

cnf(c_1015,negated_conjecture,
    ( k4_xboole_0(sK135,k4_xboole_0(sK135,k2_zfmisc_1(k1_relat_1(sK135),k2_relat_1(sK135)))) != sK135 ),
    inference(cnf_transformation,[],[f3043])).

cnf(c_1016,negated_conjecture,
    ( v1_relat_1(sK135) ),
    inference(cnf_transformation,[],[f2536])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_48673,c_44518,c_1015,c_1016])).

%------------------------------------------------------------------------------
