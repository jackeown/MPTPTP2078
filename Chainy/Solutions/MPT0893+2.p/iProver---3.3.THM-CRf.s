%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0893+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:56 EST 2020

% Result     : Theorem 5.61s
% Output     : CNFRefutation 5.61s
% Verified   : 
% Statistics : Number of formulae       :   14 (  14 expanded)
%              Number of clauses        :    2 (   2 expanded)
%              Number of leaves         :    4 (   4 expanded)
%              Depth                    :    7
%              Number of atoms          :   15 (  15 expanded)
%              Number of equality atoms :   14 (  14 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1350,conjecture,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1351,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(negated_conjecture,[],[f1350])).

fof(f2721,plain,(
    ? [X0,X1,X2,X3] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) != k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(ennf_transformation,[],[f1351])).

fof(f3752,plain,
    ( ? [X0,X1,X2,X3] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) != k4_zfmisc_1(X0,X1,X2,X3)
   => k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK393,sK394),sK395),sK396) != k4_zfmisc_1(sK393,sK394,sK395,sK396) ),
    introduced(choice_axiom,[])).

fof(f3753,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK393,sK394),sK395),sK396) != k4_zfmisc_1(sK393,sK394,sK395,sK396) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK393,sK394,sK395,sK396])],[f2721,f3752])).

fof(f6126,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK393,sK394),sK395),sK396) != k4_zfmisc_1(sK393,sK394,sK395,sK396) ),
    inference(cnf_transformation,[],[f3753])).

fof(f1277,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5959,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f1277])).

fof(f1275,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5957,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f1275])).

fof(f6148,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f5959,f5957])).

fof(f6922,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK393,sK394),sK395),sK396) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK393,sK394),sK395),sK396) ),
    inference(definition_unfolding,[],[f6126,f6148])).

cnf(c_2347,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK393,sK394),sK395),sK396) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK393,sK394),sK395),sK396) ),
    inference(cnf_transformation,[],[f6922])).

cnf(c_11599,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_2347])).

%------------------------------------------------------------------------------
