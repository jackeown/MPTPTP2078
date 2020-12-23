%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0904+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:57 EST 2020

% Result     : Theorem 31.38s
% Output     : CNFRefutation 31.38s
% Verified   : 
% Statistics : Number of formulae       :   33 ( 107 expanded)
%              Number of clauses        :   12 (  21 expanded)
%              Number of leaves         :    6 (  30 expanded)
%              Depth                    :   10
%              Number of atoms          :   83 ( 266 expanded)
%              Number of equality atoms :    5 (  34 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f343,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) )
     => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1554,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ( ~ r1_xboole_0(X2,X3)
        & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f343])).

fof(f4305,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1554])).

fof(f1371,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ~ r1_xboole_0(k4_zfmisc_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))
     => ( ~ r1_xboole_0(X3,X7)
        & ~ r1_xboole_0(X2,X6)
        & ~ r1_xboole_0(X1,X5)
        & ~ r1_xboole_0(X0,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1372,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( ~ r1_xboole_0(k4_zfmisc_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))
       => ( ~ r1_xboole_0(X3,X7)
          & ~ r1_xboole_0(X2,X6)
          & ~ r1_xboole_0(X1,X5)
          & ~ r1_xboole_0(X0,X4) ) ) ),
    inference(negated_conjecture,[],[f1371])).

fof(f2762,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( r1_xboole_0(X3,X7)
        | r1_xboole_0(X2,X6)
        | r1_xboole_0(X1,X5)
        | r1_xboole_0(X0,X4) )
      & ~ r1_xboole_0(k4_zfmisc_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) ) ),
    inference(ennf_transformation,[],[f1372])).

fof(f3816,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( ( r1_xboole_0(X3,X7)
          | r1_xboole_0(X2,X6)
          | r1_xboole_0(X1,X5)
          | r1_xboole_0(X0,X4) )
        & ~ r1_xboole_0(k4_zfmisc_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) )
   => ( ( r1_xboole_0(sK417,sK421)
        | r1_xboole_0(sK416,sK420)
        | r1_xboole_0(sK415,sK419)
        | r1_xboole_0(sK414,sK418) )
      & ~ r1_xboole_0(k4_zfmisc_1(sK414,sK415,sK416,sK417),k4_zfmisc_1(sK418,sK419,sK420,sK421)) ) ),
    introduced(choice_axiom,[])).

fof(f3817,plain,
    ( ( r1_xboole_0(sK417,sK421)
      | r1_xboole_0(sK416,sK420)
      | r1_xboole_0(sK415,sK419)
      | r1_xboole_0(sK414,sK418) )
    & ~ r1_xboole_0(k4_zfmisc_1(sK414,sK415,sK416,sK417),k4_zfmisc_1(sK418,sK419,sK420,sK421)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK414,sK415,sK416,sK417,sK418,sK419,sK420,sK421])],[f2762,f3816])).

fof(f6244,plain,(
    ~ r1_xboole_0(k4_zfmisc_1(sK414,sK415,sK416,sK417),k4_zfmisc_1(sK418,sK419,sK420,sK421)) ),
    inference(cnf_transformation,[],[f3817])).

fof(f1279,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6027,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f1279])).

fof(f1277,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6025,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f1277])).

fof(f6264,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f6027,f6025])).

fof(f7095,plain,(
    ~ r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK414,sK415),sK416),sK417),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK418,sK419),sK420),sK421)) ),
    inference(definition_unfolding,[],[f6244,f6264,f6264])).

fof(f4306,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(cnf_transformation,[],[f1554])).

fof(f1358,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_xboole_0(k3_zfmisc_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))
     => ( ~ r1_xboole_0(X2,X5)
        & ~ r1_xboole_0(X1,X4)
        & ~ r1_xboole_0(X0,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2749,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( ~ r1_xboole_0(X2,X5)
        & ~ r1_xboole_0(X1,X4)
        & ~ r1_xboole_0(X0,X3) )
      | r1_xboole_0(k3_zfmisc_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) ) ),
    inference(ennf_transformation,[],[f1358])).

fof(f6207,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r1_xboole_0(X1,X4)
      | r1_xboole_0(k3_zfmisc_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) ) ),
    inference(cnf_transformation,[],[f2749])).

fof(f7058,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r1_xboole_0(X1,X4)
      | r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)) ) ),
    inference(definition_unfolding,[],[f6207,f6025,f6025])).

fof(f6245,plain,
    ( r1_xboole_0(sK417,sK421)
    | r1_xboole_0(sK416,sK420)
    | r1_xboole_0(sK415,sK419)
    | r1_xboole_0(sK414,sK418) ),
    inference(cnf_transformation,[],[f3817])).

cnf(c_472,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f4305])).

cnf(c_2404,negated_conjecture,
    ( ~ r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK414,sK415),sK416),sK417),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK418,sK419),sK420),sK421)) ),
    inference(cnf_transformation,[],[f7095])).

cnf(c_99489,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK414,sK415),sK416),k2_zfmisc_1(k2_zfmisc_1(sK418,sK419),sK420)) ),
    inference(resolution,[status(thm)],[c_472,c_2404])).

cnf(c_99497,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1(sK414,sK415),k2_zfmisc_1(sK418,sK419)) ),
    inference(resolution,[status(thm)],[c_99489,c_472])).

cnf(c_471,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f4306])).

cnf(c_99897,plain,
    ( ~ r1_xboole_0(sK415,sK419) ),
    inference(resolution,[status(thm)],[c_99497,c_471])).

cnf(c_99895,plain,
    ( ~ r1_xboole_0(sK414,sK418) ),
    inference(resolution,[status(thm)],[c_99497,c_472])).

cnf(c_2366,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(X2,X0),X3),k2_zfmisc_1(k2_zfmisc_1(X4,X1),X5)) ),
    inference(cnf_transformation,[],[f7058])).

cnf(c_89192,plain,
    ( r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK414,sK415),sK416),sK417),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK418,sK419),sK420),sK421))
    | ~ r1_xboole_0(sK416,sK420) ),
    inference(instantiation,[status(thm)],[c_2366])).

cnf(c_88607,plain,
    ( r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK414,sK415),sK416),sK417),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK418,sK419),sK420),sK421))
    | ~ r1_xboole_0(sK417,sK421) ),
    inference(instantiation,[status(thm)],[c_471])).

cnf(c_2403,negated_conjecture,
    ( r1_xboole_0(sK414,sK418)
    | r1_xboole_0(sK415,sK419)
    | r1_xboole_0(sK416,sK420)
    | r1_xboole_0(sK417,sK421) ),
    inference(cnf_transformation,[],[f6245])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_99897,c_99895,c_89192,c_88607,c_2403,c_2404])).

%------------------------------------------------------------------------------
