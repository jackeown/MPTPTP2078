%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0928+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:57 EST 2020

% Result     : Theorem 31.45s
% Output     : CNFRefutation 31.45s
% Verified   : 
% Statistics : Number of formulae       :   36 (  69 expanded)
%              Number of clauses        :   10 (  10 expanded)
%              Number of leaves         :    6 (  18 expanded)
%              Depth                    :    8
%              Number of atoms          :   98 ( 247 expanded)
%              Number of equality atoms :    5 (  14 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1385,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_tarski(X4,X5)
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k3_zfmisc_1(X0,X2,X4),k3_zfmisc_1(X1,X3,X5)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2804,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( r1_tarski(k3_zfmisc_1(X0,X2,X4),k3_zfmisc_1(X1,X3,X5))
      | ~ r1_tarski(X4,X5)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1385])).

fof(f2805,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( r1_tarski(k3_zfmisc_1(X0,X2,X4),k3_zfmisc_1(X1,X3,X5))
      | ~ r1_tarski(X4,X5)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f2804])).

fof(f6400,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_tarski(k3_zfmisc_1(X0,X2,X4),k3_zfmisc_1(X1,X3,X5))
      | ~ r1_tarski(X4,X5)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2805])).

fof(f1277,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6133,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f1277])).

fof(f7351,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_tarski(k2_zfmisc_1(k2_zfmisc_1(X0,X2),X4),k2_zfmisc_1(k2_zfmisc_1(X1,X3),X5))
      | ~ r1_tarski(X4,X5)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f6400,f6133,f6133])).

fof(f335,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1574,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f335])).

fof(f1575,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f1574])).

fof(f4402,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1575])).

fof(f1397,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( r1_tarski(X6,X7)
        & r1_tarski(X4,X5)
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k4_zfmisc_1(X0,X2,X4,X6),k4_zfmisc_1(X1,X3,X5,X7)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1398,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( ( r1_tarski(X6,X7)
          & r1_tarski(X4,X5)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X1) )
       => r1_tarski(k4_zfmisc_1(X0,X2,X4,X6),k4_zfmisc_1(X1,X3,X5,X7)) ) ),
    inference(negated_conjecture,[],[f1397])).

fof(f2821,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ~ r1_tarski(k4_zfmisc_1(X0,X2,X4,X6),k4_zfmisc_1(X1,X3,X5,X7))
      & r1_tarski(X6,X7)
      & r1_tarski(X4,X5)
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1398])).

fof(f2822,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ~ r1_tarski(k4_zfmisc_1(X0,X2,X4,X6),k4_zfmisc_1(X1,X3,X5,X7))
      & r1_tarski(X6,X7)
      & r1_tarski(X4,X5)
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f2821])).

fof(f3926,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( ~ r1_tarski(k4_zfmisc_1(X0,X2,X4,X6),k4_zfmisc_1(X1,X3,X5,X7))
        & r1_tarski(X6,X7)
        & r1_tarski(X4,X5)
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k4_zfmisc_1(sK456,sK458,sK460,sK462),k4_zfmisc_1(sK457,sK459,sK461,sK463))
      & r1_tarski(sK462,sK463)
      & r1_tarski(sK460,sK461)
      & r1_tarski(sK458,sK459)
      & r1_tarski(sK456,sK457) ) ),
    introduced(choice_axiom,[])).

fof(f3927,plain,
    ( ~ r1_tarski(k4_zfmisc_1(sK456,sK458,sK460,sK462),k4_zfmisc_1(sK457,sK459,sK461,sK463))
    & r1_tarski(sK462,sK463)
    & r1_tarski(sK460,sK461)
    & r1_tarski(sK458,sK459)
    & r1_tarski(sK456,sK457) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK456,sK457,sK458,sK459,sK460,sK461,sK462,sK463])],[f2822,f3926])).

fof(f6459,plain,(
    ~ r1_tarski(k4_zfmisc_1(sK456,sK458,sK460,sK462),k4_zfmisc_1(sK457,sK459,sK461,sK463)) ),
    inference(cnf_transformation,[],[f3927])).

fof(f1279,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6135,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f1279])).

fof(f6474,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f6135,f6133])).

fof(f7404,plain,(
    ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK456,sK458),sK460),sK462),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK457,sK459),sK461),sK463)) ),
    inference(definition_unfolding,[],[f6459,f6474,f6474])).

fof(f6458,plain,(
    r1_tarski(sK462,sK463) ),
    inference(cnf_transformation,[],[f3927])).

fof(f6457,plain,(
    r1_tarski(sK460,sK461) ),
    inference(cnf_transformation,[],[f3927])).

fof(f6456,plain,(
    r1_tarski(sK458,sK459) ),
    inference(cnf_transformation,[],[f3927])).

fof(f6455,plain,(
    r1_tarski(sK456,sK457) ),
    inference(cnf_transformation,[],[f3927])).

cnf(c_2451,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X3)
    | ~ r1_tarski(X4,X5)
    | r1_tarski(k2_zfmisc_1(k2_zfmisc_1(X0,X2),X4),k2_zfmisc_1(k2_zfmisc_1(X1,X3),X5)) ),
    inference(cnf_transformation,[],[f7351])).

cnf(c_115778,plain,
    ( r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK456,sK458),sK460),k2_zfmisc_1(k2_zfmisc_1(sK457,sK459),sK461))
    | ~ r1_tarski(sK460,sK461)
    | ~ r1_tarski(sK458,sK459)
    | ~ r1_tarski(sK456,sK457) ),
    inference(instantiation,[status(thm)],[c_2451])).

cnf(c_460,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X3)
    | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f4402])).

cnf(c_113954,plain,
    ( r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK456,sK458),sK460),sK462),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK457,sK459),sK461),sK463))
    | ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK456,sK458),sK460),k2_zfmisc_1(k2_zfmisc_1(sK457,sK459),sK461))
    | ~ r1_tarski(sK462,sK463) ),
    inference(instantiation,[status(thm)],[c_460])).

cnf(c_2506,negated_conjecture,
    ( ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK456,sK458),sK460),sK462),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK457,sK459),sK461),sK463)) ),
    inference(cnf_transformation,[],[f7404])).

cnf(c_2507,negated_conjecture,
    ( r1_tarski(sK462,sK463) ),
    inference(cnf_transformation,[],[f6458])).

cnf(c_2508,negated_conjecture,
    ( r1_tarski(sK460,sK461) ),
    inference(cnf_transformation,[],[f6457])).

cnf(c_2509,negated_conjecture,
    ( r1_tarski(sK458,sK459) ),
    inference(cnf_transformation,[],[f6456])).

cnf(c_2510,negated_conjecture,
    ( r1_tarski(sK456,sK457) ),
    inference(cnf_transformation,[],[f6455])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_115778,c_113954,c_2506,c_2507,c_2508,c_2509,c_2510])).

%------------------------------------------------------------------------------
