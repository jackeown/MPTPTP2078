%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0319+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:35 EST 2020

% Result     : Theorem 11.27s
% Output     : CNFRefutation 11.27s
% Verified   : 
% Statistics : Number of formulae       :   29 (  40 expanded)
%              Number of clauses        :   12 (  13 expanded)
%              Number of leaves         :    5 (   9 expanded)
%              Depth                    :    6
%              Number of atoms          :   65 (  97 expanded)
%              Number of equality atoms :   13 (  19 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f28,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f435,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f854,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f435])).

fof(f337,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) )
     => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f574,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ( ~ r1_xboole_0(X2,X3)
        & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f337])).

fof(f1285,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(cnf_transformation,[],[f574])).

fof(f347,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f579,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f347])).

fof(f1300,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f579])).

fof(f1284,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f574])).

fof(f342,conjecture,(
    ! [X0,X1,X2,X3] :
      ( X0 != X1
     => ( r1_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X3,k1_tarski(X1)))
        & r1_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f343,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( X0 != X1
       => ( r1_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X3,k1_tarski(X1)))
          & r1_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X3)) ) ) ),
    inference(negated_conjecture,[],[f342])).

fof(f576,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X3,k1_tarski(X1)))
        | ~ r1_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X3)) )
      & X0 != X1 ) ),
    inference(ennf_transformation,[],[f343])).

fof(f778,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ r1_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X3,k1_tarski(X1)))
          | ~ r1_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X3)) )
        & X0 != X1 )
   => ( ( ~ r1_xboole_0(k2_zfmisc_1(sK52,k1_tarski(sK50)),k2_zfmisc_1(sK53,k1_tarski(sK51)))
        | ~ r1_xboole_0(k2_zfmisc_1(k1_tarski(sK50),sK52),k2_zfmisc_1(k1_tarski(sK51),sK53)) )
      & sK50 != sK51 ) ),
    introduced(choice_axiom,[])).

fof(f779,plain,
    ( ( ~ r1_xboole_0(k2_zfmisc_1(sK52,k1_tarski(sK50)),k2_zfmisc_1(sK53,k1_tarski(sK51)))
      | ~ r1_xboole_0(k2_zfmisc_1(k1_tarski(sK50),sK52),k2_zfmisc_1(k1_tarski(sK51),sK53)) )
    & sK50 != sK51 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK50,sK51,sK52,sK53])],[f576,f778])).

fof(f1296,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1(sK52,k1_tarski(sK50)),k2_zfmisc_1(sK53,k1_tarski(sK51)))
    | ~ r1_xboole_0(k2_zfmisc_1(k1_tarski(sK50),sK52),k2_zfmisc_1(k1_tarski(sK51),sK53)) ),
    inference(cnf_transformation,[],[f779])).

fof(f1295,plain,(
    sK50 != sK51 ),
    inference(cnf_transformation,[],[f779])).

cnf(c_44,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f854])).

cnf(c_21890,plain,
    ( ~ r1_xboole_0(k1_tarski(sK51),k1_tarski(sK50))
    | r1_xboole_0(k1_tarski(sK50),k1_tarski(sK51)) ),
    inference(instantiation,[status(thm)],[c_44])).

cnf(c_461,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f1285])).

cnf(c_21770,plain,
    ( r1_xboole_0(k2_zfmisc_1(sK53,k1_tarski(sK51)),k2_zfmisc_1(sK52,k1_tarski(sK50)))
    | ~ r1_xboole_0(k1_tarski(sK51),k1_tarski(sK50)) ),
    inference(instantiation,[status(thm)],[c_461])).

cnf(c_18259,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1(sK53,k1_tarski(sK51)),k2_zfmisc_1(sK52,k1_tarski(sK50)))
    | r1_xboole_0(k2_zfmisc_1(sK52,k1_tarski(sK50)),k2_zfmisc_1(sK53,k1_tarski(sK51))) ),
    inference(instantiation,[status(thm)],[c_44])).

cnf(c_477,plain,
    ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
    | X1 = X0 ),
    inference(cnf_transformation,[],[f1300])).

cnf(c_18044,plain,
    ( r1_xboole_0(k1_tarski(sK51),k1_tarski(sK50))
    | sK50 = sK51 ),
    inference(instantiation,[status(thm)],[c_477])).

cnf(c_462,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f1284])).

cnf(c_17978,plain,
    ( r1_xboole_0(k2_zfmisc_1(k1_tarski(sK50),sK52),k2_zfmisc_1(k1_tarski(sK51),sK53))
    | ~ r1_xboole_0(k1_tarski(sK50),k1_tarski(sK51)) ),
    inference(instantiation,[status(thm)],[c_462])).

cnf(c_472,negated_conjecture,
    ( ~ r1_xboole_0(k2_zfmisc_1(k1_tarski(sK50),sK52),k2_zfmisc_1(k1_tarski(sK51),sK53))
    | ~ r1_xboole_0(k2_zfmisc_1(sK52,k1_tarski(sK50)),k2_zfmisc_1(sK53,k1_tarski(sK51))) ),
    inference(cnf_transformation,[],[f1296])).

cnf(c_473,negated_conjecture,
    ( sK50 != sK51 ),
    inference(cnf_transformation,[],[f1295])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_21890,c_21770,c_18259,c_18044,c_17978,c_472,c_473])).

%------------------------------------------------------------------------------
