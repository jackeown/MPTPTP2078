%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0892+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:56 EST 2020

% Result     : Theorem 30.83s
% Output     : CNFRefutation 30.83s
% Verified   : 
% Statistics : Number of formulae       :   23 (  40 expanded)
%              Number of clauses        :    9 (  11 expanded)
%              Number of leaves         :    4 (  10 expanded)
%              Depth                    :    7
%              Number of atoms          :   58 ( 110 expanded)
%              Number of equality atoms :    2 (   4 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f343,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) )
     => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1531,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ( ~ r1_xboole_0(X2,X3)
        & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f343])).

fof(f4240,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(cnf_transformation,[],[f1531])).

fof(f4239,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1531])).

fof(f1347,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_xboole_0(k3_zfmisc_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))
     => ( ~ r1_xboole_0(X2,X5)
        & ~ r1_xboole_0(X1,X4)
        & ~ r1_xboole_0(X0,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1348,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( ~ r1_xboole_0(k3_zfmisc_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))
       => ( ~ r1_xboole_0(X2,X5)
          & ~ r1_xboole_0(X1,X4)
          & ~ r1_xboole_0(X0,X3) ) ) ),
    inference(negated_conjecture,[],[f1347])).

fof(f2717,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ( r1_xboole_0(X2,X5)
        | r1_xboole_0(X1,X4)
        | r1_xboole_0(X0,X3) )
      & ~ r1_xboole_0(k3_zfmisc_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) ) ),
    inference(ennf_transformation,[],[f1348])).

fof(f3748,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( ( r1_xboole_0(X2,X5)
          | r1_xboole_0(X1,X4)
          | r1_xboole_0(X0,X3) )
        & ~ r1_xboole_0(k3_zfmisc_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) )
   => ( ( r1_xboole_0(sK395,sK398)
        | r1_xboole_0(sK394,sK397)
        | r1_xboole_0(sK393,sK396) )
      & ~ r1_xboole_0(k3_zfmisc_1(sK393,sK394,sK395),k3_zfmisc_1(sK396,sK397,sK398)) ) ),
    introduced(choice_axiom,[])).

fof(f3749,plain,
    ( ( r1_xboole_0(sK395,sK398)
      | r1_xboole_0(sK394,sK397)
      | r1_xboole_0(sK393,sK396) )
    & ~ r1_xboole_0(k3_zfmisc_1(sK393,sK394,sK395),k3_zfmisc_1(sK396,sK397,sK398)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK393,sK394,sK395,sK396,sK397,sK398])],[f2717,f3748])).

fof(f6119,plain,
    ( r1_xboole_0(sK395,sK398)
    | r1_xboole_0(sK394,sK397)
    | r1_xboole_0(sK393,sK396) ),
    inference(cnf_transformation,[],[f3749])).

fof(f6118,plain,(
    ~ r1_xboole_0(k3_zfmisc_1(sK393,sK394,sK395),k3_zfmisc_1(sK396,sK397,sK398)) ),
    inference(cnf_transformation,[],[f3749])).

fof(f1275,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5953,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f1275])).

fof(f6911,plain,(
    ~ r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK393,sK394),sK395),k2_zfmisc_1(k2_zfmisc_1(sK396,sK397),sK398)) ),
    inference(definition_unfolding,[],[f6118,f5953,f5953])).

cnf(c_471,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f4240])).

cnf(c_115260,plain,
    ( r1_xboole_0(k2_zfmisc_1(sK393,sK394),k2_zfmisc_1(sK396,sK397))
    | ~ r1_xboole_0(sK394,sK397) ),
    inference(instantiation,[status(thm)],[c_471])).

cnf(c_472,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f4239])).

cnf(c_115257,plain,
    ( r1_xboole_0(k2_zfmisc_1(sK393,sK394),k2_zfmisc_1(sK396,sK397))
    | ~ r1_xboole_0(sK393,sK396) ),
    inference(instantiation,[status(thm)],[c_472])).

cnf(c_108686,plain,
    ( r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK393,sK394),sK395),k2_zfmisc_1(k2_zfmisc_1(sK396,sK397),sK398))
    | ~ r1_xboole_0(sK395,sK398) ),
    inference(instantiation,[status(thm)],[c_471])).

cnf(c_108683,plain,
    ( r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK393,sK394),sK395),k2_zfmisc_1(k2_zfmisc_1(sK396,sK397),sK398))
    | ~ r1_xboole_0(k2_zfmisc_1(sK393,sK394),k2_zfmisc_1(sK396,sK397)) ),
    inference(instantiation,[status(thm)],[c_472])).

cnf(c_2344,negated_conjecture,
    ( r1_xboole_0(sK393,sK396)
    | r1_xboole_0(sK394,sK397)
    | r1_xboole_0(sK395,sK398) ),
    inference(cnf_transformation,[],[f6119])).

cnf(c_2345,negated_conjecture,
    ( ~ r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK393,sK394),sK395),k2_zfmisc_1(k2_zfmisc_1(sK396,sK397),sK398)) ),
    inference(cnf_transformation,[],[f6911])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_115260,c_115257,c_108686,c_108683,c_2344,c_2345])).

%------------------------------------------------------------------------------
