%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0825+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:54 EST 2020

% Result     : Theorem 35.50s
% Output     : CNFRefutation 35.50s
% Verified   : 
% Statistics : Number of formulae       :   35 (  40 expanded)
%              Number of clauses        :   10 (  10 expanded)
%              Number of leaves         :    9 (  11 expanded)
%              Depth                    :    9
%              Number of atoms          :  155 ( 175 expanded)
%              Number of equality atoms :   31 (  31 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f286,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2641,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4,X5] :
                  ( k4_tarski(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) ) )
            & ( ? [X4,X5] :
                  ( k4_tarski(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f286])).

fof(f2642,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X6,X7] :
                  ( k4_tarski(X6,X7) = X3
                  & r2_hidden(X7,X1)
                  & r2_hidden(X6,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ? [X11,X12] :
                  ( k4_tarski(X11,X12) = X8
                  & r2_hidden(X12,X1)
                  & r2_hidden(X11,X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f2641])).

fof(f2645,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK47(X0,X1,X8),sK48(X0,X1,X8)) = X8
        & r2_hidden(sK48(X0,X1,X8),X1)
        & r2_hidden(sK47(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f2644,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6,X7] :
          ( k4_tarski(X6,X7) = X3
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( k4_tarski(sK45(X0,X1,X2),sK46(X0,X1,X2)) = X3
        & r2_hidden(sK46(X0,X1,X2),X1)
        & r2_hidden(sK45(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f2643,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != X3
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X6,X7] :
                ( k4_tarski(X6,X7) = X3
                & r2_hidden(X7,X1)
                & r2_hidden(X6,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X5,X4] :
              ( k4_tarski(X4,X5) != sK44(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK44(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK44(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK44(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f2646,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK44(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK44(X0,X1,X2),X2) )
          & ( ( k4_tarski(sK45(X0,X1,X2),sK46(X0,X1,X2)) = sK44(X0,X1,X2)
              & r2_hidden(sK46(X0,X1,X2),X1)
              & r2_hidden(sK45(X0,X1,X2),X0) )
            | r2_hidden(sK44(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k4_tarski(sK47(X0,X1,X8),sK48(X0,X1,X8)) = X8
                & r2_hidden(sK48(X0,X1,X8),X1)
                & r2_hidden(sK47(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK44,sK45,sK46,sK47,sK48])],[f2642,f2645,f2644,f2643])).

fof(f3761,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( r2_hidden(X8,X2)
      | k4_tarski(X9,X10) != X8
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2646])).

fof(f6255,plain,(
    ! [X2,X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),X2)
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f3761])).

fof(f6256,plain,(
    ! [X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0) ) ),
    inference(equality_resolution,[],[f6255])).

fof(f696,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4502,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f696])).

fof(f865,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( ! [X2] :
            ( r2_hidden(X2,X0)
           => r2_hidden(k4_tarski(X2,X2),X1) )
       => r1_tarski(k6_relat_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1955,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_relat_1(X0),X1)
      | ? [X2] :
          ( ~ r2_hidden(k4_tarski(X2,X2),X1)
          & r2_hidden(X2,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f865])).

fof(f1956,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_relat_1(X0),X1)
      | ? [X2] :
          ( ~ r2_hidden(k4_tarski(X2,X2),X1)
          & r2_hidden(X2,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1955])).

fof(f3000,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k4_tarski(X2,X2),X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(k4_tarski(sK179(X0,X1),sK179(X0,X1)),X1)
        & r2_hidden(sK179(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f3001,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_relat_1(X0),X1)
      | ( ~ r2_hidden(k4_tarski(sK179(X0,X1),sK179(X0,X1)),X1)
        & r2_hidden(sK179(X0,X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK179])],[f1956,f3000])).

fof(f4705,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_relat_1(X0),X1)
      | ~ r2_hidden(k4_tarski(sK179(X0,X1),sK179(X0,X1)),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f3001])).

fof(f4704,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_relat_1(X0),X1)
      | r2_hidden(sK179(X0,X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f3001])).

fof(f1234,conjecture,(
    ! [X0] : r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X0,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1235,negated_conjecture,(
    ~ ! [X0] : r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X0,X0)) ),
    inference(negated_conjecture,[],[f1234])).

fof(f2502,plain,(
    ? [X0] : ~ r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X0,X0)) ),
    inference(ennf_transformation,[],[f1235])).

fof(f3380,plain,
    ( ? [X0] : ~ r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X0,X0))
   => ~ r1_tarski(k6_relat_1(sK324),k2_zfmisc_1(sK324,sK324)) ),
    introduced(choice_axiom,[])).

fof(f3381,plain,(
    ~ r1_tarski(k6_relat_1(sK324),k2_zfmisc_1(sK324,sK324)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK324])],[f2502,f3380])).

fof(f5507,plain,(
    ~ r1_tarski(k6_relat_1(sK324),k2_zfmisc_1(sK324,sK324)) ),
    inference(cnf_transformation,[],[f3381])).

cnf(c_366,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f6256])).

cnf(c_120212,plain,
    ( ~ r2_hidden(sK179(sK324,k2_zfmisc_1(sK324,sK324)),sK324)
    | r2_hidden(k4_tarski(sK179(sK324,k2_zfmisc_1(sK324,sK324)),sK179(sK324,k2_zfmisc_1(sK324,sK324))),k2_zfmisc_1(sK324,sK324)) ),
    inference(instantiation,[status(thm)],[c_366])).

cnf(c_1104,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4502])).

cnf(c_102046,plain,
    ( v1_relat_1(k2_zfmisc_1(sK324,sK324)) ),
    inference(instantiation,[status(thm)],[c_1104])).

cnf(c_1306,plain,
    ( r1_tarski(k6_relat_1(X0),X1)
    | ~ r2_hidden(k4_tarski(sK179(X0,X1),sK179(X0,X1)),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f4705])).

cnf(c_100368,plain,
    ( r1_tarski(k6_relat_1(sK324),k2_zfmisc_1(sK324,sK324))
    | ~ r2_hidden(k4_tarski(sK179(sK324,k2_zfmisc_1(sK324,sK324)),sK179(sK324,k2_zfmisc_1(sK324,sK324))),k2_zfmisc_1(sK324,sK324))
    | ~ v1_relat_1(k2_zfmisc_1(sK324,sK324)) ),
    inference(instantiation,[status(thm)],[c_1306])).

cnf(c_1307,plain,
    ( r1_tarski(k6_relat_1(X0),X1)
    | r2_hidden(sK179(X0,X1),X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f4704])).

cnf(c_100369,plain,
    ( r1_tarski(k6_relat_1(sK324),k2_zfmisc_1(sK324,sK324))
    | r2_hidden(sK179(sK324,k2_zfmisc_1(sK324,sK324)),sK324)
    | ~ v1_relat_1(k2_zfmisc_1(sK324,sK324)) ),
    inference(instantiation,[status(thm)],[c_1307])).

cnf(c_2108,negated_conjecture,
    ( ~ r1_tarski(k6_relat_1(sK324),k2_zfmisc_1(sK324,sK324)) ),
    inference(cnf_transformation,[],[f5507])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_120212,c_102046,c_100368,c_100369,c_2108])).

%------------------------------------------------------------------------------
