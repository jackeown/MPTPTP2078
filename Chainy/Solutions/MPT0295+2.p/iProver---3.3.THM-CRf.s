%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0295+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:34 EST 2020

% Result     : Theorem 19.61s
% Output     : CNFRefutation 19.61s
% Verified   : 
% Statistics : Number of formulae       :   43 (  67 expanded)
%              Number of clauses        :   15 (  15 expanded)
%              Number of leaves         :    8 (  20 expanded)
%              Depth                    :    9
%              Number of atoms          :  201 ( 435 expanded)
%              Number of equality atoms :   45 ( 113 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f313,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( ! [X4,X5] :
            ~ ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X2)
              & r2_hidden(X4,X1) )
        & r2_hidden(X3,X0)
        & r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f314,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( ! [X4,X5] :
              ~ ( k4_tarski(X4,X5) = X3
                & r2_hidden(X5,X2)
                & r2_hidden(X4,X1) )
          & r2_hidden(X3,X0)
          & r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(negated_conjecture,[],[f313])).

fof(f525,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4,X5] :
          ( k4_tarski(X4,X5) != X3
          | ~ r2_hidden(X5,X2)
          | ~ r2_hidden(X4,X1) )
      & r2_hidden(X3,X0)
      & r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f314])).

fof(f702,plain,
    ( ? [X0,X1,X2,X3] :
        ( ! [X4,X5] :
            ( k4_tarski(X4,X5) != X3
            | ~ r2_hidden(X5,X2)
            | ~ r2_hidden(X4,X1) )
        & r2_hidden(X3,X0)
        & r1_tarski(X0,k2_zfmisc_1(X1,X2)) )
   => ( ! [X5,X4] :
          ( k4_tarski(X4,X5) != sK39
          | ~ r2_hidden(X5,sK38)
          | ~ r2_hidden(X4,sK37) )
      & r2_hidden(sK39,sK36)
      & r1_tarski(sK36,k2_zfmisc_1(sK37,sK38)) ) ),
    introduced(choice_axiom,[])).

fof(f703,plain,
    ( ! [X4,X5] :
        ( k4_tarski(X4,X5) != sK39
        | ~ r2_hidden(X5,sK38)
        | ~ r2_hidden(X4,sK37) )
    & r2_hidden(sK39,sK36)
    & r1_tarski(sK36,k2_zfmisc_1(sK37,sK38)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK36,sK37,sK38,sK39])],[f525,f702])).

fof(f1162,plain,(
    ! [X4,X5] :
      ( k4_tarski(X4,X5) != sK39
      | ~ r2_hidden(X5,sK38)
      | ~ r2_hidden(X4,sK37) ) ),
    inference(cnf_transformation,[],[f703])).

fof(f285,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f675,plain,(
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
    inference(nnf_transformation,[],[f285])).

fof(f676,plain,(
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
    inference(rectify,[],[f675])).

fof(f679,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK28(X0,X1,X8),sK29(X0,X1,X8)) = X8
        & r2_hidden(sK29(X0,X1,X8),X1)
        & r2_hidden(sK28(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f678,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6,X7] :
          ( k4_tarski(X6,X7) = X3
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( k4_tarski(sK26(X0,X1,X2),sK27(X0,X1,X2)) = X3
        & r2_hidden(sK27(X0,X1,X2),X1)
        & r2_hidden(sK26(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f677,plain,(
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
              ( k4_tarski(X4,X5) != sK25(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK25(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK25(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK25(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f680,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK25(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK25(X0,X1,X2),X2) )
          & ( ( k4_tarski(sK26(X0,X1,X2),sK27(X0,X1,X2)) = sK25(X0,X1,X2)
              & r2_hidden(sK27(X0,X1,X2),X1)
              & r2_hidden(sK26(X0,X1,X2),X0) )
            | r2_hidden(sK25(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k4_tarski(sK28(X0,X1,X8),sK29(X0,X1,X8)) = X8
                & r2_hidden(sK29(X0,X1,X8),X1)
                & r2_hidden(sK28(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK25,sK26,sK27,sK28,sK29])],[f676,f679,f678,f677])).

fof(f1108,plain,(
    ! [X2,X0,X8,X1] :
      ( k4_tarski(sK28(X0,X1,X8),sK29(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f680])).

fof(f1702,plain,(
    ! [X0,X8,X1] :
      ( k4_tarski(sK28(X0,X1,X8),sK29(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f1108])).

fof(f1106,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK28(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f680])).

fof(f1704,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK28(X0,X1,X8),X0)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f1106])).

fof(f1107,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK29(X0,X1,X8),X1)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f680])).

fof(f1703,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK29(X0,X1,X8),X1)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f1107])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f404,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f585,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f404])).

fof(f586,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f585])).

fof(f587,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f588,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f586,f587])).

fof(f741,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f588])).

fof(f1161,plain,(
    r2_hidden(sK39,sK36) ),
    inference(cnf_transformation,[],[f703])).

fof(f1160,plain,(
    r1_tarski(sK36,k2_zfmisc_1(sK37,sK38)) ),
    inference(cnf_transformation,[],[f703])).

cnf(c_415,negated_conjecture,
    ( ~ r2_hidden(X0,sK37)
    | ~ r2_hidden(X1,sK38)
    | k4_tarski(X0,X1) != sK39 ),
    inference(cnf_transformation,[],[f1162])).

cnf(c_47576,plain,
    ( ~ r2_hidden(X0,sK38)
    | ~ r2_hidden(sK28(sK37,sK38,sK39),sK37)
    | k4_tarski(sK28(sK37,sK38,sK39),X0) != sK39 ),
    inference(instantiation,[status(thm)],[c_415])).

cnf(c_78734,plain,
    ( ~ r2_hidden(sK29(sK37,sK38,sK39),sK38)
    | ~ r2_hidden(sK28(sK37,sK38,sK39),sK37)
    | k4_tarski(sK28(sK37,sK38,sK39),sK29(sK37,sK38,sK39)) != sK39 ),
    inference(instantiation,[status(thm)],[c_47576])).

cnf(c_366,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | k4_tarski(sK28(X1,X2,X0),sK29(X1,X2,X0)) = X0 ),
    inference(cnf_transformation,[],[f1702])).

cnf(c_28859,plain,
    ( ~ r2_hidden(sK39,k2_zfmisc_1(sK37,sK38))
    | k4_tarski(sK28(sK37,sK38,sK39),sK29(sK37,sK38,sK39)) = sK39 ),
    inference(instantiation,[status(thm)],[c_366])).

cnf(c_368,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK28(X1,X2,X0),X1) ),
    inference(cnf_transformation,[],[f1704])).

cnf(c_28860,plain,
    ( r2_hidden(sK28(sK37,sK38,sK39),sK37)
    | ~ r2_hidden(sK39,k2_zfmisc_1(sK37,sK38)) ),
    inference(instantiation,[status(thm)],[c_368])).

cnf(c_367,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK29(X1,X2,X0),X2) ),
    inference(cnf_transformation,[],[f1703])).

cnf(c_28861,plain,
    ( r2_hidden(sK29(sK37,sK38,sK39),sK38)
    | ~ r2_hidden(sK39,k2_zfmisc_1(sK37,sK38)) ),
    inference(instantiation,[status(thm)],[c_367])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f741])).

cnf(c_19152,plain,
    ( ~ r1_tarski(sK36,X0)
    | r2_hidden(sK39,X0)
    | ~ r2_hidden(sK39,sK36) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_22569,plain,
    ( ~ r1_tarski(sK36,k2_zfmisc_1(sK37,sK38))
    | r2_hidden(sK39,k2_zfmisc_1(sK37,sK38))
    | ~ r2_hidden(sK39,sK36) ),
    inference(instantiation,[status(thm)],[c_19152])).

cnf(c_416,negated_conjecture,
    ( r2_hidden(sK39,sK36) ),
    inference(cnf_transformation,[],[f1161])).

cnf(c_417,negated_conjecture,
    ( r1_tarski(sK36,k2_zfmisc_1(sK37,sK38)) ),
    inference(cnf_transformation,[],[f1160])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_78734,c_28859,c_28860,c_28861,c_22569,c_416,c_417])).

%------------------------------------------------------------------------------
