%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0589+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:46 EST 2020

% Result     : Theorem 42.62s
% Output     : CNFRefutation 42.62s
% Verified   : 
% Statistics : Number of formulae       :   37 (  43 expanded)
%              Number of clauses        :   10 (  10 expanded)
%              Number of leaves         :    9 (  11 expanded)
%              Depth                    :    8
%              Number of atoms          :  124 ( 152 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f869,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f1551,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f869])).

fof(f1552,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f1551])).

fof(f1553,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK11(X0,X1),X1)
        & r2_hidden(sK11(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1554,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK11(X0,X1),X1)
          & r2_hidden(sK11(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f1552,f1553])).

fof(f2012,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK11(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f1554])).

fof(f325,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1689,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f325])).

fof(f1690,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f1689])).

fof(f2455,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f1690])).

fof(f650,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1944,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f650])).

fof(f1945,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f1944])).

fof(f1948,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK146(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1947,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK145(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1946,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK144(X0,X1),X3),X0)
          | ~ r2_hidden(sK144(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK144(X0,X1),X4),X0)
          | r2_hidden(sK144(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1949,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK144(X0,X1),X3),X0)
            | ~ r2_hidden(sK144(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK144(X0,X1),sK145(X0,X1)),X0)
            | r2_hidden(sK144(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK146(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK144,sK145,sK146])],[f1945,f1948,f1947,f1946])).

fof(f3052,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK146(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1949])).

fof(f4057,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK146(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f3052])).

fof(f2011,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK11(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f1554])).

fof(f783,conjecture,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f784,negated_conjecture,(
    ~ ! [X0,X1] : r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) ),
    inference(negated_conjecture,[],[f783])).

fof(f1449,plain,(
    ? [X0,X1] : ~ r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) ),
    inference(ennf_transformation,[],[f784])).

fof(f1986,plain,
    ( ? [X0,X1] : ~ r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0)
   => ~ r1_tarski(k1_relat_1(k2_zfmisc_1(sK161,sK162)),sK161) ),
    introduced(choice_axiom,[])).

fof(f1987,plain,(
    ~ r1_tarski(k1_relat_1(k2_zfmisc_1(sK161,sK162)),sK161) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK161,sK162])],[f1449,f1986])).

fof(f3214,plain,(
    ~ r1_tarski(k1_relat_1(k2_zfmisc_1(sK161,sK162)),sK161) ),
    inference(cnf_transformation,[],[f1987])).

cnf(c_10,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK11(X0,X1),X1) ),
    inference(cnf_transformation,[],[f2012])).

cnf(c_145292,plain,
    ( r1_tarski(k1_relat_1(k2_zfmisc_1(sK161,sK162)),sK161)
    | ~ r2_hidden(sK11(k1_relat_1(k2_zfmisc_1(sK161,sK162)),sK161),sK161) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_443,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f2455])).

cnf(c_89721,plain,
    ( ~ r2_hidden(k4_tarski(sK11(k1_relat_1(k2_zfmisc_1(sK161,sK162)),sK161),sK146(k2_zfmisc_1(sK161,sK162),sK11(k1_relat_1(k2_zfmisc_1(sK161,sK162)),sK161))),k2_zfmisc_1(sK161,sK162))
    | r2_hidden(sK11(k1_relat_1(k2_zfmisc_1(sK161,sK162)),sK161),sK161) ),
    inference(instantiation,[status(thm)],[c_443])).

cnf(c_1039,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,sK146(X1,X0)),X1) ),
    inference(cnf_transformation,[],[f4057])).

cnf(c_69065,plain,
    ( r2_hidden(k4_tarski(sK11(k1_relat_1(k2_zfmisc_1(sK161,sK162)),sK161),sK146(k2_zfmisc_1(sK161,sK162),sK11(k1_relat_1(k2_zfmisc_1(sK161,sK162)),sK161))),k2_zfmisc_1(sK161,sK162))
    | ~ r2_hidden(sK11(k1_relat_1(k2_zfmisc_1(sK161,sK162)),sK161),k1_relat_1(k2_zfmisc_1(sK161,sK162))) ),
    inference(instantiation,[status(thm)],[c_1039])).

cnf(c_11,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK11(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2011])).

cnf(c_56573,plain,
    ( r1_tarski(k1_relat_1(k2_zfmisc_1(sK161,sK162)),sK161)
    | r2_hidden(sK11(k1_relat_1(k2_zfmisc_1(sK161,sK162)),sK161),k1_relat_1(k2_zfmisc_1(sK161,sK162))) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1198,negated_conjecture,
    ( ~ r1_tarski(k1_relat_1(k2_zfmisc_1(sK161,sK162)),sK161) ),
    inference(cnf_transformation,[],[f3214])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_145292,c_89721,c_69065,c_56573,c_1198])).

%------------------------------------------------------------------------------
