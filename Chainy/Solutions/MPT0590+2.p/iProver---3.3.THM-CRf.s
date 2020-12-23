%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0590+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:46 EST 2020

% Result     : Theorem 27.45s
% Output     : CNFRefutation 27.45s
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
fof(f325,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1690,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f325])).

fof(f1691,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f1690])).

fof(f2457,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f1691])).

fof(f651,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1951,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f651])).

fof(f1952,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f1951])).

fof(f1955,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK149(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1954,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK148(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1953,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK147(X0,X1)),X0)
          | ~ r2_hidden(sK147(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK147(X0,X1)),X0)
          | r2_hidden(sK147(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1956,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK147(X0,X1)),X0)
            | ~ r2_hidden(sK147(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK148(X0,X1),sK147(X0,X1)),X0)
            | r2_hidden(sK147(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK149(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK147,sK148,sK149])],[f1952,f1955,f1954,f1953])).

fof(f3057,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK149(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1956])).

fof(f4061,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK149(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f3057])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f870,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f1552,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f870])).

fof(f1553,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f1552])).

fof(f1554,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK11(X0,X1),X1)
        & r2_hidden(sK11(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1555,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK11(X0,X1),X1)
          & r2_hidden(sK11(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f1553,f1554])).

fof(f2012,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK11(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f1555])).

fof(f2013,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK11(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f1555])).

fof(f784,conjecture,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f785,negated_conjecture,(
    ~ ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
    inference(negated_conjecture,[],[f784])).

fof(f1450,plain,(
    ? [X0,X1] : ~ r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
    inference(ennf_transformation,[],[f785])).

fof(f1987,plain,
    ( ? [X0,X1] : ~ r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1)
   => ~ r1_tarski(k2_relat_1(k2_zfmisc_1(sK161,sK162)),sK162) ),
    introduced(choice_axiom,[])).

fof(f1988,plain,(
    ~ r1_tarski(k2_relat_1(k2_zfmisc_1(sK161,sK162)),sK162) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK161,sK162])],[f1450,f1987])).

fof(f3216,plain,(
    ~ r1_tarski(k2_relat_1(k2_zfmisc_1(sK161,sK162)),sK162) ),
    inference(cnf_transformation,[],[f1988])).

cnf(c_442,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f2457])).

cnf(c_93290,plain,
    ( ~ r2_hidden(k4_tarski(sK149(k2_zfmisc_1(sK161,sK162),sK11(k2_relat_1(k2_zfmisc_1(sK161,sK162)),sK162)),sK11(k2_relat_1(k2_zfmisc_1(sK161,sK162)),sK162)),k2_zfmisc_1(sK161,sK162))
    | r2_hidden(sK11(k2_relat_1(k2_zfmisc_1(sK161,sK162)),sK162),sK162) ),
    inference(instantiation,[status(thm)],[c_442])).

cnf(c_1043,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(k4_tarski(sK149(X1,X0),X0),X1) ),
    inference(cnf_transformation,[],[f4061])).

cnf(c_72008,plain,
    ( r2_hidden(k4_tarski(sK149(k2_zfmisc_1(sK161,sK162),sK11(k2_relat_1(k2_zfmisc_1(sK161,sK162)),sK162)),sK11(k2_relat_1(k2_zfmisc_1(sK161,sK162)),sK162)),k2_zfmisc_1(sK161,sK162))
    | ~ r2_hidden(sK11(k2_relat_1(k2_zfmisc_1(sK161,sK162)),sK162),k2_relat_1(k2_zfmisc_1(sK161,sK162))) ),
    inference(instantiation,[status(thm)],[c_1043])).

cnf(c_11,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK11(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2012])).

cnf(c_62136,plain,
    ( r1_tarski(k2_relat_1(k2_zfmisc_1(sK161,sK162)),sK162)
    | r2_hidden(sK11(k2_relat_1(k2_zfmisc_1(sK161,sK162)),sK162),k2_relat_1(k2_zfmisc_1(sK161,sK162))) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_10,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK11(X0,X1),X1) ),
    inference(cnf_transformation,[],[f2013])).

cnf(c_62128,plain,
    ( r1_tarski(k2_relat_1(k2_zfmisc_1(sK161,sK162)),sK162)
    | ~ r2_hidden(sK11(k2_relat_1(k2_zfmisc_1(sK161,sK162)),sK162),sK162) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1199,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(k2_zfmisc_1(sK161,sK162)),sK162) ),
    inference(cnf_transformation,[],[f3216])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_93290,c_72008,c_62136,c_62128,c_1199])).

%------------------------------------------------------------------------------
