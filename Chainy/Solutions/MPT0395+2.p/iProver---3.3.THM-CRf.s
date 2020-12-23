%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0395+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:38 EST 2020

% Result     : Theorem 23.55s
% Output     : CNFRefutation 23.55s
% Verified   : 
% Statistics : Number of formulae       :   42 (  61 expanded)
%              Number of clauses        :   14 (  15 expanded)
%              Number of leaves         :    8 (  15 expanded)
%              Depth                    :    9
%              Number of atoms          :  139 ( 207 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1003,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f1004,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f1003])).

fof(f1329,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1004])).

fof(f2640,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f1329])).

fof(f545,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f921,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ( ? [X3] :
              ( r1_tarski(X2,X3)
              & r2_hidden(X3,X1) )
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f545])).

fof(f1248,plain,(
    ! [X0,X1] :
      ( ( r1_setfam_1(X0,X1)
        | ? [X2] :
            ( ! [X3] :
                ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( ? [X3] :
                ( r1_tarski(X2,X3)
                & r2_hidden(X3,X1) )
            | ~ r2_hidden(X2,X0) )
        | ~ r1_setfam_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f921])).

fof(f1249,plain,(
    ! [X0,X1] :
      ( ( r1_setfam_1(X0,X1)
        | ? [X2] :
            ( ! [X3] :
                ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) )
      & ( ! [X4] :
            ( ? [X5] :
                ( r1_tarski(X4,X5)
                & r2_hidden(X5,X1) )
            | ~ r2_hidden(X4,X0) )
        | ~ r1_setfam_1(X0,X1) ) ) ),
    inference(rectify,[],[f1248])).

fof(f1251,plain,(
    ! [X4,X1] :
      ( ? [X5] :
          ( r1_tarski(X4,X5)
          & r2_hidden(X5,X1) )
     => ( r1_tarski(X4,sK95(X1,X4))
        & r2_hidden(sK95(X1,X4),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f1250,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r1_tarski(X2,X3)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X0) )
     => ( ! [X3] :
            ( ~ r1_tarski(sK94(X0,X1),X3)
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK94(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1252,plain,(
    ! [X0,X1] :
      ( ( r1_setfam_1(X0,X1)
        | ( ! [X3] :
              ( ~ r1_tarski(sK94(X0,X1),X3)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(sK94(X0,X1),X0) ) )
      & ( ! [X4] :
            ( ( r1_tarski(X4,sK95(X1,X4))
              & r2_hidden(sK95(X1,X4),X1) )
            | ~ r2_hidden(X4,X0) )
        | ~ r1_setfam_1(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK94,sK95])],[f1249,f1251,f1250])).

fof(f2132,plain,(
    ! [X0,X3,X1] :
      ( r1_setfam_1(X0,X1)
      | ~ r1_tarski(sK94(X0,X1),X3)
      | ~ r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f1252])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f586,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f962,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f586])).

fof(f963,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f962])).

fof(f964,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK11(X0,X1),X1)
        & r2_hidden(sK11(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f965,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK11(X0,X1),X1)
          & r2_hidden(sK11(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f963,f964])).

fof(f1270,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f965])).

fof(f2131,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
      | r2_hidden(sK94(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f1252])).

fof(f554,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_setfam_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f555,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,X1)
       => r1_setfam_1(X0,X1) ) ),
    inference(negated_conjecture,[],[f554])).

fof(f924,plain,(
    ? [X0,X1] :
      ( ~ r1_setfam_1(X0,X1)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f555])).

fof(f1257,plain,
    ( ? [X0,X1] :
        ( ~ r1_setfam_1(X0,X1)
        & r1_tarski(X0,X1) )
   => ( ~ r1_setfam_1(sK98,sK99)
      & r1_tarski(sK98,sK99) ) ),
    introduced(choice_axiom,[])).

fof(f1258,plain,
    ( ~ r1_setfam_1(sK98,sK99)
    & r1_tarski(sK98,sK99) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK98,sK99])],[f924,f1257])).

fof(f2143,plain,(
    ~ r1_setfam_1(sK98,sK99) ),
    inference(cnf_transformation,[],[f1258])).

fof(f2142,plain,(
    r1_tarski(sK98,sK99) ),
    inference(cnf_transformation,[],[f1258])).

cnf(c_68,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f2640])).

cnf(c_96657,plain,
    ( r1_tarski(sK94(sK98,sK99),sK94(sK98,sK99)) ),
    inference(instantiation,[status(thm)],[c_68])).

cnf(c_853,plain,
    ( r1_setfam_1(X0,X1)
    | ~ r1_tarski(sK94(X0,X1),X2)
    | ~ r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f2132])).

cnf(c_40761,plain,
    ( r1_setfam_1(sK98,sK99)
    | ~ r1_tarski(sK94(sK98,sK99),X0)
    | ~ r2_hidden(X0,sK99) ),
    inference(instantiation,[status(thm)],[c_853])).

cnf(c_79736,plain,
    ( r1_setfam_1(sK98,sK99)
    | ~ r1_tarski(sK94(sK98,sK99),sK94(sK98,sK99))
    | ~ r2_hidden(sK94(sK98,sK99),sK99) ),
    inference(instantiation,[status(thm)],[c_40761])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f1270])).

cnf(c_48592,plain,
    ( ~ r1_tarski(sK98,X0)
    | r2_hidden(sK94(sK98,sK99),X0)
    | ~ r2_hidden(sK94(sK98,sK99),sK98) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_67083,plain,
    ( ~ r1_tarski(sK98,sK99)
    | r2_hidden(sK94(sK98,sK99),sK99)
    | ~ r2_hidden(sK94(sK98,sK99),sK98) ),
    inference(instantiation,[status(thm)],[c_48592])).

cnf(c_854,plain,
    ( r1_setfam_1(X0,X1)
    | r2_hidden(sK94(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2131])).

cnf(c_866,negated_conjecture,
    ( ~ r1_setfam_1(sK98,sK99) ),
    inference(cnf_transformation,[],[f2143])).

cnf(c_8503,plain,
    ( r2_hidden(sK94(X0,X1),X0)
    | sK99 != X1
    | sK98 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_854,c_866])).

cnf(c_8504,plain,
    ( r2_hidden(sK94(sK98,sK99),sK98) ),
    inference(unflattening,[status(thm)],[c_8503])).

cnf(c_867,negated_conjecture,
    ( r1_tarski(sK98,sK99) ),
    inference(cnf_transformation,[],[f2142])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_96657,c_79736,c_67083,c_8504,c_866,c_867])).

%------------------------------------------------------------------------------
