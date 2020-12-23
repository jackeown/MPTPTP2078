%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0324+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:35 EST 2020

% Result     : Theorem 11.50s
% Output     : CNFRefutation 11.50s
% Verified   : 
% Statistics : Number of formulae       :   35 (  57 expanded)
%              Number of clauses        :   11 (  11 expanded)
%              Number of leaves         :    6 (  15 expanded)
%              Depth                    :   11
%              Number of atoms          :  130 ( 182 expanded)
%              Number of equality atoms :   19 (  29 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f665,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f666,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f665])).

fof(f667,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f666])).

fof(f668,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK7(X0,X1,X2),X1)
          | ~ r2_hidden(sK7(X0,X1,X2),X0)
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK7(X0,X1,X2),X1)
            & r2_hidden(sK7(X0,X1,X2),X0) )
          | r2_hidden(sK7(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f669,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK7(X0,X1,X2),X1)
            | ~ r2_hidden(sK7(X0,X1,X2),X0)
            | ~ r2_hidden(sK7(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK7(X0,X1,X2),X1)
              & r2_hidden(sK7(X0,X1,X2),X0) )
            | r2_hidden(sK7(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f667,f668])).

fof(f864,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f669])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1000,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f1498,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f864,f1000])).

fof(f1868,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f1498])).

fof(f334,axiom,(
    ! [X0,X1,X2,X3] : k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) = k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1318,plain,(
    ! [X2,X0,X3,X1] : k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) = k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) ),
    inference(cnf_transformation,[],[f334])).

fof(f1767,plain,(
    ! [X2,X0,X3,X1] : k4_xboole_0(k2_zfmisc_1(X0,X2),k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) = k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(definition_unfolding,[],[f1318,f1000,f1000,f1000])).

fof(f348,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( ( r2_hidden(X0,k2_zfmisc_1(X3,X4))
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) )
     => r2_hidden(X0,k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f349,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( ( r2_hidden(X0,k2_zfmisc_1(X3,X4))
          & r2_hidden(X0,k2_zfmisc_1(X1,X2)) )
       => r2_hidden(X0,k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4))) ) ),
    inference(negated_conjecture,[],[f348])).

fof(f593,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4)))
      & r2_hidden(X0,k2_zfmisc_1(X3,X4))
      & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f349])).

fof(f594,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4)))
      & r2_hidden(X0,k2_zfmisc_1(X3,X4))
      & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(flattening,[],[f593])).

fof(f808,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( ~ r2_hidden(X0,k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4)))
        & r2_hidden(X0,k2_zfmisc_1(X3,X4))
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) )
   => ( ~ r2_hidden(sK54,k2_zfmisc_1(k3_xboole_0(sK55,sK57),k3_xboole_0(sK56,sK58)))
      & r2_hidden(sK54,k2_zfmisc_1(sK57,sK58))
      & r2_hidden(sK54,k2_zfmisc_1(sK55,sK56)) ) ),
    introduced(choice_axiom,[])).

fof(f809,plain,
    ( ~ r2_hidden(sK54,k2_zfmisc_1(k3_xboole_0(sK55,sK57),k3_xboole_0(sK56,sK58)))
    & r2_hidden(sK54,k2_zfmisc_1(sK57,sK58))
    & r2_hidden(sK54,k2_zfmisc_1(sK55,sK56)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK54,sK55,sK56,sK57,sK58])],[f594,f808])).

fof(f1347,plain,(
    ~ r2_hidden(sK54,k2_zfmisc_1(k3_xboole_0(sK55,sK57),k3_xboole_0(sK56,sK58))) ),
    inference(cnf_transformation,[],[f809])).

fof(f1779,plain,(
    ~ r2_hidden(sK54,k2_zfmisc_1(k4_xboole_0(sK55,k4_xboole_0(sK55,sK57)),k4_xboole_0(sK56,k4_xboole_0(sK56,sK58)))) ),
    inference(definition_unfolding,[],[f1347,f1000,f1000])).

fof(f1346,plain,(
    r2_hidden(sK54,k2_zfmisc_1(sK57,sK58)) ),
    inference(cnf_transformation,[],[f809])).

fof(f1345,plain,(
    r2_hidden(sK54,k2_zfmisc_1(sK55,sK56)) ),
    inference(cnf_transformation,[],[f809])).

cnf(c_22,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f1868])).

cnf(c_23158,plain,
    ( ~ r2_hidden(sK54,X0)
    | ~ r2_hidden(sK54,k2_zfmisc_1(sK57,sK58))
    | r2_hidden(sK54,k4_xboole_0(X0,k4_xboole_0(X0,k2_zfmisc_1(sK57,sK58)))) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_27910,plain,
    ( ~ r2_hidden(sK54,k2_zfmisc_1(sK57,sK58))
    | ~ r2_hidden(sK54,k2_zfmisc_1(sK55,sK56))
    | r2_hidden(sK54,k4_xboole_0(k2_zfmisc_1(sK55,sK56),k4_xboole_0(k2_zfmisc_1(sK55,sK56),k2_zfmisc_1(sK57,sK58)))) ),
    inference(instantiation,[status(thm)],[c_23158])).

cnf(c_461,plain,
    ( k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k4_xboole_0(k2_zfmisc_1(X0,X2),k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) ),
    inference(cnf_transformation,[],[f1767])).

cnf(c_488,negated_conjecture,
    ( ~ r2_hidden(sK54,k2_zfmisc_1(k4_xboole_0(sK55,k4_xboole_0(sK55,sK57)),k4_xboole_0(sK56,k4_xboole_0(sK56,sK58)))) ),
    inference(cnf_transformation,[],[f1779])).

cnf(c_17863,plain,
    ( r2_hidden(sK54,k2_zfmisc_1(k4_xboole_0(sK55,k4_xboole_0(sK55,sK57)),k4_xboole_0(sK56,k4_xboole_0(sK56,sK58)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_488])).

cnf(c_19213,plain,
    ( r2_hidden(sK54,k4_xboole_0(k2_zfmisc_1(sK55,sK56),k4_xboole_0(k2_zfmisc_1(sK55,sK56),k2_zfmisc_1(sK57,sK58)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_461,c_17863])).

cnf(c_21024,plain,
    ( ~ r2_hidden(sK54,k4_xboole_0(k2_zfmisc_1(sK55,sK56),k4_xboole_0(k2_zfmisc_1(sK55,sK56),k2_zfmisc_1(sK57,sK58)))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_19213])).

cnf(c_489,negated_conjecture,
    ( r2_hidden(sK54,k2_zfmisc_1(sK57,sK58)) ),
    inference(cnf_transformation,[],[f1346])).

cnf(c_490,negated_conjecture,
    ( r2_hidden(sK54,k2_zfmisc_1(sK55,sK56)) ),
    inference(cnf_transformation,[],[f1345])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_27910,c_21024,c_489,c_490])).

%------------------------------------------------------------------------------
