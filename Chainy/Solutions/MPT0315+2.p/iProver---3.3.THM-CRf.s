%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0315+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:34 EST 2020

% Result     : Theorem 14.42s
% Output     : CNFRefutation 14.42s
% Verified   : 
% Statistics : Number of formulae       :   38 (  72 expanded)
%              Number of clauses        :   12 (  13 expanded)
%              Number of leaves         :    7 (  21 expanded)
%              Depth                    :    8
%              Number of atoms          :   97 ( 187 expanded)
%              Number of equality atoms :    7 (  24 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f33,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f424,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f33])).

fof(f436,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f424])).

fof(f665,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK14(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f666,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK14(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f436,f665])).

fof(f859,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f666])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f956,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f1432,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f859,f956])).

fof(f317,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ~ ( ! [X5,X6] :
            ~ ( r2_hidden(X6,k3_xboole_0(X2,X4))
              & r2_hidden(X5,k3_xboole_0(X1,X3))
              & k4_tarski(X5,X6) = X0 )
        & r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f556,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ? [X5,X6] :
          ( r2_hidden(X6,k3_xboole_0(X2,X4))
          & r2_hidden(X5,k3_xboole_0(X1,X3))
          & k4_tarski(X5,X6) = X0 )
      | ~ r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) ) ),
    inference(ennf_transformation,[],[f317])).

fof(f759,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5,X6] :
          ( r2_hidden(X6,k3_xboole_0(X2,X4))
          & r2_hidden(X5,k3_xboole_0(X1,X3))
          & k4_tarski(X5,X6) = X0 )
     => ( r2_hidden(sK47(X0,X1,X2,X3,X4),k3_xboole_0(X2,X4))
        & r2_hidden(sK46(X0,X1,X2,X3,X4),k3_xboole_0(X1,X3))
        & k4_tarski(sK46(X0,X1,X2,X3,X4),sK47(X0,X1,X2,X3,X4)) = X0 ) ) ),
    introduced(choice_axiom,[])).

fof(f760,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( r2_hidden(sK47(X0,X1,X2,X3,X4),k3_xboole_0(X2,X4))
        & r2_hidden(sK46(X0,X1,X2,X3,X4),k3_xboole_0(X1,X3))
        & k4_tarski(sK46(X0,X1,X2,X3,X4),sK47(X0,X1,X2,X3,X4)) = X0 )
      | ~ r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK46,sK47])],[f556,f759])).

fof(f1243,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(sK46(X0,X1,X2,X3,X4),k3_xboole_0(X1,X3))
      | ~ r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) ) ),
    inference(cnf_transformation,[],[f760])).

fof(f1676,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(sK46(X0,X1,X2,X3,X4),k4_xboole_0(X1,k4_xboole_0(X1,X3)))
      | ~ r2_hidden(X0,k4_xboole_0(k2_zfmisc_1(X1,X2),k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)))) ) ),
    inference(definition_unfolding,[],[f1243,f956,f956])).

fof(f1244,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(sK47(X0,X1,X2,X3,X4),k3_xboole_0(X2,X4))
      | ~ r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) ) ),
    inference(cnf_transformation,[],[f760])).

fof(f1675,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(sK47(X0,X1,X2,X3,X4),k4_xboole_0(X2,k4_xboole_0(X2,X4)))
      | ~ r2_hidden(X0,k4_xboole_0(k2_zfmisc_1(X1,X2),k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)))) ) ),
    inference(definition_unfolding,[],[f1244,f956,f956])).

fof(f858,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK14(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f666])).

fof(f1433,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK14(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f858,f956])).

fof(f337,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) )
     => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f338,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X3)
          | r1_xboole_0(X0,X1) )
       => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    inference(negated_conjecture,[],[f337])).

fof(f570,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      & ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f338])).

fof(f768,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
        & ( r1_xboole_0(X2,X3)
          | r1_xboole_0(X0,X1) ) )
   => ( ~ r1_xboole_0(k2_zfmisc_1(sK50,sK52),k2_zfmisc_1(sK51,sK53))
      & ( r1_xboole_0(sK52,sK53)
        | r1_xboole_0(sK50,sK51) ) ) ),
    introduced(choice_axiom,[])).

fof(f769,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1(sK50,sK52),k2_zfmisc_1(sK51,sK53))
    & ( r1_xboole_0(sK52,sK53)
      | r1_xboole_0(sK50,sK51) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK50,sK51,sK52,sK53])],[f570,f768])).

fof(f1275,plain,(
    ~ r1_xboole_0(k2_zfmisc_1(sK50,sK52),k2_zfmisc_1(sK51,sK53)) ),
    inference(cnf_transformation,[],[f769])).

fof(f1274,plain,
    ( r1_xboole_0(sK52,sK53)
    | r1_xboole_0(sK50,sK51) ),
    inference(cnf_transformation,[],[f769])).

cnf(c_58,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f1432])).

cnf(c_41123,plain,
    ( ~ r1_xboole_0(sK52,sK53)
    | ~ r2_hidden(sK47(sK14(k2_zfmisc_1(sK50,sK52),k2_zfmisc_1(sK51,sK53)),sK50,sK52,sK51,sK53),k4_xboole_0(sK52,k4_xboole_0(sK52,sK53))) ),
    inference(instantiation,[status(thm)],[c_58])).

cnf(c_40951,plain,
    ( ~ r1_xboole_0(sK50,sK51)
    | ~ r2_hidden(sK46(sK14(k2_zfmisc_1(sK50,sK52),k2_zfmisc_1(sK51,sK53)),sK50,sK52,sK51,sK53),k4_xboole_0(sK50,k4_xboole_0(sK50,sK51))) ),
    inference(instantiation,[status(thm)],[c_58])).

cnf(c_430,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(k2_zfmisc_1(X1,X2),k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))))
    | r2_hidden(sK46(X0,X1,X2,X3,X4),k4_xboole_0(X1,k4_xboole_0(X1,X3))) ),
    inference(cnf_transformation,[],[f1676])).

cnf(c_25072,plain,
    ( r2_hidden(sK46(sK14(k2_zfmisc_1(sK50,sK52),k2_zfmisc_1(sK51,sK53)),sK50,sK52,sK51,sK53),k4_xboole_0(sK50,k4_xboole_0(sK50,sK51)))
    | ~ r2_hidden(sK14(k2_zfmisc_1(sK50,sK52),k2_zfmisc_1(sK51,sK53)),k4_xboole_0(k2_zfmisc_1(sK50,sK52),k4_xboole_0(k2_zfmisc_1(sK50,sK52),k2_zfmisc_1(sK51,sK53)))) ),
    inference(instantiation,[status(thm)],[c_430])).

cnf(c_429,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(k2_zfmisc_1(X1,X2),k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))))
    | r2_hidden(sK47(X0,X1,X2,X3,X4),k4_xboole_0(X2,k4_xboole_0(X2,X4))) ),
    inference(cnf_transformation,[],[f1675])).

cnf(c_25073,plain,
    ( r2_hidden(sK47(sK14(k2_zfmisc_1(sK50,sK52),k2_zfmisc_1(sK51,sK53)),sK50,sK52,sK51,sK53),k4_xboole_0(sK52,k4_xboole_0(sK52,sK53)))
    | ~ r2_hidden(sK14(k2_zfmisc_1(sK50,sK52),k2_zfmisc_1(sK51,sK53)),k4_xboole_0(k2_zfmisc_1(sK50,sK52),k4_xboole_0(k2_zfmisc_1(sK50,sK52),k2_zfmisc_1(sK51,sK53)))) ),
    inference(instantiation,[status(thm)],[c_429])).

cnf(c_59,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK14(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f1433])).

cnf(c_20364,plain,
    ( r1_xboole_0(k2_zfmisc_1(sK50,sK52),k2_zfmisc_1(sK51,sK53))
    | r2_hidden(sK14(k2_zfmisc_1(sK50,sK52),k2_zfmisc_1(sK51,sK53)),k4_xboole_0(k2_zfmisc_1(sK50,sK52),k4_xboole_0(k2_zfmisc_1(sK50,sK52),k2_zfmisc_1(sK51,sK53)))) ),
    inference(instantiation,[status(thm)],[c_59])).

cnf(c_461,negated_conjecture,
    ( ~ r1_xboole_0(k2_zfmisc_1(sK50,sK52),k2_zfmisc_1(sK51,sK53)) ),
    inference(cnf_transformation,[],[f1275])).

cnf(c_462,negated_conjecture,
    ( r1_xboole_0(sK52,sK53)
    | r1_xboole_0(sK50,sK51) ),
    inference(cnf_transformation,[],[f1274])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_41123,c_40951,c_25072,c_25073,c_20364,c_461,c_462])).

%------------------------------------------------------------------------------
