%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0862+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:17 EST 2020

% Result     : Theorem 0.87s
% Output     : CNFRefutation 0.87s
% Verified   : 
% Statistics : Number of formulae       :   40 (  52 expanded)
%              Number of clauses        :   13 (  13 expanded)
%              Number of leaves         :    7 (  12 expanded)
%              Depth                    :   10
%              Number of atoms          :  191 ( 245 expanded)
%              Number of equality atoms :  117 ( 153 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f12])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f13])).

fof(f15,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK1(X0,X1,X2) != X1
            & sK1(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( sK1(X0,X1,X2) = X1
          | sK1(X0,X1,X2) = X0
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK1(X0,X1,X2) != X1
              & sK1(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( sK1(X0,X1,X2) = X1
            | sK1(X0,X1,X2) = X0
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f14,f15])).

fof(f23,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f41,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_tarski(X0,X1)) ) ),
    inference(equality_resolution,[],[f23])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f8])).

fof(f10,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK0(X0,X1) != X0
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( sK0(X0,X1) = X0
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK0(X0,X1) != X0
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( sK0(X0,X1) = X0
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f10])).

fof(f19,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f36,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f19])).

fof(f4,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)))
     => ( ( k2_mcart_1(X0) = X3
          | k2_mcart_1(X0) = X2 )
        & k1_mcart_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)))
       => ( ( k2_mcart_1(X0) = X3
            | k2_mcart_1(X0) = X2 )
          & k1_mcart_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f7,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ( k2_mcart_1(X0) != X3
          & k2_mcart_1(X0) != X2 )
        | k1_mcart_1(X0) != X1 )
      & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ( k2_mcart_1(X0) != X3
            & k2_mcart_1(X0) != X2 )
          | k1_mcart_1(X0) != X1 )
        & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))) )
   => ( ( ( k2_mcart_1(sK2) != sK5
          & k2_mcart_1(sK2) != sK4 )
        | k1_mcart_1(sK2) != sK3 )
      & r2_hidden(sK2,k2_zfmisc_1(k1_tarski(sK3),k2_tarski(sK4,sK5))) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ( ( k2_mcart_1(sK2) != sK5
        & k2_mcart_1(sK2) != sK4 )
      | k1_mcart_1(sK2) != sK3 )
    & r2_hidden(sK2,k2_zfmisc_1(k1_tarski(sK3),k2_tarski(sK4,sK5))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f7,f17])).

fof(f33,plain,
    ( k2_mcart_1(sK2) != sK5
    | k1_mcart_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f18])).

fof(f32,plain,
    ( k2_mcart_1(sK2) != sK4
    | k1_mcart_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f18])).

fof(f31,plain,(
    r2_hidden(sK2,k2_zfmisc_1(k1_tarski(sK3),k2_tarski(sK4,sK5))) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k2_tarski(X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_529,plain,
    ( ~ r2_hidden(k2_mcart_1(sK2),k2_tarski(sK4,X0))
    | k2_mcart_1(sK2) = X0
    | k2_mcart_1(sK2) = sK4 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_642,plain,
    ( ~ r2_hidden(k2_mcart_1(sK2),k2_tarski(sK4,sK5))
    | k2_mcart_1(sK2) = sK4
    | k2_mcart_1(sK2) = sK5 ),
    inference(instantiation,[status(thm)],[c_529])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k1_mcart_1(X0),X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_485,plain,
    ( r2_hidden(k1_mcart_1(sK2),k1_tarski(sK3))
    | ~ r2_hidden(sK2,k2_zfmisc_1(k1_tarski(sK3),k2_tarski(sK4,sK5))) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k2_mcart_1(X0),X2) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_482,plain,
    ( r2_hidden(k2_mcart_1(sK2),k2_tarski(sK4,sK5))
    | ~ r2_hidden(sK2,k2_zfmisc_1(k1_tarski(sK3),k2_tarski(sK4,sK5))) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_475,plain,
    ( ~ r2_hidden(k1_mcart_1(sK2),k1_tarski(sK3))
    | k1_mcart_1(sK2) = sK3 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_12,negated_conjecture,
    ( k1_mcart_1(sK2) != sK3
    | k2_mcart_1(sK2) != sK5 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_13,negated_conjecture,
    ( k1_mcart_1(sK2) != sK3
    | k2_mcart_1(sK2) != sK4 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_14,negated_conjecture,
    ( r2_hidden(sK2,k2_zfmisc_1(k1_tarski(sK3),k2_tarski(sK4,sK5))) ),
    inference(cnf_transformation,[],[f31])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_642,c_485,c_482,c_475,c_12,c_13,c_14])).


%------------------------------------------------------------------------------
