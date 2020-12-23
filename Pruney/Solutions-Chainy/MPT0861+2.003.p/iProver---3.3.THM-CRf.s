%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:57:37 EST 2020

% Result     : Theorem 23.72s
% Output     : CNFRefutation 23.72s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 322 expanded)
%              Number of clauses        :   62 (  80 expanded)
%              Number of leaves         :   14 (  83 expanded)
%              Depth                    :   18
%              Number of atoms          :  348 (1046 expanded)
%              Number of equality atoms :  139 ( 417 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f14])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f15])).

fof(f17,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f17])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)))
     => ( k2_mcart_1(X0) = X3
        & ( k1_mcart_1(X0) = X2
          | k1_mcart_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)))
       => ( k2_mcart_1(X0) = X3
          & ( k1_mcart_1(X0) = X2
            | k1_mcart_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ( k2_mcart_1(X0) != X3
        | ( k1_mcart_1(X0) != X2
          & k1_mcart_1(X0) != X1 ) )
      & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( k2_mcart_1(X0) != X3
          | ( k1_mcart_1(X0) != X2
            & k1_mcart_1(X0) != X1 ) )
        & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))) )
   => ( ( k2_mcart_1(sK1) != sK4
        | ( k1_mcart_1(sK1) != sK3
          & k1_mcart_1(sK1) != sK2 ) )
      & r2_hidden(sK1,k2_zfmisc_1(k2_tarski(sK2,sK3),k1_tarski(sK4))) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ( k2_mcart_1(sK1) != sK4
      | ( k1_mcart_1(sK1) != sK3
        & k1_mcart_1(sK1) != sK2 ) )
    & r2_hidden(sK1,k2_zfmisc_1(k2_tarski(sK2,sK3),k1_tarski(sK4))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f13,f27])).

fof(f52,plain,(
    r2_hidden(sK1,k2_zfmisc_1(k2_tarski(sK2,sK3),k1_tarski(sK4))) ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f39,f40])).

fof(f56,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f38,f55])).

fof(f66,plain,(
    r2_hidden(sK1,k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK3),k2_enumset1(sK4,sK4,sK4,sK4))) ),
    inference(definition_unfolding,[],[f52,f55,f56])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f19])).

fof(f37,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f53,plain,
    ( k2_mcart_1(sK1) != sK4
    | k1_mcart_1(sK1) != sK2 ),
    inference(cnf_transformation,[],[f28])).

fof(f54,plain,
    ( k2_mcart_1(sK1) != sK4
    | k1_mcart_1(sK1) != sK3 ),
    inference(cnf_transformation,[],[f28])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f23])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
      | X0 = X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))
      | X0 = X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f46,f56])).

fof(f30,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f68,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f30])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) ) ) ),
    inference(flattening,[],[f25])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k2_enumset1(X0,X0,X0,X1),X2) = k2_enumset1(X0,X0,X0,X1)
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f49,f55,f55])).

fof(f29,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f69,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f29])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))) ) ),
    inference(definition_unfolding,[],[f45,f56])).

fof(f72,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))) ),
    inference(equality_resolution,[],[f61])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f70,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f36])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_4652,plain,
    ( r2_hidden(sK0(X0,X0,X1),X1)
    | k4_xboole_0(X0,X0) = X1 ),
    inference(resolution,[status(thm)],[c_1,c_2])).

cnf(c_296,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_293,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2827,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_296,c_293])).

cnf(c_7493,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK0(X2,X2,X0),X0)
    | r2_hidden(k4_xboole_0(X2,X2),X1) ),
    inference(resolution,[status(thm)],[c_4652,c_2827])).

cnf(c_22,negated_conjecture,
    ( r2_hidden(sK1,k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK3),k2_enumset1(sK4,sK4,sK4,sK4))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_57419,plain,
    ( r2_hidden(sK0(X0,X0,sK1),sK1)
    | r2_hidden(k4_xboole_0(X0,X0),k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK3),k2_enumset1(sK4,sK4,sK4,sK4))) ),
    inference(resolution,[status(thm)],[c_7493,c_22])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k1_mcart_1(X0),X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_59670,plain,
    ( r2_hidden(sK0(X0,X0,sK1),sK1)
    | r2_hidden(k1_mcart_1(k4_xboole_0(X0,X0)),k2_enumset1(sK2,sK2,sK2,sK3)) ),
    inference(resolution,[status(thm)],[c_57419,c_19])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_2825,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X3,X1)
    | X3 != X2 ),
    inference(resolution,[status(thm)],[c_296,c_6])).

cnf(c_13242,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | ~ r2_hidden(X2,X1)
    | r2_hidden(X2,X0) ),
    inference(resolution,[status(thm)],[c_2825,c_293])).

cnf(c_60478,plain,
    ( ~ r1_tarski(X0,k2_enumset1(sK2,sK2,sK2,sK3))
    | ~ r1_tarski(k2_enumset1(sK2,sK2,sK2,sK3),X0)
    | r2_hidden(sK0(X1,X1,sK1),sK1)
    | r2_hidden(k1_mcart_1(k4_xboole_0(X1,X1)),X0) ),
    inference(resolution,[status(thm)],[c_59670,c_13242])).

cnf(c_23,plain,
    ( r2_hidden(sK1,k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK3),k2_enumset1(sK4,sK4,sK4,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_21,negated_conjecture,
    ( k1_mcart_1(sK1) != sK2
    | k2_mcart_1(sK1) != sK4 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_20,negated_conjecture,
    ( k1_mcart_1(sK1) != sK3
    | k2_mcart_1(sK1) != sK4 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k2_mcart_1(X0),X2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_782,plain,
    ( r2_hidden(k2_mcart_1(sK1),k2_enumset1(sK4,sK4,sK4,sK4))
    | ~ r2_hidden(sK1,k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK3),k2_enumset1(sK4,sK4,sK4,sK4))) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_785,plain,
    ( r2_hidden(k1_mcart_1(sK1),k2_enumset1(sK2,sK2,sK2,sK3))
    | ~ r2_hidden(sK1,k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK3),k2_enumset1(sK4,sK4,sK4,sK4))) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_786,plain,
    ( r2_hidden(k1_mcart_1(sK1),k2_enumset1(sK2,sK2,sK2,sK3)) = iProver_top
    | r2_hidden(sK1,k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK3),k2_enumset1(sK4,sK4,sK4,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_785])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))
    | X2 = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_904,plain,
    ( ~ r2_hidden(k2_mcart_1(sK1),k2_enumset1(sK4,sK4,sK4,sK4))
    | r2_hidden(k2_mcart_1(sK1),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(X0,X0,X0,X0)))
    | X0 = k2_mcart_1(sK1) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_916,plain,
    ( ~ r2_hidden(k2_mcart_1(sK1),k2_enumset1(sK4,sK4,sK4,sK4))
    | r2_hidden(k2_mcart_1(sK1),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK4,sK4,sK4,sK4)))
    | sK4 = k2_mcart_1(sK1) ),
    inference(instantiation,[status(thm)],[c_904])).

cnf(c_294,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_805,plain,
    ( k2_mcart_1(sK1) != X0
    | k2_mcart_1(sK1) = sK4
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_294])).

cnf(c_969,plain,
    ( k2_mcart_1(sK1) != k2_mcart_1(sK1)
    | k2_mcart_1(sK1) = sK4
    | sK4 != k2_mcart_1(sK1) ),
    inference(instantiation,[status(thm)],[c_805])).

cnf(c_970,plain,
    ( k2_mcart_1(sK1) = k2_mcart_1(sK1) ),
    inference(instantiation,[status(thm)],[c_293])).

cnf(c_2801,plain,
    ( k1_mcart_1(sK1) = k1_mcart_1(sK1) ),
    inference(instantiation,[status(thm)],[c_293])).

cnf(c_4445,plain,
    ( ~ r1_tarski(X0,k2_enumset1(sK2,sK2,sK2,sK3))
    | ~ r1_tarski(k2_enumset1(sK2,sK2,sK2,sK3),X0)
    | X0 = k2_enumset1(sK2,sK2,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_935,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k1_mcart_1(sK1),k2_enumset1(sK2,sK2,sK2,sK3))
    | X1 != k2_enumset1(sK2,sK2,sK2,sK3)
    | X0 != k1_mcart_1(sK1) ),
    inference(instantiation,[status(thm)],[c_296])).

cnf(c_5068,plain,
    ( r2_hidden(k1_mcart_1(sK1),X0)
    | ~ r2_hidden(k1_mcart_1(sK1),k2_enumset1(sK2,sK2,sK2,sK3))
    | X0 != k2_enumset1(sK2,sK2,sK2,sK3)
    | k1_mcart_1(sK1) != k1_mcart_1(sK1) ),
    inference(instantiation,[status(thm)],[c_935])).

cnf(c_5074,plain,
    ( X0 != k2_enumset1(sK2,sK2,sK2,sK3)
    | k1_mcart_1(sK1) != k1_mcart_1(sK1)
    | r2_hidden(k1_mcart_1(sK1),X0) = iProver_top
    | r2_hidden(k1_mcart_1(sK1),k2_enumset1(sK2,sK2,sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5068])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_3106,plain,
    ( ~ r2_hidden(k2_mcart_1(X0),X1)
    | ~ r2_hidden(k2_mcart_1(X0),k4_xboole_0(X2,X1)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_7141,plain,
    ( ~ r2_hidden(k2_mcart_1(sK1),k2_enumset1(X0,X0,X0,X0))
    | ~ r2_hidden(k2_mcart_1(sK1),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(X0,X0,X0,X0))) ),
    inference(instantiation,[status(thm)],[c_3106])).

cnf(c_7143,plain,
    ( ~ r2_hidden(k2_mcart_1(sK1),k2_enumset1(sK4,sK4,sK4,sK4))
    | ~ r2_hidden(k2_mcart_1(sK1),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK4,sK4,sK4,sK4))) ),
    inference(instantiation,[status(thm)],[c_7141])).

cnf(c_613,plain,
    ( r2_hidden(sK1,k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK3),k2_enumset1(sK4,sK4,sK4,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_614,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_880,plain,
    ( r2_hidden(k1_mcart_1(sK1),k2_enumset1(sK2,sK2,sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_613,c_614])).

cnf(c_621,plain,
    ( X0 = X1
    | r2_hidden(X1,X2) != iProver_top
    | r2_hidden(X1,k4_xboole_0(X2,k2_enumset1(X0,X0,X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_15,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | k4_xboole_0(k2_enumset1(X0,X0,X0,X2),X1) = k2_enumset1(X0,X0,X0,X2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_618,plain,
    ( k4_xboole_0(k2_enumset1(X0,X0,X0,X1),X2) = k2_enumset1(X0,X0,X0,X1)
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X1,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_627,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1778,plain,
    ( k4_xboole_0(k2_enumset1(X0,X0,X0,X1),k4_xboole_0(X2,X3)) = k2_enumset1(X0,X0,X0,X1)
    | r2_hidden(X1,X2) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_618,c_627])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_620,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3482,plain,
    ( k4_xboole_0(k2_enumset1(X0,X0,X0,X1),k4_xboole_0(X2,k2_enumset1(X0,X0,X0,X0))) = k2_enumset1(X0,X0,X0,X1)
    | r2_hidden(X1,X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1778,c_620])).

cnf(c_7359,plain,
    ( k4_xboole_0(k2_enumset1(X0,X0,X0,X1),k4_xboole_0(k4_xboole_0(X2,k2_enumset1(X1,X1,X1,X1)),k2_enumset1(X0,X0,X0,X0))) = k2_enumset1(X0,X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_3482,c_620])).

cnf(c_628,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_7802,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X2)) != iProver_top
    | r2_hidden(X0,k4_xboole_0(k4_xboole_0(X3,k2_enumset1(X2,X2,X2,X2)),k2_enumset1(X1,X1,X1,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7359,c_628])).

cnf(c_78152,plain,
    ( X0 = X1
    | r2_hidden(X0,k2_enumset1(X1,X1,X1,X2)) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X3,k2_enumset1(X2,X2,X2,X2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_621,c_7802])).

cnf(c_80901,plain,
    ( X0 = X1
    | X2 = X0
    | r2_hidden(X0,X3) != iProver_top
    | r2_hidden(X0,k2_enumset1(X2,X2,X2,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_621,c_78152])).

cnf(c_82788,plain,
    ( k1_mcart_1(sK1) = sK2
    | k1_mcart_1(sK1) = sK3
    | r2_hidden(k1_mcart_1(sK1),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_880,c_80901])).

cnf(c_88431,plain,
    ( ~ r1_tarski(X0,k2_enumset1(sK2,sK2,sK2,sK3))
    | ~ r1_tarski(k2_enumset1(sK2,sK2,sK2,sK3),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_60478,c_22,c_23,c_21,c_20,c_782,c_786,c_916,c_969,c_970,c_2801,c_4445,c_5074,c_7143,c_82788])).

cnf(c_7,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_88449,plain,
    ( ~ r1_tarski(k2_enumset1(sK2,sK2,sK2,sK3),k2_enumset1(sK2,sK2,sK2,sK3)) ),
    inference(resolution,[status(thm)],[c_88431,c_7])).

cnf(c_852,plain,
    ( r1_tarski(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_6308,plain,
    ( r1_tarski(k2_enumset1(sK2,sK2,sK2,sK3),k2_enumset1(sK2,sK2,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_852])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_88449,c_6308])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:53:02 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 23.72/3.47  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.72/3.47  
% 23.72/3.47  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.72/3.47  
% 23.72/3.47  ------  iProver source info
% 23.72/3.47  
% 23.72/3.47  git: date: 2020-06-30 10:37:57 +0100
% 23.72/3.47  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.72/3.47  git: non_committed_changes: false
% 23.72/3.47  git: last_make_outside_of_git: false
% 23.72/3.47  
% 23.72/3.47  ------ 
% 23.72/3.47  
% 23.72/3.47  ------ Input Options
% 23.72/3.47  
% 23.72/3.47  --out_options                           all
% 23.72/3.47  --tptp_safe_out                         true
% 23.72/3.47  --problem_path                          ""
% 23.72/3.47  --include_path                          ""
% 23.72/3.47  --clausifier                            res/vclausify_rel
% 23.72/3.47  --clausifier_options                    --mode clausify
% 23.72/3.47  --stdin                                 false
% 23.72/3.47  --stats_out                             sel
% 23.72/3.47  
% 23.72/3.47  ------ General Options
% 23.72/3.47  
% 23.72/3.47  --fof                                   false
% 23.72/3.47  --time_out_real                         604.99
% 23.72/3.47  --time_out_virtual                      -1.
% 23.72/3.47  --symbol_type_check                     false
% 23.72/3.47  --clausify_out                          false
% 23.72/3.47  --sig_cnt_out                           false
% 23.72/3.47  --trig_cnt_out                          false
% 23.72/3.47  --trig_cnt_out_tolerance                1.
% 23.72/3.47  --trig_cnt_out_sk_spl                   false
% 23.72/3.47  --abstr_cl_out                          false
% 23.72/3.47  
% 23.72/3.47  ------ Global Options
% 23.72/3.47  
% 23.72/3.47  --schedule                              none
% 23.72/3.47  --add_important_lit                     false
% 23.72/3.47  --prop_solver_per_cl                    1000
% 23.72/3.47  --min_unsat_core                        false
% 23.72/3.47  --soft_assumptions                      false
% 23.72/3.47  --soft_lemma_size                       3
% 23.72/3.47  --prop_impl_unit_size                   0
% 23.72/3.47  --prop_impl_unit                        []
% 23.72/3.47  --share_sel_clauses                     true
% 23.72/3.47  --reset_solvers                         false
% 23.72/3.47  --bc_imp_inh                            [conj_cone]
% 23.72/3.47  --conj_cone_tolerance                   3.
% 23.72/3.47  --extra_neg_conj                        none
% 23.72/3.47  --large_theory_mode                     true
% 23.72/3.47  --prolific_symb_bound                   200
% 23.72/3.47  --lt_threshold                          2000
% 23.72/3.47  --clause_weak_htbl                      true
% 23.72/3.47  --gc_record_bc_elim                     false
% 23.72/3.47  
% 23.72/3.47  ------ Preprocessing Options
% 23.72/3.47  
% 23.72/3.47  --preprocessing_flag                    true
% 23.72/3.47  --time_out_prep_mult                    0.1
% 23.72/3.47  --splitting_mode                        input
% 23.72/3.47  --splitting_grd                         true
% 23.72/3.47  --splitting_cvd                         false
% 23.72/3.47  --splitting_cvd_svl                     false
% 23.72/3.47  --splitting_nvd                         32
% 23.72/3.47  --sub_typing                            true
% 23.72/3.47  --prep_gs_sim                           false
% 23.72/3.47  --prep_unflatten                        true
% 23.72/3.47  --prep_res_sim                          true
% 23.72/3.47  --prep_upred                            true
% 23.72/3.47  --prep_sem_filter                       exhaustive
% 23.72/3.47  --prep_sem_filter_out                   false
% 23.72/3.47  --pred_elim                             false
% 23.72/3.47  --res_sim_input                         true
% 23.72/3.47  --eq_ax_congr_red                       true
% 23.72/3.47  --pure_diseq_elim                       true
% 23.72/3.47  --brand_transform                       false
% 23.72/3.47  --non_eq_to_eq                          false
% 23.72/3.47  --prep_def_merge                        true
% 23.72/3.47  --prep_def_merge_prop_impl              false
% 23.72/3.47  --prep_def_merge_mbd                    true
% 23.72/3.47  --prep_def_merge_tr_red                 false
% 23.72/3.47  --prep_def_merge_tr_cl                  false
% 23.72/3.47  --smt_preprocessing                     true
% 23.72/3.47  --smt_ac_axioms                         fast
% 23.72/3.47  --preprocessed_out                      false
% 23.72/3.47  --preprocessed_stats                    false
% 23.72/3.47  
% 23.72/3.47  ------ Abstraction refinement Options
% 23.72/3.47  
% 23.72/3.47  --abstr_ref                             []
% 23.72/3.47  --abstr_ref_prep                        false
% 23.72/3.47  --abstr_ref_until_sat                   false
% 23.72/3.47  --abstr_ref_sig_restrict                funpre
% 23.72/3.47  --abstr_ref_af_restrict_to_split_sk     false
% 23.72/3.47  --abstr_ref_under                       []
% 23.72/3.47  
% 23.72/3.47  ------ SAT Options
% 23.72/3.47  
% 23.72/3.47  --sat_mode                              false
% 23.72/3.47  --sat_fm_restart_options                ""
% 23.72/3.47  --sat_gr_def                            false
% 23.72/3.47  --sat_epr_types                         true
% 23.72/3.47  --sat_non_cyclic_types                  false
% 23.72/3.47  --sat_finite_models                     false
% 23.72/3.47  --sat_fm_lemmas                         false
% 23.72/3.47  --sat_fm_prep                           false
% 23.72/3.47  --sat_fm_uc_incr                        true
% 23.72/3.47  --sat_out_model                         small
% 23.72/3.47  --sat_out_clauses                       false
% 23.72/3.47  
% 23.72/3.47  ------ QBF Options
% 23.72/3.47  
% 23.72/3.47  --qbf_mode                              false
% 23.72/3.47  --qbf_elim_univ                         false
% 23.72/3.47  --qbf_dom_inst                          none
% 23.72/3.47  --qbf_dom_pre_inst                      false
% 23.72/3.47  --qbf_sk_in                             false
% 23.72/3.47  --qbf_pred_elim                         true
% 23.72/3.47  --qbf_split                             512
% 23.72/3.47  
% 23.72/3.47  ------ BMC1 Options
% 23.72/3.47  
% 23.72/3.47  --bmc1_incremental                      false
% 23.72/3.47  --bmc1_axioms                           reachable_all
% 23.72/3.47  --bmc1_min_bound                        0
% 23.72/3.47  --bmc1_max_bound                        -1
% 23.72/3.47  --bmc1_max_bound_default                -1
% 23.72/3.47  --bmc1_symbol_reachability              true
% 23.72/3.47  --bmc1_property_lemmas                  false
% 23.72/3.47  --bmc1_k_induction                      false
% 23.72/3.47  --bmc1_non_equiv_states                 false
% 23.72/3.47  --bmc1_deadlock                         false
% 23.72/3.47  --bmc1_ucm                              false
% 23.72/3.47  --bmc1_add_unsat_core                   none
% 23.72/3.47  --bmc1_unsat_core_children              false
% 23.72/3.47  --bmc1_unsat_core_extrapolate_axioms    false
% 23.72/3.47  --bmc1_out_stat                         full
% 23.72/3.47  --bmc1_ground_init                      false
% 23.72/3.47  --bmc1_pre_inst_next_state              false
% 23.72/3.47  --bmc1_pre_inst_state                   false
% 23.72/3.47  --bmc1_pre_inst_reach_state             false
% 23.72/3.47  --bmc1_out_unsat_core                   false
% 23.72/3.47  --bmc1_aig_witness_out                  false
% 23.72/3.47  --bmc1_verbose                          false
% 23.72/3.47  --bmc1_dump_clauses_tptp                false
% 23.72/3.47  --bmc1_dump_unsat_core_tptp             false
% 23.72/3.47  --bmc1_dump_file                        -
% 23.72/3.47  --bmc1_ucm_expand_uc_limit              128
% 23.72/3.47  --bmc1_ucm_n_expand_iterations          6
% 23.72/3.47  --bmc1_ucm_extend_mode                  1
% 23.72/3.47  --bmc1_ucm_init_mode                    2
% 23.72/3.47  --bmc1_ucm_cone_mode                    none
% 23.72/3.47  --bmc1_ucm_reduced_relation_type        0
% 23.72/3.47  --bmc1_ucm_relax_model                  4
% 23.72/3.47  --bmc1_ucm_full_tr_after_sat            true
% 23.72/3.47  --bmc1_ucm_expand_neg_assumptions       false
% 23.72/3.47  --bmc1_ucm_layered_model                none
% 23.72/3.47  --bmc1_ucm_max_lemma_size               10
% 23.72/3.47  
% 23.72/3.47  ------ AIG Options
% 23.72/3.47  
% 23.72/3.47  --aig_mode                              false
% 23.72/3.47  
% 23.72/3.47  ------ Instantiation Options
% 23.72/3.47  
% 23.72/3.47  --instantiation_flag                    true
% 23.72/3.47  --inst_sos_flag                         false
% 23.72/3.47  --inst_sos_phase                        true
% 23.72/3.47  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.72/3.47  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.72/3.47  --inst_lit_sel_side                     num_symb
% 23.72/3.47  --inst_solver_per_active                1400
% 23.72/3.47  --inst_solver_calls_frac                1.
% 23.72/3.47  --inst_passive_queue_type               priority_queues
% 23.72/3.47  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.72/3.47  --inst_passive_queues_freq              [25;2]
% 23.72/3.47  --inst_dismatching                      true
% 23.72/3.47  --inst_eager_unprocessed_to_passive     true
% 23.72/3.47  --inst_prop_sim_given                   true
% 23.72/3.47  --inst_prop_sim_new                     false
% 23.72/3.47  --inst_subs_new                         false
% 23.72/3.47  --inst_eq_res_simp                      false
% 23.72/3.47  --inst_subs_given                       false
% 23.72/3.47  --inst_orphan_elimination               true
% 23.72/3.47  --inst_learning_loop_flag               true
% 23.72/3.47  --inst_learning_start                   3000
% 23.72/3.47  --inst_learning_factor                  2
% 23.72/3.47  --inst_start_prop_sim_after_learn       3
% 23.72/3.47  --inst_sel_renew                        solver
% 23.72/3.47  --inst_lit_activity_flag                true
% 23.72/3.47  --inst_restr_to_given                   false
% 23.72/3.47  --inst_activity_threshold               500
% 23.72/3.47  --inst_out_proof                        true
% 23.72/3.47  
% 23.72/3.47  ------ Resolution Options
% 23.72/3.47  
% 23.72/3.47  --resolution_flag                       true
% 23.72/3.47  --res_lit_sel                           adaptive
% 23.72/3.47  --res_lit_sel_side                      none
% 23.72/3.47  --res_ordering                          kbo
% 23.72/3.47  --res_to_prop_solver                    active
% 23.72/3.47  --res_prop_simpl_new                    false
% 23.72/3.47  --res_prop_simpl_given                  true
% 23.72/3.47  --res_passive_queue_type                priority_queues
% 23.72/3.47  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.72/3.47  --res_passive_queues_freq               [15;5]
% 23.72/3.47  --res_forward_subs                      full
% 23.72/3.47  --res_backward_subs                     full
% 23.72/3.47  --res_forward_subs_resolution           true
% 23.72/3.47  --res_backward_subs_resolution          true
% 23.72/3.47  --res_orphan_elimination                true
% 23.72/3.47  --res_time_limit                        2.
% 23.72/3.47  --res_out_proof                         true
% 23.72/3.47  
% 23.72/3.47  ------ Superposition Options
% 23.72/3.47  
% 23.72/3.47  --superposition_flag                    true
% 23.72/3.47  --sup_passive_queue_type                priority_queues
% 23.72/3.47  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.72/3.47  --sup_passive_queues_freq               [1;4]
% 23.72/3.47  --demod_completeness_check              fast
% 23.72/3.47  --demod_use_ground                      true
% 23.72/3.47  --sup_to_prop_solver                    passive
% 23.72/3.47  --sup_prop_simpl_new                    true
% 23.72/3.47  --sup_prop_simpl_given                  true
% 23.72/3.47  --sup_fun_splitting                     false
% 23.72/3.47  --sup_smt_interval                      50000
% 23.72/3.47  
% 23.72/3.47  ------ Superposition Simplification Setup
% 23.72/3.47  
% 23.72/3.47  --sup_indices_passive                   []
% 23.72/3.47  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.72/3.47  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.72/3.47  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.72/3.47  --sup_full_triv                         [TrivRules;PropSubs]
% 23.72/3.47  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.72/3.47  --sup_full_bw                           [BwDemod]
% 23.72/3.47  --sup_immed_triv                        [TrivRules]
% 23.72/3.47  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.72/3.47  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.72/3.47  --sup_immed_bw_main                     []
% 23.72/3.47  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.72/3.47  --sup_input_triv                        [Unflattening;TrivRules]
% 23.72/3.47  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.72/3.47  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.72/3.47  
% 23.72/3.47  ------ Combination Options
% 23.72/3.47  
% 23.72/3.47  --comb_res_mult                         3
% 23.72/3.47  --comb_sup_mult                         2
% 23.72/3.47  --comb_inst_mult                        10
% 23.72/3.47  
% 23.72/3.47  ------ Debug Options
% 23.72/3.47  
% 23.72/3.47  --dbg_backtrace                         false
% 23.72/3.47  --dbg_dump_prop_clauses                 false
% 23.72/3.47  --dbg_dump_prop_clauses_file            -
% 23.72/3.47  --dbg_out_stat                          false
% 23.72/3.47  ------ Parsing...
% 23.72/3.47  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.72/3.47  
% 23.72/3.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 23.72/3.47  
% 23.72/3.47  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.72/3.47  
% 23.72/3.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.72/3.47  ------ Proving...
% 23.72/3.47  ------ Problem Properties 
% 23.72/3.47  
% 23.72/3.47  
% 23.72/3.47  clauses                                 22
% 23.72/3.47  conjectures                             3
% 23.72/3.47  EPR                                     2
% 23.72/3.47  Horn                                    16
% 23.72/3.47  unary                                   3
% 23.72/3.47  binary                                  11
% 23.72/3.47  lits                                    50
% 23.72/3.47  lits eq                                 12
% 23.72/3.47  fd_pure                                 0
% 23.72/3.47  fd_pseudo                               0
% 23.72/3.47  fd_cond                                 0
% 23.72/3.47  fd_pseudo_cond                          5
% 23.72/3.47  AC symbols                              0
% 23.72/3.47  
% 23.72/3.47  ------ Input Options Time Limit: Unbounded
% 23.72/3.47  
% 23.72/3.47  
% 23.72/3.47  ------ 
% 23.72/3.47  Current options:
% 23.72/3.47  ------ 
% 23.72/3.47  
% 23.72/3.47  ------ Input Options
% 23.72/3.47  
% 23.72/3.47  --out_options                           all
% 23.72/3.47  --tptp_safe_out                         true
% 23.72/3.47  --problem_path                          ""
% 23.72/3.47  --include_path                          ""
% 23.72/3.47  --clausifier                            res/vclausify_rel
% 23.72/3.47  --clausifier_options                    --mode clausify
% 23.72/3.47  --stdin                                 false
% 23.72/3.47  --stats_out                             sel
% 23.72/3.47  
% 23.72/3.47  ------ General Options
% 23.72/3.47  
% 23.72/3.47  --fof                                   false
% 23.72/3.47  --time_out_real                         604.99
% 23.72/3.47  --time_out_virtual                      -1.
% 23.72/3.47  --symbol_type_check                     false
% 23.72/3.47  --clausify_out                          false
% 23.72/3.47  --sig_cnt_out                           false
% 23.72/3.47  --trig_cnt_out                          false
% 23.72/3.47  --trig_cnt_out_tolerance                1.
% 23.72/3.47  --trig_cnt_out_sk_spl                   false
% 23.72/3.47  --abstr_cl_out                          false
% 23.72/3.47  
% 23.72/3.47  ------ Global Options
% 23.72/3.47  
% 23.72/3.47  --schedule                              none
% 23.72/3.47  --add_important_lit                     false
% 23.72/3.47  --prop_solver_per_cl                    1000
% 23.72/3.47  --min_unsat_core                        false
% 23.72/3.47  --soft_assumptions                      false
% 23.72/3.47  --soft_lemma_size                       3
% 23.72/3.47  --prop_impl_unit_size                   0
% 23.72/3.47  --prop_impl_unit                        []
% 23.72/3.47  --share_sel_clauses                     true
% 23.72/3.47  --reset_solvers                         false
% 23.72/3.47  --bc_imp_inh                            [conj_cone]
% 23.72/3.47  --conj_cone_tolerance                   3.
% 23.72/3.47  --extra_neg_conj                        none
% 23.72/3.47  --large_theory_mode                     true
% 23.72/3.47  --prolific_symb_bound                   200
% 23.72/3.47  --lt_threshold                          2000
% 23.72/3.47  --clause_weak_htbl                      true
% 23.72/3.47  --gc_record_bc_elim                     false
% 23.72/3.47  
% 23.72/3.47  ------ Preprocessing Options
% 23.72/3.47  
% 23.72/3.47  --preprocessing_flag                    true
% 23.72/3.47  --time_out_prep_mult                    0.1
% 23.72/3.47  --splitting_mode                        input
% 23.72/3.47  --splitting_grd                         true
% 23.72/3.47  --splitting_cvd                         false
% 23.72/3.47  --splitting_cvd_svl                     false
% 23.72/3.47  --splitting_nvd                         32
% 23.72/3.47  --sub_typing                            true
% 23.72/3.47  --prep_gs_sim                           false
% 23.72/3.47  --prep_unflatten                        true
% 23.72/3.47  --prep_res_sim                          true
% 23.72/3.47  --prep_upred                            true
% 23.72/3.47  --prep_sem_filter                       exhaustive
% 23.72/3.47  --prep_sem_filter_out                   false
% 23.72/3.47  --pred_elim                             false
% 23.72/3.47  --res_sim_input                         true
% 23.72/3.47  --eq_ax_congr_red                       true
% 23.72/3.47  --pure_diseq_elim                       true
% 23.72/3.47  --brand_transform                       false
% 23.72/3.47  --non_eq_to_eq                          false
% 23.72/3.47  --prep_def_merge                        true
% 23.72/3.47  --prep_def_merge_prop_impl              false
% 23.72/3.47  --prep_def_merge_mbd                    true
% 23.72/3.47  --prep_def_merge_tr_red                 false
% 23.72/3.47  --prep_def_merge_tr_cl                  false
% 23.72/3.47  --smt_preprocessing                     true
% 23.72/3.47  --smt_ac_axioms                         fast
% 23.72/3.47  --preprocessed_out                      false
% 23.72/3.47  --preprocessed_stats                    false
% 23.72/3.47  
% 23.72/3.47  ------ Abstraction refinement Options
% 23.72/3.47  
% 23.72/3.47  --abstr_ref                             []
% 23.72/3.47  --abstr_ref_prep                        false
% 23.72/3.47  --abstr_ref_until_sat                   false
% 23.72/3.47  --abstr_ref_sig_restrict                funpre
% 23.72/3.47  --abstr_ref_af_restrict_to_split_sk     false
% 23.72/3.47  --abstr_ref_under                       []
% 23.72/3.47  
% 23.72/3.47  ------ SAT Options
% 23.72/3.47  
% 23.72/3.47  --sat_mode                              false
% 23.72/3.47  --sat_fm_restart_options                ""
% 23.72/3.47  --sat_gr_def                            false
% 23.72/3.47  --sat_epr_types                         true
% 23.72/3.47  --sat_non_cyclic_types                  false
% 23.72/3.47  --sat_finite_models                     false
% 23.72/3.47  --sat_fm_lemmas                         false
% 23.72/3.47  --sat_fm_prep                           false
% 23.72/3.47  --sat_fm_uc_incr                        true
% 23.72/3.47  --sat_out_model                         small
% 23.72/3.47  --sat_out_clauses                       false
% 23.72/3.47  
% 23.72/3.47  ------ QBF Options
% 23.72/3.47  
% 23.72/3.47  --qbf_mode                              false
% 23.72/3.47  --qbf_elim_univ                         false
% 23.72/3.47  --qbf_dom_inst                          none
% 23.72/3.47  --qbf_dom_pre_inst                      false
% 23.72/3.47  --qbf_sk_in                             false
% 23.72/3.47  --qbf_pred_elim                         true
% 23.72/3.47  --qbf_split                             512
% 23.72/3.47  
% 23.72/3.47  ------ BMC1 Options
% 23.72/3.47  
% 23.72/3.47  --bmc1_incremental                      false
% 23.72/3.47  --bmc1_axioms                           reachable_all
% 23.72/3.47  --bmc1_min_bound                        0
% 23.72/3.47  --bmc1_max_bound                        -1
% 23.72/3.47  --bmc1_max_bound_default                -1
% 23.72/3.47  --bmc1_symbol_reachability              true
% 23.72/3.47  --bmc1_property_lemmas                  false
% 23.72/3.47  --bmc1_k_induction                      false
% 23.72/3.47  --bmc1_non_equiv_states                 false
% 23.72/3.47  --bmc1_deadlock                         false
% 23.72/3.47  --bmc1_ucm                              false
% 23.72/3.47  --bmc1_add_unsat_core                   none
% 23.72/3.47  --bmc1_unsat_core_children              false
% 23.72/3.47  --bmc1_unsat_core_extrapolate_axioms    false
% 23.72/3.47  --bmc1_out_stat                         full
% 23.72/3.47  --bmc1_ground_init                      false
% 23.72/3.47  --bmc1_pre_inst_next_state              false
% 23.72/3.47  --bmc1_pre_inst_state                   false
% 23.72/3.47  --bmc1_pre_inst_reach_state             false
% 23.72/3.47  --bmc1_out_unsat_core                   false
% 23.72/3.47  --bmc1_aig_witness_out                  false
% 23.72/3.47  --bmc1_verbose                          false
% 23.72/3.47  --bmc1_dump_clauses_tptp                false
% 23.72/3.47  --bmc1_dump_unsat_core_tptp             false
% 23.72/3.47  --bmc1_dump_file                        -
% 23.72/3.47  --bmc1_ucm_expand_uc_limit              128
% 23.72/3.47  --bmc1_ucm_n_expand_iterations          6
% 23.72/3.47  --bmc1_ucm_extend_mode                  1
% 23.72/3.47  --bmc1_ucm_init_mode                    2
% 23.72/3.47  --bmc1_ucm_cone_mode                    none
% 23.72/3.47  --bmc1_ucm_reduced_relation_type        0
% 23.72/3.47  --bmc1_ucm_relax_model                  4
% 23.72/3.47  --bmc1_ucm_full_tr_after_sat            true
% 23.72/3.47  --bmc1_ucm_expand_neg_assumptions       false
% 23.72/3.47  --bmc1_ucm_layered_model                none
% 23.72/3.47  --bmc1_ucm_max_lemma_size               10
% 23.72/3.47  
% 23.72/3.47  ------ AIG Options
% 23.72/3.47  
% 23.72/3.47  --aig_mode                              false
% 23.72/3.47  
% 23.72/3.47  ------ Instantiation Options
% 23.72/3.47  
% 23.72/3.47  --instantiation_flag                    true
% 23.72/3.47  --inst_sos_flag                         false
% 23.72/3.47  --inst_sos_phase                        true
% 23.72/3.47  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.72/3.47  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.72/3.47  --inst_lit_sel_side                     num_symb
% 23.72/3.47  --inst_solver_per_active                1400
% 23.72/3.47  --inst_solver_calls_frac                1.
% 23.72/3.47  --inst_passive_queue_type               priority_queues
% 23.72/3.47  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.72/3.47  --inst_passive_queues_freq              [25;2]
% 23.72/3.47  --inst_dismatching                      true
% 23.72/3.47  --inst_eager_unprocessed_to_passive     true
% 23.72/3.47  --inst_prop_sim_given                   true
% 23.72/3.47  --inst_prop_sim_new                     false
% 23.72/3.47  --inst_subs_new                         false
% 23.72/3.47  --inst_eq_res_simp                      false
% 23.72/3.47  --inst_subs_given                       false
% 23.72/3.47  --inst_orphan_elimination               true
% 23.72/3.47  --inst_learning_loop_flag               true
% 23.72/3.47  --inst_learning_start                   3000
% 23.72/3.47  --inst_learning_factor                  2
% 23.72/3.47  --inst_start_prop_sim_after_learn       3
% 23.72/3.47  --inst_sel_renew                        solver
% 23.72/3.47  --inst_lit_activity_flag                true
% 23.72/3.47  --inst_restr_to_given                   false
% 23.72/3.47  --inst_activity_threshold               500
% 23.72/3.47  --inst_out_proof                        true
% 23.72/3.47  
% 23.72/3.47  ------ Resolution Options
% 23.72/3.47  
% 23.72/3.47  --resolution_flag                       true
% 23.72/3.47  --res_lit_sel                           adaptive
% 23.72/3.47  --res_lit_sel_side                      none
% 23.72/3.47  --res_ordering                          kbo
% 23.72/3.47  --res_to_prop_solver                    active
% 23.72/3.47  --res_prop_simpl_new                    false
% 23.72/3.47  --res_prop_simpl_given                  true
% 23.72/3.48  --res_passive_queue_type                priority_queues
% 23.72/3.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.72/3.48  --res_passive_queues_freq               [15;5]
% 23.72/3.48  --res_forward_subs                      full
% 23.72/3.48  --res_backward_subs                     full
% 23.72/3.48  --res_forward_subs_resolution           true
% 23.72/3.48  --res_backward_subs_resolution          true
% 23.72/3.48  --res_orphan_elimination                true
% 23.72/3.48  --res_time_limit                        2.
% 23.72/3.48  --res_out_proof                         true
% 23.72/3.48  
% 23.72/3.48  ------ Superposition Options
% 23.72/3.48  
% 23.72/3.48  --superposition_flag                    true
% 23.72/3.48  --sup_passive_queue_type                priority_queues
% 23.72/3.48  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.72/3.48  --sup_passive_queues_freq               [1;4]
% 23.72/3.48  --demod_completeness_check              fast
% 23.72/3.48  --demod_use_ground                      true
% 23.72/3.48  --sup_to_prop_solver                    passive
% 23.72/3.48  --sup_prop_simpl_new                    true
% 23.72/3.48  --sup_prop_simpl_given                  true
% 23.72/3.48  --sup_fun_splitting                     false
% 23.72/3.48  --sup_smt_interval                      50000
% 23.72/3.48  
% 23.72/3.48  ------ Superposition Simplification Setup
% 23.72/3.48  
% 23.72/3.48  --sup_indices_passive                   []
% 23.72/3.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.72/3.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.72/3.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.72/3.48  --sup_full_triv                         [TrivRules;PropSubs]
% 23.72/3.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.72/3.48  --sup_full_bw                           [BwDemod]
% 23.72/3.48  --sup_immed_triv                        [TrivRules]
% 23.72/3.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.72/3.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.72/3.48  --sup_immed_bw_main                     []
% 23.72/3.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.72/3.48  --sup_input_triv                        [Unflattening;TrivRules]
% 23.72/3.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.72/3.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.72/3.48  
% 23.72/3.48  ------ Combination Options
% 23.72/3.48  
% 23.72/3.48  --comb_res_mult                         3
% 23.72/3.48  --comb_sup_mult                         2
% 23.72/3.48  --comb_inst_mult                        10
% 23.72/3.48  
% 23.72/3.48  ------ Debug Options
% 23.72/3.48  
% 23.72/3.48  --dbg_backtrace                         false
% 23.72/3.48  --dbg_dump_prop_clauses                 false
% 23.72/3.48  --dbg_dump_prop_clauses_file            -
% 23.72/3.48  --dbg_out_stat                          false
% 23.72/3.48  
% 23.72/3.48  
% 23.72/3.48  
% 23.72/3.48  
% 23.72/3.48  ------ Proving...
% 23.72/3.48  
% 23.72/3.48  
% 23.72/3.48  % SZS status Theorem for theBenchmark.p
% 23.72/3.48  
% 23.72/3.48  % SZS output start CNFRefutation for theBenchmark.p
% 23.72/3.48  
% 23.72/3.48  fof(f1,axiom,(
% 23.72/3.48    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 23.72/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.72/3.48  
% 23.72/3.48  fof(f14,plain,(
% 23.72/3.48    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 23.72/3.48    inference(nnf_transformation,[],[f1])).
% 23.72/3.48  
% 23.72/3.48  fof(f15,plain,(
% 23.72/3.48    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 23.72/3.48    inference(flattening,[],[f14])).
% 23.72/3.48  
% 23.72/3.48  fof(f16,plain,(
% 23.72/3.48    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 23.72/3.48    inference(rectify,[],[f15])).
% 23.72/3.48  
% 23.72/3.48  fof(f17,plain,(
% 23.72/3.48    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 23.72/3.48    introduced(choice_axiom,[])).
% 23.72/3.48  
% 23.72/3.48  fof(f18,plain,(
% 23.72/3.48    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 23.72/3.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f17])).
% 23.72/3.48  
% 23.72/3.48  fof(f33,plain,(
% 23.72/3.48    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 23.72/3.48    inference(cnf_transformation,[],[f18])).
% 23.72/3.48  
% 23.72/3.48  fof(f32,plain,(
% 23.72/3.48    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 23.72/3.48    inference(cnf_transformation,[],[f18])).
% 23.72/3.48  
% 23.72/3.48  fof(f10,conjecture,(
% 23.72/3.48    ! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))) => (k2_mcart_1(X0) = X3 & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)))),
% 23.72/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.72/3.48  
% 23.72/3.48  fof(f11,negated_conjecture,(
% 23.72/3.48    ~! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))) => (k2_mcart_1(X0) = X3 & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)))),
% 23.72/3.48    inference(negated_conjecture,[],[f10])).
% 23.72/3.48  
% 23.72/3.48  fof(f13,plain,(
% 23.72/3.48    ? [X0,X1,X2,X3] : ((k2_mcart_1(X0) != X3 | (k1_mcart_1(X0) != X2 & k1_mcart_1(X0) != X1)) & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))))),
% 23.72/3.48    inference(ennf_transformation,[],[f11])).
% 23.72/3.48  
% 23.72/3.48  fof(f27,plain,(
% 23.72/3.48    ? [X0,X1,X2,X3] : ((k2_mcart_1(X0) != X3 | (k1_mcart_1(X0) != X2 & k1_mcart_1(X0) != X1)) & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)))) => ((k2_mcart_1(sK1) != sK4 | (k1_mcart_1(sK1) != sK3 & k1_mcart_1(sK1) != sK2)) & r2_hidden(sK1,k2_zfmisc_1(k2_tarski(sK2,sK3),k1_tarski(sK4))))),
% 23.72/3.48    introduced(choice_axiom,[])).
% 23.72/3.48  
% 23.72/3.48  fof(f28,plain,(
% 23.72/3.48    (k2_mcart_1(sK1) != sK4 | (k1_mcart_1(sK1) != sK3 & k1_mcart_1(sK1) != sK2)) & r2_hidden(sK1,k2_zfmisc_1(k2_tarski(sK2,sK3),k1_tarski(sK4)))),
% 23.72/3.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f13,f27])).
% 23.72/3.48  
% 23.72/3.48  fof(f52,plain,(
% 23.72/3.48    r2_hidden(sK1,k2_zfmisc_1(k2_tarski(sK2,sK3),k1_tarski(sK4)))),
% 23.72/3.48    inference(cnf_transformation,[],[f28])).
% 23.72/3.48  
% 23.72/3.48  fof(f3,axiom,(
% 23.72/3.48    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 23.72/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.72/3.48  
% 23.72/3.48  fof(f38,plain,(
% 23.72/3.48    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 23.72/3.48    inference(cnf_transformation,[],[f3])).
% 23.72/3.48  
% 23.72/3.48  fof(f4,axiom,(
% 23.72/3.48    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 23.72/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.72/3.48  
% 23.72/3.48  fof(f39,plain,(
% 23.72/3.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 23.72/3.48    inference(cnf_transformation,[],[f4])).
% 23.72/3.48  
% 23.72/3.48  fof(f5,axiom,(
% 23.72/3.48    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 23.72/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.72/3.48  
% 23.72/3.48  fof(f40,plain,(
% 23.72/3.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 23.72/3.48    inference(cnf_transformation,[],[f5])).
% 23.72/3.48  
% 23.72/3.48  fof(f55,plain,(
% 23.72/3.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 23.72/3.48    inference(definition_unfolding,[],[f39,f40])).
% 23.72/3.48  
% 23.72/3.48  fof(f56,plain,(
% 23.72/3.48    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 23.72/3.48    inference(definition_unfolding,[],[f38,f55])).
% 23.72/3.48  
% 23.72/3.48  fof(f66,plain,(
% 23.72/3.48    r2_hidden(sK1,k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK3),k2_enumset1(sK4,sK4,sK4,sK4)))),
% 23.72/3.48    inference(definition_unfolding,[],[f52,f55,f56])).
% 23.72/3.48  
% 23.72/3.48  fof(f9,axiom,(
% 23.72/3.48    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 23.72/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.72/3.48  
% 23.72/3.48  fof(f12,plain,(
% 23.72/3.48    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 23.72/3.48    inference(ennf_transformation,[],[f9])).
% 23.72/3.48  
% 23.72/3.48  fof(f50,plain,(
% 23.72/3.48    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 23.72/3.48    inference(cnf_transformation,[],[f12])).
% 23.72/3.48  
% 23.72/3.48  fof(f2,axiom,(
% 23.72/3.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 23.72/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.72/3.48  
% 23.72/3.48  fof(f19,plain,(
% 23.72/3.48    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 23.72/3.48    inference(nnf_transformation,[],[f2])).
% 23.72/3.48  
% 23.72/3.48  fof(f20,plain,(
% 23.72/3.48    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 23.72/3.48    inference(flattening,[],[f19])).
% 23.72/3.48  
% 23.72/3.48  fof(f37,plain,(
% 23.72/3.48    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 23.72/3.48    inference(cnf_transformation,[],[f20])).
% 23.72/3.48  
% 23.72/3.48  fof(f53,plain,(
% 23.72/3.48    k2_mcart_1(sK1) != sK4 | k1_mcart_1(sK1) != sK2),
% 23.72/3.48    inference(cnf_transformation,[],[f28])).
% 23.72/3.48  
% 23.72/3.48  fof(f54,plain,(
% 23.72/3.48    k2_mcart_1(sK1) != sK4 | k1_mcart_1(sK1) != sK3),
% 23.72/3.48    inference(cnf_transformation,[],[f28])).
% 23.72/3.48  
% 23.72/3.48  fof(f51,plain,(
% 23.72/3.48    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 23.72/3.48    inference(cnf_transformation,[],[f12])).
% 23.72/3.48  
% 23.72/3.48  fof(f7,axiom,(
% 23.72/3.48    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 23.72/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.72/3.48  
% 23.72/3.48  fof(f23,plain,(
% 23.72/3.48    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 23.72/3.48    inference(nnf_transformation,[],[f7])).
% 23.72/3.48  
% 23.72/3.48  fof(f24,plain,(
% 23.72/3.48    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 23.72/3.48    inference(flattening,[],[f23])).
% 23.72/3.48  
% 23.72/3.48  fof(f46,plain,(
% 23.72/3.48    ( ! [X2,X0,X1] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) )),
% 23.72/3.48    inference(cnf_transformation,[],[f24])).
% 23.72/3.48  
% 23.72/3.48  fof(f60,plain,(
% 23.72/3.48    ( ! [X2,X0,X1] : (r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))) | X0 = X2 | ~r2_hidden(X0,X1)) )),
% 23.72/3.48    inference(definition_unfolding,[],[f46,f56])).
% 23.72/3.48  
% 23.72/3.48  fof(f30,plain,(
% 23.72/3.48    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 23.72/3.48    inference(cnf_transformation,[],[f18])).
% 23.72/3.48  
% 23.72/3.48  fof(f68,plain,(
% 23.72/3.48    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 23.72/3.48    inference(equality_resolution,[],[f30])).
% 23.72/3.48  
% 23.72/3.48  fof(f8,axiom,(
% 23.72/3.48    ! [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 23.72/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.72/3.48  
% 23.72/3.48  fof(f25,plain,(
% 23.72/3.48    ! [X0,X1,X2] : ((k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) | (r2_hidden(X1,X2) | r2_hidden(X0,X2))) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)))),
% 23.72/3.48    inference(nnf_transformation,[],[f8])).
% 23.72/3.48  
% 23.72/3.48  fof(f26,plain,(
% 23.72/3.48    ! [X0,X1,X2] : ((k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)))),
% 23.72/3.48    inference(flattening,[],[f25])).
% 23.72/3.48  
% 23.72/3.48  fof(f49,plain,(
% 23.72/3.48    ( ! [X2,X0,X1] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 23.72/3.48    inference(cnf_transformation,[],[f26])).
% 23.72/3.48  
% 23.72/3.48  fof(f63,plain,(
% 23.72/3.48    ( ! [X2,X0,X1] : (k4_xboole_0(k2_enumset1(X0,X0,X0,X1),X2) = k2_enumset1(X0,X0,X0,X1) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 23.72/3.48    inference(definition_unfolding,[],[f49,f55,f55])).
% 23.72/3.48  
% 23.72/3.48  fof(f29,plain,(
% 23.72/3.48    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 23.72/3.48    inference(cnf_transformation,[],[f18])).
% 23.72/3.48  
% 23.72/3.48  fof(f69,plain,(
% 23.72/3.48    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 23.72/3.48    inference(equality_resolution,[],[f29])).
% 23.72/3.48  
% 23.72/3.48  fof(f45,plain,(
% 23.72/3.48    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 23.72/3.48    inference(cnf_transformation,[],[f24])).
% 23.72/3.48  
% 23.72/3.48  fof(f61,plain,(
% 23.72/3.48    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))) )),
% 23.72/3.48    inference(definition_unfolding,[],[f45,f56])).
% 23.72/3.48  
% 23.72/3.48  fof(f72,plain,(
% 23.72/3.48    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))) )),
% 23.72/3.48    inference(equality_resolution,[],[f61])).
% 23.72/3.48  
% 23.72/3.48  fof(f36,plain,(
% 23.72/3.48    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 23.72/3.48    inference(cnf_transformation,[],[f20])).
% 23.72/3.48  
% 23.72/3.48  fof(f70,plain,(
% 23.72/3.48    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 23.72/3.48    inference(equality_resolution,[],[f36])).
% 23.72/3.48  
% 23.72/3.48  cnf(c_1,plain,
% 23.72/3.48      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 23.72/3.48      | r2_hidden(sK0(X0,X1,X2),X2)
% 23.72/3.48      | k4_xboole_0(X0,X1) = X2 ),
% 23.72/3.48      inference(cnf_transformation,[],[f33]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_2,plain,
% 23.72/3.48      ( r2_hidden(sK0(X0,X1,X2),X0)
% 23.72/3.48      | r2_hidden(sK0(X0,X1,X2),X2)
% 23.72/3.48      | k4_xboole_0(X0,X1) = X2 ),
% 23.72/3.48      inference(cnf_transformation,[],[f32]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_4652,plain,
% 23.72/3.48      ( r2_hidden(sK0(X0,X0,X1),X1) | k4_xboole_0(X0,X0) = X1 ),
% 23.72/3.48      inference(resolution,[status(thm)],[c_1,c_2]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_296,plain,
% 23.72/3.48      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 23.72/3.48      theory(equality) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_293,plain,( X0 = X0 ),theory(equality) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_2827,plain,
% 23.72/3.48      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X1) | X2 != X0 ),
% 23.72/3.48      inference(resolution,[status(thm)],[c_296,c_293]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_7493,plain,
% 23.72/3.48      ( ~ r2_hidden(X0,X1)
% 23.72/3.48      | r2_hidden(sK0(X2,X2,X0),X0)
% 23.72/3.48      | r2_hidden(k4_xboole_0(X2,X2),X1) ),
% 23.72/3.48      inference(resolution,[status(thm)],[c_4652,c_2827]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_22,negated_conjecture,
% 23.72/3.48      ( r2_hidden(sK1,k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK3),k2_enumset1(sK4,sK4,sK4,sK4))) ),
% 23.72/3.48      inference(cnf_transformation,[],[f66]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_57419,plain,
% 23.72/3.48      ( r2_hidden(sK0(X0,X0,sK1),sK1)
% 23.72/3.48      | r2_hidden(k4_xboole_0(X0,X0),k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK3),k2_enumset1(sK4,sK4,sK4,sK4))) ),
% 23.72/3.48      inference(resolution,[status(thm)],[c_7493,c_22]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_19,plain,
% 23.72/3.48      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 23.72/3.48      | r2_hidden(k1_mcart_1(X0),X1) ),
% 23.72/3.48      inference(cnf_transformation,[],[f50]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_59670,plain,
% 23.72/3.48      ( r2_hidden(sK0(X0,X0,sK1),sK1)
% 23.72/3.48      | r2_hidden(k1_mcart_1(k4_xboole_0(X0,X0)),k2_enumset1(sK2,sK2,sK2,sK3)) ),
% 23.72/3.48      inference(resolution,[status(thm)],[c_57419,c_19]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_6,plain,
% 23.72/3.48      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 23.72/3.48      inference(cnf_transformation,[],[f37]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_2825,plain,
% 23.72/3.48      ( ~ r1_tarski(X0,X1)
% 23.72/3.48      | ~ r1_tarski(X1,X0)
% 23.72/3.48      | ~ r2_hidden(X2,X0)
% 23.72/3.48      | r2_hidden(X3,X1)
% 23.72/3.48      | X3 != X2 ),
% 23.72/3.48      inference(resolution,[status(thm)],[c_296,c_6]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_13242,plain,
% 23.72/3.48      ( ~ r1_tarski(X0,X1)
% 23.72/3.48      | ~ r1_tarski(X1,X0)
% 23.72/3.48      | ~ r2_hidden(X2,X1)
% 23.72/3.48      | r2_hidden(X2,X0) ),
% 23.72/3.48      inference(resolution,[status(thm)],[c_2825,c_293]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_60478,plain,
% 23.72/3.48      ( ~ r1_tarski(X0,k2_enumset1(sK2,sK2,sK2,sK3))
% 23.72/3.48      | ~ r1_tarski(k2_enumset1(sK2,sK2,sK2,sK3),X0)
% 23.72/3.48      | r2_hidden(sK0(X1,X1,sK1),sK1)
% 23.72/3.48      | r2_hidden(k1_mcart_1(k4_xboole_0(X1,X1)),X0) ),
% 23.72/3.48      inference(resolution,[status(thm)],[c_59670,c_13242]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_23,plain,
% 23.72/3.48      ( r2_hidden(sK1,k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK3),k2_enumset1(sK4,sK4,sK4,sK4))) = iProver_top ),
% 23.72/3.48      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_21,negated_conjecture,
% 23.72/3.48      ( k1_mcart_1(sK1) != sK2 | k2_mcart_1(sK1) != sK4 ),
% 23.72/3.48      inference(cnf_transformation,[],[f53]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_20,negated_conjecture,
% 23.72/3.48      ( k1_mcart_1(sK1) != sK3 | k2_mcart_1(sK1) != sK4 ),
% 23.72/3.48      inference(cnf_transformation,[],[f54]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_18,plain,
% 23.72/3.48      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 23.72/3.48      | r2_hidden(k2_mcart_1(X0),X2) ),
% 23.72/3.48      inference(cnf_transformation,[],[f51]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_782,plain,
% 23.72/3.48      ( r2_hidden(k2_mcart_1(sK1),k2_enumset1(sK4,sK4,sK4,sK4))
% 23.72/3.48      | ~ r2_hidden(sK1,k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK3),k2_enumset1(sK4,sK4,sK4,sK4))) ),
% 23.72/3.48      inference(instantiation,[status(thm)],[c_18]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_785,plain,
% 23.72/3.48      ( r2_hidden(k1_mcart_1(sK1),k2_enumset1(sK2,sK2,sK2,sK3))
% 23.72/3.48      | ~ r2_hidden(sK1,k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK3),k2_enumset1(sK4,sK4,sK4,sK4))) ),
% 23.72/3.48      inference(instantiation,[status(thm)],[c_19]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_786,plain,
% 23.72/3.48      ( r2_hidden(k1_mcart_1(sK1),k2_enumset1(sK2,sK2,sK2,sK3)) = iProver_top
% 23.72/3.48      | r2_hidden(sK1,k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK3),k2_enumset1(sK4,sK4,sK4,sK4))) != iProver_top ),
% 23.72/3.48      inference(predicate_to_equality,[status(thm)],[c_785]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_12,plain,
% 23.72/3.48      ( ~ r2_hidden(X0,X1)
% 23.72/3.48      | r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))
% 23.72/3.48      | X2 = X0 ),
% 23.72/3.48      inference(cnf_transformation,[],[f60]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_904,plain,
% 23.72/3.48      ( ~ r2_hidden(k2_mcart_1(sK1),k2_enumset1(sK4,sK4,sK4,sK4))
% 23.72/3.48      | r2_hidden(k2_mcart_1(sK1),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(X0,X0,X0,X0)))
% 23.72/3.48      | X0 = k2_mcart_1(sK1) ),
% 23.72/3.48      inference(instantiation,[status(thm)],[c_12]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_916,plain,
% 23.72/3.48      ( ~ r2_hidden(k2_mcart_1(sK1),k2_enumset1(sK4,sK4,sK4,sK4))
% 23.72/3.48      | r2_hidden(k2_mcart_1(sK1),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK4,sK4,sK4,sK4)))
% 23.72/3.48      | sK4 = k2_mcart_1(sK1) ),
% 23.72/3.48      inference(instantiation,[status(thm)],[c_904]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_294,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_805,plain,
% 23.72/3.48      ( k2_mcart_1(sK1) != X0 | k2_mcart_1(sK1) = sK4 | sK4 != X0 ),
% 23.72/3.48      inference(instantiation,[status(thm)],[c_294]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_969,plain,
% 23.72/3.48      ( k2_mcart_1(sK1) != k2_mcart_1(sK1)
% 23.72/3.48      | k2_mcart_1(sK1) = sK4
% 23.72/3.48      | sK4 != k2_mcart_1(sK1) ),
% 23.72/3.48      inference(instantiation,[status(thm)],[c_805]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_970,plain,
% 23.72/3.48      ( k2_mcart_1(sK1) = k2_mcart_1(sK1) ),
% 23.72/3.48      inference(instantiation,[status(thm)],[c_293]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_2801,plain,
% 23.72/3.48      ( k1_mcart_1(sK1) = k1_mcart_1(sK1) ),
% 23.72/3.48      inference(instantiation,[status(thm)],[c_293]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_4445,plain,
% 23.72/3.48      ( ~ r1_tarski(X0,k2_enumset1(sK2,sK2,sK2,sK3))
% 23.72/3.48      | ~ r1_tarski(k2_enumset1(sK2,sK2,sK2,sK3),X0)
% 23.72/3.48      | X0 = k2_enumset1(sK2,sK2,sK2,sK3) ),
% 23.72/3.48      inference(instantiation,[status(thm)],[c_6]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_935,plain,
% 23.72/3.48      ( r2_hidden(X0,X1)
% 23.72/3.48      | ~ r2_hidden(k1_mcart_1(sK1),k2_enumset1(sK2,sK2,sK2,sK3))
% 23.72/3.48      | X1 != k2_enumset1(sK2,sK2,sK2,sK3)
% 23.72/3.48      | X0 != k1_mcart_1(sK1) ),
% 23.72/3.48      inference(instantiation,[status(thm)],[c_296]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_5068,plain,
% 23.72/3.48      ( r2_hidden(k1_mcart_1(sK1),X0)
% 23.72/3.48      | ~ r2_hidden(k1_mcart_1(sK1),k2_enumset1(sK2,sK2,sK2,sK3))
% 23.72/3.48      | X0 != k2_enumset1(sK2,sK2,sK2,sK3)
% 23.72/3.48      | k1_mcart_1(sK1) != k1_mcart_1(sK1) ),
% 23.72/3.48      inference(instantiation,[status(thm)],[c_935]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_5074,plain,
% 23.72/3.48      ( X0 != k2_enumset1(sK2,sK2,sK2,sK3)
% 23.72/3.48      | k1_mcart_1(sK1) != k1_mcart_1(sK1)
% 23.72/3.48      | r2_hidden(k1_mcart_1(sK1),X0) = iProver_top
% 23.72/3.48      | r2_hidden(k1_mcart_1(sK1),k2_enumset1(sK2,sK2,sK2,sK3)) != iProver_top ),
% 23.72/3.48      inference(predicate_to_equality,[status(thm)],[c_5068]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_4,plain,
% 23.72/3.48      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 23.72/3.48      inference(cnf_transformation,[],[f68]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_3106,plain,
% 23.72/3.48      ( ~ r2_hidden(k2_mcart_1(X0),X1)
% 23.72/3.48      | ~ r2_hidden(k2_mcart_1(X0),k4_xboole_0(X2,X1)) ),
% 23.72/3.48      inference(instantiation,[status(thm)],[c_4]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_7141,plain,
% 23.72/3.48      ( ~ r2_hidden(k2_mcart_1(sK1),k2_enumset1(X0,X0,X0,X0))
% 23.72/3.48      | ~ r2_hidden(k2_mcart_1(sK1),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(X0,X0,X0,X0))) ),
% 23.72/3.48      inference(instantiation,[status(thm)],[c_3106]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_7143,plain,
% 23.72/3.48      ( ~ r2_hidden(k2_mcart_1(sK1),k2_enumset1(sK4,sK4,sK4,sK4))
% 23.72/3.48      | ~ r2_hidden(k2_mcart_1(sK1),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK4,sK4,sK4,sK4))) ),
% 23.72/3.48      inference(instantiation,[status(thm)],[c_7141]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_613,plain,
% 23.72/3.48      ( r2_hidden(sK1,k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK3),k2_enumset1(sK4,sK4,sK4,sK4))) = iProver_top ),
% 23.72/3.48      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_614,plain,
% 23.72/3.48      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 23.72/3.48      | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
% 23.72/3.48      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_880,plain,
% 23.72/3.48      ( r2_hidden(k1_mcart_1(sK1),k2_enumset1(sK2,sK2,sK2,sK3)) = iProver_top ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_613,c_614]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_621,plain,
% 23.72/3.48      ( X0 = X1
% 23.72/3.48      | r2_hidden(X1,X2) != iProver_top
% 23.72/3.48      | r2_hidden(X1,k4_xboole_0(X2,k2_enumset1(X0,X0,X0,X0))) = iProver_top ),
% 23.72/3.48      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_15,plain,
% 23.72/3.48      ( r2_hidden(X0,X1)
% 23.72/3.48      | r2_hidden(X2,X1)
% 23.72/3.48      | k4_xboole_0(k2_enumset1(X0,X0,X0,X2),X1) = k2_enumset1(X0,X0,X0,X2) ),
% 23.72/3.48      inference(cnf_transformation,[],[f63]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_618,plain,
% 23.72/3.48      ( k4_xboole_0(k2_enumset1(X0,X0,X0,X1),X2) = k2_enumset1(X0,X0,X0,X1)
% 23.72/3.48      | r2_hidden(X0,X2) = iProver_top
% 23.72/3.48      | r2_hidden(X1,X2) = iProver_top ),
% 23.72/3.48      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_5,plain,
% 23.72/3.48      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 23.72/3.48      inference(cnf_transformation,[],[f69]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_627,plain,
% 23.72/3.48      ( r2_hidden(X0,X1) = iProver_top
% 23.72/3.48      | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
% 23.72/3.48      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_1778,plain,
% 23.72/3.48      ( k4_xboole_0(k2_enumset1(X0,X0,X0,X1),k4_xboole_0(X2,X3)) = k2_enumset1(X0,X0,X0,X1)
% 23.72/3.48      | r2_hidden(X1,X2) = iProver_top
% 23.72/3.48      | r2_hidden(X0,k4_xboole_0(X2,X3)) = iProver_top ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_618,c_627]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_13,plain,
% 23.72/3.48      ( ~ r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0))) ),
% 23.72/3.48      inference(cnf_transformation,[],[f72]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_620,plain,
% 23.72/3.48      ( r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0))) != iProver_top ),
% 23.72/3.48      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_3482,plain,
% 23.72/3.48      ( k4_xboole_0(k2_enumset1(X0,X0,X0,X1),k4_xboole_0(X2,k2_enumset1(X0,X0,X0,X0))) = k2_enumset1(X0,X0,X0,X1)
% 23.72/3.48      | r2_hidden(X1,X2) = iProver_top ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_1778,c_620]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_7359,plain,
% 23.72/3.48      ( k4_xboole_0(k2_enumset1(X0,X0,X0,X1),k4_xboole_0(k4_xboole_0(X2,k2_enumset1(X1,X1,X1,X1)),k2_enumset1(X0,X0,X0,X0))) = k2_enumset1(X0,X0,X0,X1) ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_3482,c_620]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_628,plain,
% 23.72/3.48      ( r2_hidden(X0,X1) != iProver_top
% 23.72/3.48      | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 23.72/3.48      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_7802,plain,
% 23.72/3.48      ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X2)) != iProver_top
% 23.72/3.48      | r2_hidden(X0,k4_xboole_0(k4_xboole_0(X3,k2_enumset1(X2,X2,X2,X2)),k2_enumset1(X1,X1,X1,X1))) != iProver_top ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_7359,c_628]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_78152,plain,
% 23.72/3.48      ( X0 = X1
% 23.72/3.48      | r2_hidden(X0,k2_enumset1(X1,X1,X1,X2)) != iProver_top
% 23.72/3.48      | r2_hidden(X0,k4_xboole_0(X3,k2_enumset1(X2,X2,X2,X2))) != iProver_top ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_621,c_7802]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_80901,plain,
% 23.72/3.48      ( X0 = X1
% 23.72/3.48      | X2 = X0
% 23.72/3.48      | r2_hidden(X0,X3) != iProver_top
% 23.72/3.48      | r2_hidden(X0,k2_enumset1(X2,X2,X2,X1)) != iProver_top ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_621,c_78152]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_82788,plain,
% 23.72/3.48      ( k1_mcart_1(sK1) = sK2
% 23.72/3.48      | k1_mcart_1(sK1) = sK3
% 23.72/3.48      | r2_hidden(k1_mcart_1(sK1),X0) != iProver_top ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_880,c_80901]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_88431,plain,
% 23.72/3.48      ( ~ r1_tarski(X0,k2_enumset1(sK2,sK2,sK2,sK3))
% 23.72/3.48      | ~ r1_tarski(k2_enumset1(sK2,sK2,sK2,sK3),X0) ),
% 23.72/3.48      inference(global_propositional_subsumption,
% 23.72/3.48                [status(thm)],
% 23.72/3.48                [c_60478,c_22,c_23,c_21,c_20,c_782,c_786,c_916,c_969,
% 23.72/3.48                 c_970,c_2801,c_4445,c_5074,c_7143,c_82788]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_7,plain,
% 23.72/3.48      ( r1_tarski(X0,X0) ),
% 23.72/3.48      inference(cnf_transformation,[],[f70]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_88449,plain,
% 23.72/3.48      ( ~ r1_tarski(k2_enumset1(sK2,sK2,sK2,sK3),k2_enumset1(sK2,sK2,sK2,sK3)) ),
% 23.72/3.48      inference(resolution,[status(thm)],[c_88431,c_7]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_852,plain,
% 23.72/3.48      ( r1_tarski(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1)) ),
% 23.72/3.48      inference(instantiation,[status(thm)],[c_7]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_6308,plain,
% 23.72/3.48      ( r1_tarski(k2_enumset1(sK2,sK2,sK2,sK3),k2_enumset1(sK2,sK2,sK2,sK3)) ),
% 23.72/3.48      inference(instantiation,[status(thm)],[c_852]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(contradiction,plain,
% 23.72/3.48      ( $false ),
% 23.72/3.48      inference(minisat,[status(thm)],[c_88449,c_6308]) ).
% 23.72/3.48  
% 23.72/3.48  
% 23.72/3.48  % SZS output end CNFRefutation for theBenchmark.p
% 23.72/3.48  
% 23.72/3.48  ------                               Statistics
% 23.72/3.48  
% 23.72/3.48  ------ Selected
% 23.72/3.48  
% 23.72/3.48  total_time:                             2.792
% 23.72/3.48  
%------------------------------------------------------------------------------
