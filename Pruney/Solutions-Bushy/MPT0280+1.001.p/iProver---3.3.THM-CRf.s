%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0280+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:54 EST 2020

% Result     : Theorem 6.93s
% Output     : CNFRefutation 6.93s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 116 expanded)
%              Number of clauses        :   28 (  32 expanded)
%              Number of leaves         :   10 (  24 expanded)
%              Depth                    :   11
%              Number of atoms          :  253 ( 536 expanded)
%              Number of equality atoms :   20 (  44 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f17])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f19])).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f13])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK0(X0,X1),X0)
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( r1_tarski(sK0(X0,X1),X0)
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK0(X0,X1),X0)
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( r1_tarski(sK0(X0,X1),X0)
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f15])).

fof(f29,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f46,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f29])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f21])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f22])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & ~ r2_hidden(sK2(X0,X1,X2),X0) )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( r2_hidden(sK2(X0,X1,X2),X1)
          | r2_hidden(sK2(X0,X1,X2),X0)
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & ~ r2_hidden(sK2(X0,X1,X2),X0) )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( r2_hidden(sK2(X0,X1,X2),X1)
            | r2_hidden(sK2(X0,X1,X2),X0)
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f23,f24])).

fof(f36,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f49,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f36])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f47,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f38])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f10])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f30,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f45,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f30])).

fof(f7,conjecture,(
    ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1))) ),
    inference(negated_conjecture,[],[f7])).

fof(f12,plain,(
    ? [X0,X1] : ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1))) ),
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,
    ( ? [X0,X1] : ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1)))
   => ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(sK3),k1_zfmisc_1(sK4)),k1_zfmisc_1(k2_xboole_0(sK3,sK4))) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(sK3),k1_zfmisc_1(sK4)),k1_zfmisc_1(k2_xboole_0(sK3,sK4))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f12,f26])).

fof(f44,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(sK3),k1_zfmisc_1(sK4)),k1_zfmisc_1(k2_xboole_0(sK3,sK4))) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_2740,plain,
    ( r2_hidden(sK1(sK1(k2_xboole_0(k1_zfmisc_1(sK3),k1_zfmisc_1(sK4)),k1_zfmisc_1(k2_xboole_0(sK3,sK4))),k2_xboole_0(sK3,sK4)),X0)
    | ~ r2_hidden(sK1(sK1(k2_xboole_0(k1_zfmisc_1(sK3),k1_zfmisc_1(sK4)),k1_zfmisc_1(k2_xboole_0(sK3,sK4))),k2_xboole_0(sK3,sK4)),sK1(k2_xboole_0(k1_zfmisc_1(sK3),k1_zfmisc_1(sK4)),k1_zfmisc_1(k2_xboole_0(sK3,sK4))))
    | ~ r1_tarski(sK1(k2_xboole_0(k1_zfmisc_1(sK3),k1_zfmisc_1(sK4)),k1_zfmisc_1(k2_xboole_0(sK3,sK4))),X0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_23412,plain,
    ( ~ r2_hidden(sK1(sK1(k2_xboole_0(k1_zfmisc_1(sK3),k1_zfmisc_1(sK4)),k1_zfmisc_1(k2_xboole_0(sK3,sK4))),k2_xboole_0(sK3,sK4)),sK1(k2_xboole_0(k1_zfmisc_1(sK3),k1_zfmisc_1(sK4)),k1_zfmisc_1(k2_xboole_0(sK3,sK4))))
    | r2_hidden(sK1(sK1(k2_xboole_0(k1_zfmisc_1(sK3),k1_zfmisc_1(sK4)),k1_zfmisc_1(k2_xboole_0(sK3,sK4))),k2_xboole_0(sK3,sK4)),sK4)
    | ~ r1_tarski(sK1(k2_xboole_0(k1_zfmisc_1(sK3),k1_zfmisc_1(sK4)),k1_zfmisc_1(k2_xboole_0(sK3,sK4))),sK4) ),
    inference(instantiation,[status(thm)],[c_2740])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2443,plain,
    ( ~ r2_hidden(sK1(k2_xboole_0(k1_zfmisc_1(sK3),k1_zfmisc_1(sK4)),k1_zfmisc_1(k2_xboole_0(sK3,sK4))),k1_zfmisc_1(X0))
    | r1_tarski(sK1(k2_xboole_0(k1_zfmisc_1(sK3),k1_zfmisc_1(sK4)),k1_zfmisc_1(k2_xboole_0(sK3,sK4))),X0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_9395,plain,
    ( ~ r2_hidden(sK1(k2_xboole_0(k1_zfmisc_1(sK3),k1_zfmisc_1(sK4)),k1_zfmisc_1(k2_xboole_0(sK3,sK4))),k1_zfmisc_1(sK4))
    | r1_tarski(sK1(k2_xboole_0(k1_zfmisc_1(sK3),k1_zfmisc_1(sK4)),k1_zfmisc_1(k2_xboole_0(sK3,sK4))),sK4) ),
    inference(instantiation,[status(thm)],[c_2443])).

cnf(c_13,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_788,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k2_xboole_0(X1,k1_zfmisc_1(X2)))
    | r2_hidden(X0,k1_zfmisc_1(X2)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1977,plain,
    ( r2_hidden(sK1(k2_xboole_0(k1_zfmisc_1(sK3),k1_zfmisc_1(sK4)),k1_zfmisc_1(k2_xboole_0(sK3,sK4))),X0)
    | ~ r2_hidden(sK1(k2_xboole_0(k1_zfmisc_1(sK3),k1_zfmisc_1(sK4)),k1_zfmisc_1(k2_xboole_0(sK3,sK4))),k2_xboole_0(X0,k1_zfmisc_1(X1)))
    | r2_hidden(sK1(k2_xboole_0(k1_zfmisc_1(sK3),k1_zfmisc_1(sK4)),k1_zfmisc_1(k2_xboole_0(sK3,sK4))),k1_zfmisc_1(X1)) ),
    inference(instantiation,[status(thm)],[c_788])).

cnf(c_5844,plain,
    ( ~ r2_hidden(sK1(k2_xboole_0(k1_zfmisc_1(sK3),k1_zfmisc_1(sK4)),k1_zfmisc_1(k2_xboole_0(sK3,sK4))),k2_xboole_0(k1_zfmisc_1(sK3),k1_zfmisc_1(sK4)))
    | r2_hidden(sK1(k2_xboole_0(k1_zfmisc_1(sK3),k1_zfmisc_1(sK4)),k1_zfmisc_1(k2_xboole_0(sK3,sK4))),k1_zfmisc_1(sK4))
    | r2_hidden(sK1(k2_xboole_0(k1_zfmisc_1(sK3),k1_zfmisc_1(sK4)),k1_zfmisc_1(k2_xboole_0(sK3,sK4))),k1_zfmisc_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_1977])).

cnf(c_2445,plain,
    ( ~ r2_hidden(sK1(k2_xboole_0(k1_zfmisc_1(sK3),k1_zfmisc_1(sK4)),k1_zfmisc_1(k2_xboole_0(sK3,sK4))),k1_zfmisc_1(sK3))
    | r1_tarski(sK1(k2_xboole_0(k1_zfmisc_1(sK3),k1_zfmisc_1(sK4)),k1_zfmisc_1(k2_xboole_0(sK3,sK4))),sK3) ),
    inference(instantiation,[status(thm)],[c_2443])).

cnf(c_15,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1556,plain,
    ( r1_tarski(sK3,k2_xboole_0(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1509,plain,
    ( r2_hidden(sK1(sK1(k2_xboole_0(k1_zfmisc_1(sK3),k1_zfmisc_1(sK4)),k1_zfmisc_1(k2_xboole_0(sK3,sK4))),k2_xboole_0(sK3,sK4)),k2_xboole_0(sK3,sK4))
    | ~ r2_hidden(sK1(sK1(k2_xboole_0(k1_zfmisc_1(sK3),k1_zfmisc_1(sK4)),k1_zfmisc_1(k2_xboole_0(sK3,sK4))),k2_xboole_0(sK3,sK4)),sK4) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_903,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(sK3,sK4))
    | ~ r1_tarski(sK1(k2_xboole_0(k1_zfmisc_1(sK3),k1_zfmisc_1(sK4)),k1_zfmisc_1(k2_xboole_0(sK3,sK4))),X0)
    | r1_tarski(sK1(k2_xboole_0(k1_zfmisc_1(sK3),k1_zfmisc_1(sK4)),k1_zfmisc_1(k2_xboole_0(sK3,sK4))),k2_xboole_0(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_905,plain,
    ( r1_tarski(sK1(k2_xboole_0(k1_zfmisc_1(sK3),k1_zfmisc_1(sK4)),k1_zfmisc_1(k2_xboole_0(sK3,sK4))),k2_xboole_0(sK3,sK4))
    | ~ r1_tarski(sK1(k2_xboole_0(k1_zfmisc_1(sK3),k1_zfmisc_1(sK4)),k1_zfmisc_1(k2_xboole_0(sK3,sK4))),sK3)
    | ~ r1_tarski(sK3,k2_xboole_0(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_903])).

cnf(c_6,plain,
    ( r2_hidden(sK1(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_894,plain,
    ( r2_hidden(sK1(sK1(k2_xboole_0(k1_zfmisc_1(sK3),k1_zfmisc_1(sK4)),k1_zfmisc_1(k2_xboole_0(sK3,sK4))),k2_xboole_0(sK3,sK4)),sK1(k2_xboole_0(k1_zfmisc_1(sK3),k1_zfmisc_1(sK4)),k1_zfmisc_1(k2_xboole_0(sK3,sK4))))
    | r1_tarski(sK1(k2_xboole_0(k1_zfmisc_1(sK3),k1_zfmisc_1(sK4)),k1_zfmisc_1(k2_xboole_0(sK3,sK4))),k2_xboole_0(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_5,plain,
    ( ~ r2_hidden(sK1(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_895,plain,
    ( ~ r2_hidden(sK1(sK1(k2_xboole_0(k1_zfmisc_1(sK3),k1_zfmisc_1(sK4)),k1_zfmisc_1(k2_xboole_0(sK3,sK4))),k2_xboole_0(sK3,sK4)),k2_xboole_0(sK3,sK4))
    | r1_tarski(sK1(k2_xboole_0(k1_zfmisc_1(sK3),k1_zfmisc_1(sK4)),k1_zfmisc_1(k2_xboole_0(sK3,sK4))),k2_xboole_0(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_765,plain,
    ( r2_hidden(sK1(k2_xboole_0(k1_zfmisc_1(sK3),k1_zfmisc_1(sK4)),k1_zfmisc_1(k2_xboole_0(sK3,sK4))),k1_zfmisc_1(k2_xboole_0(sK3,sK4)))
    | ~ r1_tarski(sK1(k2_xboole_0(k1_zfmisc_1(sK3),k1_zfmisc_1(sK4)),k1_zfmisc_1(k2_xboole_0(sK3,sK4))),k2_xboole_0(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_719,plain,
    ( r2_hidden(sK1(k2_xboole_0(k1_zfmisc_1(sK3),k1_zfmisc_1(sK4)),k1_zfmisc_1(k2_xboole_0(sK3,sK4))),k2_xboole_0(k1_zfmisc_1(sK3),k1_zfmisc_1(sK4)))
    | r1_tarski(k2_xboole_0(k1_zfmisc_1(sK3),k1_zfmisc_1(sK4)),k1_zfmisc_1(k2_xboole_0(sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_716,plain,
    ( ~ r2_hidden(sK1(k2_xboole_0(k1_zfmisc_1(sK3),k1_zfmisc_1(sK4)),k1_zfmisc_1(k2_xboole_0(sK3,sK4))),k1_zfmisc_1(k2_xboole_0(sK3,sK4)))
    | r1_tarski(k2_xboole_0(k1_zfmisc_1(sK3),k1_zfmisc_1(sK4)),k1_zfmisc_1(k2_xboole_0(sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_16,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(sK3),k1_zfmisc_1(sK4)),k1_zfmisc_1(k2_xboole_0(sK3,sK4))) ),
    inference(cnf_transformation,[],[f44])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_23412,c_9395,c_5844,c_2445,c_1556,c_1509,c_905,c_894,c_895,c_765,c_719,c_716,c_16])).


%------------------------------------------------------------------------------
