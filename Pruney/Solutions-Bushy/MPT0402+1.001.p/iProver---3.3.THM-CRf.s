%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0402+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:13 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 119 expanded)
%              Number of clauses        :   24 (  28 expanded)
%              Number of leaves         :   10 (  33 expanded)
%              Depth                    :   10
%              Number of atoms          :  248 ( 502 expanded)
%              Number of equality atoms :   58 (  90 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f18,plain,(
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
    inference(rectify,[],[f17])).

fof(f19,plain,(
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

fof(f20,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f19])).

fof(f30,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f47,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f30])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
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

fof(f11,plain,(
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
    inference(rectify,[],[f10])).

fof(f12,plain,(
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

fof(f13,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f12])).

fof(f24,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f44,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f24])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
     => ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ? [X3] :
              ( r1_tarski(X2,X3)
              & r2_hidden(X3,X1) )
          | ~ r2_hidden(X2,X0) )
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f14,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( r1_tarski(X2,X3)
          & r2_hidden(X3,X1) )
     => ( r1_tarski(X2,sK1(X1,X2))
        & r2_hidden(sK1(X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X2,sK1(X1,X2))
            & r2_hidden(sK1(X1,X2),X1) )
          | ~ r2_hidden(X2,X0) )
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f8,f14])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK1(X1,X2),X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( r1_setfam_1(X2,k2_tarski(X0,X1))
     => ! [X3] :
          ~ ( ~ r1_tarski(X3,X1)
            & ~ r1_tarski(X3,X0)
            & r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_setfam_1(X2,k2_tarski(X0,X1))
       => ! [X3] :
            ~ ( ~ r1_tarski(X3,X1)
              & ~ r1_tarski(X3,X0)
              & r2_hidden(X3,X2) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(X3,X1)
          & ~ r1_tarski(X3,X0)
          & r2_hidden(X3,X2) )
      & r1_setfam_1(X2,k2_tarski(X0,X1)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r1_tarski(X3,X1)
          & ~ r1_tarski(X3,X0)
          & r2_hidden(X3,X2) )
     => ( ~ r1_tarski(sK6,X1)
        & ~ r1_tarski(sK6,X0)
        & r2_hidden(sK6,X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r1_tarski(X3,X1)
            & ~ r1_tarski(X3,X0)
            & r2_hidden(X3,X2) )
        & r1_setfam_1(X2,k2_tarski(X0,X1)) )
   => ( ? [X3] :
          ( ~ r1_tarski(X3,sK4)
          & ~ r1_tarski(X3,sK3)
          & r2_hidden(X3,sK5) )
      & r1_setfam_1(sK5,k2_tarski(sK3,sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ~ r1_tarski(sK6,sK4)
    & ~ r1_tarski(sK6,sK3)
    & r2_hidden(sK6,sK5)
    & r1_setfam_1(sK5,k2_tarski(sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f9,f22,f21])).

fof(f37,plain,(
    r1_setfam_1(sK5,k2_tarski(sK3,sK4)) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f41,plain,(
    r1_setfam_1(sK5,k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))) ),
    inference(definition_unfolding,[],[f37,f36])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,sK1(X1,X2))
      | ~ r2_hidden(X2,X0)
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f40,plain,(
    ~ r1_tarski(sK6,sK4) ),
    inference(cnf_transformation,[],[f23])).

fof(f39,plain,(
    ~ r1_tarski(sK6,sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f38,plain,(
    r2_hidden(sK6,sK5) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_11,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_666,plain,
    ( ~ r2_hidden(sK1(k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),X0),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)))
    | r2_hidden(sK1(k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),X0),k1_tarski(sK3))
    | r2_hidden(sK1(k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),X0),k1_tarski(sK4)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_668,plain,
    ( ~ r2_hidden(sK1(k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),sK6),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)))
    | r2_hidden(sK1(k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),sK6),k1_tarski(sK3))
    | r2_hidden(sK1(k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),sK6),k1_tarski(sK4)) ),
    inference(instantiation,[status(thm)],[c_666])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_633,plain,
    ( ~ r2_hidden(sK1(k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),sK6),k1_tarski(sK4))
    | sK1(k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),sK6) = sK4 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_630,plain,
    ( ~ r2_hidden(sK1(k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),sK6),k1_tarski(sK3))
    | sK1(k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),sK6) = sK3 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_5,plain,
    ( ~ r1_setfam_1(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(sK1(X1,X2),X1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_15,negated_conjecture,
    ( r1_setfam_1(sK5,k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_229,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK1(X2,X0),X2)
    | k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)) != X2
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_15])).

cnf(c_230,plain,
    ( ~ r2_hidden(X0,sK5)
    | r2_hidden(sK1(k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),X0),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))) ),
    inference(unflattening,[status(thm)],[c_229])).

cnf(c_232,plain,
    ( r2_hidden(sK1(k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),sK6),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)))
    | ~ r2_hidden(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_230])).

cnf(c_4,plain,
    ( ~ r1_setfam_1(X0,X1)
    | r1_tarski(X2,sK1(X1,X2))
    | ~ r2_hidden(X2,X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_12,negated_conjecture,
    ( ~ r1_tarski(sK6,sK4) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_175,plain,
    ( ~ r1_setfam_1(X0,X1)
    | ~ r2_hidden(X2,X0)
    | sK1(X1,X2) != sK4
    | sK6 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_12])).

cnf(c_176,plain,
    ( ~ r1_setfam_1(X0,X1)
    | ~ r2_hidden(sK6,X0)
    | sK1(X1,sK6) != sK4 ),
    inference(unflattening,[status(thm)],[c_175])).

cnf(c_221,plain,
    ( ~ r2_hidden(sK6,X0)
    | k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)) != X1
    | sK1(X1,sK6) != sK4
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_176,c_15])).

cnf(c_222,plain,
    ( ~ r2_hidden(sK6,sK5)
    | sK1(k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),sK6) != sK4 ),
    inference(unflattening,[status(thm)],[c_221])).

cnf(c_13,negated_conjecture,
    ( ~ r1_tarski(sK6,sK3) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_190,plain,
    ( ~ r1_setfam_1(X0,X1)
    | ~ r2_hidden(X2,X0)
    | sK1(X1,X2) != sK3
    | sK6 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_13])).

cnf(c_191,plain,
    ( ~ r1_setfam_1(X0,X1)
    | ~ r2_hidden(sK6,X0)
    | sK1(X1,sK6) != sK3 ),
    inference(unflattening,[status(thm)],[c_190])).

cnf(c_213,plain,
    ( ~ r2_hidden(sK6,X0)
    | k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)) != X1
    | sK1(X1,sK6) != sK3
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_191,c_15])).

cnf(c_214,plain,
    ( ~ r2_hidden(sK6,sK5)
    | sK1(k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),sK6) != sK3 ),
    inference(unflattening,[status(thm)],[c_213])).

cnf(c_14,negated_conjecture,
    ( r2_hidden(sK6,sK5) ),
    inference(cnf_transformation,[],[f38])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_668,c_633,c_630,c_232,c_222,c_214,c_14])).


%------------------------------------------------------------------------------
