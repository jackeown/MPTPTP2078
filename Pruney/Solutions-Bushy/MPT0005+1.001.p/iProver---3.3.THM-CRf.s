%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0005+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:13 EST 2020

% Result     : Theorem 0.74s
% Output     : CNFRefutation 0.74s
% Verified   : 
% Statistics : Number of formulae       :   36 (  51 expanded)
%              Number of clauses        :   13 (  13 expanded)
%              Number of leaves         :    6 (  12 expanded)
%              Depth                    :    9
%              Number of atoms          :  179 ( 287 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f9,plain,(
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
    inference(flattening,[],[f8])).

fof(f10,plain,(
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
    inference(rectify,[],[f9])).

fof(f11,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & ~ r2_hidden(sK0(X0,X1,X2),X0) )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( r2_hidden(sK0(X0,X1,X2),X1)
          | r2_hidden(sK0(X0,X1,X2),X0)
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & ~ r2_hidden(sK0(X0,X1,X2),X0) )
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( r2_hidden(sK0(X0,X1,X2),X1)
            | r2_hidden(sK0(X0,X1,X2),X0)
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f11])).

fof(f17,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f32,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f17])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f6,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f13,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f6,f13])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( ~ r2_hidden(X2,X0)
            & r2_hidden(X2,X1) )
        & ~ ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) )
        & r2_hidden(X2,k2_xboole_0(X0,X1))
        & r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( ~ r2_hidden(X2,X0)
              & r2_hidden(X2,X1) )
          & ~ ( ~ r2_hidden(X2,X1)
              & r2_hidden(X2,X0) )
          & r2_hidden(X2,k2_xboole_0(X0,X1))
          & r1_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X2,X0)
        | ~ r2_hidden(X2,X1) )
      & ( r2_hidden(X2,X1)
        | ~ r2_hidden(X2,X0) )
      & r2_hidden(X2,k2_xboole_0(X0,X1))
      & r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
        & ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
        & r2_hidden(X2,k2_xboole_0(X0,X1))
        & r1_xboole_0(X0,X1) )
   => ( ( r2_hidden(sK4,sK2)
        | ~ r2_hidden(sK4,sK3) )
      & ( r2_hidden(sK4,sK3)
        | ~ r2_hidden(sK4,sK2) )
      & r2_hidden(sK4,k2_xboole_0(sK2,sK3))
      & r1_xboole_0(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ( r2_hidden(sK4,sK2)
      | ~ r2_hidden(sK4,sK3) )
    & ( r2_hidden(sK4,sK3)
      | ~ r2_hidden(sK4,sK2) )
    & r2_hidden(sK4,k2_xboole_0(sK2,sK3))
    & r1_xboole_0(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f7,f15])).

fof(f26,plain,(
    r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f28,plain,
    ( r2_hidden(sK4,sK3)
    | ~ r2_hidden(sK4,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f29,plain,
    ( r2_hidden(sK4,sK2)
    | ~ r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f27,plain,(
    r2_hidden(sK4,k2_xboole_0(sK2,sK3)) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_561,plain,
    ( ~ r2_hidden(sK4,k2_xboole_0(sK2,sK3))
    | r2_hidden(sK4,sK3)
    | r2_hidden(sK4,sK2) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_6,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_12,negated_conjecture,
    ( r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_198,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | sK3 != X1
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_12])).

cnf(c_199,plain,
    ( ~ r2_hidden(X0,sK3)
    | ~ r2_hidden(X0,sK2) ),
    inference(unflattening,[status(thm)],[c_198])).

cnf(c_10,negated_conjecture,
    ( r2_hidden(sK4,sK3)
    | ~ r2_hidden(sK4,sK2) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_98,plain,
    ( ~ r2_hidden(sK4,sK2)
    | r2_hidden(sK4,sK3) ),
    inference(prop_impl,[status(thm)],[c_10])).

cnf(c_99,plain,
    ( r2_hidden(sK4,sK3)
    | ~ r2_hidden(sK4,sK2) ),
    inference(renaming,[status(thm)],[c_98])).

cnf(c_217,plain,
    ( ~ r2_hidden(sK4,sK2) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_199,c_99])).

cnf(c_9,negated_conjecture,
    ( ~ r2_hidden(sK4,sK3)
    | r2_hidden(sK4,sK2) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_11,negated_conjecture,
    ( r2_hidden(sK4,k2_xboole_0(sK2,sK3)) ),
    inference(cnf_transformation,[],[f27])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_561,c_217,c_9,c_11])).


%------------------------------------------------------------------------------
