%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0265+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:52 EST 2020

% Result     : Theorem 3.62s
% Output     : CNFRefutation 3.62s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 838 expanded)
%              Number of clauses        :   48 ( 244 expanded)
%              Number of leaves         :   13 ( 206 expanded)
%              Depth                    :   19
%              Number of atoms          :  373 (4866 expanded)
%              Number of equality atoms :  181 (2132 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f20,plain,(
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
    inference(rectify,[],[f19])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f21])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,X1)
     => ( k3_xboole_0(k2_tarski(X0,X2),X1) = k1_tarski(X0)
        | ( X0 != X2
          & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,X1)
       => ( k3_xboole_0(k2_tarski(X0,X2),X1) = k1_tarski(X0)
          | ( X0 != X2
            & r2_hidden(X2,X1) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( k3_xboole_0(k2_tarski(X0,X2),X1) != k1_tarski(X0)
      & ( X0 = X2
        | ~ r2_hidden(X2,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( k3_xboole_0(k2_tarski(X0,X2),X1) != k1_tarski(X0)
      & ( X0 = X2
        | ~ r2_hidden(X2,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f7])).

fof(f23,plain,
    ( ? [X0,X1,X2] :
        ( k3_xboole_0(k2_tarski(X0,X2),X1) != k1_tarski(X0)
        & ( X0 = X2
          | ~ r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) )
   => ( k3_xboole_0(k2_tarski(sK3,sK5),sK4) != k1_tarski(sK3)
      & ( sK3 = sK5
        | ~ r2_hidden(sK5,sK4) )
      & r2_hidden(sK3,sK4) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( k3_xboole_0(k2_tarski(sK3,sK5),sK4) != k1_tarski(sK3)
    & ( sK3 = sK5
      | ~ r2_hidden(sK5,sK4) )
    & r2_hidden(sK3,sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f8,f23])).

fof(f44,plain,(
    k3_xboole_0(k2_tarski(sK3,sK5),sK4) != k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f10,plain,(
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
    inference(rectify,[],[f9])).

fof(f11,plain,(
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

fof(f12,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f11])).

fof(f27,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f45,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f27])).

fof(f46,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f45])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f3])).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f13])).

fof(f15,plain,(
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
    inference(rectify,[],[f14])).

fof(f16,plain,(
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

fof(f17,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f16])).

fof(f30,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f52,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_tarski(X0,X1)) ) ),
    inference(equality_resolution,[],[f30])).

fof(f26,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f47,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f26])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f42,plain,(
    r2_hidden(sK3,sK4) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f43,plain,
    ( sK3 = sK5
    | ~ r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f24])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f31,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f50,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f31])).

fof(f51,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f50])).

cnf(c_206,plain,
    ( X0 != X1
    | X2 != X3
    | k2_tarski(X0,X2) = k2_tarski(X1,X3) ),
    theory(equality)).

cnf(c_205,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_4384,plain,
    ( ~ r2_hidden(X0,k2_tarski(X1,X2))
    | r2_hidden(X3,k2_tarski(X4,X5))
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    inference(resolution,[status(thm)],[c_206,c_205])).

cnf(c_13,plain,
    ( r2_hidden(sK2(X0,X1,X2),X0)
    | r2_hidden(sK2(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_17,negated_conjecture,
    ( k3_xboole_0(k2_tarski(sK3,sK5),sK4) != k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_3056,plain,
    ( r2_hidden(sK2(k2_tarski(sK3,sK5),sK4,k1_tarski(sK3)),k2_tarski(sK3,sK5))
    | r2_hidden(sK2(k2_tarski(sK3,sK5),sK4,k1_tarski(sK3)),k1_tarski(sK3)) ),
    inference(resolution,[status(thm)],[c_13,c_17])).

cnf(c_13428,plain,
    ( r2_hidden(X0,k2_tarski(X1,X2))
    | r2_hidden(sK2(k2_tarski(sK3,sK5),sK4,k1_tarski(sK3)),k1_tarski(sK3))
    | X0 != sK2(k2_tarski(sK3,sK5),sK4,k1_tarski(sK3))
    | X2 != sK5
    | X1 != sK3 ),
    inference(resolution,[status(thm)],[c_4384,c_3056])).

cnf(c_3,plain,
    ( r2_hidden(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_54,plain,
    ( r2_hidden(sK3,k1_tarski(sK3)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k2_tarski(X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_3229,plain,
    ( r2_hidden(sK2(k2_tarski(sK3,sK5),sK4,k1_tarski(sK3)),k1_tarski(sK3))
    | sK2(k2_tarski(sK3,sK5),sK4,k1_tarski(sK3)) = sK5
    | sK2(k2_tarski(sK3,sK5),sK4,k1_tarski(sK3)) = sK3 ),
    inference(resolution,[status(thm)],[c_3056,c_10])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_3340,plain,
    ( sK2(k2_tarski(sK3,sK5),sK4,k1_tarski(sK3)) = sK5
    | sK2(k2_tarski(sK3,sK5),sK4,k1_tarski(sK3)) = sK3 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3229,c_4])).

cnf(c_3354,plain,
    ( r2_hidden(X0,sK2(k2_tarski(sK3,sK5),sK4,k1_tarski(sK3)))
    | ~ r2_hidden(X1,sK5)
    | X0 != X1
    | sK2(k2_tarski(sK3,sK5),sK4,k1_tarski(sK3)) = sK3 ),
    inference(resolution,[status(thm)],[c_3340,c_205])).

cnf(c_3656,plain,
    ( r2_hidden(X0,sK2(k2_tarski(sK3,sK5),sK4,k1_tarski(sK3)))
    | ~ r2_hidden(X0,k1_tarski(X1))
    | ~ r2_hidden(X1,sK5)
    | sK2(k2_tarski(sK3,sK5),sK4,k1_tarski(sK3)) = sK3 ),
    inference(resolution,[status(thm)],[c_3354,c_4])).

cnf(c_12,plain,
    ( r2_hidden(sK2(X0,X1,X2),X1)
    | r2_hidden(sK2(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_3016,plain,
    ( r2_hidden(sK2(k2_tarski(sK3,sK5),sK4,k1_tarski(sK3)),k1_tarski(sK3))
    | r2_hidden(sK2(k2_tarski(sK3,sK5),sK4,k1_tarski(sK3)),sK4) ),
    inference(resolution,[status(thm)],[c_12,c_17])).

cnf(c_5919,plain,
    ( r2_hidden(sK2(k2_tarski(sK3,sK5),sK4,k1_tarski(sK3)),sK2(k2_tarski(sK3,sK5),sK4,k1_tarski(sK3)))
    | r2_hidden(sK2(k2_tarski(sK3,sK5),sK4,k1_tarski(sK3)),sK4)
    | ~ r2_hidden(sK3,sK5)
    | sK2(k2_tarski(sK3,sK5),sK4,k1_tarski(sK3)) = sK3 ),
    inference(resolution,[status(thm)],[c_3656,c_3016])).

cnf(c_19,negated_conjecture,
    ( r2_hidden(sK3,sK4) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_201,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_895,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_201])).

cnf(c_715,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK3,sK4)
    | X1 != sK4
    | X0 != sK3 ),
    inference(instantiation,[status(thm)],[c_205])).

cnf(c_894,plain,
    ( r2_hidden(X0,sK4)
    | ~ r2_hidden(sK3,sK4)
    | X0 != sK3
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_715])).

cnf(c_1958,plain,
    ( r2_hidden(sK2(k2_tarski(sK3,sK5),sK4,k1_tarski(sK3)),sK4)
    | ~ r2_hidden(sK3,sK4)
    | sK2(k2_tarski(sK3,sK5),sK4,k1_tarski(sK3)) != sK3
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_894])).

cnf(c_4186,plain,
    ( ~ r2_hidden(sK2(k2_tarski(sK3,sK5),sK4,k1_tarski(sK3)),k1_tarski(sK3))
    | sK2(k2_tarski(sK3,sK5),sK4,k1_tarski(sK3)) = sK3 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_6116,plain,
    ( r2_hidden(sK2(k2_tarski(sK3,sK5),sK4,k1_tarski(sK3)),sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5919,c_19,c_895,c_1958,c_3016,c_4186])).

cnf(c_2744,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_205,c_201])).

cnf(c_202,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3348,plain,
    ( X0 != sK5
    | sK2(k2_tarski(sK3,sK5),sK4,k1_tarski(sK3)) = X0
    | sK2(k2_tarski(sK3,sK5),sK4,k1_tarski(sK3)) = sK3 ),
    inference(resolution,[status(thm)],[c_3340,c_202])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_1410,plain,
    ( X0 != k3_xboole_0(X1,X2)
    | k3_xboole_0(X2,X1) = X0 ),
    inference(resolution,[status(thm)],[c_202,c_0])).

cnf(c_3603,plain,
    ( sK2(k2_tarski(sK3,sK5),sK4,k1_tarski(sK3)) = sK3
    | k3_xboole_0(X0,X1) = sK2(k2_tarski(sK3,sK5),sK4,k1_tarski(sK3))
    | k3_xboole_0(X1,X0) != sK5 ),
    inference(resolution,[status(thm)],[c_3348,c_1410])).

cnf(c_18,negated_conjecture,
    ( ~ r2_hidden(sK5,sK4)
    | sK3 = sK5 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1414,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_202,c_201])).

cnf(c_3347,plain,
    ( sK2(k2_tarski(sK3,sK5),sK4,k1_tarski(sK3)) = sK3
    | sK5 = sK2(k2_tarski(sK3,sK5),sK4,k1_tarski(sK3)) ),
    inference(resolution,[status(thm)],[c_3340,c_1414])).

cnf(c_3353,plain,
    ( sK2(k2_tarski(sK3,sK5),sK4,k1_tarski(sK3)) = sK3
    | sK3 != sK5 ),
    inference(instantiation,[status(thm)],[c_3348])).

cnf(c_1313,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK2(k2_tarski(sK3,sK5),sK4,k1_tarski(sK3)),sK4)
    | X0 != sK2(k2_tarski(sK3,sK5),sK4,k1_tarski(sK3))
    | X1 != sK4 ),
    inference(instantiation,[status(thm)],[c_205])).

cnf(c_6371,plain,
    ( ~ r2_hidden(sK2(k2_tarski(sK3,sK5),sK4,k1_tarski(sK3)),sK4)
    | r2_hidden(sK5,sK4)
    | sK4 != sK4
    | sK5 != sK2(k2_tarski(sK3,sK5),sK4,k1_tarski(sK3)) ),
    inference(instantiation,[status(thm)],[c_1313])).

cnf(c_6602,plain,
    ( sK2(k2_tarski(sK3,sK5),sK4,k1_tarski(sK3)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3603,c_19,c_18,c_895,c_1958,c_3016,c_3347,c_3353,c_4186,c_6371])).

cnf(c_6923,plain,
    ( r2_hidden(sK2(k2_tarski(sK3,sK5),sK4,k1_tarski(sK3)),X0)
    | ~ r2_hidden(sK3,X0) ),
    inference(resolution,[status(thm)],[c_2744,c_6602])).

cnf(c_11,plain,
    ( ~ r2_hidden(sK2(X0,X1,X2),X1)
    | ~ r2_hidden(sK2(X0,X1,X2),X0)
    | ~ r2_hidden(sK2(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_9088,plain,
    ( ~ r2_hidden(sK2(k2_tarski(sK3,sK5),sK4,k1_tarski(sK3)),k2_tarski(sK3,sK5))
    | ~ r2_hidden(sK2(k2_tarski(sK3,sK5),sK4,k1_tarski(sK3)),sK4)
    | ~ r2_hidden(sK3,k1_tarski(sK3))
    | k3_xboole_0(k2_tarski(sK3,sK5),sK4) = k1_tarski(sK3) ),
    inference(resolution,[status(thm)],[c_6923,c_11])).

cnf(c_14451,plain,
    ( r2_hidden(sK2(k2_tarski(sK3,sK5),sK4,k1_tarski(sK3)),k1_tarski(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13428,c_19,c_17,c_54,c_895,c_1958,c_3016,c_3056,c_4186,c_9088])).

cnf(c_14472,plain,
    ( ~ r2_hidden(sK2(k2_tarski(sK3,sK5),sK4,k1_tarski(sK3)),k2_tarski(sK3,sK5))
    | ~ r2_hidden(sK2(k2_tarski(sK3,sK5),sK4,k1_tarski(sK3)),sK4)
    | k3_xboole_0(k2_tarski(sK3,sK5),sK4) = k1_tarski(sK3) ),
    inference(resolution,[status(thm)],[c_14451,c_11])).

cnf(c_14870,plain,
    ( ~ r2_hidden(sK2(k2_tarski(sK3,sK5),sK4,k1_tarski(sK3)),k2_tarski(sK3,sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14472,c_19,c_17,c_54,c_895,c_1958,c_3016,c_4186,c_9088])).

cnf(c_14884,plain,
    ( ~ r2_hidden(sK3,k2_tarski(sK3,sK5)) ),
    inference(resolution,[status(thm)],[c_14870,c_6923])).

cnf(c_9,plain,
    ( r2_hidden(X0,k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_14888,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_14884,c_9])).


%------------------------------------------------------------------------------
