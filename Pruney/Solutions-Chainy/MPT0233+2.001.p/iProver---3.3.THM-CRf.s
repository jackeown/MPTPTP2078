%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:31:16 EST 2020

% Result     : Theorem 51.49s
% Output     : CNFRefutation 51.49s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 694 expanded)
%              Number of clauses        :   55 ( 229 expanded)
%              Number of leaves         :   20 ( 171 expanded)
%              Depth                    :   22
%              Number of atoms          :  292 (1617 expanded)
%              Number of equality atoms :  180 ( 909 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f27,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( X0 != X3
          & X0 != X2
          & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(negated_conjecture,[],[f27])).

fof(f37,plain,(
    ? [X0,X1,X2,X3] :
      ( X0 != X3
      & X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f56,plain,
    ( ? [X0,X1,X2,X3] :
        ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) )
   => ( sK4 != sK7
      & sK4 != sK6
      & r1_tarski(k2_tarski(sK4,sK5),k2_tarski(sK6,sK7)) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
    ( sK4 != sK7
    & sK4 != sK6
    & r1_tarski(k2_tarski(sK4,sK5),k2_tarski(sK6,sK7)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f37,f56])).

fof(f102,plain,(
    r1_tarski(k2_tarski(sK4,sK5),k2_tarski(sK6,sK7)) ),
    inference(cnf_transformation,[],[f57])).

fof(f26,axiom,(
    ! [X0,X1] : k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f101,plain,(
    ! [X0,X1] : k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f26])).

fof(f18,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f90,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f126,plain,(
    ! [X0,X1] : k3_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X1)) = k2_tarski(X0,X0) ),
    inference(definition_unfolding,[],[f101,f90,f90])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f33])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
    <=> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) ) ) ),
    inference(flattening,[],[f54])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
      | X0 != X1
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(k2_tarski(X0,X1),k3_xboole_0(k2_tarski(X0,X1),X2)) = k2_tarski(X0,X0)
      | X0 != X1
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f100,f67,f90])).

fof(f141,plain,(
    ! [X2,X1] :
      ( k5_xboole_0(k2_tarski(X1,X1),k3_xboole_0(k2_tarski(X1,X1),X2)) = k2_tarski(X1,X1)
      | r2_hidden(X1,X2) ) ),
    inference(equality_resolution,[],[f122])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | k5_xboole_0(k2_tarski(X0,X1),k3_xboole_0(k2_tarski(X0,X1),X2)) != k2_tarski(X0,X0) ) ),
    inference(definition_unfolding,[],[f97,f67,f90])).

fof(f5,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f40])).

fof(f63,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f38])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f13,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f110,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f71,f67,f67])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f60,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f29])).

fof(f12,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f103,plain,(
    sK4 != sK6 ),
    inference(cnf_transformation,[],[f57])).

fof(f104,plain,(
    sK4 != sK7 ),
    inference(cnf_transformation,[],[f57])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f50,plain,(
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
    inference(flattening,[],[f49])).

fof(f51,plain,(
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
    inference(rectify,[],[f50])).

fof(f52,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK3(X0,X1,X2) != X1
            & sK3(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( sK3(X0,X1,X2) = X1
          | sK3(X0,X1,X2) = X0
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK3(X0,X1,X2) != X1
              & sK3(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( sK3(X0,X1,X2) = X1
            | sK3(X0,X1,X2) = X0
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f51,f52])).

fof(f83,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f140,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_tarski(X0,X1)) ) ),
    inference(equality_resolution,[],[f83])).

fof(f84,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f138,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f84])).

fof(f139,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f138])).

cnf(c_38,negated_conjecture,
    ( r1_tarski(k2_tarski(sK4,sK5),k2_tarski(sK6,sK7)) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_957,plain,
    ( r1_tarski(k2_tarski(sK4,sK5),k2_tarski(sK6,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_35,plain,
    ( k3_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X1)) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_3,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_11,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_978,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1960,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_978])).

cnf(c_1973,plain,
    ( r1_tarski(k2_tarski(X0,X0),k2_tarski(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_35,c_1960])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_977,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_12788,plain,
    ( r1_tarski(k2_tarski(X0,X1),X2) != iProver_top
    | r1_tarski(k2_tarski(X0,X0),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1973,c_977])).

cnf(c_168649,plain,
    ( r1_tarski(k2_tarski(sK4,sK4),k2_tarski(sK6,sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_957,c_12788])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_976,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_169918,plain,
    ( k3_xboole_0(k2_tarski(sK4,sK4),k2_tarski(sK6,sK7)) = k2_tarski(sK4,sK4) ),
    inference(superposition,[status(thm)],[c_168649,c_976])).

cnf(c_31,plain,
    ( r2_hidden(X0,X1)
    | k5_xboole_0(k2_tarski(X0,X0),k3_xboole_0(k2_tarski(X0,X0),X1)) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f141])).

cnf(c_961,plain,
    ( k5_xboole_0(k2_tarski(X0,X0),k3_xboole_0(k2_tarski(X0,X0),X1)) = k2_tarski(X0,X0)
    | r2_hidden(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_3711,plain,
    ( k3_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK6,sK7)) = k2_tarski(sK4,sK5) ),
    inference(superposition,[status(thm)],[c_957,c_976])).

cnf(c_34,plain,
    ( ~ r2_hidden(X0,X1)
    | k5_xboole_0(k2_tarski(X0,X2),k3_xboole_0(k2_tarski(X0,X2),X1)) != k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_958,plain,
    ( k5_xboole_0(k2_tarski(X0,X1),k3_xboole_0(k2_tarski(X0,X1),X2)) != k2_tarski(X0,X0)
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_16415,plain,
    ( k5_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK4,sK5)) != k2_tarski(sK4,sK4)
    | r2_hidden(sK4,k2_tarski(sK6,sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3711,c_958])).

cnf(c_7,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_981,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_15,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_338,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | X3 != X1
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_15])).

cnf(c_339,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) ),
    inference(unflattening,[status(thm)],[c_338])).

cnf(c_955,plain,
    ( r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_339])).

cnf(c_2597,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_981,c_955])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_2856,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k1_xboole_0))) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2597,c_0])).

cnf(c_2872,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k1_xboole_0))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2856,c_2597])).

cnf(c_4,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_14,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2874,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2872,c_4,c_14])).

cnf(c_16441,plain,
    ( k2_tarski(sK4,sK4) != k1_xboole_0
    | r2_hidden(sK4,k2_tarski(sK6,sK7)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_16415,c_2874])).

cnf(c_37,negated_conjecture,
    ( sK4 != sK6 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_36,negated_conjecture,
    ( sK4 != sK7 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_29,plain,
    ( ~ r2_hidden(X0,k2_tarski(X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f140])).

cnf(c_1199,plain,
    ( ~ r2_hidden(sK4,k2_tarski(sK6,X0))
    | sK4 = X0
    | sK4 = sK6 ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_3659,plain,
    ( ~ r2_hidden(sK4,k2_tarski(sK6,sK7))
    | sK4 = sK6
    | sK4 = sK7 ),
    inference(instantiation,[status(thm)],[c_1199])).

cnf(c_3660,plain,
    ( sK4 = sK6
    | sK4 = sK7
    | r2_hidden(sK4,k2_tarski(sK6,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3659])).

cnf(c_16705,plain,
    ( r2_hidden(sK4,k2_tarski(sK6,sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16441,c_37,c_36,c_3660])).

cnf(c_16710,plain,
    ( k5_xboole_0(k2_tarski(sK4,sK4),k3_xboole_0(k2_tarski(sK4,sK4),k2_tarski(sK6,sK7))) = k2_tarski(sK4,sK4) ),
    inference(superposition,[status(thm)],[c_961,c_16705])).

cnf(c_16717,plain,
    ( k5_xboole_0(k2_tarski(sK4,sK4),k3_xboole_0(k2_tarski(sK4,sK4),k2_tarski(sK4,sK4))) = k3_xboole_0(k2_tarski(sK4,sK4),k2_tarski(sK6,sK7)) ),
    inference(superposition,[status(thm)],[c_16710,c_0])).

cnf(c_16736,plain,
    ( k3_xboole_0(k2_tarski(sK4,sK4),k2_tarski(sK6,sK7)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_16717,c_35,c_2874])).

cnf(c_169921,plain,
    ( k2_tarski(sK4,sK4) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_169918,c_16736])).

cnf(c_16396,plain,
    ( k3_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X0)
    | r2_hidden(X0,k5_xboole_0(k2_tarski(X0,X1),k3_xboole_0(k2_tarski(X0,X1),X2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_958])).

cnf(c_33118,plain,
    ( k2_tarski(sK4,sK4) != k1_xboole_0
    | r2_hidden(sK4,k5_xboole_0(k2_tarski(sK4,sK4),k3_xboole_0(k2_tarski(sK4,sK4),k2_tarski(sK6,sK7)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_16736,c_16396])).

cnf(c_33183,plain,
    ( k2_tarski(sK4,sK4) != k1_xboole_0
    | r2_hidden(sK4,k5_xboole_0(k2_tarski(sK4,sK4),k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_33118,c_16736])).

cnf(c_33184,plain,
    ( k2_tarski(sK4,sK4) != k1_xboole_0
    | r2_hidden(sK4,k2_tarski(sK4,sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_33183,c_14])).

cnf(c_28,plain,
    ( r2_hidden(X0,k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f139])).

cnf(c_963,plain,
    ( r2_hidden(X0,k2_tarski(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_33792,plain,
    ( k2_tarski(sK4,sK4) != k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_33184,c_963])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_169921,c_33792])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:16:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.34  % Running in FOF mode
% 51.49/6.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 51.49/6.97  
% 51.49/6.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 51.49/6.97  
% 51.49/6.97  ------  iProver source info
% 51.49/6.97  
% 51.49/6.97  git: date: 2020-06-30 10:37:57 +0100
% 51.49/6.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 51.49/6.97  git: non_committed_changes: false
% 51.49/6.97  git: last_make_outside_of_git: false
% 51.49/6.97  
% 51.49/6.97  ------ 
% 51.49/6.97  
% 51.49/6.97  ------ Input Options
% 51.49/6.97  
% 51.49/6.97  --out_options                           all
% 51.49/6.97  --tptp_safe_out                         true
% 51.49/6.97  --problem_path                          ""
% 51.49/6.97  --include_path                          ""
% 51.49/6.97  --clausifier                            res/vclausify_rel
% 51.49/6.97  --clausifier_options                    --mode clausify
% 51.49/6.97  --stdin                                 false
% 51.49/6.97  --stats_out                             all
% 51.49/6.97  
% 51.49/6.97  ------ General Options
% 51.49/6.97  
% 51.49/6.97  --fof                                   false
% 51.49/6.97  --time_out_real                         305.
% 51.49/6.97  --time_out_virtual                      -1.
% 51.49/6.97  --symbol_type_check                     false
% 51.49/6.97  --clausify_out                          false
% 51.49/6.97  --sig_cnt_out                           false
% 51.49/6.97  --trig_cnt_out                          false
% 51.49/6.97  --trig_cnt_out_tolerance                1.
% 51.49/6.97  --trig_cnt_out_sk_spl                   false
% 51.49/6.97  --abstr_cl_out                          false
% 51.49/6.97  
% 51.49/6.97  ------ Global Options
% 51.49/6.97  
% 51.49/6.97  --schedule                              default
% 51.49/6.97  --add_important_lit                     false
% 51.49/6.97  --prop_solver_per_cl                    1000
% 51.49/6.97  --min_unsat_core                        false
% 51.49/6.97  --soft_assumptions                      false
% 51.49/6.97  --soft_lemma_size                       3
% 51.49/6.97  --prop_impl_unit_size                   0
% 51.49/6.97  --prop_impl_unit                        []
% 51.49/6.97  --share_sel_clauses                     true
% 51.49/6.97  --reset_solvers                         false
% 51.49/6.97  --bc_imp_inh                            [conj_cone]
% 51.49/6.97  --conj_cone_tolerance                   3.
% 51.49/6.97  --extra_neg_conj                        none
% 51.49/6.97  --large_theory_mode                     true
% 51.49/6.97  --prolific_symb_bound                   200
% 51.49/6.97  --lt_threshold                          2000
% 51.49/6.97  --clause_weak_htbl                      true
% 51.49/6.97  --gc_record_bc_elim                     false
% 51.49/6.97  
% 51.49/6.97  ------ Preprocessing Options
% 51.49/6.97  
% 51.49/6.97  --preprocessing_flag                    true
% 51.49/6.97  --time_out_prep_mult                    0.1
% 51.49/6.97  --splitting_mode                        input
% 51.49/6.97  --splitting_grd                         true
% 51.49/6.97  --splitting_cvd                         false
% 51.49/6.97  --splitting_cvd_svl                     false
% 51.49/6.97  --splitting_nvd                         32
% 51.49/6.97  --sub_typing                            true
% 51.49/6.97  --prep_gs_sim                           true
% 51.49/6.97  --prep_unflatten                        true
% 51.49/6.97  --prep_res_sim                          true
% 51.49/6.97  --prep_upred                            true
% 51.49/6.97  --prep_sem_filter                       exhaustive
% 51.49/6.97  --prep_sem_filter_out                   false
% 51.49/6.97  --pred_elim                             true
% 51.49/6.97  --res_sim_input                         true
% 51.49/6.97  --eq_ax_congr_red                       true
% 51.49/6.97  --pure_diseq_elim                       true
% 51.49/6.97  --brand_transform                       false
% 51.49/6.97  --non_eq_to_eq                          false
% 51.49/6.97  --prep_def_merge                        true
% 51.49/6.97  --prep_def_merge_prop_impl              false
% 51.49/6.97  --prep_def_merge_mbd                    true
% 51.49/6.97  --prep_def_merge_tr_red                 false
% 51.49/6.97  --prep_def_merge_tr_cl                  false
% 51.49/6.97  --smt_preprocessing                     true
% 51.49/6.97  --smt_ac_axioms                         fast
% 51.49/6.97  --preprocessed_out                      false
% 51.49/6.97  --preprocessed_stats                    false
% 51.49/6.97  
% 51.49/6.97  ------ Abstraction refinement Options
% 51.49/6.97  
% 51.49/6.97  --abstr_ref                             []
% 51.49/6.97  --abstr_ref_prep                        false
% 51.49/6.97  --abstr_ref_until_sat                   false
% 51.49/6.97  --abstr_ref_sig_restrict                funpre
% 51.49/6.97  --abstr_ref_af_restrict_to_split_sk     false
% 51.49/6.97  --abstr_ref_under                       []
% 51.49/6.97  
% 51.49/6.97  ------ SAT Options
% 51.49/6.97  
% 51.49/6.97  --sat_mode                              false
% 51.49/6.97  --sat_fm_restart_options                ""
% 51.49/6.97  --sat_gr_def                            false
% 51.49/6.97  --sat_epr_types                         true
% 51.49/6.97  --sat_non_cyclic_types                  false
% 51.49/6.97  --sat_finite_models                     false
% 51.49/6.97  --sat_fm_lemmas                         false
% 51.49/6.97  --sat_fm_prep                           false
% 51.49/6.97  --sat_fm_uc_incr                        true
% 51.49/6.97  --sat_out_model                         small
% 51.49/6.97  --sat_out_clauses                       false
% 51.49/6.97  
% 51.49/6.97  ------ QBF Options
% 51.49/6.97  
% 51.49/6.97  --qbf_mode                              false
% 51.49/6.97  --qbf_elim_univ                         false
% 51.49/6.97  --qbf_dom_inst                          none
% 51.49/6.97  --qbf_dom_pre_inst                      false
% 51.49/6.97  --qbf_sk_in                             false
% 51.49/6.97  --qbf_pred_elim                         true
% 51.49/6.97  --qbf_split                             512
% 51.49/6.97  
% 51.49/6.97  ------ BMC1 Options
% 51.49/6.97  
% 51.49/6.97  --bmc1_incremental                      false
% 51.49/6.97  --bmc1_axioms                           reachable_all
% 51.49/6.97  --bmc1_min_bound                        0
% 51.49/6.97  --bmc1_max_bound                        -1
% 51.49/6.97  --bmc1_max_bound_default                -1
% 51.49/6.97  --bmc1_symbol_reachability              true
% 51.49/6.97  --bmc1_property_lemmas                  false
% 51.49/6.97  --bmc1_k_induction                      false
% 51.49/6.97  --bmc1_non_equiv_states                 false
% 51.49/6.97  --bmc1_deadlock                         false
% 51.49/6.97  --bmc1_ucm                              false
% 51.49/6.97  --bmc1_add_unsat_core                   none
% 51.49/6.97  --bmc1_unsat_core_children              false
% 51.49/6.97  --bmc1_unsat_core_extrapolate_axioms    false
% 51.49/6.97  --bmc1_out_stat                         full
% 51.49/6.97  --bmc1_ground_init                      false
% 51.49/6.97  --bmc1_pre_inst_next_state              false
% 51.49/6.97  --bmc1_pre_inst_state                   false
% 51.49/6.97  --bmc1_pre_inst_reach_state             false
% 51.49/6.97  --bmc1_out_unsat_core                   false
% 51.49/6.97  --bmc1_aig_witness_out                  false
% 51.49/6.97  --bmc1_verbose                          false
% 51.49/6.97  --bmc1_dump_clauses_tptp                false
% 51.49/6.97  --bmc1_dump_unsat_core_tptp             false
% 51.49/6.97  --bmc1_dump_file                        -
% 51.49/6.97  --bmc1_ucm_expand_uc_limit              128
% 51.49/6.97  --bmc1_ucm_n_expand_iterations          6
% 51.49/6.97  --bmc1_ucm_extend_mode                  1
% 51.49/6.97  --bmc1_ucm_init_mode                    2
% 51.49/6.97  --bmc1_ucm_cone_mode                    none
% 51.49/6.97  --bmc1_ucm_reduced_relation_type        0
% 51.49/6.97  --bmc1_ucm_relax_model                  4
% 51.49/6.97  --bmc1_ucm_full_tr_after_sat            true
% 51.49/6.97  --bmc1_ucm_expand_neg_assumptions       false
% 51.49/6.97  --bmc1_ucm_layered_model                none
% 51.49/6.97  --bmc1_ucm_max_lemma_size               10
% 51.49/6.97  
% 51.49/6.97  ------ AIG Options
% 51.49/6.97  
% 51.49/6.97  --aig_mode                              false
% 51.49/6.97  
% 51.49/6.97  ------ Instantiation Options
% 51.49/6.97  
% 51.49/6.97  --instantiation_flag                    true
% 51.49/6.97  --inst_sos_flag                         false
% 51.49/6.97  --inst_sos_phase                        true
% 51.49/6.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 51.49/6.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 51.49/6.97  --inst_lit_sel_side                     num_symb
% 51.49/6.97  --inst_solver_per_active                1400
% 51.49/6.97  --inst_solver_calls_frac                1.
% 51.49/6.97  --inst_passive_queue_type               priority_queues
% 51.49/6.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 51.49/6.97  --inst_passive_queues_freq              [25;2]
% 51.49/6.97  --inst_dismatching                      true
% 51.49/6.97  --inst_eager_unprocessed_to_passive     true
% 51.49/6.97  --inst_prop_sim_given                   true
% 51.49/6.97  --inst_prop_sim_new                     false
% 51.49/6.97  --inst_subs_new                         false
% 51.49/6.97  --inst_eq_res_simp                      false
% 51.49/6.97  --inst_subs_given                       false
% 51.49/6.97  --inst_orphan_elimination               true
% 51.49/6.97  --inst_learning_loop_flag               true
% 51.49/6.97  --inst_learning_start                   3000
% 51.49/6.97  --inst_learning_factor                  2
% 51.49/6.97  --inst_start_prop_sim_after_learn       3
% 51.49/6.97  --inst_sel_renew                        solver
% 51.49/6.97  --inst_lit_activity_flag                true
% 51.49/6.97  --inst_restr_to_given                   false
% 51.49/6.97  --inst_activity_threshold               500
% 51.49/6.97  --inst_out_proof                        true
% 51.49/6.97  
% 51.49/6.97  ------ Resolution Options
% 51.49/6.97  
% 51.49/6.97  --resolution_flag                       true
% 51.49/6.97  --res_lit_sel                           adaptive
% 51.49/6.97  --res_lit_sel_side                      none
% 51.49/6.97  --res_ordering                          kbo
% 51.49/6.97  --res_to_prop_solver                    active
% 51.49/6.97  --res_prop_simpl_new                    false
% 51.49/6.97  --res_prop_simpl_given                  true
% 51.49/6.97  --res_passive_queue_type                priority_queues
% 51.49/6.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 51.49/6.97  --res_passive_queues_freq               [15;5]
% 51.49/6.97  --res_forward_subs                      full
% 51.49/6.97  --res_backward_subs                     full
% 51.49/6.97  --res_forward_subs_resolution           true
% 51.49/6.97  --res_backward_subs_resolution          true
% 51.49/6.97  --res_orphan_elimination                true
% 51.49/6.97  --res_time_limit                        2.
% 51.49/6.97  --res_out_proof                         true
% 51.49/6.97  
% 51.49/6.97  ------ Superposition Options
% 51.49/6.97  
% 51.49/6.97  --superposition_flag                    true
% 51.49/6.97  --sup_passive_queue_type                priority_queues
% 51.49/6.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 51.49/6.97  --sup_passive_queues_freq               [8;1;4]
% 51.49/6.97  --demod_completeness_check              fast
% 51.49/6.97  --demod_use_ground                      true
% 51.49/6.97  --sup_to_prop_solver                    passive
% 51.49/6.97  --sup_prop_simpl_new                    true
% 51.49/6.97  --sup_prop_simpl_given                  true
% 51.49/6.97  --sup_fun_splitting                     false
% 51.49/6.97  --sup_smt_interval                      50000
% 51.49/6.97  
% 51.49/6.97  ------ Superposition Simplification Setup
% 51.49/6.97  
% 51.49/6.97  --sup_indices_passive                   []
% 51.49/6.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 51.49/6.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 51.49/6.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 51.49/6.97  --sup_full_triv                         [TrivRules;PropSubs]
% 51.49/6.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 51.49/6.97  --sup_full_bw                           [BwDemod]
% 51.49/6.97  --sup_immed_triv                        [TrivRules]
% 51.49/6.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 51.49/6.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 51.49/6.97  --sup_immed_bw_main                     []
% 51.49/6.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 51.49/6.97  --sup_input_triv                        [Unflattening;TrivRules]
% 51.49/6.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 51.49/6.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 51.49/6.97  
% 51.49/6.97  ------ Combination Options
% 51.49/6.97  
% 51.49/6.97  --comb_res_mult                         3
% 51.49/6.97  --comb_sup_mult                         2
% 51.49/6.97  --comb_inst_mult                        10
% 51.49/6.97  
% 51.49/6.97  ------ Debug Options
% 51.49/6.97  
% 51.49/6.97  --dbg_backtrace                         false
% 51.49/6.97  --dbg_dump_prop_clauses                 false
% 51.49/6.97  --dbg_dump_prop_clauses_file            -
% 51.49/6.97  --dbg_out_stat                          false
% 51.49/6.97  ------ Parsing...
% 51.49/6.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 51.49/6.97  
% 51.49/6.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 51.49/6.97  
% 51.49/6.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 51.49/6.97  
% 51.49/6.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 51.49/6.97  ------ Proving...
% 51.49/6.97  ------ Problem Properties 
% 51.49/6.97  
% 51.49/6.97  
% 51.49/6.97  clauses                                 37
% 51.49/6.97  conjectures                             3
% 51.49/6.97  EPR                                     5
% 51.49/6.97  Horn                                    29
% 51.49/6.97  unary                                   19
% 51.49/6.97  binary                                  5
% 51.49/6.97  lits                                    72
% 51.49/6.97  lits eq                                 40
% 51.49/6.97  fd_pure                                 0
% 51.49/6.97  fd_pseudo                               0
% 51.49/6.97  fd_cond                                 1
% 51.49/6.97  fd_pseudo_cond                          9
% 51.49/6.97  AC symbols                              0
% 51.49/6.97  
% 51.49/6.97  ------ Schedule dynamic 5 is on 
% 51.49/6.97  
% 51.49/6.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 51.49/6.97  
% 51.49/6.97  
% 51.49/6.97  ------ 
% 51.49/6.97  Current options:
% 51.49/6.97  ------ 
% 51.49/6.97  
% 51.49/6.97  ------ Input Options
% 51.49/6.97  
% 51.49/6.97  --out_options                           all
% 51.49/6.97  --tptp_safe_out                         true
% 51.49/6.97  --problem_path                          ""
% 51.49/6.97  --include_path                          ""
% 51.49/6.97  --clausifier                            res/vclausify_rel
% 51.49/6.97  --clausifier_options                    --mode clausify
% 51.49/6.97  --stdin                                 false
% 51.49/6.97  --stats_out                             all
% 51.49/6.97  
% 51.49/6.97  ------ General Options
% 51.49/6.97  
% 51.49/6.97  --fof                                   false
% 51.49/6.97  --time_out_real                         305.
% 51.49/6.97  --time_out_virtual                      -1.
% 51.49/6.97  --symbol_type_check                     false
% 51.49/6.97  --clausify_out                          false
% 51.49/6.97  --sig_cnt_out                           false
% 51.49/6.97  --trig_cnt_out                          false
% 51.49/6.97  --trig_cnt_out_tolerance                1.
% 51.49/6.97  --trig_cnt_out_sk_spl                   false
% 51.49/6.97  --abstr_cl_out                          false
% 51.49/6.97  
% 51.49/6.97  ------ Global Options
% 51.49/6.97  
% 51.49/6.97  --schedule                              default
% 51.49/6.97  --add_important_lit                     false
% 51.49/6.97  --prop_solver_per_cl                    1000
% 51.49/6.97  --min_unsat_core                        false
% 51.49/6.97  --soft_assumptions                      false
% 51.49/6.97  --soft_lemma_size                       3
% 51.49/6.97  --prop_impl_unit_size                   0
% 51.49/6.97  --prop_impl_unit                        []
% 51.49/6.97  --share_sel_clauses                     true
% 51.49/6.97  --reset_solvers                         false
% 51.49/6.97  --bc_imp_inh                            [conj_cone]
% 51.49/6.97  --conj_cone_tolerance                   3.
% 51.49/6.97  --extra_neg_conj                        none
% 51.49/6.97  --large_theory_mode                     true
% 51.49/6.97  --prolific_symb_bound                   200
% 51.49/6.97  --lt_threshold                          2000
% 51.49/6.97  --clause_weak_htbl                      true
% 51.49/6.97  --gc_record_bc_elim                     false
% 51.49/6.97  
% 51.49/6.97  ------ Preprocessing Options
% 51.49/6.97  
% 51.49/6.97  --preprocessing_flag                    true
% 51.49/6.97  --time_out_prep_mult                    0.1
% 51.49/6.97  --splitting_mode                        input
% 51.49/6.97  --splitting_grd                         true
% 51.49/6.97  --splitting_cvd                         false
% 51.49/6.97  --splitting_cvd_svl                     false
% 51.49/6.97  --splitting_nvd                         32
% 51.49/6.97  --sub_typing                            true
% 51.49/6.97  --prep_gs_sim                           true
% 51.49/6.97  --prep_unflatten                        true
% 51.49/6.97  --prep_res_sim                          true
% 51.49/6.97  --prep_upred                            true
% 51.49/6.97  --prep_sem_filter                       exhaustive
% 51.49/6.97  --prep_sem_filter_out                   false
% 51.49/6.97  --pred_elim                             true
% 51.49/6.97  --res_sim_input                         true
% 51.49/6.97  --eq_ax_congr_red                       true
% 51.49/6.97  --pure_diseq_elim                       true
% 51.49/6.97  --brand_transform                       false
% 51.49/6.97  --non_eq_to_eq                          false
% 51.49/6.97  --prep_def_merge                        true
% 51.49/6.97  --prep_def_merge_prop_impl              false
% 51.49/6.97  --prep_def_merge_mbd                    true
% 51.49/6.97  --prep_def_merge_tr_red                 false
% 51.49/6.97  --prep_def_merge_tr_cl                  false
% 51.49/6.97  --smt_preprocessing                     true
% 51.49/6.97  --smt_ac_axioms                         fast
% 51.49/6.97  --preprocessed_out                      false
% 51.49/6.97  --preprocessed_stats                    false
% 51.49/6.97  
% 51.49/6.97  ------ Abstraction refinement Options
% 51.49/6.97  
% 51.49/6.97  --abstr_ref                             []
% 51.49/6.97  --abstr_ref_prep                        false
% 51.49/6.97  --abstr_ref_until_sat                   false
% 51.49/6.97  --abstr_ref_sig_restrict                funpre
% 51.49/6.97  --abstr_ref_af_restrict_to_split_sk     false
% 51.49/6.97  --abstr_ref_under                       []
% 51.49/6.97  
% 51.49/6.97  ------ SAT Options
% 51.49/6.97  
% 51.49/6.97  --sat_mode                              false
% 51.49/6.97  --sat_fm_restart_options                ""
% 51.49/6.97  --sat_gr_def                            false
% 51.49/6.97  --sat_epr_types                         true
% 51.49/6.97  --sat_non_cyclic_types                  false
% 51.49/6.97  --sat_finite_models                     false
% 51.49/6.97  --sat_fm_lemmas                         false
% 51.49/6.97  --sat_fm_prep                           false
% 51.49/6.97  --sat_fm_uc_incr                        true
% 51.49/6.97  --sat_out_model                         small
% 51.49/6.97  --sat_out_clauses                       false
% 51.49/6.97  
% 51.49/6.97  ------ QBF Options
% 51.49/6.97  
% 51.49/6.97  --qbf_mode                              false
% 51.49/6.97  --qbf_elim_univ                         false
% 51.49/6.97  --qbf_dom_inst                          none
% 51.49/6.97  --qbf_dom_pre_inst                      false
% 51.49/6.97  --qbf_sk_in                             false
% 51.49/6.97  --qbf_pred_elim                         true
% 51.49/6.97  --qbf_split                             512
% 51.49/6.97  
% 51.49/6.97  ------ BMC1 Options
% 51.49/6.97  
% 51.49/6.97  --bmc1_incremental                      false
% 51.49/6.97  --bmc1_axioms                           reachable_all
% 51.49/6.97  --bmc1_min_bound                        0
% 51.49/6.97  --bmc1_max_bound                        -1
% 51.49/6.97  --bmc1_max_bound_default                -1
% 51.49/6.97  --bmc1_symbol_reachability              true
% 51.49/6.97  --bmc1_property_lemmas                  false
% 51.49/6.97  --bmc1_k_induction                      false
% 51.49/6.97  --bmc1_non_equiv_states                 false
% 51.49/6.97  --bmc1_deadlock                         false
% 51.49/6.97  --bmc1_ucm                              false
% 51.49/6.97  --bmc1_add_unsat_core                   none
% 51.49/6.97  --bmc1_unsat_core_children              false
% 51.49/6.97  --bmc1_unsat_core_extrapolate_axioms    false
% 51.49/6.97  --bmc1_out_stat                         full
% 51.49/6.97  --bmc1_ground_init                      false
% 51.49/6.97  --bmc1_pre_inst_next_state              false
% 51.49/6.97  --bmc1_pre_inst_state                   false
% 51.49/6.97  --bmc1_pre_inst_reach_state             false
% 51.49/6.97  --bmc1_out_unsat_core                   false
% 51.49/6.97  --bmc1_aig_witness_out                  false
% 51.49/6.97  --bmc1_verbose                          false
% 51.49/6.97  --bmc1_dump_clauses_tptp                false
% 51.49/6.97  --bmc1_dump_unsat_core_tptp             false
% 51.49/6.97  --bmc1_dump_file                        -
% 51.49/6.97  --bmc1_ucm_expand_uc_limit              128
% 51.49/6.97  --bmc1_ucm_n_expand_iterations          6
% 51.49/6.97  --bmc1_ucm_extend_mode                  1
% 51.49/6.97  --bmc1_ucm_init_mode                    2
% 51.49/6.97  --bmc1_ucm_cone_mode                    none
% 51.49/6.97  --bmc1_ucm_reduced_relation_type        0
% 51.49/6.97  --bmc1_ucm_relax_model                  4
% 51.49/6.97  --bmc1_ucm_full_tr_after_sat            true
% 51.49/6.97  --bmc1_ucm_expand_neg_assumptions       false
% 51.49/6.97  --bmc1_ucm_layered_model                none
% 51.49/6.97  --bmc1_ucm_max_lemma_size               10
% 51.49/6.97  
% 51.49/6.97  ------ AIG Options
% 51.49/6.97  
% 51.49/6.97  --aig_mode                              false
% 51.49/6.97  
% 51.49/6.97  ------ Instantiation Options
% 51.49/6.97  
% 51.49/6.97  --instantiation_flag                    true
% 51.49/6.97  --inst_sos_flag                         false
% 51.49/6.97  --inst_sos_phase                        true
% 51.49/6.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 51.49/6.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 51.49/6.97  --inst_lit_sel_side                     none
% 51.49/6.97  --inst_solver_per_active                1400
% 51.49/6.97  --inst_solver_calls_frac                1.
% 51.49/6.97  --inst_passive_queue_type               priority_queues
% 51.49/6.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 51.49/6.97  --inst_passive_queues_freq              [25;2]
% 51.49/6.97  --inst_dismatching                      true
% 51.49/6.97  --inst_eager_unprocessed_to_passive     true
% 51.49/6.97  --inst_prop_sim_given                   true
% 51.49/6.97  --inst_prop_sim_new                     false
% 51.49/6.97  --inst_subs_new                         false
% 51.49/6.97  --inst_eq_res_simp                      false
% 51.49/6.97  --inst_subs_given                       false
% 51.49/6.97  --inst_orphan_elimination               true
% 51.49/6.97  --inst_learning_loop_flag               true
% 51.49/6.97  --inst_learning_start                   3000
% 51.49/6.97  --inst_learning_factor                  2
% 51.49/6.97  --inst_start_prop_sim_after_learn       3
% 51.49/6.97  --inst_sel_renew                        solver
% 51.49/6.97  --inst_lit_activity_flag                true
% 51.49/6.97  --inst_restr_to_given                   false
% 51.49/6.97  --inst_activity_threshold               500
% 51.49/6.97  --inst_out_proof                        true
% 51.49/6.97  
% 51.49/6.97  ------ Resolution Options
% 51.49/6.97  
% 51.49/6.97  --resolution_flag                       false
% 51.49/6.97  --res_lit_sel                           adaptive
% 51.49/6.97  --res_lit_sel_side                      none
% 51.49/6.97  --res_ordering                          kbo
% 51.49/6.97  --res_to_prop_solver                    active
% 51.49/6.97  --res_prop_simpl_new                    false
% 51.49/6.97  --res_prop_simpl_given                  true
% 51.49/6.97  --res_passive_queue_type                priority_queues
% 51.49/6.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 51.49/6.97  --res_passive_queues_freq               [15;5]
% 51.49/6.97  --res_forward_subs                      full
% 51.49/6.97  --res_backward_subs                     full
% 51.49/6.97  --res_forward_subs_resolution           true
% 51.49/6.97  --res_backward_subs_resolution          true
% 51.49/6.97  --res_orphan_elimination                true
% 51.49/6.97  --res_time_limit                        2.
% 51.49/6.97  --res_out_proof                         true
% 51.49/6.97  
% 51.49/6.97  ------ Superposition Options
% 51.49/6.97  
% 51.49/6.97  --superposition_flag                    true
% 51.49/6.97  --sup_passive_queue_type                priority_queues
% 51.49/6.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 51.49/6.97  --sup_passive_queues_freq               [8;1;4]
% 51.49/6.97  --demod_completeness_check              fast
% 51.49/6.97  --demod_use_ground                      true
% 51.49/6.97  --sup_to_prop_solver                    passive
% 51.49/6.97  --sup_prop_simpl_new                    true
% 51.49/6.97  --sup_prop_simpl_given                  true
% 51.49/6.97  --sup_fun_splitting                     false
% 51.49/6.97  --sup_smt_interval                      50000
% 51.49/6.97  
% 51.49/6.97  ------ Superposition Simplification Setup
% 51.49/6.97  
% 51.49/6.97  --sup_indices_passive                   []
% 51.49/6.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 51.49/6.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 51.49/6.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 51.49/6.97  --sup_full_triv                         [TrivRules;PropSubs]
% 51.49/6.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 51.49/6.97  --sup_full_bw                           [BwDemod]
% 51.49/6.97  --sup_immed_triv                        [TrivRules]
% 51.49/6.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 51.49/6.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 51.49/6.97  --sup_immed_bw_main                     []
% 51.49/6.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 51.49/6.97  --sup_input_triv                        [Unflattening;TrivRules]
% 51.49/6.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 51.49/6.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 51.49/6.97  
% 51.49/6.97  ------ Combination Options
% 51.49/6.97  
% 51.49/6.97  --comb_res_mult                         3
% 51.49/6.97  --comb_sup_mult                         2
% 51.49/6.97  --comb_inst_mult                        10
% 51.49/6.97  
% 51.49/6.97  ------ Debug Options
% 51.49/6.97  
% 51.49/6.97  --dbg_backtrace                         false
% 51.49/6.97  --dbg_dump_prop_clauses                 false
% 51.49/6.97  --dbg_dump_prop_clauses_file            -
% 51.49/6.97  --dbg_out_stat                          false
% 51.49/6.97  
% 51.49/6.97  
% 51.49/6.97  
% 51.49/6.97  
% 51.49/6.97  ------ Proving...
% 51.49/6.97  
% 51.49/6.97  
% 51.49/6.97  % SZS status Theorem for theBenchmark.p
% 51.49/6.97  
% 51.49/6.97  % SZS output start CNFRefutation for theBenchmark.p
% 51.49/6.97  
% 51.49/6.97  fof(f27,conjecture,(
% 51.49/6.97    ! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 51.49/6.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.49/6.97  
% 51.49/6.97  fof(f28,negated_conjecture,(
% 51.49/6.97    ~! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 51.49/6.97    inference(negated_conjecture,[],[f27])).
% 51.49/6.97  
% 51.49/6.97  fof(f37,plain,(
% 51.49/6.97    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 51.49/6.97    inference(ennf_transformation,[],[f28])).
% 51.49/6.97  
% 51.49/6.97  fof(f56,plain,(
% 51.49/6.97    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3))) => (sK4 != sK7 & sK4 != sK6 & r1_tarski(k2_tarski(sK4,sK5),k2_tarski(sK6,sK7)))),
% 51.49/6.97    introduced(choice_axiom,[])).
% 51.49/6.97  
% 51.49/6.97  fof(f57,plain,(
% 51.49/6.97    sK4 != sK7 & sK4 != sK6 & r1_tarski(k2_tarski(sK4,sK5),k2_tarski(sK6,sK7))),
% 51.49/6.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f37,f56])).
% 51.49/6.97  
% 51.49/6.97  fof(f102,plain,(
% 51.49/6.97    r1_tarski(k2_tarski(sK4,sK5),k2_tarski(sK6,sK7))),
% 51.49/6.97    inference(cnf_transformation,[],[f57])).
% 51.49/6.97  
% 51.49/6.97  fof(f26,axiom,(
% 51.49/6.97    ! [X0,X1] : k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k1_tarski(X0)),
% 51.49/6.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.49/6.97  
% 51.49/6.97  fof(f101,plain,(
% 51.49/6.97    ( ! [X0,X1] : (k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k1_tarski(X0)) )),
% 51.49/6.97    inference(cnf_transformation,[],[f26])).
% 51.49/6.97  
% 51.49/6.97  fof(f18,axiom,(
% 51.49/6.97    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 51.49/6.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.49/6.97  
% 51.49/6.97  fof(f90,plain,(
% 51.49/6.97    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 51.49/6.97    inference(cnf_transformation,[],[f18])).
% 51.49/6.97  
% 51.49/6.97  fof(f126,plain,(
% 51.49/6.97    ( ! [X0,X1] : (k3_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X1)) = k2_tarski(X0,X0)) )),
% 51.49/6.97    inference(definition_unfolding,[],[f101,f90,f90])).
% 51.49/6.97  
% 51.49/6.97  fof(f2,axiom,(
% 51.49/6.97    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 51.49/6.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.49/6.97  
% 51.49/6.97  fof(f59,plain,(
% 51.49/6.97    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 51.49/6.97    inference(cnf_transformation,[],[f2])).
% 51.49/6.97  
% 51.49/6.97  fof(f8,axiom,(
% 51.49/6.97    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 51.49/6.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.49/6.97  
% 51.49/6.97  fof(f68,plain,(
% 51.49/6.97    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 51.49/6.97    inference(cnf_transformation,[],[f8])).
% 51.49/6.97  
% 51.49/6.97  fof(f9,axiom,(
% 51.49/6.97    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 51.49/6.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.49/6.97  
% 51.49/6.97  fof(f33,plain,(
% 51.49/6.97    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 51.49/6.97    inference(ennf_transformation,[],[f9])).
% 51.49/6.97  
% 51.49/6.97  fof(f34,plain,(
% 51.49/6.97    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 51.49/6.97    inference(flattening,[],[f33])).
% 51.49/6.97  
% 51.49/6.97  fof(f69,plain,(
% 51.49/6.97    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 51.49/6.97    inference(cnf_transformation,[],[f34])).
% 51.49/6.97  
% 51.49/6.97  fof(f10,axiom,(
% 51.49/6.97    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 51.49/6.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.49/6.97  
% 51.49/6.97  fof(f35,plain,(
% 51.49/6.97    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 51.49/6.97    inference(ennf_transformation,[],[f10])).
% 51.49/6.97  
% 51.49/6.97  fof(f70,plain,(
% 51.49/6.97    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 51.49/6.97    inference(cnf_transformation,[],[f35])).
% 51.49/6.97  
% 51.49/6.97  fof(f25,axiom,(
% 51.49/6.97    ! [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) <=> ((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)))),
% 51.49/6.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.49/6.97  
% 51.49/6.97  fof(f54,plain,(
% 51.49/6.97    ! [X0,X1,X2] : ((k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) | ((X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2))) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0)))),
% 51.49/6.97    inference(nnf_transformation,[],[f25])).
% 51.49/6.97  
% 51.49/6.97  fof(f55,plain,(
% 51.49/6.97    ! [X0,X1,X2] : ((k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) | (X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2)) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0)))),
% 51.49/6.97    inference(flattening,[],[f54])).
% 51.49/6.97  
% 51.49/6.97  fof(f100,plain,(
% 51.49/6.97    ( ! [X2,X0,X1] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) | X0 != X1 | r2_hidden(X0,X2)) )),
% 51.49/6.97    inference(cnf_transformation,[],[f55])).
% 51.49/6.97  
% 51.49/6.97  fof(f7,axiom,(
% 51.49/6.97    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 51.49/6.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.49/6.97  
% 51.49/6.97  fof(f67,plain,(
% 51.49/6.97    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 51.49/6.97    inference(cnf_transformation,[],[f7])).
% 51.49/6.97  
% 51.49/6.97  fof(f122,plain,(
% 51.49/6.97    ( ! [X2,X0,X1] : (k5_xboole_0(k2_tarski(X0,X1),k3_xboole_0(k2_tarski(X0,X1),X2)) = k2_tarski(X0,X0) | X0 != X1 | r2_hidden(X0,X2)) )),
% 51.49/6.97    inference(definition_unfolding,[],[f100,f67,f90])).
% 51.49/6.97  
% 51.49/6.97  fof(f141,plain,(
% 51.49/6.97    ( ! [X2,X1] : (k5_xboole_0(k2_tarski(X1,X1),k3_xboole_0(k2_tarski(X1,X1),X2)) = k2_tarski(X1,X1) | r2_hidden(X1,X2)) )),
% 51.49/6.97    inference(equality_resolution,[],[f122])).
% 51.49/6.97  
% 51.49/6.97  fof(f97,plain,(
% 51.49/6.97    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0)) )),
% 51.49/6.97    inference(cnf_transformation,[],[f55])).
% 51.49/6.97  
% 51.49/6.97  fof(f125,plain,(
% 51.49/6.97    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | k5_xboole_0(k2_tarski(X0,X1),k3_xboole_0(k2_tarski(X0,X1),X2)) != k2_tarski(X0,X0)) )),
% 51.49/6.97    inference(definition_unfolding,[],[f97,f67,f90])).
% 51.49/6.97  
% 51.49/6.97  fof(f5,axiom,(
% 51.49/6.97    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 51.49/6.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.49/6.97  
% 51.49/6.97  fof(f32,plain,(
% 51.49/6.97    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 51.49/6.97    inference(ennf_transformation,[],[f5])).
% 51.49/6.97  
% 51.49/6.97  fof(f40,plain,(
% 51.49/6.97    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 51.49/6.97    introduced(choice_axiom,[])).
% 51.49/6.97  
% 51.49/6.97  fof(f41,plain,(
% 51.49/6.97    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 51.49/6.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f40])).
% 51.49/6.97  
% 51.49/6.97  fof(f63,plain,(
% 51.49/6.97    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 51.49/6.97    inference(cnf_transformation,[],[f41])).
% 51.49/6.97  
% 51.49/6.97  fof(f4,axiom,(
% 51.49/6.97    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 51.49/6.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.49/6.97  
% 51.49/6.97  fof(f30,plain,(
% 51.49/6.97    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 51.49/6.97    inference(rectify,[],[f4])).
% 51.49/6.97  
% 51.49/6.97  fof(f31,plain,(
% 51.49/6.97    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 51.49/6.97    inference(ennf_transformation,[],[f30])).
% 51.49/6.97  
% 51.49/6.97  fof(f38,plain,(
% 51.49/6.97    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 51.49/6.97    introduced(choice_axiom,[])).
% 51.49/6.97  
% 51.49/6.97  fof(f39,plain,(
% 51.49/6.97    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 51.49/6.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f38])).
% 51.49/6.97  
% 51.49/6.97  fof(f62,plain,(
% 51.49/6.97    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 51.49/6.97    inference(cnf_transformation,[],[f39])).
% 51.49/6.97  
% 51.49/6.97  fof(f13,axiom,(
% 51.49/6.97    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 51.49/6.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.49/6.97  
% 51.49/6.97  fof(f73,plain,(
% 51.49/6.97    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 51.49/6.97    inference(cnf_transformation,[],[f13])).
% 51.49/6.97  
% 51.49/6.97  fof(f11,axiom,(
% 51.49/6.97    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 51.49/6.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.49/6.97  
% 51.49/6.97  fof(f71,plain,(
% 51.49/6.97    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 51.49/6.97    inference(cnf_transformation,[],[f11])).
% 51.49/6.97  
% 51.49/6.97  fof(f110,plain,(
% 51.49/6.97    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) )),
% 51.49/6.97    inference(definition_unfolding,[],[f71,f67,f67])).
% 51.49/6.97  
% 51.49/6.97  fof(f3,axiom,(
% 51.49/6.97    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 51.49/6.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.49/6.97  
% 51.49/6.97  fof(f29,plain,(
% 51.49/6.97    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 51.49/6.97    inference(rectify,[],[f3])).
% 51.49/6.97  
% 51.49/6.97  fof(f60,plain,(
% 51.49/6.97    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 51.49/6.97    inference(cnf_transformation,[],[f29])).
% 51.49/6.97  
% 51.49/6.97  fof(f12,axiom,(
% 51.49/6.97    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 51.49/6.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.49/6.97  
% 51.49/6.97  fof(f72,plain,(
% 51.49/6.97    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 51.49/6.97    inference(cnf_transformation,[],[f12])).
% 51.49/6.97  
% 51.49/6.97  fof(f103,plain,(
% 51.49/6.97    sK4 != sK6),
% 51.49/6.97    inference(cnf_transformation,[],[f57])).
% 51.49/6.97  
% 51.49/6.97  fof(f104,plain,(
% 51.49/6.97    sK4 != sK7),
% 51.49/6.97    inference(cnf_transformation,[],[f57])).
% 51.49/6.97  
% 51.49/6.97  fof(f16,axiom,(
% 51.49/6.97    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 51.49/6.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.49/6.97  
% 51.49/6.97  fof(f49,plain,(
% 51.49/6.97    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 51.49/6.97    inference(nnf_transformation,[],[f16])).
% 51.49/6.97  
% 51.49/6.97  fof(f50,plain,(
% 51.49/6.97    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 51.49/6.97    inference(flattening,[],[f49])).
% 51.49/6.97  
% 51.49/6.97  fof(f51,plain,(
% 51.49/6.97    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 51.49/6.97    inference(rectify,[],[f50])).
% 51.49/6.97  
% 51.49/6.97  fof(f52,plain,(
% 51.49/6.97    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK3(X0,X1,X2) != X1 & sK3(X0,X1,X2) != X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2))))),
% 51.49/6.97    introduced(choice_axiom,[])).
% 51.49/6.97  
% 51.49/6.97  fof(f53,plain,(
% 51.49/6.97    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK3(X0,X1,X2) != X1 & sK3(X0,X1,X2) != X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 51.49/6.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f51,f52])).
% 51.49/6.97  
% 51.49/6.97  fof(f83,plain,(
% 51.49/6.97    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 51.49/6.97    inference(cnf_transformation,[],[f53])).
% 51.49/6.97  
% 51.49/6.97  fof(f140,plain,(
% 51.49/6.97    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k2_tarski(X0,X1))) )),
% 51.49/6.97    inference(equality_resolution,[],[f83])).
% 51.49/6.97  
% 51.49/6.97  fof(f84,plain,(
% 51.49/6.97    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 51.49/6.97    inference(cnf_transformation,[],[f53])).
% 51.49/6.97  
% 51.49/6.97  fof(f138,plain,(
% 51.49/6.97    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_tarski(X4,X1) != X2) )),
% 51.49/6.97    inference(equality_resolution,[],[f84])).
% 51.49/6.97  
% 51.49/6.97  fof(f139,plain,(
% 51.49/6.97    ( ! [X4,X1] : (r2_hidden(X4,k2_tarski(X4,X1))) )),
% 51.49/6.97    inference(equality_resolution,[],[f138])).
% 51.49/6.97  
% 51.49/6.97  cnf(c_38,negated_conjecture,
% 51.49/6.97      ( r1_tarski(k2_tarski(sK4,sK5),k2_tarski(sK6,sK7)) ),
% 51.49/6.97      inference(cnf_transformation,[],[f102]) ).
% 51.49/6.97  
% 51.49/6.97  cnf(c_957,plain,
% 51.49/6.97      ( r1_tarski(k2_tarski(sK4,sK5),k2_tarski(sK6,sK7)) = iProver_top ),
% 51.49/6.97      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 51.49/6.97  
% 51.49/6.97  cnf(c_35,plain,
% 51.49/6.97      ( k3_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X1)) = k2_tarski(X0,X0) ),
% 51.49/6.97      inference(cnf_transformation,[],[f126]) ).
% 51.49/6.97  
% 51.49/6.97  cnf(c_3,plain,
% 51.49/6.97      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 51.49/6.97      inference(cnf_transformation,[],[f59]) ).
% 51.49/6.97  
% 51.49/6.97  cnf(c_11,plain,
% 51.49/6.97      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 51.49/6.97      inference(cnf_transformation,[],[f68]) ).
% 51.49/6.97  
% 51.49/6.97  cnf(c_978,plain,
% 51.49/6.97      ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
% 51.49/6.97      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 51.49/6.97  
% 51.49/6.97  cnf(c_1960,plain,
% 51.49/6.97      ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
% 51.49/6.97      inference(superposition,[status(thm)],[c_3,c_978]) ).
% 51.49/6.97  
% 51.49/6.97  cnf(c_1973,plain,
% 51.49/6.97      ( r1_tarski(k2_tarski(X0,X0),k2_tarski(X0,X1)) = iProver_top ),
% 51.49/6.97      inference(superposition,[status(thm)],[c_35,c_1960]) ).
% 51.49/6.97  
% 51.49/6.97  cnf(c_12,plain,
% 51.49/6.97      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 51.49/6.97      inference(cnf_transformation,[],[f69]) ).
% 51.49/6.97  
% 51.49/6.97  cnf(c_977,plain,
% 51.49/6.97      ( r1_tarski(X0,X1) != iProver_top
% 51.49/6.97      | r1_tarski(X1,X2) != iProver_top
% 51.49/6.97      | r1_tarski(X0,X2) = iProver_top ),
% 51.49/6.97      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 51.49/6.97  
% 51.49/6.97  cnf(c_12788,plain,
% 51.49/6.97      ( r1_tarski(k2_tarski(X0,X1),X2) != iProver_top
% 51.49/6.97      | r1_tarski(k2_tarski(X0,X0),X2) = iProver_top ),
% 51.49/6.97      inference(superposition,[status(thm)],[c_1973,c_977]) ).
% 51.49/6.97  
% 51.49/6.97  cnf(c_168649,plain,
% 51.49/6.97      ( r1_tarski(k2_tarski(sK4,sK4),k2_tarski(sK6,sK7)) = iProver_top ),
% 51.49/6.97      inference(superposition,[status(thm)],[c_957,c_12788]) ).
% 51.49/6.97  
% 51.49/6.97  cnf(c_13,plain,
% 51.49/6.97      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 51.49/6.97      inference(cnf_transformation,[],[f70]) ).
% 51.49/6.97  
% 51.49/6.97  cnf(c_976,plain,
% 51.49/6.97      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 51.49/6.97      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 51.49/6.97  
% 51.49/6.97  cnf(c_169918,plain,
% 51.49/6.97      ( k3_xboole_0(k2_tarski(sK4,sK4),k2_tarski(sK6,sK7)) = k2_tarski(sK4,sK4) ),
% 51.49/6.97      inference(superposition,[status(thm)],[c_168649,c_976]) ).
% 51.49/6.97  
% 51.49/6.97  cnf(c_31,plain,
% 51.49/6.97      ( r2_hidden(X0,X1)
% 51.49/6.97      | k5_xboole_0(k2_tarski(X0,X0),k3_xboole_0(k2_tarski(X0,X0),X1)) = k2_tarski(X0,X0) ),
% 51.49/6.97      inference(cnf_transformation,[],[f141]) ).
% 51.49/6.97  
% 51.49/6.97  cnf(c_961,plain,
% 51.49/6.97      ( k5_xboole_0(k2_tarski(X0,X0),k3_xboole_0(k2_tarski(X0,X0),X1)) = k2_tarski(X0,X0)
% 51.49/6.97      | r2_hidden(X0,X1) = iProver_top ),
% 51.49/6.97      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 51.49/6.97  
% 51.49/6.97  cnf(c_3711,plain,
% 51.49/6.97      ( k3_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK6,sK7)) = k2_tarski(sK4,sK5) ),
% 51.49/6.97      inference(superposition,[status(thm)],[c_957,c_976]) ).
% 51.49/6.97  
% 51.49/6.97  cnf(c_34,plain,
% 51.49/6.97      ( ~ r2_hidden(X0,X1)
% 51.49/6.97      | k5_xboole_0(k2_tarski(X0,X2),k3_xboole_0(k2_tarski(X0,X2),X1)) != k2_tarski(X0,X0) ),
% 51.49/6.97      inference(cnf_transformation,[],[f125]) ).
% 51.49/6.97  
% 51.49/6.97  cnf(c_958,plain,
% 51.49/6.97      ( k5_xboole_0(k2_tarski(X0,X1),k3_xboole_0(k2_tarski(X0,X1),X2)) != k2_tarski(X0,X0)
% 51.49/6.97      | r2_hidden(X0,X2) != iProver_top ),
% 51.49/6.97      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 51.49/6.97  
% 51.49/6.97  cnf(c_16415,plain,
% 51.49/6.97      ( k5_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK4,sK5)) != k2_tarski(sK4,sK4)
% 51.49/6.97      | r2_hidden(sK4,k2_tarski(sK6,sK7)) != iProver_top ),
% 51.49/6.97      inference(superposition,[status(thm)],[c_3711,c_958]) ).
% 51.49/6.97  
% 51.49/6.97  cnf(c_7,plain,
% 51.49/6.97      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 51.49/6.97      inference(cnf_transformation,[],[f63]) ).
% 51.49/6.97  
% 51.49/6.97  cnf(c_981,plain,
% 51.49/6.97      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 51.49/6.97      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 51.49/6.97  
% 51.49/6.97  cnf(c_5,plain,
% 51.49/6.97      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2)) | ~ r1_xboole_0(X1,X2) ),
% 51.49/6.97      inference(cnf_transformation,[],[f62]) ).
% 51.49/6.97  
% 51.49/6.97  cnf(c_15,plain,
% 51.49/6.97      ( r1_xboole_0(X0,k1_xboole_0) ),
% 51.49/6.97      inference(cnf_transformation,[],[f73]) ).
% 51.49/6.97  
% 51.49/6.97  cnf(c_338,plain,
% 51.49/6.97      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
% 51.49/6.97      | X3 != X1
% 51.49/6.97      | k1_xboole_0 != X2 ),
% 51.49/6.97      inference(resolution_lifted,[status(thm)],[c_5,c_15]) ).
% 51.49/6.97  
% 51.49/6.97  cnf(c_339,plain,
% 51.49/6.97      ( ~ r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) ),
% 51.49/6.97      inference(unflattening,[status(thm)],[c_338]) ).
% 51.49/6.97  
% 51.49/6.97  cnf(c_955,plain,
% 51.49/6.97      ( r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) != iProver_top ),
% 51.49/6.97      inference(predicate_to_equality,[status(thm)],[c_339]) ).
% 51.49/6.97  
% 51.49/6.97  cnf(c_2597,plain,
% 51.49/6.97      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 51.49/6.97      inference(superposition,[status(thm)],[c_981,c_955]) ).
% 51.49/6.97  
% 51.49/6.97  cnf(c_0,plain,
% 51.49/6.97      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
% 51.49/6.97      inference(cnf_transformation,[],[f110]) ).
% 51.49/6.97  
% 51.49/6.97  cnf(c_2856,plain,
% 51.49/6.97      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k1_xboole_0))) = k3_xboole_0(X0,k1_xboole_0) ),
% 51.49/6.97      inference(superposition,[status(thm)],[c_2597,c_0]) ).
% 51.49/6.97  
% 51.49/6.97  cnf(c_2872,plain,
% 51.49/6.97      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k1_xboole_0))) = k1_xboole_0 ),
% 51.49/6.97      inference(light_normalisation,[status(thm)],[c_2856,c_2597]) ).
% 51.49/6.97  
% 51.49/6.97  cnf(c_4,plain,
% 51.49/6.97      ( k3_xboole_0(X0,X0) = X0 ),
% 51.49/6.97      inference(cnf_transformation,[],[f60]) ).
% 51.49/6.97  
% 51.49/6.97  cnf(c_14,plain,
% 51.49/6.97      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 51.49/6.97      inference(cnf_transformation,[],[f72]) ).
% 51.49/6.97  
% 51.49/6.97  cnf(c_2874,plain,
% 51.49/6.97      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 51.49/6.97      inference(light_normalisation,[status(thm)],[c_2872,c_4,c_14]) ).
% 51.49/6.97  
% 51.49/6.97  cnf(c_16441,plain,
% 51.49/6.97      ( k2_tarski(sK4,sK4) != k1_xboole_0
% 51.49/6.97      | r2_hidden(sK4,k2_tarski(sK6,sK7)) != iProver_top ),
% 51.49/6.97      inference(demodulation,[status(thm)],[c_16415,c_2874]) ).
% 51.49/6.97  
% 51.49/6.97  cnf(c_37,negated_conjecture,
% 51.49/6.97      ( sK4 != sK6 ),
% 51.49/6.97      inference(cnf_transformation,[],[f103]) ).
% 51.49/6.97  
% 51.49/6.97  cnf(c_36,negated_conjecture,
% 51.49/6.97      ( sK4 != sK7 ),
% 51.49/6.97      inference(cnf_transformation,[],[f104]) ).
% 51.49/6.97  
% 51.49/6.97  cnf(c_29,plain,
% 51.49/6.97      ( ~ r2_hidden(X0,k2_tarski(X1,X2)) | X0 = X1 | X0 = X2 ),
% 51.49/6.97      inference(cnf_transformation,[],[f140]) ).
% 51.49/6.97  
% 51.49/6.97  cnf(c_1199,plain,
% 51.49/6.97      ( ~ r2_hidden(sK4,k2_tarski(sK6,X0)) | sK4 = X0 | sK4 = sK6 ),
% 51.49/6.97      inference(instantiation,[status(thm)],[c_29]) ).
% 51.49/6.97  
% 51.49/6.97  cnf(c_3659,plain,
% 51.49/6.97      ( ~ r2_hidden(sK4,k2_tarski(sK6,sK7)) | sK4 = sK6 | sK4 = sK7 ),
% 51.49/6.97      inference(instantiation,[status(thm)],[c_1199]) ).
% 51.49/6.97  
% 51.49/6.97  cnf(c_3660,plain,
% 51.49/6.97      ( sK4 = sK6
% 51.49/6.97      | sK4 = sK7
% 51.49/6.97      | r2_hidden(sK4,k2_tarski(sK6,sK7)) != iProver_top ),
% 51.49/6.97      inference(predicate_to_equality,[status(thm)],[c_3659]) ).
% 51.49/6.97  
% 51.49/6.97  cnf(c_16705,plain,
% 51.49/6.97      ( r2_hidden(sK4,k2_tarski(sK6,sK7)) != iProver_top ),
% 51.49/6.97      inference(global_propositional_subsumption,
% 51.49/6.97                [status(thm)],
% 51.49/6.97                [c_16441,c_37,c_36,c_3660]) ).
% 51.49/6.97  
% 51.49/6.97  cnf(c_16710,plain,
% 51.49/6.97      ( k5_xboole_0(k2_tarski(sK4,sK4),k3_xboole_0(k2_tarski(sK4,sK4),k2_tarski(sK6,sK7))) = k2_tarski(sK4,sK4) ),
% 51.49/6.97      inference(superposition,[status(thm)],[c_961,c_16705]) ).
% 51.49/6.97  
% 51.49/6.97  cnf(c_16717,plain,
% 51.49/6.97      ( k5_xboole_0(k2_tarski(sK4,sK4),k3_xboole_0(k2_tarski(sK4,sK4),k2_tarski(sK4,sK4))) = k3_xboole_0(k2_tarski(sK4,sK4),k2_tarski(sK6,sK7)) ),
% 51.49/6.97      inference(superposition,[status(thm)],[c_16710,c_0]) ).
% 51.49/6.97  
% 51.49/6.97  cnf(c_16736,plain,
% 51.49/6.97      ( k3_xboole_0(k2_tarski(sK4,sK4),k2_tarski(sK6,sK7)) = k1_xboole_0 ),
% 51.49/6.97      inference(demodulation,[status(thm)],[c_16717,c_35,c_2874]) ).
% 51.49/6.97  
% 51.49/6.97  cnf(c_169921,plain,
% 51.49/6.97      ( k2_tarski(sK4,sK4) = k1_xboole_0 ),
% 51.49/6.97      inference(light_normalisation,[status(thm)],[c_169918,c_16736]) ).
% 51.49/6.97  
% 51.49/6.97  cnf(c_16396,plain,
% 51.49/6.97      ( k3_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X0)
% 51.49/6.97      | r2_hidden(X0,k5_xboole_0(k2_tarski(X0,X1),k3_xboole_0(k2_tarski(X0,X1),X2))) != iProver_top ),
% 51.49/6.97      inference(superposition,[status(thm)],[c_0,c_958]) ).
% 51.49/6.97  
% 51.49/6.97  cnf(c_33118,plain,
% 51.49/6.97      ( k2_tarski(sK4,sK4) != k1_xboole_0
% 51.49/6.97      | r2_hidden(sK4,k5_xboole_0(k2_tarski(sK4,sK4),k3_xboole_0(k2_tarski(sK4,sK4),k2_tarski(sK6,sK7)))) != iProver_top ),
% 51.49/6.97      inference(superposition,[status(thm)],[c_16736,c_16396]) ).
% 51.49/6.97  
% 51.49/6.97  cnf(c_33183,plain,
% 51.49/6.97      ( k2_tarski(sK4,sK4) != k1_xboole_0
% 51.49/6.97      | r2_hidden(sK4,k5_xboole_0(k2_tarski(sK4,sK4),k1_xboole_0)) != iProver_top ),
% 51.49/6.97      inference(light_normalisation,[status(thm)],[c_33118,c_16736]) ).
% 51.49/6.97  
% 51.49/6.97  cnf(c_33184,plain,
% 51.49/6.97      ( k2_tarski(sK4,sK4) != k1_xboole_0
% 51.49/6.97      | r2_hidden(sK4,k2_tarski(sK4,sK4)) != iProver_top ),
% 51.49/6.97      inference(demodulation,[status(thm)],[c_33183,c_14]) ).
% 51.49/6.97  
% 51.49/6.97  cnf(c_28,plain,
% 51.49/6.97      ( r2_hidden(X0,k2_tarski(X0,X1)) ),
% 51.49/6.97      inference(cnf_transformation,[],[f139]) ).
% 51.49/6.97  
% 51.49/6.97  cnf(c_963,plain,
% 51.49/6.97      ( r2_hidden(X0,k2_tarski(X0,X1)) = iProver_top ),
% 51.49/6.97      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 51.49/6.97  
% 51.49/6.97  cnf(c_33792,plain,
% 51.49/6.97      ( k2_tarski(sK4,sK4) != k1_xboole_0 ),
% 51.49/6.97      inference(forward_subsumption_resolution,
% 51.49/6.97                [status(thm)],
% 51.49/6.97                [c_33184,c_963]) ).
% 51.49/6.97  
% 51.49/6.97  cnf(contradiction,plain,
% 51.49/6.97      ( $false ),
% 51.49/6.97      inference(minisat,[status(thm)],[c_169921,c_33792]) ).
% 51.49/6.97  
% 51.49/6.97  
% 51.49/6.97  % SZS output end CNFRefutation for theBenchmark.p
% 51.49/6.97  
% 51.49/6.97  ------                               Statistics
% 51.49/6.97  
% 51.49/6.97  ------ General
% 51.49/6.97  
% 51.49/6.97  abstr_ref_over_cycles:                  0
% 51.49/6.97  abstr_ref_under_cycles:                 0
% 51.49/6.97  gc_basic_clause_elim:                   0
% 51.49/6.97  forced_gc_time:                         0
% 51.49/6.97  parsing_time:                           0.013
% 51.49/6.97  unif_index_cands_time:                  0.
% 51.49/6.97  unif_index_add_time:                    0.
% 51.49/6.97  orderings_time:                         0.
% 51.49/6.97  out_proof_time:                         0.017
% 51.49/6.97  total_time:                             6.143
% 51.49/6.97  num_of_symbols:                         47
% 51.49/6.97  num_of_terms:                           184836
% 51.49/6.97  
% 51.49/6.97  ------ Preprocessing
% 51.49/6.97  
% 51.49/6.97  num_of_splits:                          0
% 51.49/6.97  num_of_split_atoms:                     0
% 51.49/6.97  num_of_reused_defs:                     0
% 51.49/6.97  num_eq_ax_congr_red:                    55
% 51.49/6.97  num_of_sem_filtered_clauses:            1
% 51.49/6.97  num_of_subtypes:                        0
% 51.49/6.97  monotx_restored_types:                  0
% 51.49/6.97  sat_num_of_epr_types:                   0
% 51.49/6.97  sat_num_of_non_cyclic_types:            0
% 51.49/6.97  sat_guarded_non_collapsed_types:        0
% 51.49/6.97  num_pure_diseq_elim:                    0
% 51.49/6.97  simp_replaced_by:                       0
% 51.49/6.97  res_preprocessed:                       164
% 51.49/6.97  prep_upred:                             0
% 51.49/6.97  prep_unflattend:                        4
% 51.49/6.97  smt_new_axioms:                         0
% 51.49/6.97  pred_elim_cands:                        2
% 51.49/6.97  pred_elim:                              1
% 51.49/6.97  pred_elim_cl:                           1
% 51.49/6.97  pred_elim_cycles:                       3
% 51.49/6.97  merged_defs:                            0
% 51.49/6.97  merged_defs_ncl:                        0
% 51.49/6.97  bin_hyper_res:                          0
% 51.49/6.97  prep_cycles:                            4
% 51.49/6.97  pred_elim_time:                         0.002
% 51.49/6.97  splitting_time:                         0.
% 51.49/6.97  sem_filter_time:                        0.
% 51.49/6.97  monotx_time:                            0.
% 51.49/6.97  subtype_inf_time:                       0.
% 51.49/6.97  
% 51.49/6.97  ------ Problem properties
% 51.49/6.97  
% 51.49/6.97  clauses:                                37
% 51.49/6.97  conjectures:                            3
% 51.49/6.97  epr:                                    5
% 51.49/6.97  horn:                                   29
% 51.49/6.97  ground:                                 3
% 51.49/6.97  unary:                                  19
% 51.49/6.97  binary:                                 5
% 51.49/6.97  lits:                                   72
% 51.49/6.97  lits_eq:                                40
% 51.49/6.97  fd_pure:                                0
% 51.49/6.97  fd_pseudo:                              0
% 51.49/6.97  fd_cond:                                1
% 51.49/6.97  fd_pseudo_cond:                         9
% 51.49/6.97  ac_symbols:                             0
% 51.49/6.97  
% 51.49/6.97  ------ Propositional Solver
% 51.49/6.97  
% 51.49/6.97  prop_solver_calls:                      41
% 51.49/6.97  prop_fast_solver_calls:                 2057
% 51.49/6.97  smt_solver_calls:                       0
% 51.49/6.97  smt_fast_solver_calls:                  0
% 51.49/6.97  prop_num_of_clauses:                    40829
% 51.49/6.97  prop_preprocess_simplified:             61324
% 51.49/6.97  prop_fo_subsumed:                       4
% 51.49/6.97  prop_solver_time:                       0.
% 51.49/6.97  smt_solver_time:                        0.
% 51.49/6.97  smt_fast_solver_time:                   0.
% 51.49/6.97  prop_fast_solver_time:                  0.
% 51.49/6.97  prop_unsat_core_time:                   0.003
% 51.49/6.97  
% 51.49/6.97  ------ QBF
% 51.49/6.97  
% 51.49/6.97  qbf_q_res:                              0
% 51.49/6.97  qbf_num_tautologies:                    0
% 51.49/6.97  qbf_prep_cycles:                        0
% 51.49/6.97  
% 51.49/6.97  ------ BMC1
% 51.49/6.97  
% 51.49/6.97  bmc1_current_bound:                     -1
% 51.49/6.97  bmc1_last_solved_bound:                 -1
% 51.49/6.97  bmc1_unsat_core_size:                   -1
% 51.49/6.97  bmc1_unsat_core_parents_size:           -1
% 51.49/6.97  bmc1_merge_next_fun:                    0
% 51.49/6.97  bmc1_unsat_core_clauses_time:           0.
% 51.49/6.97  
% 51.49/6.97  ------ Instantiation
% 51.49/6.97  
% 51.49/6.97  inst_num_of_clauses:                    7791
% 51.49/6.97  inst_num_in_passive:                    4432
% 51.49/6.97  inst_num_in_active:                     1875
% 51.49/6.97  inst_num_in_unprocessed:                1495
% 51.49/6.97  inst_num_of_loops:                      2740
% 51.49/6.97  inst_num_of_learning_restarts:          0
% 51.49/6.97  inst_num_moves_active_passive:          863
% 51.49/6.97  inst_lit_activity:                      0
% 51.49/6.97  inst_lit_activity_moves:                0
% 51.49/6.97  inst_num_tautologies:                   0
% 51.49/6.97  inst_num_prop_implied:                  0
% 51.49/6.97  inst_num_existing_simplified:           0
% 51.49/6.97  inst_num_eq_res_simplified:             0
% 51.49/6.97  inst_num_child_elim:                    0
% 51.49/6.97  inst_num_of_dismatching_blockings:      18722
% 51.49/6.97  inst_num_of_non_proper_insts:           11422
% 51.49/6.97  inst_num_of_duplicates:                 0
% 51.49/6.97  inst_inst_num_from_inst_to_res:         0
% 51.49/6.97  inst_dismatching_checking_time:         0.
% 51.49/6.97  
% 51.49/6.97  ------ Resolution
% 51.49/6.97  
% 51.49/6.97  res_num_of_clauses:                     0
% 51.49/6.97  res_num_in_passive:                     0
% 51.49/6.97  res_num_in_active:                      0
% 51.49/6.97  res_num_of_loops:                       168
% 51.49/6.97  res_forward_subset_subsumed:            2543
% 51.49/6.97  res_backward_subset_subsumed:           42
% 51.49/6.97  res_forward_subsumed:                   0
% 51.49/6.97  res_backward_subsumed:                  0
% 51.49/6.97  res_forward_subsumption_resolution:     0
% 51.49/6.97  res_backward_subsumption_resolution:    0
% 51.49/6.97  res_clause_to_clause_subsumption:       125400
% 51.49/6.97  res_orphan_elimination:                 0
% 51.49/6.97  res_tautology_del:                      680
% 51.49/6.97  res_num_eq_res_simplified:              0
% 51.49/6.97  res_num_sel_changes:                    0
% 51.49/6.97  res_moves_from_active_to_pass:          0
% 51.49/6.97  
% 51.49/6.97  ------ Superposition
% 51.49/6.97  
% 51.49/6.97  sup_time_total:                         0.
% 51.49/6.97  sup_time_generating:                    0.
% 51.49/6.98  sup_time_sim_full:                      0.
% 51.49/6.98  sup_time_sim_immed:                     0.
% 51.49/6.98  
% 51.49/6.98  sup_num_of_clauses:                     5710
% 51.49/6.98  sup_num_in_active:                      501
% 51.49/6.98  sup_num_in_passive:                     5209
% 51.49/6.98  sup_num_of_loops:                       547
% 51.49/6.98  sup_fw_superposition:                   12915
% 51.49/6.98  sup_bw_superposition:                   9525
% 51.49/6.98  sup_immediate_simplified:               9517
% 51.49/6.98  sup_given_eliminated:                   9
% 51.49/6.98  comparisons_done:                       0
% 51.49/6.98  comparisons_avoided:                    250
% 51.49/6.98  
% 51.49/6.98  ------ Simplifications
% 51.49/6.98  
% 51.49/6.98  
% 51.49/6.98  sim_fw_subset_subsumed:                 39
% 51.49/6.98  sim_bw_subset_subsumed:                 7
% 51.49/6.98  sim_fw_subsumed:                        1047
% 51.49/6.98  sim_bw_subsumed:                        118
% 51.49/6.98  sim_fw_subsumption_res:                 15
% 51.49/6.98  sim_bw_subsumption_res:                 0
% 51.49/6.98  sim_tautology_del:                      18
% 51.49/6.98  sim_eq_tautology_del:                   2376
% 51.49/6.98  sim_eq_res_simp:                        17
% 51.49/6.98  sim_fw_demodulated:                     9142
% 51.49/6.98  sim_bw_demodulated:                     181
% 51.49/6.98  sim_light_normalised:                   2615
% 51.49/6.98  sim_joinable_taut:                      0
% 51.49/6.98  sim_joinable_simp:                      0
% 51.49/6.98  sim_ac_normalised:                      0
% 51.49/6.98  sim_smt_subsumption:                    0
% 51.49/6.98  
%------------------------------------------------------------------------------
