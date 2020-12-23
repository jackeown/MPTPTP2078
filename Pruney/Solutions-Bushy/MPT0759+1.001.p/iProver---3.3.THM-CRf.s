%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0759+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:03 EST 2020

% Result     : Theorem 3.57s
% Output     : CNFRefutation 3.57s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 104 expanded)
%              Number of clauses        :   33 (  35 expanded)
%              Number of leaves         :   12 (  24 expanded)
%              Depth                    :    9
%              Number of atoms          :  266 ( 522 expanded)
%              Number of equality atoms :   99 ( 180 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f19])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f35,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f2])).

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

fof(f47,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f24])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f3])).

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
     => ( ( r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f17])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X1)
      | ~ r2_hidden(sK1(X0,X1,X2),X0)
      | ~ r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k6_subset_1(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X1)
      | ~ r2_hidden(sK1(X0,X1,X2),X0)
      | ~ r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f33,f34])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k6_subset_1(X0,X1) = X2
      | ~ r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f32,f34])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k6_subset_1(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f31,f34])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f45,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f25])).

fof(f46,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f45])).

fof(f6,conjecture,(
    ! [X0] : k6_subset_1(k1_ordinal1(X0),k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] : k6_subset_1(k1_ordinal1(X0),k1_tarski(X0)) = X0 ),
    inference(negated_conjecture,[],[f6])).

fof(f9,plain,(
    ? [X0] : k6_subset_1(k1_ordinal1(X0),k1_tarski(X0)) != X0 ),
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,
    ( ? [X0] : k6_subset_1(k1_ordinal1(X0),k1_tarski(X0)) != X0
   => k6_subset_1(k1_ordinal1(sK2),k1_tarski(sK2)) != sK2 ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    k6_subset_1(k1_ordinal1(sK2),k1_tarski(sK2)) != sK2 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f9,f21])).

fof(f38,plain,(
    k6_subset_1(k1_ordinal1(sK2),k1_tarski(sK2)) != sK2 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_163,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2311,plain,
    ( X0 != X1
    | X0 = sK1(k1_ordinal1(sK2),k1_tarski(sK2),sK2)
    | sK1(k1_ordinal1(sK2),k1_tarski(sK2),sK2) != X1 ),
    inference(instantiation,[status(thm)],[c_163])).

cnf(c_2312,plain,
    ( sK1(k1_ordinal1(sK2),k1_tarski(sK2),sK2) != sK2
    | sK2 = sK1(k1_ordinal1(sK2),k1_tarski(sK2),sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_2311])).

cnf(c_164,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1442,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK1(k1_ordinal1(sK2),k1_tarski(sK2),sK2),sK2)
    | X0 != sK1(k1_ordinal1(sK2),k1_tarski(sK2),sK2)
    | X1 != sK2 ),
    inference(instantiation,[status(thm)],[c_164])).

cnf(c_1444,plain,
    ( ~ r2_hidden(sK1(k1_ordinal1(sK2),k1_tarski(sK2),sK2),sK2)
    | r2_hidden(sK2,sK2)
    | sK2 != sK1(k1_ordinal1(sK2),k1_tarski(sK2),sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1442])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k1_ordinal1(X1)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1187,plain,
    ( r2_hidden(sK1(k1_ordinal1(sK2),k1_tarski(sK2),X0),k1_ordinal1(sK2))
    | ~ r2_hidden(sK1(k1_ordinal1(sK2),k1_tarski(sK2),X0),sK2) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1189,plain,
    ( r2_hidden(sK1(k1_ordinal1(sK2),k1_tarski(sK2),sK2),k1_ordinal1(sK2))
    | ~ r2_hidden(sK1(k1_ordinal1(sK2),k1_tarski(sK2),sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_1187])).

cnf(c_459,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK1(k1_ordinal1(sK2),k1_tarski(sK2),sK2),k1_tarski(sK2))
    | sK1(k1_ordinal1(sK2),k1_tarski(sK2),sK2) != X0
    | k1_tarski(sK2) != X1 ),
    inference(instantiation,[status(thm)],[c_164])).

cnf(c_711,plain,
    ( ~ r2_hidden(X0,k1_tarski(sK2))
    | r2_hidden(sK1(k1_ordinal1(sK2),k1_tarski(sK2),sK2),k1_tarski(sK2))
    | sK1(k1_ordinal1(sK2),k1_tarski(sK2),sK2) != X0
    | k1_tarski(sK2) != k1_tarski(sK2) ),
    inference(instantiation,[status(thm)],[c_459])).

cnf(c_713,plain,
    ( r2_hidden(sK1(k1_ordinal1(sK2),k1_tarski(sK2),sK2),k1_tarski(sK2))
    | ~ r2_hidden(sK2,k1_tarski(sK2))
    | sK1(k1_ordinal1(sK2),k1_tarski(sK2),sK2) != sK2
    | k1_tarski(sK2) != k1_tarski(sK2) ),
    inference(instantiation,[status(thm)],[c_711])).

cnf(c_13,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_ordinal1(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_662,plain,
    ( r2_hidden(sK1(k1_ordinal1(sK2),k1_tarski(sK2),sK2),X0)
    | ~ r2_hidden(sK1(k1_ordinal1(sK2),k1_tarski(sK2),sK2),k1_ordinal1(X0))
    | sK1(k1_ordinal1(sK2),k1_tarski(sK2),sK2) = X0 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_669,plain,
    ( ~ r2_hidden(sK1(k1_ordinal1(sK2),k1_tarski(sK2),sK2),k1_ordinal1(sK2))
    | r2_hidden(sK1(k1_ordinal1(sK2),k1_tarski(sK2),sK2),sK2)
    | sK1(k1_ordinal1(sK2),k1_tarski(sK2),sK2) = sK2 ),
    inference(instantiation,[status(thm)],[c_662])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_663,plain,
    ( ~ r2_hidden(sK1(k1_ordinal1(sK2),k1_tarski(sK2),sK2),k1_tarski(X0))
    | sK1(k1_ordinal1(sK2),k1_tarski(sK2),sK2) = X0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_665,plain,
    ( ~ r2_hidden(sK1(k1_ordinal1(sK2),k1_tarski(sK2),sK2),k1_tarski(sK2))
    | sK1(k1_ordinal1(sK2),k1_tarski(sK2),sK2) = sK2 ),
    inference(instantiation,[status(thm)],[c_663])).

cnf(c_5,plain,
    ( ~ r2_hidden(sK1(X0,X1,X2),X0)
    | ~ r2_hidden(sK1(X0,X1,X2),X2)
    | r2_hidden(sK1(X0,X1,X2),X1)
    | k6_subset_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_412,plain,
    ( ~ r2_hidden(sK1(k1_ordinal1(sK2),k1_tarski(sK2),sK2),k1_ordinal1(sK2))
    | r2_hidden(sK1(k1_ordinal1(sK2),k1_tarski(sK2),sK2),k1_tarski(sK2))
    | ~ r2_hidden(sK1(k1_ordinal1(sK2),k1_tarski(sK2),sK2),sK2)
    | k6_subset_1(k1_ordinal1(sK2),k1_tarski(sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_6,plain,
    ( ~ r2_hidden(sK1(X0,X1,X2),X1)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k6_subset_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_413,plain,
    ( ~ r2_hidden(sK1(k1_ordinal1(sK2),k1_tarski(sK2),sK2),k1_tarski(sK2))
    | r2_hidden(sK1(k1_ordinal1(sK2),k1_tarski(sK2),sK2),sK2)
    | k6_subset_1(k1_ordinal1(sK2),k1_tarski(sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_7,plain,
    ( r2_hidden(sK1(X0,X1,X2),X0)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k6_subset_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_414,plain,
    ( r2_hidden(sK1(k1_ordinal1(sK2),k1_tarski(sK2),sK2),k1_ordinal1(sK2))
    | r2_hidden(sK1(k1_ordinal1(sK2),k1_tarski(sK2),sK2),sK2)
    | k6_subset_1(k1_ordinal1(sK2),k1_tarski(sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_165,plain,
    ( X0 != X1
    | k1_tarski(X0) = k1_tarski(X1) ),
    theory(equality)).

cnf(c_169,plain,
    ( k1_tarski(sK2) = k1_tarski(sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_165])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_49,plain,
    ( ~ r2_hidden(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_3,plain,
    ( r2_hidden(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_40,plain,
    ( r2_hidden(sK2,k1_tarski(sK2)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_37,plain,
    ( ~ r2_hidden(sK2,k1_tarski(sK2))
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_14,negated_conjecture,
    ( k6_subset_1(k1_ordinal1(sK2),k1_tarski(sK2)) != sK2 ),
    inference(cnf_transformation,[],[f38])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2312,c_1444,c_1189,c_713,c_669,c_665,c_412,c_413,c_414,c_169,c_49,c_40,c_37,c_14])).


%------------------------------------------------------------------------------
