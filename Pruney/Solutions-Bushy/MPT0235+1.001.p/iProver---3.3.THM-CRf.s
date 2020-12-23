%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0235+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:47 EST 2020

% Result     : Theorem 3.96s
% Output     : CNFRefutation 3.96s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 171 expanded)
%              Number of clauses        :   57 (  73 expanded)
%              Number of leaves         :   11 (  35 expanded)
%              Depth                    :   11
%              Number of atoms          :  320 ( 939 expanded)
%              Number of equality atoms :  189 ( 576 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f16])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f42,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k1_tarski(X1)) ),
    inference(equality_resolution,[],[f31])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_tarski(X1) != X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f41,plain,(
    ! [X1] : r1_tarski(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f32])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
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
    inference(flattening,[],[f11])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f12])).

fof(f14,plain,(
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

fof(f15,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f14])).

fof(f25,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f38,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f25])).

fof(f39,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f38])).

fof(f26,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f36,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f26])).

fof(f37,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f36])).

fof(f24,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f40,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_tarski(X0,X1)) ) ),
    inference(equality_resolution,[],[f24])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f8,plain,(
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
    inference(rectify,[],[f7])).

fof(f9,plain,(
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

fof(f10,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f9])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
      | ~ r1_tarski(sK0(X0,X1),X0)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
      | r1_tarski(sK0(X0,X1),X0)
      | r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f4,conjecture,(
    ! [X0] : k1_zfmisc_1(k1_tarski(X0)) = k2_tarski(k1_xboole_0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0] : k1_zfmisc_1(k1_tarski(X0)) = k2_tarski(k1_xboole_0,k1_tarski(X0)) ),
    inference(negated_conjecture,[],[f4])).

fof(f6,plain,(
    ? [X0] : k1_zfmisc_1(k1_tarski(X0)) != k2_tarski(k1_xboole_0,k1_tarski(X0)) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,
    ( ? [X0] : k1_zfmisc_1(k1_tarski(X0)) != k2_tarski(k1_xboole_0,k1_tarski(X0))
   => k1_zfmisc_1(k1_tarski(sK2)) != k2_tarski(k1_xboole_0,k1_tarski(sK2)) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    k1_zfmisc_1(k1_tarski(sK2)) != k2_tarski(k1_xboole_0,k1_tarski(sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f6,f18])).

fof(f33,plain,(
    k1_zfmisc_1(k1_tarski(sK2)) != k2_tarski(k1_xboole_0,k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_713,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1307,plain,
    ( X0 != X1
    | sK0(k1_tarski(sK2),k2_tarski(k1_xboole_0,k1_tarski(sK2))) != X1
    | sK0(k1_tarski(sK2),k2_tarski(k1_xboole_0,k1_tarski(sK2))) = X0 ),
    inference(instantiation,[status(thm)],[c_713])).

cnf(c_2472,plain,
    ( X0 != sK0(k1_tarski(sK2),k2_tarski(k1_xboole_0,k1_tarski(sK2)))
    | sK0(k1_tarski(sK2),k2_tarski(k1_xboole_0,k1_tarski(sK2))) = X0
    | sK0(k1_tarski(sK2),k2_tarski(k1_xboole_0,k1_tarski(sK2))) != sK0(k1_tarski(sK2),k2_tarski(k1_xboole_0,k1_tarski(sK2))) ),
    inference(instantiation,[status(thm)],[c_1307])).

cnf(c_12092,plain,
    ( sK0(k1_tarski(sK2),k2_tarski(k1_xboole_0,k1_tarski(sK2))) != sK0(k1_tarski(sK2),k2_tarski(k1_xboole_0,k1_tarski(sK2)))
    | sK0(k1_tarski(sK2),k2_tarski(k1_xboole_0,k1_tarski(sK2))) = k1_tarski(sK2)
    | k1_tarski(sK2) != sK0(k1_tarski(sK2),k2_tarski(k1_xboole_0,k1_tarski(sK2))) ),
    inference(instantiation,[status(thm)],[c_2472])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,k1_tarski(X1))
    | k1_tarski(X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_4091,plain,
    ( ~ r1_tarski(sK0(k1_tarski(sK2),X0),k1_tarski(X1))
    | k1_tarski(X1) = sK0(k1_tarski(sK2),X0)
    | k1_xboole_0 = sK0(k1_tarski(sK2),X0) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_9464,plain,
    ( ~ r1_tarski(sK0(k1_tarski(sK2),k2_tarski(k1_xboole_0,k1_tarski(sK2))),k1_tarski(sK2))
    | k1_tarski(sK2) = sK0(k1_tarski(sK2),k2_tarski(k1_xboole_0,k1_tarski(sK2)))
    | k1_xboole_0 = sK0(k1_tarski(sK2),k2_tarski(k1_xboole_0,k1_tarski(sK2))) ),
    inference(instantiation,[status(thm)],[c_4091])).

cnf(c_716,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1486,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k2_tarski(X3,X2))
    | X0 != X2
    | X1 != k2_tarski(X3,X2) ),
    inference(instantiation,[status(thm)],[c_716])).

cnf(c_2376,plain,
    ( r2_hidden(X0,k2_tarski(k1_xboole_0,k1_tarski(sK2)))
    | ~ r2_hidden(k1_tarski(sK2),k2_tarski(k1_xboole_0,k1_tarski(sK2)))
    | X0 != k1_tarski(sK2)
    | k2_tarski(k1_xboole_0,k1_tarski(sK2)) != k2_tarski(k1_xboole_0,k1_tarski(sK2)) ),
    inference(instantiation,[status(thm)],[c_1486])).

cnf(c_6557,plain,
    ( r2_hidden(sK0(k1_tarski(sK2),k2_tarski(k1_xboole_0,k1_tarski(sK2))),k2_tarski(k1_xboole_0,k1_tarski(sK2)))
    | ~ r2_hidden(k1_tarski(sK2),k2_tarski(k1_xboole_0,k1_tarski(sK2)))
    | k2_tarski(k1_xboole_0,k1_tarski(sK2)) != k2_tarski(k1_xboole_0,k1_tarski(sK2))
    | sK0(k1_tarski(sK2),k2_tarski(k1_xboole_0,k1_tarski(sK2))) != k1_tarski(sK2) ),
    inference(instantiation,[status(thm)],[c_2376])).

cnf(c_6558,plain,
    ( k2_tarski(k1_xboole_0,k1_tarski(sK2)) != k2_tarski(k1_xboole_0,k1_tarski(sK2))
    | sK0(k1_tarski(sK2),k2_tarski(k1_xboole_0,k1_tarski(sK2))) != k1_tarski(sK2)
    | r2_hidden(sK0(k1_tarski(sK2),k2_tarski(k1_xboole_0,k1_tarski(sK2))),k2_tarski(k1_xboole_0,k1_tarski(sK2))) = iProver_top
    | r2_hidden(k1_tarski(sK2),k2_tarski(k1_xboole_0,k1_tarski(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6557])).

cnf(c_1491,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k2_tarski(X2,X3))
    | X0 != X2
    | X1 != k2_tarski(X2,X3) ),
    inference(instantiation,[status(thm)],[c_716])).

cnf(c_2636,plain,
    ( r2_hidden(X0,k2_tarski(k1_xboole_0,k1_tarski(sK2)))
    | ~ r2_hidden(k1_xboole_0,k2_tarski(k1_xboole_0,k1_tarski(sK2)))
    | X0 != k1_xboole_0
    | k2_tarski(k1_xboole_0,k1_tarski(sK2)) != k2_tarski(k1_xboole_0,k1_tarski(sK2)) ),
    inference(instantiation,[status(thm)],[c_1491])).

cnf(c_6513,plain,
    ( r2_hidden(sK0(k1_tarski(sK2),k2_tarski(k1_xboole_0,k1_tarski(sK2))),k2_tarski(k1_xboole_0,k1_tarski(sK2)))
    | ~ r2_hidden(k1_xboole_0,k2_tarski(k1_xboole_0,k1_tarski(sK2)))
    | k2_tarski(k1_xboole_0,k1_tarski(sK2)) != k2_tarski(k1_xboole_0,k1_tarski(sK2))
    | sK0(k1_tarski(sK2),k2_tarski(k1_xboole_0,k1_tarski(sK2))) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2636])).

cnf(c_11,plain,
    ( r1_tarski(k1_xboole_0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_5097,plain,
    ( r1_tarski(k1_xboole_0,k1_tarski(sK2)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_10,plain,
    ( r1_tarski(k1_tarski(X0),k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_5094,plain,
    ( r1_tarski(k1_tarski(sK2),k1_tarski(sK2)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_5095,plain,
    ( r1_tarski(k1_tarski(sK2),k1_tarski(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5094])).

cnf(c_8,plain,
    ( r2_hidden(X0,k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_3792,plain,
    ( r2_hidden(k1_xboole_0,k2_tarski(k1_xboole_0,k1_tarski(sK2))) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_7,plain,
    ( r2_hidden(X0,k2_tarski(X1,X0)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_3754,plain,
    ( r2_hidden(k1_tarski(sK2),k2_tarski(k1_xboole_0,k1_tarski(sK2))) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_3755,plain,
    ( r2_hidden(k1_tarski(sK2),k2_tarski(k1_xboole_0,k1_tarski(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3754])).

cnf(c_1136,plain,
    ( X0 != X1
    | k1_tarski(sK2) != X1
    | k1_tarski(sK2) = X0 ),
    inference(instantiation,[status(thm)],[c_713])).

cnf(c_1311,plain,
    ( X0 != k1_tarski(sK2)
    | k1_tarski(sK2) = X0
    | k1_tarski(sK2) != k1_tarski(sK2) ),
    inference(instantiation,[status(thm)],[c_1136])).

cnf(c_2924,plain,
    ( sK0(k1_tarski(sK2),k2_tarski(k1_xboole_0,k1_tarski(sK2))) != k1_tarski(sK2)
    | k1_tarski(sK2) = sK0(k1_tarski(sK2),k2_tarski(k1_xboole_0,k1_tarski(sK2)))
    | k1_tarski(sK2) != k1_tarski(sK2) ),
    inference(instantiation,[status(thm)],[c_1311])).

cnf(c_2473,plain,
    ( sK0(k1_tarski(sK2),k2_tarski(k1_xboole_0,k1_tarski(sK2))) != sK0(k1_tarski(sK2),k2_tarski(k1_xboole_0,k1_tarski(sK2)))
    | sK0(k1_tarski(sK2),k2_tarski(k1_xboole_0,k1_tarski(sK2))) = k1_xboole_0
    | k1_xboole_0 != sK0(k1_tarski(sK2),k2_tarski(k1_xboole_0,k1_tarski(sK2))) ),
    inference(instantiation,[status(thm)],[c_2472])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k2_tarski(X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1297,plain,
    ( ~ r2_hidden(sK0(k1_tarski(sK2),k2_tarski(k1_xboole_0,k1_tarski(sK2))),k2_tarski(X0,X1))
    | sK0(k1_tarski(sK2),k2_tarski(k1_xboole_0,k1_tarski(sK2))) = X0
    | sK0(k1_tarski(sK2),k2_tarski(k1_xboole_0,k1_tarski(sK2))) = X1 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2459,plain,
    ( ~ r2_hidden(sK0(k1_tarski(sK2),k2_tarski(k1_xboole_0,k1_tarski(sK2))),k2_tarski(k1_xboole_0,k1_tarski(sK2)))
    | sK0(k1_tarski(sK2),k2_tarski(k1_xboole_0,k1_tarski(sK2))) = k1_tarski(sK2)
    | sK0(k1_tarski(sK2),k2_tarski(k1_xboole_0,k1_tarski(sK2))) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1297])).

cnf(c_712,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2436,plain,
    ( sK0(k1_tarski(sK2),k2_tarski(k1_xboole_0,k1_tarski(sK2))) = sK0(k1_tarski(sK2),k2_tarski(k1_xboole_0,k1_tarski(sK2))) ),
    inference(instantiation,[status(thm)],[c_712])).

cnf(c_715,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1061,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK0(k1_tarski(sK2),k2_tarski(k1_xboole_0,k1_tarski(sK2))),k1_tarski(sK2))
    | sK0(k1_tarski(sK2),k2_tarski(k1_xboole_0,k1_tarski(sK2))) != X0
    | k1_tarski(sK2) != X1 ),
    inference(instantiation,[status(thm)],[c_715])).

cnf(c_1131,plain,
    ( ~ r1_tarski(X0,k1_tarski(sK2))
    | r1_tarski(sK0(k1_tarski(sK2),k2_tarski(k1_xboole_0,k1_tarski(sK2))),k1_tarski(sK2))
    | sK0(k1_tarski(sK2),k2_tarski(k1_xboole_0,k1_tarski(sK2))) != X0
    | k1_tarski(sK2) != k1_tarski(sK2) ),
    inference(instantiation,[status(thm)],[c_1061])).

cnf(c_2236,plain,
    ( r1_tarski(sK0(k1_tarski(sK2),k2_tarski(k1_xboole_0,k1_tarski(sK2))),k1_tarski(sK2))
    | ~ r1_tarski(k1_tarski(sK2),k1_tarski(sK2))
    | sK0(k1_tarski(sK2),k2_tarski(k1_xboole_0,k1_tarski(sK2))) != k1_tarski(sK2)
    | k1_tarski(sK2) != k1_tarski(sK2) ),
    inference(instantiation,[status(thm)],[c_1131])).

cnf(c_2237,plain,
    ( sK0(k1_tarski(sK2),k2_tarski(k1_xboole_0,k1_tarski(sK2))) != k1_tarski(sK2)
    | k1_tarski(sK2) != k1_tarski(sK2)
    | r1_tarski(sK0(k1_tarski(sK2),k2_tarski(k1_xboole_0,k1_tarski(sK2))),k1_tarski(sK2)) = iProver_top
    | r1_tarski(k1_tarski(sK2),k1_tarski(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2236])).

cnf(c_1410,plain,
    ( r2_hidden(k2_tarski(k1_xboole_0,k1_tarski(sK2)),k2_tarski(k1_zfmisc_1(k1_tarski(sK2)),k2_tarski(k1_xboole_0,k1_tarski(sK2)))) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1159,plain,
    ( ~ r2_hidden(k2_tarski(k1_xboole_0,k1_tarski(sK2)),k2_tarski(X0,X1))
    | k2_tarski(k1_xboole_0,k1_tarski(sK2)) = X0
    | k2_tarski(k1_xboole_0,k1_tarski(sK2)) = X1 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1223,plain,
    ( ~ r2_hidden(k2_tarski(k1_xboole_0,k1_tarski(sK2)),k2_tarski(X0,k2_tarski(k1_xboole_0,k1_tarski(sK2))))
    | k2_tarski(k1_xboole_0,k1_tarski(sK2)) = X0
    | k2_tarski(k1_xboole_0,k1_tarski(sK2)) = k2_tarski(k1_xboole_0,k1_tarski(sK2)) ),
    inference(instantiation,[status(thm)],[c_1159])).

cnf(c_1369,plain,
    ( ~ r2_hidden(k2_tarski(k1_xboole_0,k1_tarski(sK2)),k2_tarski(k1_zfmisc_1(k1_tarski(sK2)),k2_tarski(k1_xboole_0,k1_tarski(sK2))))
    | k2_tarski(k1_xboole_0,k1_tarski(sK2)) = k2_tarski(k1_xboole_0,k1_tarski(sK2))
    | k2_tarski(k1_xboole_0,k1_tarski(sK2)) = k1_zfmisc_1(k1_tarski(sK2)) ),
    inference(instantiation,[status(thm)],[c_1223])).

cnf(c_1292,plain,
    ( k1_tarski(sK2) = k1_tarski(sK2) ),
    inference(instantiation,[status(thm)],[c_712])).

cnf(c_1133,plain,
    ( r1_tarski(sK0(k1_tarski(sK2),k2_tarski(k1_xboole_0,k1_tarski(sK2))),k1_tarski(sK2))
    | ~ r1_tarski(k1_xboole_0,k1_tarski(sK2))
    | sK0(k1_tarski(sK2),k2_tarski(k1_xboole_0,k1_tarski(sK2))) != k1_xboole_0
    | k1_tarski(sK2) != k1_tarski(sK2) ),
    inference(instantiation,[status(thm)],[c_1131])).

cnf(c_1108,plain,
    ( r2_hidden(k1_zfmisc_1(k1_tarski(sK2)),k2_tarski(k2_tarski(k1_xboole_0,k1_tarski(sK2)),k1_zfmisc_1(k1_tarski(sK2)))) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1053,plain,
    ( k2_tarski(k1_xboole_0,k1_tarski(sK2)) != X0
    | k1_zfmisc_1(k1_tarski(sK2)) != X0
    | k1_zfmisc_1(k1_tarski(sK2)) = k2_tarski(k1_xboole_0,k1_tarski(sK2)) ),
    inference(instantiation,[status(thm)],[c_713])).

cnf(c_1089,plain,
    ( k2_tarski(k1_xboole_0,k1_tarski(sK2)) != k1_zfmisc_1(k1_tarski(sK2))
    | k1_zfmisc_1(k1_tarski(sK2)) = k2_tarski(k1_xboole_0,k1_tarski(sK2))
    | k1_zfmisc_1(k1_tarski(sK2)) != k1_zfmisc_1(k1_tarski(sK2)) ),
    inference(instantiation,[status(thm)],[c_1053])).

cnf(c_1048,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_tarski(sK2)),k2_tarski(k2_tarski(k1_xboole_0,k1_tarski(sK2)),X0))
    | k1_zfmisc_1(k1_tarski(sK2)) = X0
    | k1_zfmisc_1(k1_tarski(sK2)) = k2_tarski(k1_xboole_0,k1_tarski(sK2)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1066,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_tarski(sK2)),k2_tarski(k2_tarski(k1_xboole_0,k1_tarski(sK2)),k1_zfmisc_1(k1_tarski(sK2))))
    | k1_zfmisc_1(k1_tarski(sK2)) = k2_tarski(k1_xboole_0,k1_tarski(sK2))
    | k1_zfmisc_1(k1_tarski(sK2)) = k1_zfmisc_1(k1_tarski(sK2)) ),
    inference(instantiation,[status(thm)],[c_1048])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | ~ r1_tarski(sK0(X0,X1),X0)
    | k1_zfmisc_1(X0) = X1 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_1042,plain,
    ( ~ r2_hidden(sK0(k1_tarski(sK2),k2_tarski(k1_xboole_0,k1_tarski(sK2))),k2_tarski(k1_xboole_0,k1_tarski(sK2)))
    | ~ r1_tarski(sK0(k1_tarski(sK2),k2_tarski(k1_xboole_0,k1_tarski(sK2))),k1_tarski(sK2))
    | k1_zfmisc_1(k1_tarski(sK2)) = k2_tarski(k1_xboole_0,k1_tarski(sK2)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1046,plain,
    ( k1_zfmisc_1(k1_tarski(sK2)) = k2_tarski(k1_xboole_0,k1_tarski(sK2))
    | r2_hidden(sK0(k1_tarski(sK2),k2_tarski(k1_xboole_0,k1_tarski(sK2))),k2_tarski(k1_xboole_0,k1_tarski(sK2))) != iProver_top
    | r1_tarski(sK0(k1_tarski(sK2),k2_tarski(k1_xboole_0,k1_tarski(sK2))),k1_tarski(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1042])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(sK0(X0,X1),X0)
    | k1_zfmisc_1(X0) = X1 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_1043,plain,
    ( r2_hidden(sK0(k1_tarski(sK2),k2_tarski(k1_xboole_0,k1_tarski(sK2))),k2_tarski(k1_xboole_0,k1_tarski(sK2)))
    | r1_tarski(sK0(k1_tarski(sK2),k2_tarski(k1_xboole_0,k1_tarski(sK2))),k1_tarski(sK2))
    | k1_zfmisc_1(k1_tarski(sK2)) = k2_tarski(k1_xboole_0,k1_tarski(sK2)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_13,negated_conjecture,
    ( k1_zfmisc_1(k1_tarski(sK2)) != k2_tarski(k1_xboole_0,k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f33])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12092,c_9464,c_6558,c_6513,c_5097,c_5095,c_3792,c_3755,c_2924,c_2473,c_2459,c_2436,c_2237,c_1410,c_1369,c_1292,c_1133,c_1108,c_1089,c_1066,c_1046,c_1042,c_1043,c_13])).


%------------------------------------------------------------------------------
