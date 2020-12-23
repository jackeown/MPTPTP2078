%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:42:38 EST 2020

% Result     : Theorem 1.85s
% Output     : CNFRefutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 240 expanded)
%              Number of clauses        :   69 ( 100 expanded)
%              Number of leaves         :   14 (  40 expanded)
%              Depth                    :   16
%              Number of atoms          :  308 ( 765 expanded)
%              Number of equality atoms :  125 ( 291 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( m1_setfam_1(X1,X0)
      <=> k5_setfam_1(X0,X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ( m1_setfam_1(X1,X0)
        <=> k5_setfam_1(X0,X1) = X0 ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ( m1_setfam_1(X1,X0)
      <~> k5_setfam_1(X0,X1) = X0 )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ( k5_setfam_1(X0,X1) != X0
        | ~ m1_setfam_1(X1,X0) )
      & ( k5_setfam_1(X0,X1) = X0
        | m1_setfam_1(X1,X0) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ( k5_setfam_1(X0,X1) != X0
        | ~ m1_setfam_1(X1,X0) )
      & ( k5_setfam_1(X0,X1) = X0
        | m1_setfam_1(X1,X0) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f25])).

fof(f27,plain,
    ( ? [X0,X1] :
        ( ( k5_setfam_1(X0,X1) != X0
          | ~ m1_setfam_1(X1,X0) )
        & ( k5_setfam_1(X0,X1) = X0
          | m1_setfam_1(X1,X0) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ( k5_setfam_1(sK1,sK2) != sK1
        | ~ m1_setfam_1(sK2,sK1) )
      & ( k5_setfam_1(sK1,sK2) = sK1
        | m1_setfam_1(sK2,sK1) )
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ( k5_setfam_1(sK1,sK2) != sK1
      | ~ m1_setfam_1(sK2,sK1) )
    & ( k5_setfam_1(sK1,sK2) = sK1
      | m1_setfam_1(sK2,sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f26,f27])).

fof(f44,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(cnf_transformation,[],[f28])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k3_tarski(X1) = k5_setfam_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_tarski(X1) = k5_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k3_tarski(X1) = k5_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
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

fof(f21,plain,(
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
    inference(rectify,[],[f20])).

fof(f22,plain,(
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

fof(f23,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f49,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f18])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f48,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f29])).

fof(f31,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f32,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f50,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f32])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_setfam_1(X1,X0)
    <=> r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( m1_setfam_1(X1,X0)
        | ~ r1_tarski(X0,k3_tarski(X1)) )
      & ( r1_tarski(X0,k3_tarski(X1))
        | ~ m1_setfam_1(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_setfam_1(X1,X0)
      | ~ r1_tarski(X0,k3_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f46,plain,
    ( k5_setfam_1(sK1,sK2) != sK1
    | ~ m1_setfam_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ m1_setfam_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f45,plain,
    ( k5_setfam_1(sK1,sK2) = sK1
    | m1_setfam_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1086,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k5_setfam_1(X1,X0) = k3_tarski(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1089,plain,
    ( k5_setfam_1(X0,X1) = k3_tarski(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1521,plain,
    ( k5_setfam_1(sK1,sK2) = k3_tarski(sK2) ),
    inference(superposition,[status(thm)],[c_1086,c_1089])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | m1_subset_1(k5_setfam_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1090,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | m1_subset_1(k5_setfam_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1779,plain,
    ( m1_subset_1(k3_tarski(sK2),k1_zfmisc_1(sK1)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1521,c_1090])).

cnf(c_18,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1885,plain,
    ( m1_subset_1(k3_tarski(sK2),k1_zfmisc_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1779,c_18])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1088,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1890,plain,
    ( r2_hidden(k3_tarski(sK2),k1_zfmisc_1(sK1)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1885,c_1088])).

cnf(c_5,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_46,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_48,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK1)) = iProver_top
    | r1_tarski(sK1,sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_46])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_56,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_55,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_57,plain,
    ( r1_tarski(sK1,sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_55])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_60,plain,
    ( ~ r1_tarski(sK1,sK1)
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_8,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1201,plain,
    ( m1_subset_1(k2_subset_1(k1_zfmisc_1(X0)),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1206,plain,
    ( m1_subset_1(k2_subset_1(k1_zfmisc_1(X0)),k1_zfmisc_1(k1_zfmisc_1(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1201])).

cnf(c_1208,plain,
    ( m1_subset_1(k2_subset_1(k1_zfmisc_1(sK1)),k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1206])).

cnf(c_7,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1418,plain,
    ( k2_subset_1(k1_zfmisc_1(sK1)) = k1_zfmisc_1(sK1) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_716,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1231,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k1_zfmisc_1(X3))
    | X0 != X2
    | X1 != k1_zfmisc_1(X3) ),
    inference(instantiation,[status(thm)],[c_716])).

cnf(c_1561,plain,
    ( r2_hidden(X0,k2_subset_1(k1_zfmisc_1(X1)))
    | ~ r2_hidden(X2,k1_zfmisc_1(X1))
    | X0 != X2
    | k2_subset_1(k1_zfmisc_1(X1)) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_1231])).

cnf(c_1563,plain,
    ( X0 != X1
    | k2_subset_1(k1_zfmisc_1(X2)) != k1_zfmisc_1(X2)
    | r2_hidden(X0,k2_subset_1(k1_zfmisc_1(X2))) = iProver_top
    | r2_hidden(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1561])).

cnf(c_1565,plain,
    ( k2_subset_1(k1_zfmisc_1(sK1)) != k1_zfmisc_1(sK1)
    | sK1 != sK1
    | r2_hidden(sK1,k2_subset_1(k1_zfmisc_1(sK1))) = iProver_top
    | r2_hidden(sK1,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1563])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1342,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK1)))
    | ~ r2_hidden(X1,X0)
    | ~ v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1793,plain,
    ( ~ m1_subset_1(k2_subset_1(k1_zfmisc_1(sK1)),k1_zfmisc_1(k1_zfmisc_1(sK1)))
    | ~ r2_hidden(X0,k2_subset_1(k1_zfmisc_1(sK1)))
    | ~ v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_1342])).

cnf(c_1795,plain,
    ( m1_subset_1(k2_subset_1(k1_zfmisc_1(sK1)),k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
    | r2_hidden(X0,k2_subset_1(k1_zfmisc_1(sK1))) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1793])).

cnf(c_1797,plain,
    ( m1_subset_1(k2_subset_1(k1_zfmisc_1(sK1)),k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
    | r2_hidden(sK1,k2_subset_1(k1_zfmisc_1(sK1))) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1795])).

cnf(c_2064,plain,
    ( r2_hidden(k3_tarski(sK2),k1_zfmisc_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1890,c_48,c_56,c_57,c_60,c_1208,c_1418,c_1565,c_1797])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1092,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2069,plain,
    ( r1_tarski(k3_tarski(sK2),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2064,c_1092])).

cnf(c_9,plain,
    ( m1_setfam_1(X0,X1)
    | ~ r1_tarski(X1,k3_tarski(X0)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_141,plain,
    ( m1_setfam_1(X0,X1)
    | ~ r1_tarski(X1,k3_tarski(X0)) ),
    inference(prop_impl,[status(thm)],[c_9])).

cnf(c_15,negated_conjecture,
    ( ~ m1_setfam_1(sK2,sK1)
    | k5_setfam_1(sK1,sK2) != sK1 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_145,plain,
    ( ~ m1_setfam_1(sK2,sK1)
    | k5_setfam_1(sK1,sK2) != sK1 ),
    inference(prop_impl,[status(thm)],[c_15])).

cnf(c_265,plain,
    ( ~ r1_tarski(X0,k3_tarski(X1))
    | k5_setfam_1(sK1,sK2) != sK1
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_141,c_145])).

cnf(c_266,plain,
    ( ~ r1_tarski(sK1,k3_tarski(sK2))
    | k5_setfam_1(sK1,sK2) != sK1 ),
    inference(unflattening,[status(thm)],[c_265])).

cnf(c_479,plain,
    ( ~ r1_tarski(sK1,k3_tarski(sK2))
    | k5_setfam_1(sK1,sK2) != sK1 ),
    inference(prop_impl,[status(thm)],[c_266])).

cnf(c_1085,plain,
    ( k5_setfam_1(sK1,sK2) != sK1
    | r1_tarski(sK1,k3_tarski(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_479])).

cnf(c_1768,plain,
    ( k3_tarski(sK2) != sK1
    | r1_tarski(sK1,k3_tarski(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1521,c_1085])).

cnf(c_714,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1226,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK1,k3_tarski(sK2))
    | k3_tarski(sK2) != X1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_714])).

cnf(c_1228,plain,
    ( r1_tarski(sK1,k3_tarski(sK2))
    | ~ r1_tarski(sK1,sK1)
    | k3_tarski(sK2) != sK1
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1226])).

cnf(c_1778,plain,
    ( ~ r1_tarski(sK1,k3_tarski(sK2))
    | k3_tarski(sK2) != sK1 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1768])).

cnf(c_1881,plain,
    ( k3_tarski(sK2) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1768,c_56,c_60,c_1228,c_1778])).

cnf(c_10,plain,
    ( ~ m1_setfam_1(X0,X1)
    | r1_tarski(X1,k3_tarski(X0)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_143,plain,
    ( ~ m1_setfam_1(X0,X1)
    | r1_tarski(X1,k3_tarski(X0)) ),
    inference(prop_impl,[status(thm)],[c_10])).

cnf(c_16,negated_conjecture,
    ( m1_setfam_1(sK2,sK1)
    | k5_setfam_1(sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_147,plain,
    ( m1_setfam_1(sK2,sK1)
    | k5_setfam_1(sK1,sK2) = sK1 ),
    inference(prop_impl,[status(thm)],[c_16])).

cnf(c_275,plain,
    ( r1_tarski(X0,k3_tarski(X1))
    | k5_setfam_1(sK1,sK2) = sK1
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_143,c_147])).

cnf(c_276,plain,
    ( r1_tarski(sK1,k3_tarski(sK2))
    | k5_setfam_1(sK1,sK2) = sK1 ),
    inference(unflattening,[status(thm)],[c_275])).

cnf(c_481,plain,
    ( r1_tarski(sK1,k3_tarski(sK2))
    | k5_setfam_1(sK1,sK2) = sK1 ),
    inference(prop_impl,[status(thm)],[c_276])).

cnf(c_1084,plain,
    ( k5_setfam_1(sK1,sK2) = sK1
    | r1_tarski(sK1,k3_tarski(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_481])).

cnf(c_1767,plain,
    ( k3_tarski(sK2) = sK1
    | r1_tarski(sK1,k3_tarski(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1521,c_1084])).

cnf(c_1312,plain,
    ( ~ r1_tarski(X0,k3_tarski(sK2))
    | ~ r1_tarski(k3_tarski(sK2),X0)
    | k3_tarski(sK2) = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1313,plain,
    ( k3_tarski(sK2) = X0
    | r1_tarski(X0,k3_tarski(sK2)) != iProver_top
    | r1_tarski(k3_tarski(sK2),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1312])).

cnf(c_1315,plain,
    ( k3_tarski(sK2) = sK1
    | r1_tarski(k3_tarski(sK2),sK1) != iProver_top
    | r1_tarski(sK1,k3_tarski(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1313])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2069,c_1881,c_1767,c_1315])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:00:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.85/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.02  
% 1.85/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.85/1.02  
% 1.85/1.02  ------  iProver source info
% 1.85/1.02  
% 1.85/1.02  git: date: 2020-06-30 10:37:57 +0100
% 1.85/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.85/1.02  git: non_committed_changes: false
% 1.85/1.02  git: last_make_outside_of_git: false
% 1.85/1.02  
% 1.85/1.02  ------ 
% 1.85/1.02  
% 1.85/1.02  ------ Input Options
% 1.85/1.02  
% 1.85/1.02  --out_options                           all
% 1.85/1.02  --tptp_safe_out                         true
% 1.85/1.02  --problem_path                          ""
% 1.85/1.02  --include_path                          ""
% 1.85/1.02  --clausifier                            res/vclausify_rel
% 1.85/1.02  --clausifier_options                    --mode clausify
% 1.85/1.02  --stdin                                 false
% 1.85/1.02  --stats_out                             all
% 1.85/1.02  
% 1.85/1.02  ------ General Options
% 1.85/1.02  
% 1.85/1.02  --fof                                   false
% 1.85/1.02  --time_out_real                         305.
% 1.85/1.02  --time_out_virtual                      -1.
% 1.85/1.02  --symbol_type_check                     false
% 1.85/1.02  --clausify_out                          false
% 1.85/1.02  --sig_cnt_out                           false
% 1.85/1.02  --trig_cnt_out                          false
% 1.85/1.02  --trig_cnt_out_tolerance                1.
% 1.85/1.02  --trig_cnt_out_sk_spl                   false
% 1.85/1.02  --abstr_cl_out                          false
% 1.85/1.02  
% 1.85/1.02  ------ Global Options
% 1.85/1.02  
% 1.85/1.02  --schedule                              default
% 1.85/1.02  --add_important_lit                     false
% 1.85/1.02  --prop_solver_per_cl                    1000
% 1.85/1.02  --min_unsat_core                        false
% 1.85/1.02  --soft_assumptions                      false
% 1.85/1.02  --soft_lemma_size                       3
% 1.85/1.02  --prop_impl_unit_size                   0
% 1.85/1.02  --prop_impl_unit                        []
% 1.85/1.02  --share_sel_clauses                     true
% 1.85/1.02  --reset_solvers                         false
% 1.85/1.02  --bc_imp_inh                            [conj_cone]
% 1.85/1.02  --conj_cone_tolerance                   3.
% 1.85/1.02  --extra_neg_conj                        none
% 1.85/1.02  --large_theory_mode                     true
% 1.85/1.02  --prolific_symb_bound                   200
% 1.85/1.02  --lt_threshold                          2000
% 1.85/1.02  --clause_weak_htbl                      true
% 1.85/1.02  --gc_record_bc_elim                     false
% 1.85/1.02  
% 1.85/1.02  ------ Preprocessing Options
% 1.85/1.02  
% 1.85/1.02  --preprocessing_flag                    true
% 1.85/1.02  --time_out_prep_mult                    0.1
% 1.85/1.02  --splitting_mode                        input
% 1.85/1.02  --splitting_grd                         true
% 1.85/1.02  --splitting_cvd                         false
% 1.85/1.02  --splitting_cvd_svl                     false
% 1.85/1.02  --splitting_nvd                         32
% 1.85/1.02  --sub_typing                            true
% 1.85/1.02  --prep_gs_sim                           true
% 1.85/1.02  --prep_unflatten                        true
% 1.85/1.02  --prep_res_sim                          true
% 1.85/1.02  --prep_upred                            true
% 1.85/1.02  --prep_sem_filter                       exhaustive
% 1.85/1.02  --prep_sem_filter_out                   false
% 1.85/1.02  --pred_elim                             true
% 1.85/1.02  --res_sim_input                         true
% 1.85/1.02  --eq_ax_congr_red                       true
% 1.85/1.02  --pure_diseq_elim                       true
% 1.85/1.02  --brand_transform                       false
% 1.85/1.02  --non_eq_to_eq                          false
% 1.85/1.02  --prep_def_merge                        true
% 1.85/1.02  --prep_def_merge_prop_impl              false
% 1.85/1.02  --prep_def_merge_mbd                    true
% 1.85/1.02  --prep_def_merge_tr_red                 false
% 1.85/1.02  --prep_def_merge_tr_cl                  false
% 1.85/1.02  --smt_preprocessing                     true
% 1.85/1.02  --smt_ac_axioms                         fast
% 1.85/1.02  --preprocessed_out                      false
% 1.85/1.02  --preprocessed_stats                    false
% 1.85/1.02  
% 1.85/1.02  ------ Abstraction refinement Options
% 1.85/1.02  
% 1.85/1.02  --abstr_ref                             []
% 1.85/1.02  --abstr_ref_prep                        false
% 1.85/1.02  --abstr_ref_until_sat                   false
% 1.85/1.02  --abstr_ref_sig_restrict                funpre
% 1.85/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 1.85/1.02  --abstr_ref_under                       []
% 1.85/1.02  
% 1.85/1.02  ------ SAT Options
% 1.85/1.02  
% 1.85/1.02  --sat_mode                              false
% 1.85/1.02  --sat_fm_restart_options                ""
% 1.85/1.02  --sat_gr_def                            false
% 1.85/1.02  --sat_epr_types                         true
% 1.85/1.02  --sat_non_cyclic_types                  false
% 1.85/1.02  --sat_finite_models                     false
% 1.85/1.02  --sat_fm_lemmas                         false
% 1.85/1.02  --sat_fm_prep                           false
% 1.85/1.02  --sat_fm_uc_incr                        true
% 1.85/1.02  --sat_out_model                         small
% 1.85/1.02  --sat_out_clauses                       false
% 1.85/1.02  
% 1.85/1.02  ------ QBF Options
% 1.85/1.02  
% 1.85/1.02  --qbf_mode                              false
% 1.85/1.02  --qbf_elim_univ                         false
% 1.85/1.02  --qbf_dom_inst                          none
% 1.85/1.02  --qbf_dom_pre_inst                      false
% 1.85/1.02  --qbf_sk_in                             false
% 1.85/1.02  --qbf_pred_elim                         true
% 1.85/1.02  --qbf_split                             512
% 1.85/1.02  
% 1.85/1.02  ------ BMC1 Options
% 1.85/1.02  
% 1.85/1.02  --bmc1_incremental                      false
% 1.85/1.02  --bmc1_axioms                           reachable_all
% 1.85/1.02  --bmc1_min_bound                        0
% 1.85/1.02  --bmc1_max_bound                        -1
% 1.85/1.02  --bmc1_max_bound_default                -1
% 1.85/1.02  --bmc1_symbol_reachability              true
% 1.85/1.02  --bmc1_property_lemmas                  false
% 1.85/1.02  --bmc1_k_induction                      false
% 1.85/1.02  --bmc1_non_equiv_states                 false
% 1.85/1.02  --bmc1_deadlock                         false
% 1.85/1.02  --bmc1_ucm                              false
% 1.85/1.02  --bmc1_add_unsat_core                   none
% 1.85/1.02  --bmc1_unsat_core_children              false
% 1.85/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 1.85/1.02  --bmc1_out_stat                         full
% 1.85/1.02  --bmc1_ground_init                      false
% 1.85/1.02  --bmc1_pre_inst_next_state              false
% 1.85/1.02  --bmc1_pre_inst_state                   false
% 1.85/1.02  --bmc1_pre_inst_reach_state             false
% 1.85/1.02  --bmc1_out_unsat_core                   false
% 1.85/1.02  --bmc1_aig_witness_out                  false
% 1.85/1.02  --bmc1_verbose                          false
% 1.85/1.02  --bmc1_dump_clauses_tptp                false
% 1.85/1.02  --bmc1_dump_unsat_core_tptp             false
% 1.85/1.02  --bmc1_dump_file                        -
% 1.85/1.02  --bmc1_ucm_expand_uc_limit              128
% 1.85/1.02  --bmc1_ucm_n_expand_iterations          6
% 1.85/1.02  --bmc1_ucm_extend_mode                  1
% 1.85/1.02  --bmc1_ucm_init_mode                    2
% 1.85/1.02  --bmc1_ucm_cone_mode                    none
% 1.85/1.02  --bmc1_ucm_reduced_relation_type        0
% 1.85/1.02  --bmc1_ucm_relax_model                  4
% 1.85/1.02  --bmc1_ucm_full_tr_after_sat            true
% 1.85/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 1.85/1.02  --bmc1_ucm_layered_model                none
% 1.85/1.02  --bmc1_ucm_max_lemma_size               10
% 1.85/1.02  
% 1.85/1.02  ------ AIG Options
% 1.85/1.02  
% 1.85/1.02  --aig_mode                              false
% 1.85/1.02  
% 1.85/1.02  ------ Instantiation Options
% 1.85/1.02  
% 1.85/1.02  --instantiation_flag                    true
% 1.85/1.02  --inst_sos_flag                         false
% 1.85/1.02  --inst_sos_phase                        true
% 1.85/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.85/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.85/1.02  --inst_lit_sel_side                     num_symb
% 1.85/1.02  --inst_solver_per_active                1400
% 1.85/1.02  --inst_solver_calls_frac                1.
% 1.85/1.02  --inst_passive_queue_type               priority_queues
% 1.85/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.85/1.02  --inst_passive_queues_freq              [25;2]
% 1.85/1.02  --inst_dismatching                      true
% 1.85/1.02  --inst_eager_unprocessed_to_passive     true
% 1.85/1.02  --inst_prop_sim_given                   true
% 1.85/1.02  --inst_prop_sim_new                     false
% 1.85/1.02  --inst_subs_new                         false
% 1.85/1.02  --inst_eq_res_simp                      false
% 1.85/1.02  --inst_subs_given                       false
% 1.85/1.02  --inst_orphan_elimination               true
% 1.85/1.02  --inst_learning_loop_flag               true
% 1.85/1.02  --inst_learning_start                   3000
% 1.85/1.02  --inst_learning_factor                  2
% 1.85/1.02  --inst_start_prop_sim_after_learn       3
% 1.85/1.02  --inst_sel_renew                        solver
% 1.85/1.02  --inst_lit_activity_flag                true
% 1.85/1.02  --inst_restr_to_given                   false
% 1.85/1.02  --inst_activity_threshold               500
% 1.85/1.02  --inst_out_proof                        true
% 1.85/1.02  
% 1.85/1.02  ------ Resolution Options
% 1.85/1.02  
% 1.85/1.02  --resolution_flag                       true
% 1.85/1.02  --res_lit_sel                           adaptive
% 1.85/1.02  --res_lit_sel_side                      none
% 1.85/1.02  --res_ordering                          kbo
% 1.85/1.02  --res_to_prop_solver                    active
% 1.85/1.02  --res_prop_simpl_new                    false
% 1.85/1.02  --res_prop_simpl_given                  true
% 1.85/1.02  --res_passive_queue_type                priority_queues
% 1.85/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.85/1.02  --res_passive_queues_freq               [15;5]
% 1.85/1.02  --res_forward_subs                      full
% 1.85/1.02  --res_backward_subs                     full
% 1.85/1.02  --res_forward_subs_resolution           true
% 1.85/1.02  --res_backward_subs_resolution          true
% 1.85/1.02  --res_orphan_elimination                true
% 1.85/1.02  --res_time_limit                        2.
% 1.85/1.02  --res_out_proof                         true
% 1.85/1.02  
% 1.85/1.02  ------ Superposition Options
% 1.85/1.02  
% 1.85/1.02  --superposition_flag                    true
% 1.85/1.02  --sup_passive_queue_type                priority_queues
% 1.85/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.85/1.02  --sup_passive_queues_freq               [8;1;4]
% 1.85/1.02  --demod_completeness_check              fast
% 1.85/1.02  --demod_use_ground                      true
% 1.85/1.02  --sup_to_prop_solver                    passive
% 1.85/1.02  --sup_prop_simpl_new                    true
% 1.85/1.02  --sup_prop_simpl_given                  true
% 1.85/1.02  --sup_fun_splitting                     false
% 1.85/1.02  --sup_smt_interval                      50000
% 1.85/1.02  
% 1.85/1.02  ------ Superposition Simplification Setup
% 1.85/1.02  
% 1.85/1.02  --sup_indices_passive                   []
% 1.85/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.85/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.85/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.85/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 1.85/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.85/1.02  --sup_full_bw                           [BwDemod]
% 1.85/1.02  --sup_immed_triv                        [TrivRules]
% 1.85/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.85/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.85/1.02  --sup_immed_bw_main                     []
% 1.85/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.85/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 1.85/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.85/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.85/1.02  
% 1.85/1.02  ------ Combination Options
% 1.85/1.02  
% 1.85/1.02  --comb_res_mult                         3
% 1.85/1.02  --comb_sup_mult                         2
% 1.85/1.02  --comb_inst_mult                        10
% 1.85/1.02  
% 1.85/1.02  ------ Debug Options
% 1.85/1.02  
% 1.85/1.02  --dbg_backtrace                         false
% 1.85/1.02  --dbg_dump_prop_clauses                 false
% 1.85/1.02  --dbg_dump_prop_clauses_file            -
% 1.85/1.02  --dbg_out_stat                          false
% 1.85/1.02  ------ Parsing...
% 1.85/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.85/1.02  
% 1.85/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 1.85/1.02  
% 1.85/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.85/1.02  
% 1.85/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.85/1.02  ------ Proving...
% 1.85/1.02  ------ Problem Properties 
% 1.85/1.02  
% 1.85/1.02  
% 1.85/1.02  clauses                                 15
% 1.85/1.02  conjectures                             1
% 1.85/1.02  EPR                                     3
% 1.85/1.02  Horn                                    12
% 1.85/1.02  unary                                   4
% 1.85/1.02  binary                                  6
% 1.85/1.02  lits                                    31
% 1.85/1.02  lits eq                                 7
% 1.85/1.02  fd_pure                                 0
% 1.85/1.02  fd_pseudo                               0
% 1.85/1.02  fd_cond                                 0
% 1.85/1.02  fd_pseudo_cond                          3
% 1.85/1.02  AC symbols                              0
% 1.85/1.02  
% 1.85/1.02  ------ Schedule dynamic 5 is on 
% 1.85/1.02  
% 1.85/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.85/1.02  
% 1.85/1.02  
% 1.85/1.02  ------ 
% 1.85/1.02  Current options:
% 1.85/1.02  ------ 
% 1.85/1.02  
% 1.85/1.02  ------ Input Options
% 1.85/1.02  
% 1.85/1.02  --out_options                           all
% 1.85/1.02  --tptp_safe_out                         true
% 1.85/1.02  --problem_path                          ""
% 1.85/1.02  --include_path                          ""
% 1.85/1.02  --clausifier                            res/vclausify_rel
% 1.85/1.02  --clausifier_options                    --mode clausify
% 1.85/1.02  --stdin                                 false
% 1.85/1.02  --stats_out                             all
% 1.85/1.02  
% 1.85/1.02  ------ General Options
% 1.85/1.02  
% 1.85/1.02  --fof                                   false
% 1.85/1.02  --time_out_real                         305.
% 1.85/1.02  --time_out_virtual                      -1.
% 1.85/1.02  --symbol_type_check                     false
% 1.85/1.02  --clausify_out                          false
% 1.85/1.02  --sig_cnt_out                           false
% 1.85/1.02  --trig_cnt_out                          false
% 1.85/1.02  --trig_cnt_out_tolerance                1.
% 1.85/1.02  --trig_cnt_out_sk_spl                   false
% 1.85/1.02  --abstr_cl_out                          false
% 1.85/1.02  
% 1.85/1.02  ------ Global Options
% 1.85/1.02  
% 1.85/1.02  --schedule                              default
% 1.85/1.02  --add_important_lit                     false
% 1.85/1.02  --prop_solver_per_cl                    1000
% 1.85/1.02  --min_unsat_core                        false
% 1.85/1.02  --soft_assumptions                      false
% 1.85/1.02  --soft_lemma_size                       3
% 1.85/1.02  --prop_impl_unit_size                   0
% 1.85/1.02  --prop_impl_unit                        []
% 1.85/1.02  --share_sel_clauses                     true
% 1.85/1.02  --reset_solvers                         false
% 1.85/1.02  --bc_imp_inh                            [conj_cone]
% 1.85/1.02  --conj_cone_tolerance                   3.
% 1.85/1.02  --extra_neg_conj                        none
% 1.85/1.02  --large_theory_mode                     true
% 1.85/1.02  --prolific_symb_bound                   200
% 1.85/1.02  --lt_threshold                          2000
% 1.85/1.02  --clause_weak_htbl                      true
% 1.85/1.02  --gc_record_bc_elim                     false
% 1.85/1.02  
% 1.85/1.02  ------ Preprocessing Options
% 1.85/1.02  
% 1.85/1.02  --preprocessing_flag                    true
% 1.85/1.02  --time_out_prep_mult                    0.1
% 1.85/1.02  --splitting_mode                        input
% 1.85/1.02  --splitting_grd                         true
% 1.85/1.02  --splitting_cvd                         false
% 1.85/1.02  --splitting_cvd_svl                     false
% 1.85/1.02  --splitting_nvd                         32
% 1.85/1.02  --sub_typing                            true
% 1.85/1.02  --prep_gs_sim                           true
% 1.85/1.02  --prep_unflatten                        true
% 1.85/1.02  --prep_res_sim                          true
% 1.85/1.02  --prep_upred                            true
% 1.85/1.02  --prep_sem_filter                       exhaustive
% 1.85/1.02  --prep_sem_filter_out                   false
% 1.85/1.02  --pred_elim                             true
% 1.85/1.02  --res_sim_input                         true
% 1.85/1.02  --eq_ax_congr_red                       true
% 1.85/1.02  --pure_diseq_elim                       true
% 1.85/1.02  --brand_transform                       false
% 1.85/1.02  --non_eq_to_eq                          false
% 1.85/1.02  --prep_def_merge                        true
% 1.85/1.02  --prep_def_merge_prop_impl              false
% 1.85/1.02  --prep_def_merge_mbd                    true
% 1.85/1.02  --prep_def_merge_tr_red                 false
% 1.85/1.02  --prep_def_merge_tr_cl                  false
% 1.85/1.02  --smt_preprocessing                     true
% 1.85/1.02  --smt_ac_axioms                         fast
% 1.85/1.02  --preprocessed_out                      false
% 1.85/1.02  --preprocessed_stats                    false
% 1.85/1.02  
% 1.85/1.02  ------ Abstraction refinement Options
% 1.85/1.02  
% 1.85/1.02  --abstr_ref                             []
% 1.85/1.02  --abstr_ref_prep                        false
% 1.85/1.02  --abstr_ref_until_sat                   false
% 1.85/1.02  --abstr_ref_sig_restrict                funpre
% 1.85/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 1.85/1.02  --abstr_ref_under                       []
% 1.85/1.02  
% 1.85/1.02  ------ SAT Options
% 1.85/1.02  
% 1.85/1.02  --sat_mode                              false
% 1.85/1.02  --sat_fm_restart_options                ""
% 1.85/1.02  --sat_gr_def                            false
% 1.85/1.02  --sat_epr_types                         true
% 1.85/1.02  --sat_non_cyclic_types                  false
% 1.85/1.02  --sat_finite_models                     false
% 1.85/1.02  --sat_fm_lemmas                         false
% 1.85/1.02  --sat_fm_prep                           false
% 1.85/1.02  --sat_fm_uc_incr                        true
% 1.85/1.02  --sat_out_model                         small
% 1.85/1.02  --sat_out_clauses                       false
% 1.85/1.02  
% 1.85/1.02  ------ QBF Options
% 1.85/1.02  
% 1.85/1.02  --qbf_mode                              false
% 1.85/1.02  --qbf_elim_univ                         false
% 1.85/1.02  --qbf_dom_inst                          none
% 1.85/1.02  --qbf_dom_pre_inst                      false
% 1.85/1.02  --qbf_sk_in                             false
% 1.85/1.02  --qbf_pred_elim                         true
% 1.85/1.02  --qbf_split                             512
% 1.85/1.02  
% 1.85/1.02  ------ BMC1 Options
% 1.85/1.02  
% 1.85/1.02  --bmc1_incremental                      false
% 1.85/1.02  --bmc1_axioms                           reachable_all
% 1.85/1.02  --bmc1_min_bound                        0
% 1.85/1.02  --bmc1_max_bound                        -1
% 1.85/1.02  --bmc1_max_bound_default                -1
% 1.85/1.02  --bmc1_symbol_reachability              true
% 1.85/1.02  --bmc1_property_lemmas                  false
% 1.85/1.02  --bmc1_k_induction                      false
% 1.85/1.02  --bmc1_non_equiv_states                 false
% 1.85/1.02  --bmc1_deadlock                         false
% 1.85/1.02  --bmc1_ucm                              false
% 1.85/1.02  --bmc1_add_unsat_core                   none
% 1.85/1.02  --bmc1_unsat_core_children              false
% 1.85/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 1.85/1.02  --bmc1_out_stat                         full
% 1.85/1.02  --bmc1_ground_init                      false
% 1.85/1.02  --bmc1_pre_inst_next_state              false
% 1.85/1.02  --bmc1_pre_inst_state                   false
% 1.85/1.02  --bmc1_pre_inst_reach_state             false
% 1.85/1.02  --bmc1_out_unsat_core                   false
% 1.85/1.02  --bmc1_aig_witness_out                  false
% 1.85/1.02  --bmc1_verbose                          false
% 1.85/1.02  --bmc1_dump_clauses_tptp                false
% 1.85/1.02  --bmc1_dump_unsat_core_tptp             false
% 1.85/1.02  --bmc1_dump_file                        -
% 1.85/1.02  --bmc1_ucm_expand_uc_limit              128
% 1.85/1.02  --bmc1_ucm_n_expand_iterations          6
% 1.85/1.02  --bmc1_ucm_extend_mode                  1
% 1.85/1.02  --bmc1_ucm_init_mode                    2
% 1.85/1.02  --bmc1_ucm_cone_mode                    none
% 1.85/1.02  --bmc1_ucm_reduced_relation_type        0
% 1.85/1.02  --bmc1_ucm_relax_model                  4
% 1.85/1.02  --bmc1_ucm_full_tr_after_sat            true
% 1.85/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 1.85/1.02  --bmc1_ucm_layered_model                none
% 1.85/1.02  --bmc1_ucm_max_lemma_size               10
% 1.85/1.02  
% 1.85/1.02  ------ AIG Options
% 1.85/1.02  
% 1.85/1.02  --aig_mode                              false
% 1.85/1.02  
% 1.85/1.02  ------ Instantiation Options
% 1.85/1.02  
% 1.85/1.02  --instantiation_flag                    true
% 1.85/1.02  --inst_sos_flag                         false
% 1.85/1.02  --inst_sos_phase                        true
% 1.85/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.85/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.85/1.02  --inst_lit_sel_side                     none
% 1.85/1.02  --inst_solver_per_active                1400
% 1.85/1.02  --inst_solver_calls_frac                1.
% 1.85/1.02  --inst_passive_queue_type               priority_queues
% 1.85/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.85/1.02  --inst_passive_queues_freq              [25;2]
% 1.85/1.02  --inst_dismatching                      true
% 1.85/1.02  --inst_eager_unprocessed_to_passive     true
% 1.85/1.02  --inst_prop_sim_given                   true
% 1.85/1.02  --inst_prop_sim_new                     false
% 1.85/1.02  --inst_subs_new                         false
% 1.85/1.02  --inst_eq_res_simp                      false
% 1.85/1.02  --inst_subs_given                       false
% 1.85/1.02  --inst_orphan_elimination               true
% 1.85/1.02  --inst_learning_loop_flag               true
% 1.85/1.02  --inst_learning_start                   3000
% 1.85/1.02  --inst_learning_factor                  2
% 1.85/1.02  --inst_start_prop_sim_after_learn       3
% 1.85/1.02  --inst_sel_renew                        solver
% 1.85/1.02  --inst_lit_activity_flag                true
% 1.85/1.02  --inst_restr_to_given                   false
% 1.85/1.02  --inst_activity_threshold               500
% 1.85/1.02  --inst_out_proof                        true
% 1.85/1.02  
% 1.85/1.02  ------ Resolution Options
% 1.85/1.02  
% 1.85/1.02  --resolution_flag                       false
% 1.85/1.02  --res_lit_sel                           adaptive
% 1.85/1.02  --res_lit_sel_side                      none
% 1.85/1.02  --res_ordering                          kbo
% 1.85/1.02  --res_to_prop_solver                    active
% 1.85/1.02  --res_prop_simpl_new                    false
% 1.85/1.02  --res_prop_simpl_given                  true
% 1.85/1.02  --res_passive_queue_type                priority_queues
% 1.85/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.85/1.02  --res_passive_queues_freq               [15;5]
% 1.85/1.02  --res_forward_subs                      full
% 1.85/1.02  --res_backward_subs                     full
% 1.85/1.02  --res_forward_subs_resolution           true
% 1.85/1.02  --res_backward_subs_resolution          true
% 1.85/1.02  --res_orphan_elimination                true
% 1.85/1.02  --res_time_limit                        2.
% 1.85/1.02  --res_out_proof                         true
% 1.85/1.02  
% 1.85/1.02  ------ Superposition Options
% 1.85/1.02  
% 1.85/1.02  --superposition_flag                    true
% 1.85/1.02  --sup_passive_queue_type                priority_queues
% 1.85/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.85/1.02  --sup_passive_queues_freq               [8;1;4]
% 1.85/1.02  --demod_completeness_check              fast
% 1.85/1.02  --demod_use_ground                      true
% 1.85/1.02  --sup_to_prop_solver                    passive
% 1.85/1.02  --sup_prop_simpl_new                    true
% 1.85/1.02  --sup_prop_simpl_given                  true
% 1.85/1.02  --sup_fun_splitting                     false
% 1.85/1.02  --sup_smt_interval                      50000
% 1.85/1.02  
% 1.85/1.02  ------ Superposition Simplification Setup
% 1.85/1.02  
% 1.85/1.02  --sup_indices_passive                   []
% 1.85/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.85/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.85/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.85/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 1.85/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.85/1.02  --sup_full_bw                           [BwDemod]
% 1.85/1.02  --sup_immed_triv                        [TrivRules]
% 1.85/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.85/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.85/1.02  --sup_immed_bw_main                     []
% 1.85/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.85/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 1.85/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.85/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.85/1.02  
% 1.85/1.02  ------ Combination Options
% 1.85/1.02  
% 1.85/1.02  --comb_res_mult                         3
% 1.85/1.02  --comb_sup_mult                         2
% 1.85/1.02  --comb_inst_mult                        10
% 1.85/1.02  
% 1.85/1.02  ------ Debug Options
% 1.85/1.02  
% 1.85/1.02  --dbg_backtrace                         false
% 1.85/1.02  --dbg_dump_prop_clauses                 false
% 1.85/1.02  --dbg_dump_prop_clauses_file            -
% 1.85/1.02  --dbg_out_stat                          false
% 1.85/1.02  
% 1.85/1.02  
% 1.85/1.02  
% 1.85/1.02  
% 1.85/1.02  ------ Proving...
% 1.85/1.02  
% 1.85/1.02  
% 1.85/1.02  % SZS status Theorem for theBenchmark.p
% 1.85/1.02  
% 1.85/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 1.85/1.02  
% 1.85/1.02  fof(f10,conjecture,(
% 1.85/1.02    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (m1_setfam_1(X1,X0) <=> k5_setfam_1(X0,X1) = X0))),
% 1.85/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.85/1.02  
% 1.85/1.02  fof(f11,negated_conjecture,(
% 1.85/1.02    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (m1_setfam_1(X1,X0) <=> k5_setfam_1(X0,X1) = X0))),
% 1.85/1.02    inference(negated_conjecture,[],[f10])).
% 1.85/1.02  
% 1.85/1.02  fof(f17,plain,(
% 1.85/1.02    ? [X0,X1] : ((m1_setfam_1(X1,X0) <~> k5_setfam_1(X0,X1) = X0) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.85/1.02    inference(ennf_transformation,[],[f11])).
% 1.85/1.02  
% 1.85/1.02  fof(f25,plain,(
% 1.85/1.02    ? [X0,X1] : (((k5_setfam_1(X0,X1) != X0 | ~m1_setfam_1(X1,X0)) & (k5_setfam_1(X0,X1) = X0 | m1_setfam_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.85/1.02    inference(nnf_transformation,[],[f17])).
% 1.85/1.02  
% 1.85/1.02  fof(f26,plain,(
% 1.85/1.02    ? [X0,X1] : ((k5_setfam_1(X0,X1) != X0 | ~m1_setfam_1(X1,X0)) & (k5_setfam_1(X0,X1) = X0 | m1_setfam_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.85/1.02    inference(flattening,[],[f25])).
% 1.85/1.02  
% 1.85/1.02  fof(f27,plain,(
% 1.85/1.02    ? [X0,X1] : ((k5_setfam_1(X0,X1) != X0 | ~m1_setfam_1(X1,X0)) & (k5_setfam_1(X0,X1) = X0 | m1_setfam_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => ((k5_setfam_1(sK1,sK2) != sK1 | ~m1_setfam_1(sK2,sK1)) & (k5_setfam_1(sK1,sK2) = sK1 | m1_setfam_1(sK2,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))))),
% 1.85/1.02    introduced(choice_axiom,[])).
% 1.85/1.02  
% 1.85/1.02  fof(f28,plain,(
% 1.85/1.02    (k5_setfam_1(sK1,sK2) != sK1 | ~m1_setfam_1(sK2,sK1)) & (k5_setfam_1(sK1,sK2) = sK1 | m1_setfam_1(sK2,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1)))),
% 1.85/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f26,f27])).
% 1.85/1.02  
% 1.85/1.02  fof(f44,plain,(
% 1.85/1.02    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1)))),
% 1.85/1.02    inference(cnf_transformation,[],[f28])).
% 1.85/1.02  
% 1.85/1.02  fof(f7,axiom,(
% 1.85/1.02    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k3_tarski(X1) = k5_setfam_1(X0,X1))),
% 1.85/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.85/1.02  
% 1.85/1.02  fof(f13,plain,(
% 1.85/1.02    ! [X0,X1] : (k3_tarski(X1) = k5_setfam_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.85/1.02    inference(ennf_transformation,[],[f7])).
% 1.85/1.02  
% 1.85/1.02  fof(f41,plain,(
% 1.85/1.02    ( ! [X0,X1] : (k3_tarski(X1) = k5_setfam_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.85/1.02    inference(cnf_transformation,[],[f13])).
% 1.85/1.02  
% 1.85/1.02  fof(f6,axiom,(
% 1.85/1.02    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.85/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.85/1.02  
% 1.85/1.02  fof(f12,plain,(
% 1.85/1.02    ! [X0,X1] : (m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.85/1.02    inference(ennf_transformation,[],[f6])).
% 1.85/1.02  
% 1.85/1.02  fof(f40,plain,(
% 1.85/1.02    ( ! [X0,X1] : (m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.85/1.02    inference(cnf_transformation,[],[f12])).
% 1.85/1.02  
% 1.85/1.02  fof(f8,axiom,(
% 1.85/1.02    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.85/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.85/1.02  
% 1.85/1.02  fof(f14,plain,(
% 1.85/1.02    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.85/1.02    inference(ennf_transformation,[],[f8])).
% 1.85/1.02  
% 1.85/1.02  fof(f15,plain,(
% 1.85/1.02    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.85/1.02    inference(flattening,[],[f14])).
% 1.85/1.02  
% 1.85/1.02  fof(f42,plain,(
% 1.85/1.02    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.85/1.02    inference(cnf_transformation,[],[f15])).
% 1.85/1.02  
% 1.85/1.02  fof(f2,axiom,(
% 1.85/1.02    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.85/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.85/1.02  
% 1.85/1.02  fof(f20,plain,(
% 1.85/1.02    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.85/1.02    inference(nnf_transformation,[],[f2])).
% 1.85/1.02  
% 1.85/1.02  fof(f21,plain,(
% 1.85/1.02    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.85/1.02    inference(rectify,[],[f20])).
% 1.85/1.02  
% 1.85/1.02  fof(f22,plain,(
% 1.85/1.02    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 1.85/1.02    introduced(choice_axiom,[])).
% 1.85/1.02  
% 1.85/1.02  fof(f23,plain,(
% 1.85/1.02    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.85/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).
% 1.85/1.02  
% 1.85/1.02  fof(f33,plain,(
% 1.85/1.02    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 1.85/1.02    inference(cnf_transformation,[],[f23])).
% 1.85/1.02  
% 1.85/1.02  fof(f49,plain,(
% 1.85/1.02    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 1.85/1.02    inference(equality_resolution,[],[f33])).
% 1.85/1.02  
% 1.85/1.02  fof(f1,axiom,(
% 1.85/1.02    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.85/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.85/1.02  
% 1.85/1.02  fof(f18,plain,(
% 1.85/1.02    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.85/1.02    inference(nnf_transformation,[],[f1])).
% 1.85/1.02  
% 1.85/1.02  fof(f19,plain,(
% 1.85/1.02    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.85/1.02    inference(flattening,[],[f18])).
% 1.85/1.02  
% 1.85/1.02  fof(f29,plain,(
% 1.85/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.85/1.02    inference(cnf_transformation,[],[f19])).
% 1.85/1.02  
% 1.85/1.02  fof(f48,plain,(
% 1.85/1.02    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.85/1.02    inference(equality_resolution,[],[f29])).
% 1.85/1.02  
% 1.85/1.02  fof(f31,plain,(
% 1.85/1.02    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 1.85/1.02    inference(cnf_transformation,[],[f19])).
% 1.85/1.02  
% 1.85/1.02  fof(f4,axiom,(
% 1.85/1.02    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.85/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.85/1.02  
% 1.85/1.02  fof(f37,plain,(
% 1.85/1.02    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.85/1.02    inference(cnf_transformation,[],[f4])).
% 1.85/1.02  
% 1.85/1.02  fof(f3,axiom,(
% 1.85/1.02    ! [X0] : k2_subset_1(X0) = X0),
% 1.85/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.85/1.02  
% 1.85/1.02  fof(f36,plain,(
% 1.85/1.02    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.85/1.02    inference(cnf_transformation,[],[f3])).
% 1.85/1.02  
% 1.85/1.02  fof(f9,axiom,(
% 1.85/1.02    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.85/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.85/1.02  
% 1.85/1.02  fof(f16,plain,(
% 1.85/1.02    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.85/1.02    inference(ennf_transformation,[],[f9])).
% 1.85/1.02  
% 1.85/1.02  fof(f43,plain,(
% 1.85/1.02    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.85/1.02    inference(cnf_transformation,[],[f16])).
% 1.85/1.02  
% 1.85/1.02  fof(f32,plain,(
% 1.85/1.02    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.85/1.02    inference(cnf_transformation,[],[f23])).
% 1.85/1.02  
% 1.85/1.02  fof(f50,plain,(
% 1.85/1.02    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 1.85/1.02    inference(equality_resolution,[],[f32])).
% 1.85/1.02  
% 1.85/1.02  fof(f5,axiom,(
% 1.85/1.02    ! [X0,X1] : (m1_setfam_1(X1,X0) <=> r1_tarski(X0,k3_tarski(X1)))),
% 1.85/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.85/1.02  
% 1.85/1.02  fof(f24,plain,(
% 1.85/1.02    ! [X0,X1] : ((m1_setfam_1(X1,X0) | ~r1_tarski(X0,k3_tarski(X1))) & (r1_tarski(X0,k3_tarski(X1)) | ~m1_setfam_1(X1,X0)))),
% 1.85/1.02    inference(nnf_transformation,[],[f5])).
% 1.85/1.02  
% 1.85/1.02  fof(f39,plain,(
% 1.85/1.02    ( ! [X0,X1] : (m1_setfam_1(X1,X0) | ~r1_tarski(X0,k3_tarski(X1))) )),
% 1.85/1.02    inference(cnf_transformation,[],[f24])).
% 1.85/1.02  
% 1.85/1.02  fof(f46,plain,(
% 1.85/1.02    k5_setfam_1(sK1,sK2) != sK1 | ~m1_setfam_1(sK2,sK1)),
% 1.85/1.02    inference(cnf_transformation,[],[f28])).
% 1.85/1.02  
% 1.85/1.02  fof(f38,plain,(
% 1.85/1.02    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~m1_setfam_1(X1,X0)) )),
% 1.85/1.02    inference(cnf_transformation,[],[f24])).
% 1.85/1.02  
% 1.85/1.02  fof(f45,plain,(
% 1.85/1.02    k5_setfam_1(sK1,sK2) = sK1 | m1_setfam_1(sK2,sK1)),
% 1.85/1.02    inference(cnf_transformation,[],[f28])).
% 1.85/1.02  
% 1.85/1.02  cnf(c_17,negated_conjecture,
% 1.85/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
% 1.85/1.02      inference(cnf_transformation,[],[f44]) ).
% 1.85/1.02  
% 1.85/1.02  cnf(c_1086,plain,
% 1.85/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
% 1.85/1.02      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 1.85/1.02  
% 1.85/1.02  cnf(c_12,plain,
% 1.85/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 1.85/1.02      | k5_setfam_1(X1,X0) = k3_tarski(X0) ),
% 1.85/1.02      inference(cnf_transformation,[],[f41]) ).
% 1.85/1.02  
% 1.85/1.02  cnf(c_1089,plain,
% 1.85/1.02      ( k5_setfam_1(X0,X1) = k3_tarski(X1)
% 1.85/1.02      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 1.85/1.02      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 1.85/1.02  
% 1.85/1.02  cnf(c_1521,plain,
% 1.85/1.02      ( k5_setfam_1(sK1,sK2) = k3_tarski(sK2) ),
% 1.85/1.02      inference(superposition,[status(thm)],[c_1086,c_1089]) ).
% 1.85/1.02  
% 1.85/1.02  cnf(c_11,plain,
% 1.85/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 1.85/1.02      | m1_subset_1(k5_setfam_1(X1,X0),k1_zfmisc_1(X1)) ),
% 1.85/1.02      inference(cnf_transformation,[],[f40]) ).
% 1.85/1.02  
% 1.85/1.02  cnf(c_1090,plain,
% 1.85/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 1.85/1.02      | m1_subset_1(k5_setfam_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 1.85/1.02      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 1.85/1.02  
% 1.85/1.02  cnf(c_1779,plain,
% 1.85/1.02      ( m1_subset_1(k3_tarski(sK2),k1_zfmisc_1(sK1)) = iProver_top
% 1.85/1.02      | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top ),
% 1.85/1.02      inference(superposition,[status(thm)],[c_1521,c_1090]) ).
% 1.85/1.02  
% 1.85/1.02  cnf(c_18,plain,
% 1.85/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
% 1.85/1.02      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 1.85/1.02  
% 1.85/1.02  cnf(c_1885,plain,
% 1.85/1.02      ( m1_subset_1(k3_tarski(sK2),k1_zfmisc_1(sK1)) = iProver_top ),
% 1.85/1.02      inference(global_propositional_subsumption,
% 1.85/1.02                [status(thm)],
% 1.85/1.02                [c_1779,c_18]) ).
% 1.85/1.02  
% 1.85/1.02  cnf(c_13,plain,
% 1.85/1.02      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 1.85/1.02      inference(cnf_transformation,[],[f42]) ).
% 1.85/1.02  
% 1.85/1.02  cnf(c_1088,plain,
% 1.85/1.02      ( m1_subset_1(X0,X1) != iProver_top
% 1.85/1.02      | r2_hidden(X0,X1) = iProver_top
% 1.85/1.02      | v1_xboole_0(X1) = iProver_top ),
% 1.85/1.02      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 1.85/1.02  
% 1.85/1.02  cnf(c_1890,plain,
% 1.85/1.02      ( r2_hidden(k3_tarski(sK2),k1_zfmisc_1(sK1)) = iProver_top
% 1.85/1.02      | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
% 1.85/1.02      inference(superposition,[status(thm)],[c_1885,c_1088]) ).
% 1.85/1.02  
% 1.85/1.02  cnf(c_5,plain,
% 1.85/1.02      ( r2_hidden(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 1.85/1.02      inference(cnf_transformation,[],[f49]) ).
% 1.85/1.02  
% 1.85/1.02  cnf(c_46,plain,
% 1.85/1.02      ( r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top
% 1.85/1.02      | r1_tarski(X0,X1) != iProver_top ),
% 1.85/1.02      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 1.85/1.02  
% 1.85/1.02  cnf(c_48,plain,
% 1.85/1.02      ( r2_hidden(sK1,k1_zfmisc_1(sK1)) = iProver_top
% 1.85/1.02      | r1_tarski(sK1,sK1) != iProver_top ),
% 1.85/1.02      inference(instantiation,[status(thm)],[c_46]) ).
% 1.85/1.02  
% 1.85/1.02  cnf(c_2,plain,
% 1.85/1.02      ( r1_tarski(X0,X0) ),
% 1.85/1.02      inference(cnf_transformation,[],[f48]) ).
% 1.85/1.02  
% 1.85/1.02  cnf(c_56,plain,
% 1.85/1.02      ( r1_tarski(sK1,sK1) ),
% 1.85/1.02      inference(instantiation,[status(thm)],[c_2]) ).
% 1.85/1.02  
% 1.85/1.02  cnf(c_55,plain,
% 1.85/1.02      ( r1_tarski(X0,X0) = iProver_top ),
% 1.85/1.02      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 1.85/1.02  
% 1.85/1.02  cnf(c_57,plain,
% 1.85/1.02      ( r1_tarski(sK1,sK1) = iProver_top ),
% 1.85/1.02      inference(instantiation,[status(thm)],[c_55]) ).
% 1.85/1.02  
% 1.85/1.02  cnf(c_0,plain,
% 1.85/1.02      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 1.85/1.02      inference(cnf_transformation,[],[f31]) ).
% 1.85/1.02  
% 1.85/1.02  cnf(c_60,plain,
% 1.85/1.02      ( ~ r1_tarski(sK1,sK1) | sK1 = sK1 ),
% 1.85/1.02      inference(instantiation,[status(thm)],[c_0]) ).
% 1.85/1.02  
% 1.85/1.02  cnf(c_8,plain,
% 1.85/1.02      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 1.85/1.02      inference(cnf_transformation,[],[f37]) ).
% 1.85/1.02  
% 1.85/1.02  cnf(c_1201,plain,
% 1.85/1.02      ( m1_subset_1(k2_subset_1(k1_zfmisc_1(X0)),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
% 1.85/1.02      inference(instantiation,[status(thm)],[c_8]) ).
% 1.85/1.02  
% 1.85/1.02  cnf(c_1206,plain,
% 1.85/1.02      ( m1_subset_1(k2_subset_1(k1_zfmisc_1(X0)),k1_zfmisc_1(k1_zfmisc_1(X0))) = iProver_top ),
% 1.85/1.02      inference(predicate_to_equality,[status(thm)],[c_1201]) ).
% 1.85/1.02  
% 1.85/1.02  cnf(c_1208,plain,
% 1.85/1.02      ( m1_subset_1(k2_subset_1(k1_zfmisc_1(sK1)),k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
% 1.85/1.02      inference(instantiation,[status(thm)],[c_1206]) ).
% 1.85/1.02  
% 1.85/1.02  cnf(c_7,plain,
% 1.85/1.02      ( k2_subset_1(X0) = X0 ),
% 1.85/1.02      inference(cnf_transformation,[],[f36]) ).
% 1.85/1.02  
% 1.85/1.02  cnf(c_1418,plain,
% 1.85/1.02      ( k2_subset_1(k1_zfmisc_1(sK1)) = k1_zfmisc_1(sK1) ),
% 1.85/1.02      inference(instantiation,[status(thm)],[c_7]) ).
% 1.85/1.02  
% 1.85/1.02  cnf(c_716,plain,
% 1.85/1.02      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 1.85/1.02      theory(equality) ).
% 1.85/1.02  
% 1.85/1.02  cnf(c_1231,plain,
% 1.85/1.02      ( r2_hidden(X0,X1)
% 1.85/1.02      | ~ r2_hidden(X2,k1_zfmisc_1(X3))
% 1.85/1.02      | X0 != X2
% 1.85/1.02      | X1 != k1_zfmisc_1(X3) ),
% 1.85/1.02      inference(instantiation,[status(thm)],[c_716]) ).
% 1.85/1.02  
% 1.85/1.02  cnf(c_1561,plain,
% 1.85/1.02      ( r2_hidden(X0,k2_subset_1(k1_zfmisc_1(X1)))
% 1.85/1.02      | ~ r2_hidden(X2,k1_zfmisc_1(X1))
% 1.85/1.02      | X0 != X2
% 1.85/1.02      | k2_subset_1(k1_zfmisc_1(X1)) != k1_zfmisc_1(X1) ),
% 1.85/1.02      inference(instantiation,[status(thm)],[c_1231]) ).
% 1.85/1.02  
% 1.85/1.02  cnf(c_1563,plain,
% 1.85/1.02      ( X0 != X1
% 1.85/1.02      | k2_subset_1(k1_zfmisc_1(X2)) != k1_zfmisc_1(X2)
% 1.85/1.02      | r2_hidden(X0,k2_subset_1(k1_zfmisc_1(X2))) = iProver_top
% 1.85/1.02      | r2_hidden(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 1.85/1.02      inference(predicate_to_equality,[status(thm)],[c_1561]) ).
% 1.85/1.02  
% 1.85/1.02  cnf(c_1565,plain,
% 1.85/1.02      ( k2_subset_1(k1_zfmisc_1(sK1)) != k1_zfmisc_1(sK1)
% 1.85/1.02      | sK1 != sK1
% 1.85/1.02      | r2_hidden(sK1,k2_subset_1(k1_zfmisc_1(sK1))) = iProver_top
% 1.85/1.02      | r2_hidden(sK1,k1_zfmisc_1(sK1)) != iProver_top ),
% 1.85/1.02      inference(instantiation,[status(thm)],[c_1563]) ).
% 1.85/1.02  
% 1.85/1.02  cnf(c_14,plain,
% 1.85/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.85/1.02      | ~ r2_hidden(X2,X0)
% 1.85/1.02      | ~ v1_xboole_0(X1) ),
% 1.85/1.02      inference(cnf_transformation,[],[f43]) ).
% 1.85/1.02  
% 1.85/1.02  cnf(c_1342,plain,
% 1.85/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK1)))
% 1.85/1.02      | ~ r2_hidden(X1,X0)
% 1.85/1.02      | ~ v1_xboole_0(k1_zfmisc_1(sK1)) ),
% 1.85/1.02      inference(instantiation,[status(thm)],[c_14]) ).
% 1.85/1.02  
% 1.85/1.02  cnf(c_1793,plain,
% 1.85/1.02      ( ~ m1_subset_1(k2_subset_1(k1_zfmisc_1(sK1)),k1_zfmisc_1(k1_zfmisc_1(sK1)))
% 1.85/1.02      | ~ r2_hidden(X0,k2_subset_1(k1_zfmisc_1(sK1)))
% 1.85/1.02      | ~ v1_xboole_0(k1_zfmisc_1(sK1)) ),
% 1.85/1.02      inference(instantiation,[status(thm)],[c_1342]) ).
% 1.85/1.02  
% 1.85/1.02  cnf(c_1795,plain,
% 1.85/1.02      ( m1_subset_1(k2_subset_1(k1_zfmisc_1(sK1)),k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
% 1.85/1.02      | r2_hidden(X0,k2_subset_1(k1_zfmisc_1(sK1))) != iProver_top
% 1.85/1.02      | v1_xboole_0(k1_zfmisc_1(sK1)) != iProver_top ),
% 1.85/1.02      inference(predicate_to_equality,[status(thm)],[c_1793]) ).
% 1.85/1.02  
% 1.85/1.02  cnf(c_1797,plain,
% 1.85/1.02      ( m1_subset_1(k2_subset_1(k1_zfmisc_1(sK1)),k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
% 1.85/1.02      | r2_hidden(sK1,k2_subset_1(k1_zfmisc_1(sK1))) != iProver_top
% 1.85/1.02      | v1_xboole_0(k1_zfmisc_1(sK1)) != iProver_top ),
% 1.85/1.02      inference(instantiation,[status(thm)],[c_1795]) ).
% 1.85/1.02  
% 1.85/1.02  cnf(c_2064,plain,
% 1.85/1.02      ( r2_hidden(k3_tarski(sK2),k1_zfmisc_1(sK1)) = iProver_top ),
% 1.85/1.02      inference(global_propositional_subsumption,
% 1.85/1.02                [status(thm)],
% 1.85/1.02                [c_1890,c_48,c_56,c_57,c_60,c_1208,c_1418,c_1565,c_1797]) ).
% 1.85/1.02  
% 1.85/1.02  cnf(c_6,plain,
% 1.85/1.02      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 1.85/1.02      inference(cnf_transformation,[],[f50]) ).
% 1.85/1.02  
% 1.85/1.02  cnf(c_1092,plain,
% 1.85/1.02      ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
% 1.85/1.02      | r1_tarski(X0,X1) = iProver_top ),
% 1.85/1.02      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 1.85/1.02  
% 1.85/1.02  cnf(c_2069,plain,
% 1.85/1.02      ( r1_tarski(k3_tarski(sK2),sK1) = iProver_top ),
% 1.85/1.02      inference(superposition,[status(thm)],[c_2064,c_1092]) ).
% 1.85/1.02  
% 1.85/1.02  cnf(c_9,plain,
% 1.85/1.02      ( m1_setfam_1(X0,X1) | ~ r1_tarski(X1,k3_tarski(X0)) ),
% 1.85/1.02      inference(cnf_transformation,[],[f39]) ).
% 1.85/1.02  
% 1.85/1.02  cnf(c_141,plain,
% 1.85/1.02      ( m1_setfam_1(X0,X1) | ~ r1_tarski(X1,k3_tarski(X0)) ),
% 1.85/1.02      inference(prop_impl,[status(thm)],[c_9]) ).
% 1.85/1.02  
% 1.85/1.02  cnf(c_15,negated_conjecture,
% 1.85/1.02      ( ~ m1_setfam_1(sK2,sK1) | k5_setfam_1(sK1,sK2) != sK1 ),
% 1.85/1.02      inference(cnf_transformation,[],[f46]) ).
% 1.85/1.02  
% 1.85/1.02  cnf(c_145,plain,
% 1.85/1.02      ( ~ m1_setfam_1(sK2,sK1) | k5_setfam_1(sK1,sK2) != sK1 ),
% 1.85/1.02      inference(prop_impl,[status(thm)],[c_15]) ).
% 1.85/1.02  
% 1.85/1.02  cnf(c_265,plain,
% 1.85/1.02      ( ~ r1_tarski(X0,k3_tarski(X1))
% 1.85/1.02      | k5_setfam_1(sK1,sK2) != sK1
% 1.85/1.02      | sK2 != X1
% 1.85/1.02      | sK1 != X0 ),
% 1.85/1.02      inference(resolution_lifted,[status(thm)],[c_141,c_145]) ).
% 1.85/1.02  
% 1.85/1.02  cnf(c_266,plain,
% 1.85/1.02      ( ~ r1_tarski(sK1,k3_tarski(sK2)) | k5_setfam_1(sK1,sK2) != sK1 ),
% 1.85/1.02      inference(unflattening,[status(thm)],[c_265]) ).
% 1.85/1.02  
% 1.85/1.02  cnf(c_479,plain,
% 1.85/1.02      ( ~ r1_tarski(sK1,k3_tarski(sK2)) | k5_setfam_1(sK1,sK2) != sK1 ),
% 1.85/1.02      inference(prop_impl,[status(thm)],[c_266]) ).
% 1.85/1.02  
% 1.85/1.02  cnf(c_1085,plain,
% 1.85/1.02      ( k5_setfam_1(sK1,sK2) != sK1
% 1.85/1.02      | r1_tarski(sK1,k3_tarski(sK2)) != iProver_top ),
% 1.85/1.02      inference(predicate_to_equality,[status(thm)],[c_479]) ).
% 1.85/1.02  
% 1.85/1.02  cnf(c_1768,plain,
% 1.85/1.02      ( k3_tarski(sK2) != sK1
% 1.85/1.02      | r1_tarski(sK1,k3_tarski(sK2)) != iProver_top ),
% 1.85/1.02      inference(demodulation,[status(thm)],[c_1521,c_1085]) ).
% 1.85/1.02  
% 1.85/1.02  cnf(c_714,plain,
% 1.85/1.02      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 1.85/1.02      theory(equality) ).
% 1.85/1.02  
% 1.85/1.02  cnf(c_1226,plain,
% 1.85/1.02      ( ~ r1_tarski(X0,X1)
% 1.85/1.02      | r1_tarski(sK1,k3_tarski(sK2))
% 1.85/1.02      | k3_tarski(sK2) != X1
% 1.85/1.02      | sK1 != X0 ),
% 1.85/1.02      inference(instantiation,[status(thm)],[c_714]) ).
% 1.85/1.02  
% 1.85/1.02  cnf(c_1228,plain,
% 1.85/1.02      ( r1_tarski(sK1,k3_tarski(sK2))
% 1.85/1.02      | ~ r1_tarski(sK1,sK1)
% 1.85/1.02      | k3_tarski(sK2) != sK1
% 1.85/1.02      | sK1 != sK1 ),
% 1.85/1.02      inference(instantiation,[status(thm)],[c_1226]) ).
% 1.85/1.02  
% 1.85/1.02  cnf(c_1778,plain,
% 1.85/1.02      ( ~ r1_tarski(sK1,k3_tarski(sK2)) | k3_tarski(sK2) != sK1 ),
% 1.85/1.02      inference(predicate_to_equality_rev,[status(thm)],[c_1768]) ).
% 1.85/1.02  
% 1.85/1.02  cnf(c_1881,plain,
% 1.85/1.02      ( k3_tarski(sK2) != sK1 ),
% 1.85/1.02      inference(global_propositional_subsumption,
% 1.85/1.02                [status(thm)],
% 1.85/1.02                [c_1768,c_56,c_60,c_1228,c_1778]) ).
% 1.85/1.02  
% 1.85/1.02  cnf(c_10,plain,
% 1.85/1.02      ( ~ m1_setfam_1(X0,X1) | r1_tarski(X1,k3_tarski(X0)) ),
% 1.85/1.02      inference(cnf_transformation,[],[f38]) ).
% 1.85/1.02  
% 1.85/1.02  cnf(c_143,plain,
% 1.85/1.02      ( ~ m1_setfam_1(X0,X1) | r1_tarski(X1,k3_tarski(X0)) ),
% 1.85/1.02      inference(prop_impl,[status(thm)],[c_10]) ).
% 1.85/1.02  
% 1.85/1.02  cnf(c_16,negated_conjecture,
% 1.85/1.02      ( m1_setfam_1(sK2,sK1) | k5_setfam_1(sK1,sK2) = sK1 ),
% 1.85/1.02      inference(cnf_transformation,[],[f45]) ).
% 1.85/1.02  
% 1.85/1.02  cnf(c_147,plain,
% 1.85/1.02      ( m1_setfam_1(sK2,sK1) | k5_setfam_1(sK1,sK2) = sK1 ),
% 1.85/1.02      inference(prop_impl,[status(thm)],[c_16]) ).
% 1.85/1.02  
% 1.85/1.02  cnf(c_275,plain,
% 1.85/1.02      ( r1_tarski(X0,k3_tarski(X1))
% 1.85/1.02      | k5_setfam_1(sK1,sK2) = sK1
% 1.85/1.02      | sK2 != X1
% 1.85/1.02      | sK1 != X0 ),
% 1.85/1.02      inference(resolution_lifted,[status(thm)],[c_143,c_147]) ).
% 1.85/1.02  
% 1.85/1.02  cnf(c_276,plain,
% 1.85/1.02      ( r1_tarski(sK1,k3_tarski(sK2)) | k5_setfam_1(sK1,sK2) = sK1 ),
% 1.85/1.02      inference(unflattening,[status(thm)],[c_275]) ).
% 1.85/1.02  
% 1.85/1.02  cnf(c_481,plain,
% 1.85/1.02      ( r1_tarski(sK1,k3_tarski(sK2)) | k5_setfam_1(sK1,sK2) = sK1 ),
% 1.85/1.02      inference(prop_impl,[status(thm)],[c_276]) ).
% 1.85/1.02  
% 1.85/1.02  cnf(c_1084,plain,
% 1.85/1.02      ( k5_setfam_1(sK1,sK2) = sK1
% 1.85/1.02      | r1_tarski(sK1,k3_tarski(sK2)) = iProver_top ),
% 1.85/1.02      inference(predicate_to_equality,[status(thm)],[c_481]) ).
% 1.85/1.02  
% 1.85/1.02  cnf(c_1767,plain,
% 1.85/1.02      ( k3_tarski(sK2) = sK1
% 1.85/1.02      | r1_tarski(sK1,k3_tarski(sK2)) = iProver_top ),
% 1.85/1.02      inference(demodulation,[status(thm)],[c_1521,c_1084]) ).
% 1.85/1.02  
% 1.85/1.02  cnf(c_1312,plain,
% 1.85/1.02      ( ~ r1_tarski(X0,k3_tarski(sK2))
% 1.85/1.02      | ~ r1_tarski(k3_tarski(sK2),X0)
% 1.85/1.02      | k3_tarski(sK2) = X0 ),
% 1.85/1.02      inference(instantiation,[status(thm)],[c_0]) ).
% 1.85/1.02  
% 1.85/1.02  cnf(c_1313,plain,
% 1.85/1.02      ( k3_tarski(sK2) = X0
% 1.85/1.02      | r1_tarski(X0,k3_tarski(sK2)) != iProver_top
% 1.85/1.02      | r1_tarski(k3_tarski(sK2),X0) != iProver_top ),
% 1.85/1.02      inference(predicate_to_equality,[status(thm)],[c_1312]) ).
% 1.85/1.02  
% 1.85/1.02  cnf(c_1315,plain,
% 1.85/1.02      ( k3_tarski(sK2) = sK1
% 1.85/1.02      | r1_tarski(k3_tarski(sK2),sK1) != iProver_top
% 1.85/1.02      | r1_tarski(sK1,k3_tarski(sK2)) != iProver_top ),
% 1.85/1.02      inference(instantiation,[status(thm)],[c_1313]) ).
% 1.85/1.02  
% 1.85/1.02  cnf(contradiction,plain,
% 1.85/1.02      ( $false ),
% 1.85/1.02      inference(minisat,[status(thm)],[c_2069,c_1881,c_1767,c_1315]) ).
% 1.85/1.02  
% 1.85/1.02  
% 1.85/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 1.85/1.02  
% 1.85/1.02  ------                               Statistics
% 1.85/1.02  
% 1.85/1.02  ------ General
% 1.85/1.02  
% 1.85/1.02  abstr_ref_over_cycles:                  0
% 1.85/1.02  abstr_ref_under_cycles:                 0
% 1.85/1.02  gc_basic_clause_elim:                   0
% 1.85/1.02  forced_gc_time:                         0
% 1.85/1.02  parsing_time:                           0.007
% 1.85/1.02  unif_index_cands_time:                  0.
% 1.85/1.02  unif_index_add_time:                    0.
% 1.85/1.02  orderings_time:                         0.
% 1.85/1.02  out_proof_time:                         0.008
% 1.85/1.02  total_time:                             0.084
% 1.85/1.02  num_of_symbols:                         43
% 1.85/1.02  num_of_terms:                           1540
% 1.85/1.02  
% 1.85/1.02  ------ Preprocessing
% 1.85/1.02  
% 1.85/1.02  num_of_splits:                          0
% 1.85/1.02  num_of_split_atoms:                     0
% 1.85/1.02  num_of_reused_defs:                     0
% 1.85/1.02  num_eq_ax_congr_red:                    13
% 1.85/1.02  num_of_sem_filtered_clauses:            1
% 1.85/1.02  num_of_subtypes:                        0
% 1.85/1.02  monotx_restored_types:                  0
% 1.85/1.02  sat_num_of_epr_types:                   0
% 1.85/1.02  sat_num_of_non_cyclic_types:            0
% 1.85/1.02  sat_guarded_non_collapsed_types:        0
% 1.85/1.02  num_pure_diseq_elim:                    0
% 1.85/1.02  simp_replaced_by:                       0
% 1.85/1.02  res_preprocessed:                       79
% 1.85/1.02  prep_upred:                             0
% 1.85/1.02  prep_unflattend:                        32
% 1.85/1.02  smt_new_axioms:                         0
% 1.85/1.02  pred_elim_cands:                        4
% 1.85/1.02  pred_elim:                              1
% 1.85/1.02  pred_elim_cl:                           2
% 1.85/1.02  pred_elim_cycles:                       5
% 1.85/1.02  merged_defs:                            18
% 1.85/1.02  merged_defs_ncl:                        0
% 1.85/1.02  bin_hyper_res:                          18
% 1.85/1.02  prep_cycles:                            4
% 1.85/1.02  pred_elim_time:                         0.004
% 1.85/1.02  splitting_time:                         0.
% 1.85/1.02  sem_filter_time:                        0.
% 1.85/1.02  monotx_time:                            0.001
% 1.85/1.02  subtype_inf_time:                       0.
% 1.85/1.02  
% 1.85/1.02  ------ Problem properties
% 1.85/1.02  
% 1.85/1.02  clauses:                                15
% 1.85/1.02  conjectures:                            1
% 1.85/1.02  epr:                                    3
% 1.85/1.02  horn:                                   12
% 1.85/1.02  ground:                                 3
% 1.85/1.02  unary:                                  4
% 1.85/1.02  binary:                                 6
% 1.85/1.02  lits:                                   31
% 1.85/1.02  lits_eq:                                7
% 1.85/1.02  fd_pure:                                0
% 1.85/1.02  fd_pseudo:                              0
% 1.85/1.02  fd_cond:                                0
% 1.85/1.02  fd_pseudo_cond:                         3
% 1.85/1.02  ac_symbols:                             0
% 1.85/1.02  
% 1.85/1.02  ------ Propositional Solver
% 1.85/1.02  
% 1.85/1.02  prop_solver_calls:                      25
% 1.85/1.02  prop_fast_solver_calls:                 453
% 1.85/1.02  smt_solver_calls:                       0
% 1.85/1.02  smt_fast_solver_calls:                  0
% 1.85/1.02  prop_num_of_clauses:                    602
% 1.85/1.02  prop_preprocess_simplified:             2803
% 1.85/1.02  prop_fo_subsumed:                       5
% 1.85/1.02  prop_solver_time:                       0.
% 1.85/1.02  smt_solver_time:                        0.
% 1.85/1.02  smt_fast_solver_time:                   0.
% 1.85/1.02  prop_fast_solver_time:                  0.
% 1.85/1.02  prop_unsat_core_time:                   0.
% 1.85/1.02  
% 1.85/1.02  ------ QBF
% 1.85/1.02  
% 1.85/1.02  qbf_q_res:                              0
% 1.85/1.02  qbf_num_tautologies:                    0
% 1.85/1.02  qbf_prep_cycles:                        0
% 1.85/1.02  
% 1.85/1.02  ------ BMC1
% 1.85/1.02  
% 1.85/1.02  bmc1_current_bound:                     -1
% 1.85/1.02  bmc1_last_solved_bound:                 -1
% 1.85/1.02  bmc1_unsat_core_size:                   -1
% 1.85/1.02  bmc1_unsat_core_parents_size:           -1
% 1.85/1.02  bmc1_merge_next_fun:                    0
% 1.85/1.02  bmc1_unsat_core_clauses_time:           0.
% 1.85/1.02  
% 1.85/1.02  ------ Instantiation
% 1.85/1.02  
% 1.85/1.02  inst_num_of_clauses:                    181
% 1.85/1.02  inst_num_in_passive:                    20
% 1.85/1.02  inst_num_in_active:                     92
% 1.85/1.02  inst_num_in_unprocessed:                69
% 1.85/1.02  inst_num_of_loops:                      100
% 1.85/1.02  inst_num_of_learning_restarts:          0
% 1.85/1.02  inst_num_moves_active_passive:          6
% 1.85/1.02  inst_lit_activity:                      0
% 1.85/1.02  inst_lit_activity_moves:                0
% 1.85/1.02  inst_num_tautologies:                   0
% 1.85/1.02  inst_num_prop_implied:                  0
% 1.85/1.02  inst_num_existing_simplified:           0
% 1.85/1.02  inst_num_eq_res_simplified:             0
% 1.85/1.02  inst_num_child_elim:                    0
% 1.85/1.02  inst_num_of_dismatching_blockings:      43
% 1.85/1.02  inst_num_of_non_proper_insts:           138
% 1.85/1.02  inst_num_of_duplicates:                 0
% 1.85/1.02  inst_inst_num_from_inst_to_res:         0
% 1.85/1.02  inst_dismatching_checking_time:         0.
% 1.85/1.02  
% 1.85/1.02  ------ Resolution
% 1.85/1.02  
% 1.85/1.02  res_num_of_clauses:                     0
% 1.85/1.02  res_num_in_passive:                     0
% 1.85/1.02  res_num_in_active:                      0
% 1.85/1.02  res_num_of_loops:                       83
% 1.85/1.02  res_forward_subset_subsumed:            14
% 1.85/1.02  res_backward_subset_subsumed:           0
% 1.85/1.02  res_forward_subsumed:                   0
% 1.85/1.02  res_backward_subsumed:                  0
% 1.85/1.02  res_forward_subsumption_resolution:     0
% 1.85/1.02  res_backward_subsumption_resolution:    0
% 1.85/1.02  res_clause_to_clause_subsumption:       102
% 1.85/1.02  res_orphan_elimination:                 0
% 1.85/1.02  res_tautology_del:                      48
% 1.85/1.02  res_num_eq_res_simplified:              0
% 1.85/1.02  res_num_sel_changes:                    0
% 1.85/1.02  res_moves_from_active_to_pass:          0
% 1.85/1.02  
% 1.85/1.02  ------ Superposition
% 1.85/1.02  
% 1.85/1.02  sup_time_total:                         0.
% 1.85/1.02  sup_time_generating:                    0.
% 1.85/1.02  sup_time_sim_full:                      0.
% 1.85/1.02  sup_time_sim_immed:                     0.
% 1.85/1.02  
% 1.85/1.02  sup_num_of_clauses:                     29
% 1.85/1.02  sup_num_in_active:                      18
% 1.85/1.02  sup_num_in_passive:                     11
% 1.85/1.02  sup_num_of_loops:                       19
% 1.85/1.02  sup_fw_superposition:                   6
% 1.85/1.02  sup_bw_superposition:                   9
% 1.85/1.02  sup_immediate_simplified:               0
% 1.85/1.02  sup_given_eliminated:                   0
% 1.85/1.02  comparisons_done:                       0
% 1.85/1.02  comparisons_avoided:                    0
% 1.85/1.02  
% 1.85/1.02  ------ Simplifications
% 1.85/1.02  
% 1.85/1.02  
% 1.85/1.02  sim_fw_subset_subsumed:                 0
% 1.85/1.02  sim_bw_subset_subsumed:                 0
% 1.85/1.02  sim_fw_subsumed:                        0
% 1.85/1.02  sim_bw_subsumed:                        0
% 1.85/1.02  sim_fw_subsumption_res:                 0
% 1.85/1.02  sim_bw_subsumption_res:                 0
% 1.85/1.02  sim_tautology_del:                      1
% 1.85/1.02  sim_eq_tautology_del:                   1
% 1.85/1.02  sim_eq_res_simp:                        0
% 1.85/1.02  sim_fw_demodulated:                     0
% 1.85/1.02  sim_bw_demodulated:                     2
% 1.85/1.02  sim_light_normalised:                   1
% 1.85/1.02  sim_joinable_taut:                      0
% 1.85/1.02  sim_joinable_simp:                      0
% 1.85/1.02  sim_ac_normalised:                      0
% 1.85/1.02  sim_smt_subsumption:                    0
% 1.85/1.02  
%------------------------------------------------------------------------------
