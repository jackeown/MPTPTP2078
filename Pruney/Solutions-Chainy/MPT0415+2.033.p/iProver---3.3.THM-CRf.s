%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:42:18 EST 2020

% Result     : Theorem 1.61s
% Output     : CNFRefutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 235 expanded)
%              Number of clauses        :   53 (  79 expanded)
%              Number of leaves         :   11 (  47 expanded)
%              Depth                    :   22
%              Number of atoms          :  307 ( 872 expanded)
%              Number of equality atoms :  155 ( 399 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k7_setfam_1(X0,X1) = X2
              | ? [X3] :
                  ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
                    | ~ r2_hidden(X3,X2) )
                  & ( r2_hidden(k3_subset_1(X0,X3),X1)
                    | r2_hidden(X3,X2) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
            & ( ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(k3_subset_1(X0,X3),X1) )
                    & ( r2_hidden(k3_subset_1(X0,X3),X1)
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
              | k7_setfam_1(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k7_setfam_1(X0,X1) = X2
              | ? [X3] :
                  ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
                    | ~ r2_hidden(X3,X2) )
                  & ( r2_hidden(k3_subset_1(X0,X3),X1)
                    | r2_hidden(X3,X2) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
            & ( ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(k3_subset_1(X0,X3),X1) )
                    & ( r2_hidden(k3_subset_1(X0,X3),X1)
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
              | k7_setfam_1(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f16])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k7_setfam_1(X0,X1) = X2
              | ? [X3] :
                  ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
                    | ~ r2_hidden(X3,X2) )
                  & ( r2_hidden(k3_subset_1(X0,X3),X1)
                    | r2_hidden(X3,X2) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
            & ( ! [X4] :
                  ( ( ( r2_hidden(X4,X2)
                      | ~ r2_hidden(k3_subset_1(X0,X4),X1) )
                    & ( r2_hidden(k3_subset_1(X0,X4),X1)
                      | ~ r2_hidden(X4,X2) ) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(X0)) )
              | k7_setfam_1(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(rectify,[],[f17])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(k3_subset_1(X0,X3),X1)
            | r2_hidden(X3,X2) )
          & m1_subset_1(X3,k1_zfmisc_1(X0)) )
     => ( ( ~ r2_hidden(k3_subset_1(X0,sK0(X0,X1,X2)),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( r2_hidden(k3_subset_1(X0,sK0(X0,X1,X2)),X1)
          | r2_hidden(sK0(X0,X1,X2),X2) )
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k7_setfam_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k3_subset_1(X0,sK0(X0,X1,X2)),X1)
                  | ~ r2_hidden(sK0(X0,X1,X2),X2) )
                & ( r2_hidden(k3_subset_1(X0,sK0(X0,X1,X2)),X1)
                  | r2_hidden(sK0(X0,X1,X2),X2) )
                & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(X0)) ) )
            & ( ! [X4] :
                  ( ( ( r2_hidden(X4,X2)
                      | ~ r2_hidden(k3_subset_1(X0,X4),X1) )
                    & ( r2_hidden(k3_subset_1(X0,X4),X1)
                      | ~ r2_hidden(X4,X2) ) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(X0)) )
              | k7_setfam_1(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k7_setfam_1(X0,X1) = X2
      | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k7_setfam_1(X0,X1) = X2
      | r2_hidden(k3_subset_1(X0,sK0(X0,X1,X2)),X1)
      | r2_hidden(sK0(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ~ ( k1_xboole_0 = k7_setfam_1(X0,X1)
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ~ ( k1_xboole_0 = k7_setfam_1(X0,X1)
            & k1_xboole_0 != X1 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f13,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k7_setfam_1(X0,X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f14,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k7_setfam_1(X0,X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f13])).

fof(f21,plain,
    ( ? [X0,X1] :
        ( k1_xboole_0 = k7_setfam_1(X0,X1)
        & k1_xboole_0 != X1
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( k1_xboole_0 = k7_setfam_1(sK1,sK2)
      & k1_xboole_0 != sK2
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( k1_xboole_0 = k7_setfam_1(sK1,sK2)
    & k1_xboole_0 != sK2
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f14,f21])).

fof(f36,plain,(
    k1_xboole_0 = k7_setfam_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f28,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | k7_setfam_1(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f37,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k7_setfam_1(X0,X1))
      | ~ r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f28])).

fof(f34,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f1,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f27,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | k7_setfam_1(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f38,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ r2_hidden(X4,k7_setfam_1(X0,X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f27])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f35,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(X1))
    | k7_setfam_1(X1,X2) = X0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_471,plain,
    ( k7_setfam_1(X0,X1) = X2
    | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top
    | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | r2_hidden(sK0(X1,X2,X0),X0)
    | r2_hidden(k3_subset_1(X1,sK0(X1,X2,X0)),X2)
    | k7_setfam_1(X1,X2) = X0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_472,plain,
    ( k7_setfam_1(X0,X1) = X2
    | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
    | r2_hidden(k3_subset_1(X0,sK0(X0,X1,X2)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_11,negated_conjecture,
    ( k1_xboole_0 = k7_setfam_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | r2_hidden(X0,k7_setfam_1(X1,X2))
    | ~ r2_hidden(k3_subset_1(X1,X0),X2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_470,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | r2_hidden(X0,k7_setfam_1(X1,X2)) = iProver_top
    | r2_hidden(k3_subset_1(X1,X0),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1436,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
    | r2_hidden(X0,k7_setfam_1(sK1,sK2)) = iProver_top
    | r2_hidden(k3_subset_1(sK1,X0),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_470])).

cnf(c_1449,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top
    | r2_hidden(k3_subset_1(sK1,X0),sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1436,c_11])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_14,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(X1,k1_tarski(X0)) != X1 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_579,plain,
    ( ~ r2_hidden(X0,k1_xboole_0)
    | k4_xboole_0(k1_xboole_0,k1_tarski(X0)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_581,plain,
    ( k4_xboole_0(k1_xboole_0,k1_tarski(X0)) != k1_xboole_0
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_579])).

cnf(c_0,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_580,plain,
    ( k4_xboole_0(k1_xboole_0,k1_tarski(X0)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_3,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_585,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_670,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(instantiation,[status(thm)],[c_585])).

cnf(c_672,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_670])).

cnf(c_1540,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top
    | r2_hidden(k3_subset_1(sK1,X0),sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1449,c_14,c_581,c_580,c_672])).

cnf(c_1550,plain,
    ( k7_setfam_1(sK1,sK2) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,X0),k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
    | r2_hidden(sK0(sK1,sK2,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_472,c_1540])).

cnf(c_1556,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,X0),k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
    | r2_hidden(sK0(sK1,sK2,X0),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1550,c_11])).

cnf(c_1585,plain,
    ( m1_subset_1(sK0(sK1,sK2,X0),k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
    | k1_xboole_0 = X0
    | r2_hidden(sK0(sK1,sK2,X0),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1556,c_14])).

cnf(c_1586,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,X0),k1_zfmisc_1(sK1)) != iProver_top
    | r2_hidden(sK0(sK1,sK2,X0),X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_1585])).

cnf(c_1593,plain,
    ( k7_setfam_1(sK1,sK2) = X0
    | k1_xboole_0 = X0
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
    | r2_hidden(sK0(sK1,sK2,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_471,c_1586])).

cnf(c_1608,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
    | r2_hidden(sK0(sK1,sK2,X0),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1593,c_11])).

cnf(c_1721,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
    | k1_xboole_0 = X0
    | r2_hidden(sK0(sK1,sK2,X0),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1608,c_14])).

cnf(c_1722,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
    | r2_hidden(sK0(sK1,sK2,X0),X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_1721])).

cnf(c_466,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k7_setfam_1(X1,k7_setfam_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_468,plain,
    ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_717,plain,
    ( k7_setfam_1(sK1,k7_setfam_1(sK1,sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_466,c_468])).

cnf(c_719,plain,
    ( k7_setfam_1(sK1,k1_xboole_0) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_717,c_11])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r2_hidden(X0,k7_setfam_1(X1,X2))
    | r2_hidden(k3_subset_1(X1,X0),X2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_469,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | r2_hidden(X0,k7_setfam_1(X1,X2)) != iProver_top
    | r2_hidden(k3_subset_1(X1,X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_10,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_467,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_528,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | m1_subset_1(k7_setfam_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | r2_hidden(X2,k7_setfam_1(X1,X0)) != iProver_top
    | r2_hidden(k3_subset_1(X1,X2),X0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_469,c_467])).

cnf(c_2390,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
    | r2_hidden(X0,k7_setfam_1(sK1,k1_xboole_0)) != iProver_top
    | r2_hidden(k3_subset_1(sK1,X0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_719,c_528])).

cnf(c_2395,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
    | r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(k3_subset_1(sK1,X0),k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2390,c_719])).

cnf(c_2758,plain,
    ( r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(k3_subset_1(sK1,X0),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2395,c_14,c_672])).

cnf(c_475,plain,
    ( k4_xboole_0(X0,k1_tarski(X1)) != X0
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_685,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_475])).

cnf(c_2766,plain,
    ( r2_hidden(X0,sK2) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2758,c_685])).

cnf(c_2775,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1722,c_2766])).

cnf(c_170,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_601,plain,
    ( sK2 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_170])).

cnf(c_602,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_601])).

cnf(c_169,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_184,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_169])).

cnf(c_12,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f35])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2775,c_602,c_184,c_12,c_14])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:23:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.61/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.01  
% 1.61/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.61/1.01  
% 1.61/1.01  ------  iProver source info
% 1.61/1.01  
% 1.61/1.01  git: date: 2020-06-30 10:37:57 +0100
% 1.61/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.61/1.01  git: non_committed_changes: false
% 1.61/1.01  git: last_make_outside_of_git: false
% 1.61/1.01  
% 1.61/1.01  ------ 
% 1.61/1.01  
% 1.61/1.01  ------ Input Options
% 1.61/1.01  
% 1.61/1.01  --out_options                           all
% 1.61/1.01  --tptp_safe_out                         true
% 1.61/1.01  --problem_path                          ""
% 1.61/1.01  --include_path                          ""
% 1.61/1.01  --clausifier                            res/vclausify_rel
% 1.61/1.01  --clausifier_options                    --mode clausify
% 1.61/1.01  --stdin                                 false
% 1.61/1.01  --stats_out                             all
% 1.61/1.01  
% 1.61/1.01  ------ General Options
% 1.61/1.01  
% 1.61/1.01  --fof                                   false
% 1.61/1.01  --time_out_real                         305.
% 1.61/1.01  --time_out_virtual                      -1.
% 1.61/1.01  --symbol_type_check                     false
% 1.61/1.01  --clausify_out                          false
% 1.61/1.01  --sig_cnt_out                           false
% 1.61/1.01  --trig_cnt_out                          false
% 1.61/1.01  --trig_cnt_out_tolerance                1.
% 1.61/1.01  --trig_cnt_out_sk_spl                   false
% 1.61/1.01  --abstr_cl_out                          false
% 1.61/1.01  
% 1.61/1.01  ------ Global Options
% 1.61/1.01  
% 1.61/1.01  --schedule                              default
% 1.61/1.01  --add_important_lit                     false
% 1.61/1.01  --prop_solver_per_cl                    1000
% 1.61/1.01  --min_unsat_core                        false
% 1.61/1.01  --soft_assumptions                      false
% 1.61/1.01  --soft_lemma_size                       3
% 1.61/1.01  --prop_impl_unit_size                   0
% 1.61/1.01  --prop_impl_unit                        []
% 1.61/1.01  --share_sel_clauses                     true
% 1.61/1.01  --reset_solvers                         false
% 1.61/1.01  --bc_imp_inh                            [conj_cone]
% 1.61/1.01  --conj_cone_tolerance                   3.
% 1.61/1.01  --extra_neg_conj                        none
% 1.61/1.01  --large_theory_mode                     true
% 1.61/1.01  --prolific_symb_bound                   200
% 1.61/1.01  --lt_threshold                          2000
% 1.61/1.01  --clause_weak_htbl                      true
% 1.61/1.01  --gc_record_bc_elim                     false
% 1.61/1.01  
% 1.61/1.01  ------ Preprocessing Options
% 1.61/1.01  
% 1.61/1.01  --preprocessing_flag                    true
% 1.61/1.01  --time_out_prep_mult                    0.1
% 1.61/1.01  --splitting_mode                        input
% 1.61/1.01  --splitting_grd                         true
% 1.61/1.01  --splitting_cvd                         false
% 1.61/1.01  --splitting_cvd_svl                     false
% 1.61/1.01  --splitting_nvd                         32
% 1.61/1.01  --sub_typing                            true
% 1.61/1.01  --prep_gs_sim                           true
% 1.61/1.01  --prep_unflatten                        true
% 1.61/1.01  --prep_res_sim                          true
% 1.61/1.01  --prep_upred                            true
% 1.61/1.01  --prep_sem_filter                       exhaustive
% 1.61/1.01  --prep_sem_filter_out                   false
% 1.61/1.01  --pred_elim                             true
% 1.61/1.01  --res_sim_input                         true
% 1.61/1.01  --eq_ax_congr_red                       true
% 1.61/1.01  --pure_diseq_elim                       true
% 1.61/1.01  --brand_transform                       false
% 1.61/1.01  --non_eq_to_eq                          false
% 1.61/1.01  --prep_def_merge                        true
% 1.61/1.01  --prep_def_merge_prop_impl              false
% 1.61/1.01  --prep_def_merge_mbd                    true
% 1.61/1.01  --prep_def_merge_tr_red                 false
% 1.61/1.01  --prep_def_merge_tr_cl                  false
% 1.61/1.01  --smt_preprocessing                     true
% 1.61/1.01  --smt_ac_axioms                         fast
% 1.61/1.01  --preprocessed_out                      false
% 1.61/1.01  --preprocessed_stats                    false
% 1.61/1.01  
% 1.61/1.01  ------ Abstraction refinement Options
% 1.61/1.01  
% 1.61/1.01  --abstr_ref                             []
% 1.61/1.01  --abstr_ref_prep                        false
% 1.61/1.01  --abstr_ref_until_sat                   false
% 1.61/1.01  --abstr_ref_sig_restrict                funpre
% 1.61/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 1.61/1.01  --abstr_ref_under                       []
% 1.61/1.01  
% 1.61/1.01  ------ SAT Options
% 1.61/1.01  
% 1.61/1.01  --sat_mode                              false
% 1.61/1.01  --sat_fm_restart_options                ""
% 1.61/1.01  --sat_gr_def                            false
% 1.61/1.01  --sat_epr_types                         true
% 1.61/1.01  --sat_non_cyclic_types                  false
% 1.61/1.01  --sat_finite_models                     false
% 1.61/1.01  --sat_fm_lemmas                         false
% 1.61/1.01  --sat_fm_prep                           false
% 1.61/1.01  --sat_fm_uc_incr                        true
% 1.61/1.01  --sat_out_model                         small
% 1.61/1.01  --sat_out_clauses                       false
% 1.61/1.01  
% 1.61/1.01  ------ QBF Options
% 1.61/1.01  
% 1.61/1.01  --qbf_mode                              false
% 1.61/1.01  --qbf_elim_univ                         false
% 1.61/1.01  --qbf_dom_inst                          none
% 1.61/1.01  --qbf_dom_pre_inst                      false
% 1.61/1.01  --qbf_sk_in                             false
% 1.61/1.01  --qbf_pred_elim                         true
% 1.61/1.01  --qbf_split                             512
% 1.61/1.01  
% 1.61/1.01  ------ BMC1 Options
% 1.61/1.01  
% 1.61/1.01  --bmc1_incremental                      false
% 1.61/1.01  --bmc1_axioms                           reachable_all
% 1.61/1.01  --bmc1_min_bound                        0
% 1.61/1.01  --bmc1_max_bound                        -1
% 1.61/1.01  --bmc1_max_bound_default                -1
% 1.61/1.01  --bmc1_symbol_reachability              true
% 1.61/1.01  --bmc1_property_lemmas                  false
% 1.61/1.01  --bmc1_k_induction                      false
% 1.61/1.01  --bmc1_non_equiv_states                 false
% 1.61/1.01  --bmc1_deadlock                         false
% 1.61/1.01  --bmc1_ucm                              false
% 1.61/1.01  --bmc1_add_unsat_core                   none
% 1.61/1.01  --bmc1_unsat_core_children              false
% 1.61/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 1.61/1.01  --bmc1_out_stat                         full
% 1.61/1.01  --bmc1_ground_init                      false
% 1.61/1.01  --bmc1_pre_inst_next_state              false
% 1.61/1.01  --bmc1_pre_inst_state                   false
% 1.61/1.01  --bmc1_pre_inst_reach_state             false
% 1.61/1.01  --bmc1_out_unsat_core                   false
% 1.61/1.01  --bmc1_aig_witness_out                  false
% 1.61/1.01  --bmc1_verbose                          false
% 1.61/1.01  --bmc1_dump_clauses_tptp                false
% 1.61/1.01  --bmc1_dump_unsat_core_tptp             false
% 1.61/1.01  --bmc1_dump_file                        -
% 1.61/1.01  --bmc1_ucm_expand_uc_limit              128
% 1.61/1.01  --bmc1_ucm_n_expand_iterations          6
% 1.61/1.01  --bmc1_ucm_extend_mode                  1
% 1.61/1.01  --bmc1_ucm_init_mode                    2
% 1.61/1.01  --bmc1_ucm_cone_mode                    none
% 1.61/1.01  --bmc1_ucm_reduced_relation_type        0
% 1.61/1.01  --bmc1_ucm_relax_model                  4
% 1.61/1.01  --bmc1_ucm_full_tr_after_sat            true
% 1.61/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 1.61/1.01  --bmc1_ucm_layered_model                none
% 1.61/1.01  --bmc1_ucm_max_lemma_size               10
% 1.61/1.01  
% 1.61/1.01  ------ AIG Options
% 1.61/1.01  
% 1.61/1.01  --aig_mode                              false
% 1.61/1.01  
% 1.61/1.01  ------ Instantiation Options
% 1.61/1.01  
% 1.61/1.01  --instantiation_flag                    true
% 1.61/1.01  --inst_sos_flag                         false
% 1.61/1.01  --inst_sos_phase                        true
% 1.61/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.61/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.61/1.01  --inst_lit_sel_side                     num_symb
% 1.61/1.01  --inst_solver_per_active                1400
% 1.61/1.01  --inst_solver_calls_frac                1.
% 1.61/1.01  --inst_passive_queue_type               priority_queues
% 1.61/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.61/1.01  --inst_passive_queues_freq              [25;2]
% 1.61/1.01  --inst_dismatching                      true
% 1.61/1.01  --inst_eager_unprocessed_to_passive     true
% 1.61/1.01  --inst_prop_sim_given                   true
% 1.61/1.01  --inst_prop_sim_new                     false
% 1.61/1.01  --inst_subs_new                         false
% 1.61/1.01  --inst_eq_res_simp                      false
% 1.61/1.01  --inst_subs_given                       false
% 1.61/1.01  --inst_orphan_elimination               true
% 1.61/1.01  --inst_learning_loop_flag               true
% 1.61/1.01  --inst_learning_start                   3000
% 1.61/1.01  --inst_learning_factor                  2
% 1.61/1.01  --inst_start_prop_sim_after_learn       3
% 1.61/1.01  --inst_sel_renew                        solver
% 1.61/1.01  --inst_lit_activity_flag                true
% 1.61/1.01  --inst_restr_to_given                   false
% 1.61/1.01  --inst_activity_threshold               500
% 1.61/1.01  --inst_out_proof                        true
% 1.61/1.01  
% 1.61/1.01  ------ Resolution Options
% 1.61/1.01  
% 1.61/1.01  --resolution_flag                       true
% 1.61/1.01  --res_lit_sel                           adaptive
% 1.61/1.01  --res_lit_sel_side                      none
% 1.61/1.01  --res_ordering                          kbo
% 1.61/1.01  --res_to_prop_solver                    active
% 1.61/1.01  --res_prop_simpl_new                    false
% 1.61/1.01  --res_prop_simpl_given                  true
% 1.61/1.01  --res_passive_queue_type                priority_queues
% 1.61/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.61/1.01  --res_passive_queues_freq               [15;5]
% 1.61/1.01  --res_forward_subs                      full
% 1.61/1.01  --res_backward_subs                     full
% 1.61/1.01  --res_forward_subs_resolution           true
% 1.61/1.01  --res_backward_subs_resolution          true
% 1.61/1.01  --res_orphan_elimination                true
% 1.61/1.01  --res_time_limit                        2.
% 1.61/1.01  --res_out_proof                         true
% 1.61/1.01  
% 1.61/1.01  ------ Superposition Options
% 1.61/1.01  
% 1.61/1.01  --superposition_flag                    true
% 1.61/1.01  --sup_passive_queue_type                priority_queues
% 1.61/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.61/1.01  --sup_passive_queues_freq               [8;1;4]
% 1.61/1.01  --demod_completeness_check              fast
% 1.61/1.01  --demod_use_ground                      true
% 1.61/1.01  --sup_to_prop_solver                    passive
% 1.61/1.01  --sup_prop_simpl_new                    true
% 1.61/1.01  --sup_prop_simpl_given                  true
% 1.61/1.01  --sup_fun_splitting                     false
% 1.61/1.01  --sup_smt_interval                      50000
% 1.61/1.01  
% 1.61/1.01  ------ Superposition Simplification Setup
% 1.61/1.01  
% 1.61/1.01  --sup_indices_passive                   []
% 1.61/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.61/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.61/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.61/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 1.61/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.61/1.01  --sup_full_bw                           [BwDemod]
% 1.61/1.01  --sup_immed_triv                        [TrivRules]
% 1.61/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.61/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.61/1.01  --sup_immed_bw_main                     []
% 1.61/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.61/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 1.61/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.61/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.61/1.01  
% 1.61/1.01  ------ Combination Options
% 1.61/1.01  
% 1.61/1.01  --comb_res_mult                         3
% 1.61/1.01  --comb_sup_mult                         2
% 1.61/1.01  --comb_inst_mult                        10
% 1.61/1.01  
% 1.61/1.01  ------ Debug Options
% 1.61/1.01  
% 1.61/1.01  --dbg_backtrace                         false
% 1.61/1.01  --dbg_dump_prop_clauses                 false
% 1.61/1.01  --dbg_dump_prop_clauses_file            -
% 1.61/1.01  --dbg_out_stat                          false
% 1.61/1.01  ------ Parsing...
% 1.61/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.61/1.01  
% 1.61/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 1.61/1.01  
% 1.61/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.61/1.01  
% 1.61/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.61/1.01  ------ Proving...
% 1.61/1.01  ------ Problem Properties 
% 1.61/1.01  
% 1.61/1.01  
% 1.61/1.01  clauses                                 14
% 1.61/1.01  conjectures                             3
% 1.61/1.01  EPR                                     1
% 1.61/1.01  Horn                                    11
% 1.61/1.01  unary                                   5
% 1.61/1.01  binary                                  3
% 1.61/1.01  lits                                    38
% 1.61/1.01  lits eq                                 9
% 1.61/1.01  fd_pure                                 0
% 1.61/1.01  fd_pseudo                               0
% 1.61/1.01  fd_cond                                 0
% 1.61/1.01  fd_pseudo_cond                          3
% 1.61/1.01  AC symbols                              0
% 1.61/1.01  
% 1.61/1.01  ------ Schedule dynamic 5 is on 
% 1.61/1.01  
% 1.61/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.61/1.01  
% 1.61/1.01  
% 1.61/1.01  ------ 
% 1.61/1.01  Current options:
% 1.61/1.01  ------ 
% 1.61/1.01  
% 1.61/1.01  ------ Input Options
% 1.61/1.01  
% 1.61/1.01  --out_options                           all
% 1.61/1.01  --tptp_safe_out                         true
% 1.61/1.01  --problem_path                          ""
% 1.61/1.01  --include_path                          ""
% 1.61/1.01  --clausifier                            res/vclausify_rel
% 1.61/1.01  --clausifier_options                    --mode clausify
% 1.61/1.01  --stdin                                 false
% 1.61/1.01  --stats_out                             all
% 1.61/1.01  
% 1.61/1.01  ------ General Options
% 1.61/1.01  
% 1.61/1.01  --fof                                   false
% 1.61/1.01  --time_out_real                         305.
% 1.61/1.01  --time_out_virtual                      -1.
% 1.61/1.01  --symbol_type_check                     false
% 1.61/1.01  --clausify_out                          false
% 1.61/1.01  --sig_cnt_out                           false
% 1.61/1.01  --trig_cnt_out                          false
% 1.61/1.01  --trig_cnt_out_tolerance                1.
% 1.61/1.01  --trig_cnt_out_sk_spl                   false
% 1.61/1.01  --abstr_cl_out                          false
% 1.61/1.01  
% 1.61/1.01  ------ Global Options
% 1.61/1.01  
% 1.61/1.01  --schedule                              default
% 1.61/1.01  --add_important_lit                     false
% 1.61/1.01  --prop_solver_per_cl                    1000
% 1.61/1.01  --min_unsat_core                        false
% 1.61/1.01  --soft_assumptions                      false
% 1.61/1.01  --soft_lemma_size                       3
% 1.61/1.01  --prop_impl_unit_size                   0
% 1.61/1.01  --prop_impl_unit                        []
% 1.61/1.01  --share_sel_clauses                     true
% 1.61/1.01  --reset_solvers                         false
% 1.61/1.01  --bc_imp_inh                            [conj_cone]
% 1.61/1.01  --conj_cone_tolerance                   3.
% 1.61/1.01  --extra_neg_conj                        none
% 1.61/1.01  --large_theory_mode                     true
% 1.61/1.01  --prolific_symb_bound                   200
% 1.61/1.01  --lt_threshold                          2000
% 1.61/1.01  --clause_weak_htbl                      true
% 1.61/1.01  --gc_record_bc_elim                     false
% 1.61/1.01  
% 1.61/1.01  ------ Preprocessing Options
% 1.61/1.01  
% 1.61/1.01  --preprocessing_flag                    true
% 1.61/1.01  --time_out_prep_mult                    0.1
% 1.61/1.01  --splitting_mode                        input
% 1.61/1.01  --splitting_grd                         true
% 1.61/1.01  --splitting_cvd                         false
% 1.61/1.01  --splitting_cvd_svl                     false
% 1.61/1.01  --splitting_nvd                         32
% 1.61/1.01  --sub_typing                            true
% 1.61/1.01  --prep_gs_sim                           true
% 1.61/1.01  --prep_unflatten                        true
% 1.61/1.01  --prep_res_sim                          true
% 1.61/1.01  --prep_upred                            true
% 1.61/1.01  --prep_sem_filter                       exhaustive
% 1.61/1.01  --prep_sem_filter_out                   false
% 1.61/1.01  --pred_elim                             true
% 1.61/1.01  --res_sim_input                         true
% 1.61/1.01  --eq_ax_congr_red                       true
% 1.61/1.01  --pure_diseq_elim                       true
% 1.61/1.01  --brand_transform                       false
% 1.61/1.01  --non_eq_to_eq                          false
% 1.61/1.01  --prep_def_merge                        true
% 1.61/1.01  --prep_def_merge_prop_impl              false
% 1.61/1.01  --prep_def_merge_mbd                    true
% 1.61/1.01  --prep_def_merge_tr_red                 false
% 1.61/1.01  --prep_def_merge_tr_cl                  false
% 1.61/1.01  --smt_preprocessing                     true
% 1.61/1.01  --smt_ac_axioms                         fast
% 1.61/1.01  --preprocessed_out                      false
% 1.61/1.01  --preprocessed_stats                    false
% 1.61/1.01  
% 1.61/1.01  ------ Abstraction refinement Options
% 1.61/1.01  
% 1.61/1.01  --abstr_ref                             []
% 1.61/1.01  --abstr_ref_prep                        false
% 1.61/1.01  --abstr_ref_until_sat                   false
% 1.61/1.01  --abstr_ref_sig_restrict                funpre
% 1.61/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 1.61/1.01  --abstr_ref_under                       []
% 1.61/1.01  
% 1.61/1.01  ------ SAT Options
% 1.61/1.01  
% 1.61/1.01  --sat_mode                              false
% 1.61/1.01  --sat_fm_restart_options                ""
% 1.61/1.01  --sat_gr_def                            false
% 1.61/1.01  --sat_epr_types                         true
% 1.61/1.01  --sat_non_cyclic_types                  false
% 1.61/1.01  --sat_finite_models                     false
% 1.61/1.01  --sat_fm_lemmas                         false
% 1.61/1.01  --sat_fm_prep                           false
% 1.61/1.01  --sat_fm_uc_incr                        true
% 1.61/1.01  --sat_out_model                         small
% 1.61/1.01  --sat_out_clauses                       false
% 1.61/1.01  
% 1.61/1.01  ------ QBF Options
% 1.61/1.01  
% 1.61/1.01  --qbf_mode                              false
% 1.61/1.01  --qbf_elim_univ                         false
% 1.61/1.01  --qbf_dom_inst                          none
% 1.61/1.01  --qbf_dom_pre_inst                      false
% 1.61/1.01  --qbf_sk_in                             false
% 1.61/1.01  --qbf_pred_elim                         true
% 1.61/1.01  --qbf_split                             512
% 1.61/1.01  
% 1.61/1.01  ------ BMC1 Options
% 1.61/1.01  
% 1.61/1.01  --bmc1_incremental                      false
% 1.61/1.01  --bmc1_axioms                           reachable_all
% 1.61/1.01  --bmc1_min_bound                        0
% 1.61/1.01  --bmc1_max_bound                        -1
% 1.61/1.01  --bmc1_max_bound_default                -1
% 1.61/1.01  --bmc1_symbol_reachability              true
% 1.61/1.01  --bmc1_property_lemmas                  false
% 1.61/1.01  --bmc1_k_induction                      false
% 1.61/1.01  --bmc1_non_equiv_states                 false
% 1.61/1.01  --bmc1_deadlock                         false
% 1.61/1.01  --bmc1_ucm                              false
% 1.61/1.01  --bmc1_add_unsat_core                   none
% 1.61/1.01  --bmc1_unsat_core_children              false
% 1.61/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 1.61/1.01  --bmc1_out_stat                         full
% 1.61/1.01  --bmc1_ground_init                      false
% 1.61/1.01  --bmc1_pre_inst_next_state              false
% 1.61/1.01  --bmc1_pre_inst_state                   false
% 1.61/1.01  --bmc1_pre_inst_reach_state             false
% 1.61/1.01  --bmc1_out_unsat_core                   false
% 1.61/1.01  --bmc1_aig_witness_out                  false
% 1.61/1.01  --bmc1_verbose                          false
% 1.61/1.01  --bmc1_dump_clauses_tptp                false
% 1.61/1.01  --bmc1_dump_unsat_core_tptp             false
% 1.61/1.01  --bmc1_dump_file                        -
% 1.61/1.01  --bmc1_ucm_expand_uc_limit              128
% 1.61/1.01  --bmc1_ucm_n_expand_iterations          6
% 1.61/1.01  --bmc1_ucm_extend_mode                  1
% 1.61/1.01  --bmc1_ucm_init_mode                    2
% 1.61/1.01  --bmc1_ucm_cone_mode                    none
% 1.61/1.01  --bmc1_ucm_reduced_relation_type        0
% 1.61/1.01  --bmc1_ucm_relax_model                  4
% 1.61/1.01  --bmc1_ucm_full_tr_after_sat            true
% 1.61/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 1.61/1.01  --bmc1_ucm_layered_model                none
% 1.61/1.01  --bmc1_ucm_max_lemma_size               10
% 1.61/1.01  
% 1.61/1.01  ------ AIG Options
% 1.61/1.01  
% 1.61/1.01  --aig_mode                              false
% 1.61/1.01  
% 1.61/1.01  ------ Instantiation Options
% 1.61/1.01  
% 1.61/1.01  --instantiation_flag                    true
% 1.61/1.01  --inst_sos_flag                         false
% 1.61/1.01  --inst_sos_phase                        true
% 1.61/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.61/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.61/1.01  --inst_lit_sel_side                     none
% 1.61/1.01  --inst_solver_per_active                1400
% 1.61/1.01  --inst_solver_calls_frac                1.
% 1.61/1.01  --inst_passive_queue_type               priority_queues
% 1.61/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.61/1.01  --inst_passive_queues_freq              [25;2]
% 1.61/1.01  --inst_dismatching                      true
% 1.61/1.01  --inst_eager_unprocessed_to_passive     true
% 1.61/1.01  --inst_prop_sim_given                   true
% 1.61/1.01  --inst_prop_sim_new                     false
% 1.61/1.01  --inst_subs_new                         false
% 1.61/1.01  --inst_eq_res_simp                      false
% 1.61/1.01  --inst_subs_given                       false
% 1.61/1.01  --inst_orphan_elimination               true
% 1.61/1.01  --inst_learning_loop_flag               true
% 1.61/1.01  --inst_learning_start                   3000
% 1.61/1.01  --inst_learning_factor                  2
% 1.61/1.01  --inst_start_prop_sim_after_learn       3
% 1.61/1.01  --inst_sel_renew                        solver
% 1.61/1.01  --inst_lit_activity_flag                true
% 1.61/1.01  --inst_restr_to_given                   false
% 1.61/1.01  --inst_activity_threshold               500
% 1.61/1.01  --inst_out_proof                        true
% 1.61/1.01  
% 1.61/1.01  ------ Resolution Options
% 1.61/1.01  
% 1.61/1.01  --resolution_flag                       false
% 1.61/1.01  --res_lit_sel                           adaptive
% 1.61/1.01  --res_lit_sel_side                      none
% 1.61/1.01  --res_ordering                          kbo
% 1.61/1.01  --res_to_prop_solver                    active
% 1.61/1.01  --res_prop_simpl_new                    false
% 1.61/1.01  --res_prop_simpl_given                  true
% 1.61/1.01  --res_passive_queue_type                priority_queues
% 1.61/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.61/1.01  --res_passive_queues_freq               [15;5]
% 1.61/1.01  --res_forward_subs                      full
% 1.61/1.01  --res_backward_subs                     full
% 1.61/1.01  --res_forward_subs_resolution           true
% 1.61/1.01  --res_backward_subs_resolution          true
% 1.61/1.01  --res_orphan_elimination                true
% 1.61/1.01  --res_time_limit                        2.
% 1.61/1.01  --res_out_proof                         true
% 1.61/1.01  
% 1.61/1.01  ------ Superposition Options
% 1.61/1.01  
% 1.61/1.01  --superposition_flag                    true
% 1.61/1.01  --sup_passive_queue_type                priority_queues
% 1.61/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.61/1.01  --sup_passive_queues_freq               [8;1;4]
% 1.61/1.01  --demod_completeness_check              fast
% 1.61/1.01  --demod_use_ground                      true
% 1.61/1.01  --sup_to_prop_solver                    passive
% 1.61/1.01  --sup_prop_simpl_new                    true
% 1.61/1.01  --sup_prop_simpl_given                  true
% 1.61/1.01  --sup_fun_splitting                     false
% 1.61/1.01  --sup_smt_interval                      50000
% 1.61/1.01  
% 1.61/1.01  ------ Superposition Simplification Setup
% 1.61/1.01  
% 1.61/1.01  --sup_indices_passive                   []
% 1.61/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.61/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.61/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.61/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 1.61/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.61/1.01  --sup_full_bw                           [BwDemod]
% 1.61/1.01  --sup_immed_triv                        [TrivRules]
% 1.61/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.61/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.61/1.01  --sup_immed_bw_main                     []
% 1.61/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.61/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 1.61/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.61/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.61/1.01  
% 1.61/1.01  ------ Combination Options
% 1.61/1.01  
% 1.61/1.01  --comb_res_mult                         3
% 1.61/1.01  --comb_sup_mult                         2
% 1.61/1.01  --comb_inst_mult                        10
% 1.61/1.01  
% 1.61/1.01  ------ Debug Options
% 1.61/1.01  
% 1.61/1.01  --dbg_backtrace                         false
% 1.61/1.01  --dbg_dump_prop_clauses                 false
% 1.61/1.01  --dbg_dump_prop_clauses_file            -
% 1.61/1.01  --dbg_out_stat                          false
% 1.61/1.01  
% 1.61/1.01  
% 1.61/1.01  
% 1.61/1.01  
% 1.61/1.01  ------ Proving...
% 1.61/1.01  
% 1.61/1.01  
% 1.61/1.01  % SZS status Theorem for theBenchmark.p
% 1.61/1.01  
% 1.61/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 1.61/1.01  
% 1.61/1.01  fof(f4,axiom,(
% 1.61/1.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k7_setfam_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => (r2_hidden(X3,X2) <=> r2_hidden(k3_subset_1(X0,X3),X1))))))),
% 1.61/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.61/1.01  
% 1.61/1.01  fof(f9,plain,(
% 1.61/1.01    ! [X0,X1] : (! [X2] : ((k7_setfam_1(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> r2_hidden(k3_subset_1(X0,X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.61/1.01    inference(ennf_transformation,[],[f4])).
% 1.61/1.01  
% 1.61/1.01  fof(f16,plain,(
% 1.61/1.01    ! [X0,X1] : (! [X2] : (((k7_setfam_1(X0,X1) = X2 | ? [X3] : (((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(k3_subset_1(X0,X3),X1)) & (r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(X0))) | k7_setfam_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.61/1.01    inference(nnf_transformation,[],[f9])).
% 1.61/1.01  
% 1.61/1.01  fof(f17,plain,(
% 1.61/1.01    ! [X0,X1] : (! [X2] : (((k7_setfam_1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2)) & m1_subset_1(X3,k1_zfmisc_1(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(k3_subset_1(X0,X3),X1)) & (r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(X0))) | k7_setfam_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.61/1.01    inference(flattening,[],[f16])).
% 1.61/1.01  
% 1.61/1.01  fof(f18,plain,(
% 1.61/1.01    ! [X0,X1] : (! [X2] : (((k7_setfam_1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2)) & m1_subset_1(X3,k1_zfmisc_1(X0)))) & (! [X4] : (((r2_hidden(X4,X2) | ~r2_hidden(k3_subset_1(X0,X4),X1)) & (r2_hidden(k3_subset_1(X0,X4),X1) | ~r2_hidden(X4,X2))) | ~m1_subset_1(X4,k1_zfmisc_1(X0))) | k7_setfam_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.61/1.01    inference(rectify,[],[f17])).
% 1.61/1.01  
% 1.61/1.01  fof(f19,plain,(
% 1.61/1.01    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2)) & m1_subset_1(X3,k1_zfmisc_1(X0))) => ((~r2_hidden(k3_subset_1(X0,sK0(X0,X1,X2)),X1) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(k3_subset_1(X0,sK0(X0,X1,X2)),X1) | r2_hidden(sK0(X0,X1,X2),X2)) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(X0))))),
% 1.61/1.01    introduced(choice_axiom,[])).
% 1.61/1.01  
% 1.61/1.01  fof(f20,plain,(
% 1.61/1.01    ! [X0,X1] : (! [X2] : (((k7_setfam_1(X0,X1) = X2 | ((~r2_hidden(k3_subset_1(X0,sK0(X0,X1,X2)),X1) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(k3_subset_1(X0,sK0(X0,X1,X2)),X1) | r2_hidden(sK0(X0,X1,X2),X2)) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(X0)))) & (! [X4] : (((r2_hidden(X4,X2) | ~r2_hidden(k3_subset_1(X0,X4),X1)) & (r2_hidden(k3_subset_1(X0,X4),X1) | ~r2_hidden(X4,X2))) | ~m1_subset_1(X4,k1_zfmisc_1(X0))) | k7_setfam_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.61/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).
% 1.61/1.01  
% 1.61/1.01  fof(f29,plain,(
% 1.61/1.01    ( ! [X2,X0,X1] : (k7_setfam_1(X0,X1) = X2 | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.61/1.01    inference(cnf_transformation,[],[f20])).
% 1.61/1.01  
% 1.61/1.01  fof(f30,plain,(
% 1.61/1.01    ( ! [X2,X0,X1] : (k7_setfam_1(X0,X1) = X2 | r2_hidden(k3_subset_1(X0,sK0(X0,X1,X2)),X1) | r2_hidden(sK0(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.61/1.01    inference(cnf_transformation,[],[f20])).
% 1.61/1.01  
% 1.61/1.01  fof(f7,conjecture,(
% 1.61/1.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ~(k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1))),
% 1.61/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.61/1.01  
% 1.61/1.01  fof(f8,negated_conjecture,(
% 1.61/1.01    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ~(k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1))),
% 1.61/1.01    inference(negated_conjecture,[],[f7])).
% 1.61/1.01  
% 1.61/1.01  fof(f13,plain,(
% 1.61/1.01    ? [X0,X1] : ((k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.61/1.01    inference(ennf_transformation,[],[f8])).
% 1.61/1.01  
% 1.61/1.01  fof(f14,plain,(
% 1.61/1.01    ? [X0,X1] : (k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.61/1.01    inference(flattening,[],[f13])).
% 1.61/1.01  
% 1.61/1.01  fof(f21,plain,(
% 1.61/1.01    ? [X0,X1] : (k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (k1_xboole_0 = k7_setfam_1(sK1,sK2) & k1_xboole_0 != sK2 & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))))),
% 1.61/1.01    introduced(choice_axiom,[])).
% 1.61/1.01  
% 1.61/1.01  fof(f22,plain,(
% 1.61/1.01    k1_xboole_0 = k7_setfam_1(sK1,sK2) & k1_xboole_0 != sK2 & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1)))),
% 1.61/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f14,f21])).
% 1.61/1.01  
% 1.61/1.01  fof(f36,plain,(
% 1.61/1.01    k1_xboole_0 = k7_setfam_1(sK1,sK2)),
% 1.61/1.01    inference(cnf_transformation,[],[f22])).
% 1.61/1.01  
% 1.61/1.01  fof(f28,plain,(
% 1.61/1.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(k3_subset_1(X0,X4),X1) | ~m1_subset_1(X4,k1_zfmisc_1(X0)) | k7_setfam_1(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.61/1.01    inference(cnf_transformation,[],[f20])).
% 1.61/1.01  
% 1.61/1.01  fof(f37,plain,(
% 1.61/1.01    ( ! [X4,X0,X1] : (r2_hidden(X4,k7_setfam_1(X0,X1)) | ~r2_hidden(k3_subset_1(X0,X4),X1) | ~m1_subset_1(X4,k1_zfmisc_1(X0)) | ~m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.61/1.01    inference(equality_resolution,[],[f28])).
% 1.61/1.01  
% 1.61/1.01  fof(f34,plain,(
% 1.61/1.01    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1)))),
% 1.61/1.01    inference(cnf_transformation,[],[f22])).
% 1.61/1.01  
% 1.61/1.01  fof(f2,axiom,(
% 1.61/1.01    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.61/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.61/1.01  
% 1.61/1.01  fof(f15,plain,(
% 1.61/1.01    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 1.61/1.01    inference(nnf_transformation,[],[f2])).
% 1.61/1.01  
% 1.61/1.01  fof(f24,plain,(
% 1.61/1.01    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 1.61/1.01    inference(cnf_transformation,[],[f15])).
% 1.61/1.01  
% 1.61/1.01  fof(f1,axiom,(
% 1.61/1.01    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.61/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.61/1.01  
% 1.61/1.01  fof(f23,plain,(
% 1.61/1.01    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.61/1.01    inference(cnf_transformation,[],[f1])).
% 1.61/1.01  
% 1.61/1.01  fof(f3,axiom,(
% 1.61/1.01    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.61/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.61/1.01  
% 1.61/1.01  fof(f26,plain,(
% 1.61/1.01    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.61/1.01    inference(cnf_transformation,[],[f3])).
% 1.61/1.01  
% 1.61/1.01  fof(f5,axiom,(
% 1.61/1.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1)),
% 1.61/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.61/1.01  
% 1.61/1.01  fof(f10,plain,(
% 1.61/1.01    ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.61/1.01    inference(ennf_transformation,[],[f5])).
% 1.61/1.01  
% 1.61/1.01  fof(f32,plain,(
% 1.61/1.01    ( ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.61/1.01    inference(cnf_transformation,[],[f10])).
% 1.61/1.01  
% 1.61/1.01  fof(f27,plain,(
% 1.61/1.01    ( ! [X4,X2,X0,X1] : (r2_hidden(k3_subset_1(X0,X4),X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,k1_zfmisc_1(X0)) | k7_setfam_1(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.61/1.01    inference(cnf_transformation,[],[f20])).
% 1.61/1.01  
% 1.61/1.01  fof(f38,plain,(
% 1.61/1.01    ( ! [X4,X0,X1] : (r2_hidden(k3_subset_1(X0,X4),X1) | ~r2_hidden(X4,k7_setfam_1(X0,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(X0)) | ~m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.61/1.01    inference(equality_resolution,[],[f27])).
% 1.61/1.01  
% 1.61/1.01  fof(f6,axiom,(
% 1.61/1.01    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.61/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.61/1.01  
% 1.61/1.01  fof(f11,plain,(
% 1.61/1.01    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.61/1.01    inference(ennf_transformation,[],[f6])).
% 1.61/1.01  
% 1.61/1.01  fof(f12,plain,(
% 1.61/1.01    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.61/1.01    inference(flattening,[],[f11])).
% 1.61/1.01  
% 1.61/1.01  fof(f33,plain,(
% 1.61/1.01    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.61/1.01    inference(cnf_transformation,[],[f12])).
% 1.61/1.01  
% 1.61/1.01  fof(f35,plain,(
% 1.61/1.01    k1_xboole_0 != sK2),
% 1.61/1.01    inference(cnf_transformation,[],[f22])).
% 1.61/1.01  
% 1.61/1.01  cnf(c_6,plain,
% 1.61/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 1.61/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 1.61/1.01      | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(X1))
% 1.61/1.01      | k7_setfam_1(X1,X2) = X0 ),
% 1.61/1.01      inference(cnf_transformation,[],[f29]) ).
% 1.61/1.01  
% 1.61/1.01  cnf(c_471,plain,
% 1.61/1.01      ( k7_setfam_1(X0,X1) = X2
% 1.61/1.01      | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top
% 1.61/1.01      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top
% 1.61/1.01      | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(X0)) = iProver_top ),
% 1.61/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 1.61/1.01  
% 1.61/1.01  cnf(c_5,plain,
% 1.61/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 1.61/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 1.61/1.01      | r2_hidden(sK0(X1,X2,X0),X0)
% 1.61/1.01      | r2_hidden(k3_subset_1(X1,sK0(X1,X2,X0)),X2)
% 1.61/1.01      | k7_setfam_1(X1,X2) = X0 ),
% 1.61/1.01      inference(cnf_transformation,[],[f30]) ).
% 1.61/1.01  
% 1.61/1.01  cnf(c_472,plain,
% 1.61/1.01      ( k7_setfam_1(X0,X1) = X2
% 1.61/1.01      | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top
% 1.61/1.01      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top
% 1.61/1.01      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
% 1.61/1.01      | r2_hidden(k3_subset_1(X0,sK0(X0,X1,X2)),X1) = iProver_top ),
% 1.61/1.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 1.61/1.01  
% 1.61/1.01  cnf(c_11,negated_conjecture,
% 1.61/1.01      ( k1_xboole_0 = k7_setfam_1(sK1,sK2) ),
% 1.61/1.01      inference(cnf_transformation,[],[f36]) ).
% 1.61/1.01  
% 1.61/1.01  cnf(c_7,plain,
% 1.61/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.61/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 1.61/1.01      | ~ m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1)))
% 1.61/1.01      | r2_hidden(X0,k7_setfam_1(X1,X2))
% 1.61/1.01      | ~ r2_hidden(k3_subset_1(X1,X0),X2) ),
% 1.61/1.01      inference(cnf_transformation,[],[f37]) ).
% 1.61/1.01  
% 1.61/1.01  cnf(c_470,plain,
% 1.61/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 1.61/1.01      | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 1.61/1.01      | m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 1.61/1.01      | r2_hidden(X0,k7_setfam_1(X1,X2)) = iProver_top
% 1.61/1.01      | r2_hidden(k3_subset_1(X1,X0),X2) != iProver_top ),
% 1.61/1.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 1.61/1.01  
% 1.61/1.01  cnf(c_1436,plain,
% 1.61/1.01      ( m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top
% 1.61/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
% 1.61/1.01      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
% 1.61/1.01      | r2_hidden(X0,k7_setfam_1(sK1,sK2)) = iProver_top
% 1.61/1.01      | r2_hidden(k3_subset_1(sK1,X0),sK2) != iProver_top ),
% 1.61/1.01      inference(superposition,[status(thm)],[c_11,c_470]) ).
% 1.61/1.01  
% 1.61/1.01  cnf(c_1449,plain,
% 1.61/1.01      ( m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top
% 1.61/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
% 1.61/1.02      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
% 1.61/1.02      | r2_hidden(X0,k1_xboole_0) = iProver_top
% 1.61/1.02      | r2_hidden(k3_subset_1(sK1,X0),sK2) != iProver_top ),
% 1.61/1.02      inference(light_normalisation,[status(thm)],[c_1436,c_11]) ).
% 1.61/1.02  
% 1.61/1.02  cnf(c_13,negated_conjecture,
% 1.61/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
% 1.61/1.02      inference(cnf_transformation,[],[f34]) ).
% 1.61/1.02  
% 1.61/1.02  cnf(c_14,plain,
% 1.61/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
% 1.61/1.02      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 1.61/1.02  
% 1.61/1.02  cnf(c_2,plain,
% 1.61/1.02      ( ~ r2_hidden(X0,X1) | k4_xboole_0(X1,k1_tarski(X0)) != X1 ),
% 1.61/1.02      inference(cnf_transformation,[],[f24]) ).
% 1.61/1.02  
% 1.61/1.02  cnf(c_579,plain,
% 1.61/1.02      ( ~ r2_hidden(X0,k1_xboole_0)
% 1.61/1.02      | k4_xboole_0(k1_xboole_0,k1_tarski(X0)) != k1_xboole_0 ),
% 1.61/1.02      inference(instantiation,[status(thm)],[c_2]) ).
% 1.61/1.02  
% 1.61/1.02  cnf(c_581,plain,
% 1.61/1.02      ( k4_xboole_0(k1_xboole_0,k1_tarski(X0)) != k1_xboole_0
% 1.61/1.02      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 1.61/1.02      inference(predicate_to_equality,[status(thm)],[c_579]) ).
% 1.61/1.02  
% 1.61/1.02  cnf(c_0,plain,
% 1.61/1.02      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 1.61/1.02      inference(cnf_transformation,[],[f23]) ).
% 1.61/1.02  
% 1.61/1.02  cnf(c_580,plain,
% 1.61/1.02      ( k4_xboole_0(k1_xboole_0,k1_tarski(X0)) = k1_xboole_0 ),
% 1.61/1.02      inference(instantiation,[status(thm)],[c_0]) ).
% 1.61/1.02  
% 1.61/1.02  cnf(c_3,plain,
% 1.61/1.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 1.61/1.02      inference(cnf_transformation,[],[f26]) ).
% 1.61/1.02  
% 1.61/1.02  cnf(c_585,plain,
% 1.61/1.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ),
% 1.61/1.02      inference(instantiation,[status(thm)],[c_3]) ).
% 1.61/1.02  
% 1.61/1.02  cnf(c_670,plain,
% 1.61/1.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
% 1.61/1.02      inference(instantiation,[status(thm)],[c_585]) ).
% 1.61/1.02  
% 1.61/1.02  cnf(c_672,plain,
% 1.61/1.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
% 1.61/1.02      inference(predicate_to_equality,[status(thm)],[c_670]) ).
% 1.61/1.02  
% 1.61/1.02  cnf(c_1540,plain,
% 1.61/1.02      ( m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top
% 1.61/1.02      | r2_hidden(k3_subset_1(sK1,X0),sK2) != iProver_top ),
% 1.61/1.02      inference(global_propositional_subsumption,
% 1.61/1.02                [status(thm)],
% 1.61/1.02                [c_1449,c_14,c_581,c_580,c_672]) ).
% 1.61/1.02  
% 1.61/1.02  cnf(c_1550,plain,
% 1.61/1.02      ( k7_setfam_1(sK1,sK2) = X0
% 1.61/1.02      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
% 1.61/1.02      | m1_subset_1(sK0(sK1,sK2,X0),k1_zfmisc_1(sK1)) != iProver_top
% 1.61/1.02      | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
% 1.61/1.02      | r2_hidden(sK0(sK1,sK2,X0),X0) = iProver_top ),
% 1.61/1.02      inference(superposition,[status(thm)],[c_472,c_1540]) ).
% 1.61/1.02  
% 1.61/1.02  cnf(c_1556,plain,
% 1.61/1.02      ( k1_xboole_0 = X0
% 1.61/1.02      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
% 1.61/1.02      | m1_subset_1(sK0(sK1,sK2,X0),k1_zfmisc_1(sK1)) != iProver_top
% 1.61/1.02      | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
% 1.61/1.02      | r2_hidden(sK0(sK1,sK2,X0),X0) = iProver_top ),
% 1.61/1.02      inference(demodulation,[status(thm)],[c_1550,c_11]) ).
% 1.61/1.02  
% 1.61/1.02  cnf(c_1585,plain,
% 1.61/1.02      ( m1_subset_1(sK0(sK1,sK2,X0),k1_zfmisc_1(sK1)) != iProver_top
% 1.61/1.02      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
% 1.61/1.02      | k1_xboole_0 = X0
% 1.61/1.02      | r2_hidden(sK0(sK1,sK2,X0),X0) = iProver_top ),
% 1.61/1.02      inference(global_propositional_subsumption,
% 1.61/1.02                [status(thm)],
% 1.61/1.02                [c_1556,c_14]) ).
% 1.61/1.02  
% 1.61/1.02  cnf(c_1586,plain,
% 1.61/1.02      ( k1_xboole_0 = X0
% 1.61/1.02      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
% 1.61/1.02      | m1_subset_1(sK0(sK1,sK2,X0),k1_zfmisc_1(sK1)) != iProver_top
% 1.61/1.02      | r2_hidden(sK0(sK1,sK2,X0),X0) = iProver_top ),
% 1.61/1.02      inference(renaming,[status(thm)],[c_1585]) ).
% 1.61/1.02  
% 1.61/1.02  cnf(c_1593,plain,
% 1.61/1.02      ( k7_setfam_1(sK1,sK2) = X0
% 1.61/1.02      | k1_xboole_0 = X0
% 1.61/1.02      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
% 1.61/1.02      | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
% 1.61/1.02      | r2_hidden(sK0(sK1,sK2,X0),X0) = iProver_top ),
% 1.61/1.02      inference(superposition,[status(thm)],[c_471,c_1586]) ).
% 1.61/1.02  
% 1.61/1.02  cnf(c_1608,plain,
% 1.61/1.02      ( k1_xboole_0 = X0
% 1.61/1.02      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
% 1.61/1.02      | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
% 1.61/1.02      | r2_hidden(sK0(sK1,sK2,X0),X0) = iProver_top ),
% 1.61/1.02      inference(demodulation,[status(thm)],[c_1593,c_11]) ).
% 1.61/1.02  
% 1.61/1.02  cnf(c_1721,plain,
% 1.61/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
% 1.61/1.02      | k1_xboole_0 = X0
% 1.61/1.02      | r2_hidden(sK0(sK1,sK2,X0),X0) = iProver_top ),
% 1.61/1.02      inference(global_propositional_subsumption,
% 1.61/1.02                [status(thm)],
% 1.61/1.02                [c_1608,c_14]) ).
% 1.61/1.02  
% 1.61/1.02  cnf(c_1722,plain,
% 1.61/1.02      ( k1_xboole_0 = X0
% 1.61/1.02      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
% 1.61/1.02      | r2_hidden(sK0(sK1,sK2,X0),X0) = iProver_top ),
% 1.61/1.02      inference(renaming,[status(thm)],[c_1721]) ).
% 1.61/1.02  
% 1.61/1.02  cnf(c_466,plain,
% 1.61/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
% 1.61/1.02      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 1.61/1.02  
% 1.61/1.02  cnf(c_9,plain,
% 1.61/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 1.61/1.02      | k7_setfam_1(X1,k7_setfam_1(X1,X0)) = X0 ),
% 1.61/1.02      inference(cnf_transformation,[],[f32]) ).
% 1.61/1.02  
% 1.61/1.02  cnf(c_468,plain,
% 1.61/1.02      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
% 1.61/1.02      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 1.61/1.02      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 1.61/1.02  
% 1.61/1.02  cnf(c_717,plain,
% 1.61/1.02      ( k7_setfam_1(sK1,k7_setfam_1(sK1,sK2)) = sK2 ),
% 1.61/1.02      inference(superposition,[status(thm)],[c_466,c_468]) ).
% 1.61/1.02  
% 1.61/1.02  cnf(c_719,plain,
% 1.61/1.02      ( k7_setfam_1(sK1,k1_xboole_0) = sK2 ),
% 1.61/1.02      inference(light_normalisation,[status(thm)],[c_717,c_11]) ).
% 1.61/1.02  
% 1.61/1.02  cnf(c_8,plain,
% 1.61/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.61/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 1.61/1.02      | ~ m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1)))
% 1.61/1.02      | ~ r2_hidden(X0,k7_setfam_1(X1,X2))
% 1.61/1.02      | r2_hidden(k3_subset_1(X1,X0),X2) ),
% 1.61/1.02      inference(cnf_transformation,[],[f38]) ).
% 1.61/1.02  
% 1.61/1.02  cnf(c_469,plain,
% 1.61/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 1.61/1.02      | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 1.61/1.02      | m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 1.61/1.02      | r2_hidden(X0,k7_setfam_1(X1,X2)) != iProver_top
% 1.61/1.02      | r2_hidden(k3_subset_1(X1,X0),X2) = iProver_top ),
% 1.61/1.02      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 1.61/1.02  
% 1.61/1.02  cnf(c_10,plain,
% 1.61/1.02      ( m1_subset_1(X0,X1)
% 1.61/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 1.61/1.02      | ~ r2_hidden(X0,X2) ),
% 1.61/1.02      inference(cnf_transformation,[],[f33]) ).
% 1.61/1.02  
% 1.61/1.02  cnf(c_467,plain,
% 1.61/1.02      ( m1_subset_1(X0,X1) = iProver_top
% 1.61/1.02      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 1.61/1.02      | r2_hidden(X0,X2) != iProver_top ),
% 1.61/1.02      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 1.61/1.02  
% 1.61/1.02  cnf(c_528,plain,
% 1.61/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 1.61/1.02      | m1_subset_1(k7_setfam_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 1.61/1.02      | r2_hidden(X2,k7_setfam_1(X1,X0)) != iProver_top
% 1.61/1.02      | r2_hidden(k3_subset_1(X1,X2),X0) = iProver_top ),
% 1.61/1.02      inference(forward_subsumption_resolution,
% 1.61/1.02                [status(thm)],
% 1.61/1.02                [c_469,c_467]) ).
% 1.61/1.02  
% 1.61/1.02  cnf(c_2390,plain,
% 1.61/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
% 1.61/1.02      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
% 1.61/1.02      | r2_hidden(X0,k7_setfam_1(sK1,k1_xboole_0)) != iProver_top
% 1.61/1.02      | r2_hidden(k3_subset_1(sK1,X0),k1_xboole_0) = iProver_top ),
% 1.61/1.02      inference(superposition,[status(thm)],[c_719,c_528]) ).
% 1.61/1.02  
% 1.61/1.02  cnf(c_2395,plain,
% 1.61/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
% 1.61/1.02      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
% 1.61/1.02      | r2_hidden(X0,sK2) != iProver_top
% 1.61/1.02      | r2_hidden(k3_subset_1(sK1,X0),k1_xboole_0) = iProver_top ),
% 1.61/1.02      inference(light_normalisation,[status(thm)],[c_2390,c_719]) ).
% 1.61/1.02  
% 1.61/1.02  cnf(c_2758,plain,
% 1.61/1.02      ( r2_hidden(X0,sK2) != iProver_top
% 1.61/1.02      | r2_hidden(k3_subset_1(sK1,X0),k1_xboole_0) = iProver_top ),
% 1.61/1.02      inference(global_propositional_subsumption,
% 1.61/1.02                [status(thm)],
% 1.61/1.02                [c_2395,c_14,c_672]) ).
% 1.61/1.02  
% 1.61/1.02  cnf(c_475,plain,
% 1.61/1.02      ( k4_xboole_0(X0,k1_tarski(X1)) != X0
% 1.61/1.02      | r2_hidden(X1,X0) != iProver_top ),
% 1.61/1.02      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 1.61/1.02  
% 1.61/1.02  cnf(c_685,plain,
% 1.61/1.02      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 1.61/1.02      inference(superposition,[status(thm)],[c_0,c_475]) ).
% 1.61/1.02  
% 1.61/1.02  cnf(c_2766,plain,
% 1.61/1.02      ( r2_hidden(X0,sK2) != iProver_top ),
% 1.61/1.02      inference(forward_subsumption_resolution,
% 1.61/1.02                [status(thm)],
% 1.61/1.02                [c_2758,c_685]) ).
% 1.61/1.02  
% 1.61/1.02  cnf(c_2775,plain,
% 1.61/1.02      ( sK2 = k1_xboole_0
% 1.61/1.02      | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top ),
% 1.61/1.02      inference(superposition,[status(thm)],[c_1722,c_2766]) ).
% 1.61/1.02  
% 1.61/1.02  cnf(c_170,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 1.61/1.02  
% 1.61/1.02  cnf(c_601,plain,
% 1.61/1.02      ( sK2 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK2 ),
% 1.61/1.02      inference(instantiation,[status(thm)],[c_170]) ).
% 1.61/1.02  
% 1.61/1.02  cnf(c_602,plain,
% 1.61/1.02      ( sK2 != k1_xboole_0
% 1.61/1.02      | k1_xboole_0 = sK2
% 1.61/1.02      | k1_xboole_0 != k1_xboole_0 ),
% 1.61/1.02      inference(instantiation,[status(thm)],[c_601]) ).
% 1.61/1.02  
% 1.61/1.02  cnf(c_169,plain,( X0 = X0 ),theory(equality) ).
% 1.61/1.02  
% 1.61/1.02  cnf(c_184,plain,
% 1.61/1.02      ( k1_xboole_0 = k1_xboole_0 ),
% 1.61/1.02      inference(instantiation,[status(thm)],[c_169]) ).
% 1.61/1.02  
% 1.61/1.02  cnf(c_12,negated_conjecture,
% 1.61/1.02      ( k1_xboole_0 != sK2 ),
% 1.61/1.02      inference(cnf_transformation,[],[f35]) ).
% 1.61/1.02  
% 1.61/1.02  cnf(contradiction,plain,
% 1.61/1.02      ( $false ),
% 1.61/1.02      inference(minisat,[status(thm)],[c_2775,c_602,c_184,c_12,c_14]) ).
% 1.61/1.02  
% 1.61/1.02  
% 1.61/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 1.61/1.02  
% 1.61/1.02  ------                               Statistics
% 1.61/1.02  
% 1.61/1.02  ------ General
% 1.61/1.02  
% 1.61/1.02  abstr_ref_over_cycles:                  0
% 1.61/1.02  abstr_ref_under_cycles:                 0
% 1.61/1.02  gc_basic_clause_elim:                   0
% 1.61/1.02  forced_gc_time:                         0
% 1.61/1.02  parsing_time:                           0.008
% 1.61/1.02  unif_index_cands_time:                  0.
% 1.61/1.02  unif_index_add_time:                    0.
% 1.61/1.02  orderings_time:                         0.
% 1.61/1.02  out_proof_time:                         0.011
% 1.61/1.02  total_time:                             0.124
% 1.61/1.02  num_of_symbols:                         42
% 1.61/1.02  num_of_terms:                           2935
% 1.61/1.02  
% 1.61/1.02  ------ Preprocessing
% 1.61/1.02  
% 1.61/1.02  num_of_splits:                          0
% 1.61/1.02  num_of_split_atoms:                     0
% 1.61/1.02  num_of_reused_defs:                     0
% 1.61/1.02  num_eq_ax_congr_red:                    10
% 1.61/1.02  num_of_sem_filtered_clauses:            1
% 1.61/1.02  num_of_subtypes:                        0
% 1.61/1.02  monotx_restored_types:                  0
% 1.61/1.02  sat_num_of_epr_types:                   0
% 1.61/1.02  sat_num_of_non_cyclic_types:            0
% 1.61/1.02  sat_guarded_non_collapsed_types:        0
% 1.61/1.02  num_pure_diseq_elim:                    0
% 1.61/1.02  simp_replaced_by:                       0
% 1.61/1.02  res_preprocessed:                       59
% 1.61/1.02  prep_upred:                             0
% 1.61/1.02  prep_unflattend:                        0
% 1.61/1.02  smt_new_axioms:                         0
% 1.61/1.02  pred_elim_cands:                        2
% 1.61/1.02  pred_elim:                              0
% 1.61/1.02  pred_elim_cl:                           0
% 1.61/1.02  pred_elim_cycles:                       1
% 1.61/1.02  merged_defs:                            6
% 1.61/1.02  merged_defs_ncl:                        0
% 1.61/1.02  bin_hyper_res:                          6
% 1.61/1.02  prep_cycles:                            3
% 1.61/1.02  pred_elim_time:                         0.
% 1.61/1.02  splitting_time:                         0.
% 1.61/1.02  sem_filter_time:                        0.
% 1.61/1.02  monotx_time:                            0.
% 1.61/1.02  subtype_inf_time:                       0.
% 1.61/1.02  
% 1.61/1.02  ------ Problem properties
% 1.61/1.02  
% 1.61/1.02  clauses:                                14
% 1.61/1.02  conjectures:                            3
% 1.61/1.02  epr:                                    1
% 1.61/1.02  horn:                                   11
% 1.61/1.02  ground:                                 3
% 1.61/1.02  unary:                                  5
% 1.61/1.02  binary:                                 3
% 1.61/1.02  lits:                                   38
% 1.61/1.02  lits_eq:                                9
% 1.61/1.02  fd_pure:                                0
% 1.61/1.02  fd_pseudo:                              0
% 1.61/1.02  fd_cond:                                0
% 1.61/1.02  fd_pseudo_cond:                         3
% 1.61/1.02  ac_symbols:                             0
% 1.61/1.02  
% 1.61/1.02  ------ Propositional Solver
% 1.61/1.02  
% 1.61/1.02  prop_solver_calls:                      24
% 1.61/1.02  prop_fast_solver_calls:                 459
% 1.61/1.02  smt_solver_calls:                       0
% 1.61/1.02  smt_fast_solver_calls:                  0
% 1.61/1.02  prop_num_of_clauses:                    988
% 1.61/1.02  prop_preprocess_simplified:             2685
% 1.61/1.02  prop_fo_subsumed:                       14
% 1.61/1.02  prop_solver_time:                       0.
% 1.61/1.02  smt_solver_time:                        0.
% 1.61/1.02  smt_fast_solver_time:                   0.
% 1.61/1.02  prop_fast_solver_time:                  0.
% 1.61/1.02  prop_unsat_core_time:                   0.
% 1.61/1.02  
% 1.61/1.02  ------ QBF
% 1.61/1.02  
% 1.61/1.02  qbf_q_res:                              0
% 1.61/1.02  qbf_num_tautologies:                    0
% 1.61/1.02  qbf_prep_cycles:                        0
% 1.61/1.02  
% 1.61/1.02  ------ BMC1
% 1.61/1.02  
% 1.61/1.02  bmc1_current_bound:                     -1
% 1.61/1.02  bmc1_last_solved_bound:                 -1
% 1.61/1.02  bmc1_unsat_core_size:                   -1
% 1.61/1.02  bmc1_unsat_core_parents_size:           -1
% 1.61/1.02  bmc1_merge_next_fun:                    0
% 1.61/1.02  bmc1_unsat_core_clauses_time:           0.
% 1.61/1.02  
% 1.61/1.02  ------ Instantiation
% 1.61/1.02  
% 1.61/1.02  inst_num_of_clauses:                    298
% 1.61/1.02  inst_num_in_passive:                    35
% 1.61/1.02  inst_num_in_active:                     160
% 1.61/1.02  inst_num_in_unprocessed:                103
% 1.61/1.02  inst_num_of_loops:                      190
% 1.61/1.02  inst_num_of_learning_restarts:          0
% 1.61/1.02  inst_num_moves_active_passive:          26
% 1.61/1.02  inst_lit_activity:                      0
% 1.61/1.02  inst_lit_activity_moves:                0
% 1.61/1.02  inst_num_tautologies:                   0
% 1.61/1.02  inst_num_prop_implied:                  0
% 1.61/1.02  inst_num_existing_simplified:           0
% 1.61/1.02  inst_num_eq_res_simplified:             0
% 1.61/1.02  inst_num_child_elim:                    0
% 1.61/1.02  inst_num_of_dismatching_blockings:      117
% 1.61/1.02  inst_num_of_non_proper_insts:           310
% 1.61/1.02  inst_num_of_duplicates:                 0
% 1.61/1.02  inst_inst_num_from_inst_to_res:         0
% 1.61/1.02  inst_dismatching_checking_time:         0.
% 1.61/1.02  
% 1.61/1.02  ------ Resolution
% 1.61/1.02  
% 1.61/1.02  res_num_of_clauses:                     0
% 1.61/1.02  res_num_in_passive:                     0
% 1.61/1.02  res_num_in_active:                      0
% 1.61/1.02  res_num_of_loops:                       62
% 1.61/1.02  res_forward_subset_subsumed:            39
% 1.61/1.02  res_backward_subset_subsumed:           2
% 1.61/1.02  res_forward_subsumed:                   0
% 1.61/1.02  res_backward_subsumed:                  0
% 1.61/1.02  res_forward_subsumption_resolution:     0
% 1.61/1.02  res_backward_subsumption_resolution:    0
% 1.61/1.02  res_clause_to_clause_subsumption:       187
% 1.61/1.02  res_orphan_elimination:                 0
% 1.61/1.02  res_tautology_del:                      32
% 1.61/1.02  res_num_eq_res_simplified:              0
% 1.61/1.02  res_num_sel_changes:                    0
% 1.61/1.02  res_moves_from_active_to_pass:          0
% 1.61/1.02  
% 1.61/1.02  ------ Superposition
% 1.61/1.02  
% 1.61/1.02  sup_time_total:                         0.
% 1.61/1.02  sup_time_generating:                    0.
% 1.61/1.02  sup_time_sim_full:                      0.
% 1.61/1.02  sup_time_sim_immed:                     0.
% 1.61/1.02  
% 1.61/1.02  sup_num_of_clauses:                     59
% 1.61/1.02  sup_num_in_active:                      38
% 1.61/1.02  sup_num_in_passive:                     21
% 1.61/1.02  sup_num_of_loops:                       37
% 1.61/1.02  sup_fw_superposition:                   43
% 1.61/1.02  sup_bw_superposition:                   21
% 1.61/1.02  sup_immediate_simplified:               18
% 1.61/1.02  sup_given_eliminated:                   0
% 1.61/1.02  comparisons_done:                       0
% 1.61/1.02  comparisons_avoided:                    3
% 1.61/1.02  
% 1.61/1.02  ------ Simplifications
% 1.61/1.02  
% 1.61/1.02  
% 1.61/1.02  sim_fw_subset_subsumed:                 1
% 1.61/1.02  sim_bw_subset_subsumed:                 3
% 1.61/1.02  sim_fw_subsumed:                        7
% 1.61/1.02  sim_bw_subsumed:                        0
% 1.61/1.02  sim_fw_subsumption_res:                 2
% 1.61/1.02  sim_bw_subsumption_res:                 0
% 1.61/1.02  sim_tautology_del:                      1
% 1.61/1.02  sim_eq_tautology_del:                   1
% 1.61/1.02  sim_eq_res_simp:                        0
% 1.61/1.02  sim_fw_demodulated:                     4
% 1.61/1.02  sim_bw_demodulated:                     0
% 1.61/1.02  sim_light_normalised:                   8
% 1.61/1.02  sim_joinable_taut:                      0
% 1.61/1.02  sim_joinable_simp:                      0
% 1.61/1.02  sim_ac_normalised:                      0
% 1.61/1.02  sim_smt_subsumption:                    0
% 1.61/1.02  
%------------------------------------------------------------------------------
