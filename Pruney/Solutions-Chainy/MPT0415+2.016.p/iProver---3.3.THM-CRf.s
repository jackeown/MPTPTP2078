%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:42:15 EST 2020

% Result     : Theorem 3.20s
% Output     : CNFRefutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 458 expanded)
%              Number of clauses        :   63 ( 169 expanded)
%              Number of leaves         :   11 (  93 expanded)
%              Depth                    :   19
%              Number of atoms          :  324 (1801 expanded)
%              Number of equality atoms :  183 ( 842 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f22,plain,
    ( ? [X0,X1] :
        ( k1_xboole_0 = k7_setfam_1(X0,X1)
        & k1_xboole_0 != X1
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( k1_xboole_0 = k7_setfam_1(sK1,sK2)
      & k1_xboole_0 != sK2
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( k1_xboole_0 = k7_setfam_1(sK1,sK2)
    & k1_xboole_0 != sK2
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f14,f22])).

fof(f36,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
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

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

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
    inference(nnf_transformation,[],[f11])).

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
            & ( ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(k3_subset_1(X0,X3),X1) )
                    & ( r2_hidden(k3_subset_1(X0,X3),X1)
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
              | k7_setfam_1(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f17])).

fof(f19,plain,(
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
    inference(rectify,[],[f18])).

fof(f20,plain,(
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

fof(f21,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k7_setfam_1(X0,X1) = X2
      | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f38,plain,(
    k1_xboole_0 = k7_setfam_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f37,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k7_setfam_1(X0,X1) = X2
      | r2_hidden(k3_subset_1(X0,sK0(X0,X1,X2)),X1)
      | r2_hidden(sK0(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f31,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | k7_setfam_1(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f41,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k7_setfam_1(X0,X1))
      | ~ r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f31])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f15])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f39,plain,(
    ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f26])).

fof(f2,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f40,plain,(
    ! [X1] : k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(equality_resolution,[],[f25])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_316,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(X1))
    | k7_setfam_1(X1,X2) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_320,plain,
    ( k7_setfam_1(X0,X1) = X2
    | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top
    | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_323,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1707,plain,
    ( k7_setfam_1(X0,X1) = X2
    | k3_subset_1(X0,k3_subset_1(X0,sK0(X0,X1,X2))) = sK0(X0,X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_320,c_323])).

cnf(c_8438,plain,
    ( k7_setfam_1(sK1,X0) = sK2
    | k3_subset_1(sK1,k3_subset_1(sK1,sK0(sK1,X0,sK2))) = sK0(sK1,X0,sK2)
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_316,c_1707])).

cnf(c_8577,plain,
    ( k7_setfam_1(sK1,sK2) = sK2
    | k3_subset_1(sK1,k3_subset_1(sK1,sK0(sK1,sK2,sK2))) = sK0(sK1,sK2,sK2) ),
    inference(superposition,[status(thm)],[c_316,c_8438])).

cnf(c_12,negated_conjecture,
    ( k1_xboole_0 = k7_setfam_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_8596,plain,
    ( k3_subset_1(sK1,k3_subset_1(sK1,sK0(sK1,sK2,sK2))) = sK0(sK1,sK2,sK2)
    | sK2 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_8577,c_12])).

cnf(c_15,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_13,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_447,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK1)))
    | m1_subset_1(sK0(sK1,X0,sK2),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1)))
    | k7_setfam_1(sK1,X0) = sK2 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_574,plain,
    ( m1_subset_1(sK0(sK1,sK2,sK2),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1)))
    | k7_setfam_1(sK1,sK2) = sK2 ),
    inference(instantiation,[status(thm)],[c_447])).

cnf(c_575,plain,
    ( k7_setfam_1(sK1,sK2) = sK2
    | m1_subset_1(sK0(sK1,sK2,sK2),k1_zfmisc_1(sK1)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_574])).

cnf(c_128,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_598,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_128])).

cnf(c_129,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_572,plain,
    ( X0 != X1
    | sK2 != X1
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_129])).

cnf(c_938,plain,
    ( X0 != sK2
    | sK2 = X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_572])).

cnf(c_2296,plain,
    ( k7_setfam_1(sK1,X0) != sK2
    | sK2 = k7_setfam_1(sK1,X0)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_938])).

cnf(c_3126,plain,
    ( k7_setfam_1(sK1,sK2) != sK2
    | sK2 = k7_setfam_1(sK1,sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_2296])).

cnf(c_3139,plain,
    ( ~ m1_subset_1(sK0(sK1,X0,sK2),k1_zfmisc_1(sK1))
    | k3_subset_1(sK1,k3_subset_1(sK1,sK0(sK1,X0,sK2))) = sK0(sK1,X0,sK2) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_5321,plain,
    ( ~ m1_subset_1(sK0(sK1,sK2,sK2),k1_zfmisc_1(sK1))
    | k3_subset_1(sK1,k3_subset_1(sK1,sK0(sK1,sK2,sK2))) = sK0(sK1,sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_3139])).

cnf(c_5322,plain,
    ( k3_subset_1(sK1,k3_subset_1(sK1,sK0(sK1,sK2,sK2))) = sK0(sK1,sK2,sK2)
    | m1_subset_1(sK0(sK1,sK2,sK2),k1_zfmisc_1(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5321])).

cnf(c_442,plain,
    ( sK2 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_129])).

cnf(c_5308,plain,
    ( sK2 != k7_setfam_1(sK1,X0)
    | k1_xboole_0 != k7_setfam_1(sK1,X0)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_442])).

cnf(c_7856,plain,
    ( sK2 != k7_setfam_1(sK1,sK2)
    | k1_xboole_0 != k7_setfam_1(sK1,sK2)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_5308])).

cnf(c_8630,plain,
    ( k3_subset_1(sK1,k3_subset_1(sK1,sK0(sK1,sK2,sK2))) = sK0(sK1,sK2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8596,c_15,c_13,c_12,c_575,c_598,c_3126,c_5322,c_7856])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_324,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_8634,plain,
    ( m1_subset_1(sK0(sK1,sK2,sK2),k1_zfmisc_1(sK1)) = iProver_top
    | m1_subset_1(k3_subset_1(sK1,sK0(sK1,sK2,sK2)),k1_zfmisc_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8630,c_324])).

cnf(c_8716,plain,
    ( m1_subset_1(sK0(sK1,sK2,sK2),k1_zfmisc_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8634,c_15,c_13,c_12,c_575,c_598,c_3126,c_7856])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | r2_hidden(sK0(X1,X2,X0),X0)
    | r2_hidden(k3_subset_1(X1,sK0(X1,X2,X0)),X2)
    | k7_setfam_1(X1,X2) = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_321,plain,
    ( k7_setfam_1(X0,X1) = X2
    | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
    | r2_hidden(k3_subset_1(X0,sK0(X0,X1,X2)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | r2_hidden(X0,k7_setfam_1(X1,X2))
    | ~ r2_hidden(k3_subset_1(X1,X0),X2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_319,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | r2_hidden(X0,k7_setfam_1(X1,X2)) = iProver_top
    | r2_hidden(k3_subset_1(X1,X0),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | m1_subset_1(k7_setfam_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_317,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | m1_subset_1(k7_setfam_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_389,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | r2_hidden(X0,k7_setfam_1(X1,X2)) = iProver_top
    | r2_hidden(k3_subset_1(X1,X0),X2) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_319,c_317])).

cnf(c_2239,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top
    | r2_hidden(X0,k7_setfam_1(sK1,sK2)) = iProver_top
    | r2_hidden(k3_subset_1(sK1,X0),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_316,c_389])).

cnf(c_2247,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top
    | r2_hidden(k3_subset_1(sK1,X0),sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2239,c_12])).

cnf(c_0,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_325,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_586,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_325])).

cnf(c_2318,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top
    | r2_hidden(k3_subset_1(sK1,X0),sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2247,c_586])).

cnf(c_2326,plain,
    ( k7_setfam_1(sK1,sK2) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,X0),k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
    | r2_hidden(sK0(sK1,sK2,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_321,c_2318])).

cnf(c_2342,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,X0),k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
    | r2_hidden(sK0(sK1,sK2,X0),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2326,c_12])).

cnf(c_2371,plain,
    ( m1_subset_1(sK0(sK1,sK2,X0),k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
    | k1_xboole_0 = X0
    | r2_hidden(sK0(sK1,sK2,X0),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2342,c_15])).

cnf(c_2372,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,X0),k1_zfmisc_1(sK1)) != iProver_top
    | r2_hidden(sK0(sK1,sK2,X0),X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_2371])).

cnf(c_8727,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
    | r2_hidden(sK0(sK1,sK2,sK2),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_8716,c_2372])).

cnf(c_8636,plain,
    ( m1_subset_1(k3_subset_1(sK1,sK0(sK1,sK2,sK2)),k1_zfmisc_1(sK1)) != iProver_top
    | r2_hidden(sK0(sK1,sK2,sK2),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_8630,c_2318])).

cnf(c_3140,plain,
    ( ~ m1_subset_1(sK0(sK1,X0,sK2),k1_zfmisc_1(sK1))
    | m1_subset_1(k3_subset_1(sK1,sK0(sK1,X0,sK2)),k1_zfmisc_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_5301,plain,
    ( ~ m1_subset_1(sK0(sK1,sK2,sK2),k1_zfmisc_1(sK1))
    | m1_subset_1(k3_subset_1(sK1,sK0(sK1,sK2,sK2)),k1_zfmisc_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_3140])).

cnf(c_5302,plain,
    ( m1_subset_1(sK0(sK1,sK2,sK2),k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(k3_subset_1(sK1,sK0(sK1,sK2,sK2)),k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5301])).

cnf(c_443,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_442])).

cnf(c_1,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_44,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_43,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8727,c_8636,c_7856,c_5302,c_3126,c_598,c_575,c_443,c_44,c_43,c_12,c_13,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:41:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.20/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.00  
% 3.20/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.20/1.00  
% 3.20/1.00  ------  iProver source info
% 3.20/1.00  
% 3.20/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.20/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.20/1.00  git: non_committed_changes: false
% 3.20/1.00  git: last_make_outside_of_git: false
% 3.20/1.00  
% 3.20/1.00  ------ 
% 3.20/1.00  
% 3.20/1.00  ------ Input Options
% 3.20/1.00  
% 3.20/1.00  --out_options                           all
% 3.20/1.00  --tptp_safe_out                         true
% 3.20/1.00  --problem_path                          ""
% 3.20/1.00  --include_path                          ""
% 3.20/1.00  --clausifier                            res/vclausify_rel
% 3.20/1.00  --clausifier_options                    --mode clausify
% 3.20/1.00  --stdin                                 false
% 3.20/1.00  --stats_out                             all
% 3.20/1.00  
% 3.20/1.00  ------ General Options
% 3.20/1.00  
% 3.20/1.00  --fof                                   false
% 3.20/1.00  --time_out_real                         305.
% 3.20/1.00  --time_out_virtual                      -1.
% 3.20/1.00  --symbol_type_check                     false
% 3.20/1.00  --clausify_out                          false
% 3.20/1.00  --sig_cnt_out                           false
% 3.20/1.00  --trig_cnt_out                          false
% 3.20/1.00  --trig_cnt_out_tolerance                1.
% 3.20/1.00  --trig_cnt_out_sk_spl                   false
% 3.20/1.00  --abstr_cl_out                          false
% 3.20/1.00  
% 3.20/1.00  ------ Global Options
% 3.20/1.00  
% 3.20/1.00  --schedule                              default
% 3.20/1.00  --add_important_lit                     false
% 3.20/1.00  --prop_solver_per_cl                    1000
% 3.20/1.00  --min_unsat_core                        false
% 3.20/1.00  --soft_assumptions                      false
% 3.20/1.00  --soft_lemma_size                       3
% 3.20/1.00  --prop_impl_unit_size                   0
% 3.20/1.00  --prop_impl_unit                        []
% 3.20/1.00  --share_sel_clauses                     true
% 3.20/1.00  --reset_solvers                         false
% 3.20/1.00  --bc_imp_inh                            [conj_cone]
% 3.20/1.00  --conj_cone_tolerance                   3.
% 3.20/1.00  --extra_neg_conj                        none
% 3.20/1.00  --large_theory_mode                     true
% 3.20/1.00  --prolific_symb_bound                   200
% 3.20/1.00  --lt_threshold                          2000
% 3.20/1.00  --clause_weak_htbl                      true
% 3.20/1.00  --gc_record_bc_elim                     false
% 3.20/1.00  
% 3.20/1.00  ------ Preprocessing Options
% 3.20/1.00  
% 3.20/1.00  --preprocessing_flag                    true
% 3.20/1.00  --time_out_prep_mult                    0.1
% 3.20/1.00  --splitting_mode                        input
% 3.20/1.00  --splitting_grd                         true
% 3.20/1.00  --splitting_cvd                         false
% 3.20/1.00  --splitting_cvd_svl                     false
% 3.20/1.00  --splitting_nvd                         32
% 3.20/1.00  --sub_typing                            true
% 3.20/1.00  --prep_gs_sim                           true
% 3.20/1.00  --prep_unflatten                        true
% 3.20/1.00  --prep_res_sim                          true
% 3.20/1.00  --prep_upred                            true
% 3.20/1.00  --prep_sem_filter                       exhaustive
% 3.20/1.00  --prep_sem_filter_out                   false
% 3.20/1.00  --pred_elim                             true
% 3.20/1.00  --res_sim_input                         true
% 3.20/1.00  --eq_ax_congr_red                       true
% 3.20/1.00  --pure_diseq_elim                       true
% 3.20/1.00  --brand_transform                       false
% 3.20/1.00  --non_eq_to_eq                          false
% 3.20/1.00  --prep_def_merge                        true
% 3.20/1.00  --prep_def_merge_prop_impl              false
% 3.20/1.00  --prep_def_merge_mbd                    true
% 3.20/1.00  --prep_def_merge_tr_red                 false
% 3.20/1.00  --prep_def_merge_tr_cl                  false
% 3.20/1.00  --smt_preprocessing                     true
% 3.20/1.00  --smt_ac_axioms                         fast
% 3.20/1.00  --preprocessed_out                      false
% 3.20/1.00  --preprocessed_stats                    false
% 3.20/1.00  
% 3.20/1.00  ------ Abstraction refinement Options
% 3.20/1.00  
% 3.20/1.00  --abstr_ref                             []
% 3.20/1.00  --abstr_ref_prep                        false
% 3.20/1.00  --abstr_ref_until_sat                   false
% 3.20/1.00  --abstr_ref_sig_restrict                funpre
% 3.20/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.20/1.00  --abstr_ref_under                       []
% 3.20/1.00  
% 3.20/1.00  ------ SAT Options
% 3.20/1.00  
% 3.20/1.00  --sat_mode                              false
% 3.20/1.00  --sat_fm_restart_options                ""
% 3.20/1.00  --sat_gr_def                            false
% 3.20/1.00  --sat_epr_types                         true
% 3.20/1.00  --sat_non_cyclic_types                  false
% 3.20/1.00  --sat_finite_models                     false
% 3.20/1.00  --sat_fm_lemmas                         false
% 3.20/1.00  --sat_fm_prep                           false
% 3.20/1.00  --sat_fm_uc_incr                        true
% 3.20/1.00  --sat_out_model                         small
% 3.20/1.00  --sat_out_clauses                       false
% 3.20/1.00  
% 3.20/1.00  ------ QBF Options
% 3.20/1.00  
% 3.20/1.00  --qbf_mode                              false
% 3.20/1.00  --qbf_elim_univ                         false
% 3.20/1.00  --qbf_dom_inst                          none
% 3.20/1.00  --qbf_dom_pre_inst                      false
% 3.20/1.00  --qbf_sk_in                             false
% 3.20/1.00  --qbf_pred_elim                         true
% 3.20/1.00  --qbf_split                             512
% 3.20/1.00  
% 3.20/1.00  ------ BMC1 Options
% 3.20/1.00  
% 3.20/1.00  --bmc1_incremental                      false
% 3.20/1.00  --bmc1_axioms                           reachable_all
% 3.20/1.00  --bmc1_min_bound                        0
% 3.20/1.00  --bmc1_max_bound                        -1
% 3.20/1.00  --bmc1_max_bound_default                -1
% 3.20/1.00  --bmc1_symbol_reachability              true
% 3.20/1.00  --bmc1_property_lemmas                  false
% 3.20/1.00  --bmc1_k_induction                      false
% 3.20/1.00  --bmc1_non_equiv_states                 false
% 3.20/1.00  --bmc1_deadlock                         false
% 3.20/1.00  --bmc1_ucm                              false
% 3.20/1.00  --bmc1_add_unsat_core                   none
% 3.20/1.00  --bmc1_unsat_core_children              false
% 3.20/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.20/1.00  --bmc1_out_stat                         full
% 3.20/1.00  --bmc1_ground_init                      false
% 3.20/1.00  --bmc1_pre_inst_next_state              false
% 3.20/1.00  --bmc1_pre_inst_state                   false
% 3.20/1.00  --bmc1_pre_inst_reach_state             false
% 3.20/1.00  --bmc1_out_unsat_core                   false
% 3.20/1.00  --bmc1_aig_witness_out                  false
% 3.20/1.00  --bmc1_verbose                          false
% 3.20/1.00  --bmc1_dump_clauses_tptp                false
% 3.20/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.20/1.00  --bmc1_dump_file                        -
% 3.20/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.20/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.20/1.00  --bmc1_ucm_extend_mode                  1
% 3.20/1.00  --bmc1_ucm_init_mode                    2
% 3.20/1.00  --bmc1_ucm_cone_mode                    none
% 3.20/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.20/1.00  --bmc1_ucm_relax_model                  4
% 3.20/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.20/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.20/1.00  --bmc1_ucm_layered_model                none
% 3.20/1.00  --bmc1_ucm_max_lemma_size               10
% 3.20/1.00  
% 3.20/1.00  ------ AIG Options
% 3.20/1.00  
% 3.20/1.00  --aig_mode                              false
% 3.20/1.00  
% 3.20/1.00  ------ Instantiation Options
% 3.20/1.00  
% 3.20/1.00  --instantiation_flag                    true
% 3.20/1.00  --inst_sos_flag                         false
% 3.20/1.00  --inst_sos_phase                        true
% 3.20/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.20/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.20/1.00  --inst_lit_sel_side                     num_symb
% 3.20/1.00  --inst_solver_per_active                1400
% 3.20/1.00  --inst_solver_calls_frac                1.
% 3.20/1.00  --inst_passive_queue_type               priority_queues
% 3.20/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.20/1.00  --inst_passive_queues_freq              [25;2]
% 3.20/1.00  --inst_dismatching                      true
% 3.20/1.00  --inst_eager_unprocessed_to_passive     true
% 3.20/1.00  --inst_prop_sim_given                   true
% 3.20/1.00  --inst_prop_sim_new                     false
% 3.20/1.00  --inst_subs_new                         false
% 3.20/1.00  --inst_eq_res_simp                      false
% 3.20/1.00  --inst_subs_given                       false
% 3.20/1.00  --inst_orphan_elimination               true
% 3.20/1.00  --inst_learning_loop_flag               true
% 3.20/1.00  --inst_learning_start                   3000
% 3.20/1.00  --inst_learning_factor                  2
% 3.20/1.00  --inst_start_prop_sim_after_learn       3
% 3.20/1.00  --inst_sel_renew                        solver
% 3.20/1.00  --inst_lit_activity_flag                true
% 3.20/1.00  --inst_restr_to_given                   false
% 3.20/1.00  --inst_activity_threshold               500
% 3.20/1.00  --inst_out_proof                        true
% 3.20/1.00  
% 3.20/1.00  ------ Resolution Options
% 3.20/1.00  
% 3.20/1.00  --resolution_flag                       true
% 3.20/1.00  --res_lit_sel                           adaptive
% 3.20/1.00  --res_lit_sel_side                      none
% 3.20/1.00  --res_ordering                          kbo
% 3.20/1.00  --res_to_prop_solver                    active
% 3.20/1.00  --res_prop_simpl_new                    false
% 3.20/1.00  --res_prop_simpl_given                  true
% 3.20/1.00  --res_passive_queue_type                priority_queues
% 3.20/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.20/1.00  --res_passive_queues_freq               [15;5]
% 3.20/1.00  --res_forward_subs                      full
% 3.20/1.00  --res_backward_subs                     full
% 3.20/1.00  --res_forward_subs_resolution           true
% 3.20/1.00  --res_backward_subs_resolution          true
% 3.20/1.00  --res_orphan_elimination                true
% 3.20/1.00  --res_time_limit                        2.
% 3.20/1.00  --res_out_proof                         true
% 3.20/1.00  
% 3.20/1.00  ------ Superposition Options
% 3.20/1.00  
% 3.20/1.00  --superposition_flag                    true
% 3.20/1.00  --sup_passive_queue_type                priority_queues
% 3.20/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.20/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.20/1.00  --demod_completeness_check              fast
% 3.20/1.00  --demod_use_ground                      true
% 3.20/1.00  --sup_to_prop_solver                    passive
% 3.20/1.00  --sup_prop_simpl_new                    true
% 3.20/1.00  --sup_prop_simpl_given                  true
% 3.20/1.00  --sup_fun_splitting                     false
% 3.20/1.00  --sup_smt_interval                      50000
% 3.20/1.00  
% 3.20/1.00  ------ Superposition Simplification Setup
% 3.20/1.00  
% 3.20/1.00  --sup_indices_passive                   []
% 3.20/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.20/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/1.00  --sup_full_bw                           [BwDemod]
% 3.20/1.00  --sup_immed_triv                        [TrivRules]
% 3.20/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.20/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/1.00  --sup_immed_bw_main                     []
% 3.20/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.20/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.20/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.20/1.00  
% 3.20/1.00  ------ Combination Options
% 3.20/1.00  
% 3.20/1.00  --comb_res_mult                         3
% 3.20/1.00  --comb_sup_mult                         2
% 3.20/1.00  --comb_inst_mult                        10
% 3.20/1.00  
% 3.20/1.00  ------ Debug Options
% 3.20/1.00  
% 3.20/1.00  --dbg_backtrace                         false
% 3.20/1.00  --dbg_dump_prop_clauses                 false
% 3.20/1.00  --dbg_dump_prop_clauses_file            -
% 3.20/1.00  --dbg_out_stat                          false
% 3.20/1.00  ------ Parsing...
% 3.20/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.20/1.00  
% 3.20/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.20/1.00  
% 3.20/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.20/1.00  
% 3.20/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.20/1.00  ------ Proving...
% 3.20/1.00  ------ Problem Properties 
% 3.20/1.00  
% 3.20/1.00  
% 3.20/1.00  clauses                                 15
% 3.20/1.00  conjectures                             3
% 3.20/1.00  EPR                                     1
% 3.20/1.00  Horn                                    12
% 3.20/1.00  unary                                   6
% 3.20/1.00  binary                                  3
% 3.20/1.00  lits                                    39
% 3.20/1.00  lits eq                                 11
% 3.20/1.00  fd_pure                                 0
% 3.20/1.00  fd_pseudo                               0
% 3.20/1.00  fd_cond                                 1
% 3.20/1.00  fd_pseudo_cond                          3
% 3.20/1.00  AC symbols                              0
% 3.20/1.00  
% 3.20/1.00  ------ Schedule dynamic 5 is on 
% 3.20/1.00  
% 3.20/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.20/1.00  
% 3.20/1.00  
% 3.20/1.00  ------ 
% 3.20/1.00  Current options:
% 3.20/1.00  ------ 
% 3.20/1.00  
% 3.20/1.00  ------ Input Options
% 3.20/1.00  
% 3.20/1.00  --out_options                           all
% 3.20/1.00  --tptp_safe_out                         true
% 3.20/1.00  --problem_path                          ""
% 3.20/1.00  --include_path                          ""
% 3.20/1.00  --clausifier                            res/vclausify_rel
% 3.20/1.00  --clausifier_options                    --mode clausify
% 3.20/1.00  --stdin                                 false
% 3.20/1.00  --stats_out                             all
% 3.20/1.00  
% 3.20/1.00  ------ General Options
% 3.20/1.00  
% 3.20/1.00  --fof                                   false
% 3.20/1.00  --time_out_real                         305.
% 3.20/1.00  --time_out_virtual                      -1.
% 3.20/1.00  --symbol_type_check                     false
% 3.20/1.00  --clausify_out                          false
% 3.20/1.00  --sig_cnt_out                           false
% 3.20/1.00  --trig_cnt_out                          false
% 3.20/1.00  --trig_cnt_out_tolerance                1.
% 3.20/1.00  --trig_cnt_out_sk_spl                   false
% 3.20/1.00  --abstr_cl_out                          false
% 3.20/1.00  
% 3.20/1.00  ------ Global Options
% 3.20/1.00  
% 3.20/1.00  --schedule                              default
% 3.20/1.00  --add_important_lit                     false
% 3.20/1.00  --prop_solver_per_cl                    1000
% 3.20/1.00  --min_unsat_core                        false
% 3.20/1.00  --soft_assumptions                      false
% 3.20/1.00  --soft_lemma_size                       3
% 3.20/1.00  --prop_impl_unit_size                   0
% 3.20/1.00  --prop_impl_unit                        []
% 3.20/1.00  --share_sel_clauses                     true
% 3.20/1.00  --reset_solvers                         false
% 3.20/1.00  --bc_imp_inh                            [conj_cone]
% 3.20/1.00  --conj_cone_tolerance                   3.
% 3.20/1.00  --extra_neg_conj                        none
% 3.20/1.00  --large_theory_mode                     true
% 3.20/1.00  --prolific_symb_bound                   200
% 3.20/1.00  --lt_threshold                          2000
% 3.20/1.00  --clause_weak_htbl                      true
% 3.20/1.00  --gc_record_bc_elim                     false
% 3.20/1.00  
% 3.20/1.00  ------ Preprocessing Options
% 3.20/1.00  
% 3.20/1.00  --preprocessing_flag                    true
% 3.20/1.00  --time_out_prep_mult                    0.1
% 3.20/1.00  --splitting_mode                        input
% 3.20/1.00  --splitting_grd                         true
% 3.20/1.00  --splitting_cvd                         false
% 3.20/1.00  --splitting_cvd_svl                     false
% 3.20/1.00  --splitting_nvd                         32
% 3.20/1.00  --sub_typing                            true
% 3.20/1.00  --prep_gs_sim                           true
% 3.20/1.00  --prep_unflatten                        true
% 3.20/1.00  --prep_res_sim                          true
% 3.20/1.00  --prep_upred                            true
% 3.20/1.00  --prep_sem_filter                       exhaustive
% 3.20/1.00  --prep_sem_filter_out                   false
% 3.20/1.00  --pred_elim                             true
% 3.20/1.00  --res_sim_input                         true
% 3.20/1.00  --eq_ax_congr_red                       true
% 3.20/1.00  --pure_diseq_elim                       true
% 3.20/1.00  --brand_transform                       false
% 3.20/1.00  --non_eq_to_eq                          false
% 3.20/1.00  --prep_def_merge                        true
% 3.20/1.00  --prep_def_merge_prop_impl              false
% 3.20/1.00  --prep_def_merge_mbd                    true
% 3.20/1.00  --prep_def_merge_tr_red                 false
% 3.20/1.00  --prep_def_merge_tr_cl                  false
% 3.20/1.00  --smt_preprocessing                     true
% 3.20/1.00  --smt_ac_axioms                         fast
% 3.20/1.00  --preprocessed_out                      false
% 3.20/1.00  --preprocessed_stats                    false
% 3.20/1.00  
% 3.20/1.00  ------ Abstraction refinement Options
% 3.20/1.00  
% 3.20/1.00  --abstr_ref                             []
% 3.20/1.00  --abstr_ref_prep                        false
% 3.20/1.00  --abstr_ref_until_sat                   false
% 3.20/1.00  --abstr_ref_sig_restrict                funpre
% 3.20/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.20/1.00  --abstr_ref_under                       []
% 3.20/1.00  
% 3.20/1.00  ------ SAT Options
% 3.20/1.00  
% 3.20/1.00  --sat_mode                              false
% 3.20/1.00  --sat_fm_restart_options                ""
% 3.20/1.00  --sat_gr_def                            false
% 3.20/1.00  --sat_epr_types                         true
% 3.20/1.00  --sat_non_cyclic_types                  false
% 3.20/1.00  --sat_finite_models                     false
% 3.20/1.00  --sat_fm_lemmas                         false
% 3.20/1.00  --sat_fm_prep                           false
% 3.20/1.00  --sat_fm_uc_incr                        true
% 3.20/1.00  --sat_out_model                         small
% 3.20/1.00  --sat_out_clauses                       false
% 3.20/1.00  
% 3.20/1.00  ------ QBF Options
% 3.20/1.00  
% 3.20/1.00  --qbf_mode                              false
% 3.20/1.00  --qbf_elim_univ                         false
% 3.20/1.00  --qbf_dom_inst                          none
% 3.20/1.00  --qbf_dom_pre_inst                      false
% 3.20/1.00  --qbf_sk_in                             false
% 3.20/1.00  --qbf_pred_elim                         true
% 3.20/1.00  --qbf_split                             512
% 3.20/1.00  
% 3.20/1.00  ------ BMC1 Options
% 3.20/1.00  
% 3.20/1.00  --bmc1_incremental                      false
% 3.20/1.00  --bmc1_axioms                           reachable_all
% 3.20/1.00  --bmc1_min_bound                        0
% 3.20/1.00  --bmc1_max_bound                        -1
% 3.20/1.00  --bmc1_max_bound_default                -1
% 3.20/1.00  --bmc1_symbol_reachability              true
% 3.20/1.00  --bmc1_property_lemmas                  false
% 3.20/1.00  --bmc1_k_induction                      false
% 3.20/1.00  --bmc1_non_equiv_states                 false
% 3.20/1.00  --bmc1_deadlock                         false
% 3.20/1.00  --bmc1_ucm                              false
% 3.20/1.00  --bmc1_add_unsat_core                   none
% 3.20/1.00  --bmc1_unsat_core_children              false
% 3.20/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.20/1.00  --bmc1_out_stat                         full
% 3.20/1.00  --bmc1_ground_init                      false
% 3.20/1.00  --bmc1_pre_inst_next_state              false
% 3.20/1.00  --bmc1_pre_inst_state                   false
% 3.20/1.00  --bmc1_pre_inst_reach_state             false
% 3.20/1.00  --bmc1_out_unsat_core                   false
% 3.20/1.00  --bmc1_aig_witness_out                  false
% 3.20/1.00  --bmc1_verbose                          false
% 3.20/1.00  --bmc1_dump_clauses_tptp                false
% 3.20/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.20/1.00  --bmc1_dump_file                        -
% 3.20/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.20/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.20/1.00  --bmc1_ucm_extend_mode                  1
% 3.20/1.00  --bmc1_ucm_init_mode                    2
% 3.20/1.00  --bmc1_ucm_cone_mode                    none
% 3.20/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.20/1.00  --bmc1_ucm_relax_model                  4
% 3.20/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.20/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.20/1.00  --bmc1_ucm_layered_model                none
% 3.20/1.00  --bmc1_ucm_max_lemma_size               10
% 3.20/1.00  
% 3.20/1.00  ------ AIG Options
% 3.20/1.00  
% 3.20/1.00  --aig_mode                              false
% 3.20/1.00  
% 3.20/1.00  ------ Instantiation Options
% 3.20/1.00  
% 3.20/1.00  --instantiation_flag                    true
% 3.20/1.00  --inst_sos_flag                         false
% 3.20/1.00  --inst_sos_phase                        true
% 3.20/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.20/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.20/1.00  --inst_lit_sel_side                     none
% 3.20/1.00  --inst_solver_per_active                1400
% 3.20/1.00  --inst_solver_calls_frac                1.
% 3.20/1.00  --inst_passive_queue_type               priority_queues
% 3.20/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.20/1.00  --inst_passive_queues_freq              [25;2]
% 3.20/1.00  --inst_dismatching                      true
% 3.20/1.00  --inst_eager_unprocessed_to_passive     true
% 3.20/1.00  --inst_prop_sim_given                   true
% 3.20/1.00  --inst_prop_sim_new                     false
% 3.20/1.00  --inst_subs_new                         false
% 3.20/1.00  --inst_eq_res_simp                      false
% 3.20/1.00  --inst_subs_given                       false
% 3.20/1.00  --inst_orphan_elimination               true
% 3.20/1.00  --inst_learning_loop_flag               true
% 3.20/1.00  --inst_learning_start                   3000
% 3.20/1.00  --inst_learning_factor                  2
% 3.20/1.00  --inst_start_prop_sim_after_learn       3
% 3.20/1.00  --inst_sel_renew                        solver
% 3.20/1.00  --inst_lit_activity_flag                true
% 3.20/1.00  --inst_restr_to_given                   false
% 3.20/1.00  --inst_activity_threshold               500
% 3.20/1.00  --inst_out_proof                        true
% 3.20/1.00  
% 3.20/1.00  ------ Resolution Options
% 3.20/1.00  
% 3.20/1.00  --resolution_flag                       false
% 3.20/1.00  --res_lit_sel                           adaptive
% 3.20/1.00  --res_lit_sel_side                      none
% 3.20/1.00  --res_ordering                          kbo
% 3.20/1.00  --res_to_prop_solver                    active
% 3.20/1.00  --res_prop_simpl_new                    false
% 3.20/1.00  --res_prop_simpl_given                  true
% 3.20/1.00  --res_passive_queue_type                priority_queues
% 3.20/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.20/1.00  --res_passive_queues_freq               [15;5]
% 3.20/1.00  --res_forward_subs                      full
% 3.20/1.00  --res_backward_subs                     full
% 3.20/1.00  --res_forward_subs_resolution           true
% 3.20/1.00  --res_backward_subs_resolution          true
% 3.20/1.00  --res_orphan_elimination                true
% 3.20/1.00  --res_time_limit                        2.
% 3.20/1.00  --res_out_proof                         true
% 3.20/1.00  
% 3.20/1.00  ------ Superposition Options
% 3.20/1.00  
% 3.20/1.00  --superposition_flag                    true
% 3.20/1.00  --sup_passive_queue_type                priority_queues
% 3.20/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.20/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.20/1.00  --demod_completeness_check              fast
% 3.20/1.00  --demod_use_ground                      true
% 3.20/1.00  --sup_to_prop_solver                    passive
% 3.20/1.00  --sup_prop_simpl_new                    true
% 3.20/1.00  --sup_prop_simpl_given                  true
% 3.20/1.00  --sup_fun_splitting                     false
% 3.20/1.00  --sup_smt_interval                      50000
% 3.20/1.00  
% 3.20/1.00  ------ Superposition Simplification Setup
% 3.20/1.00  
% 3.20/1.00  --sup_indices_passive                   []
% 3.20/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.20/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/1.00  --sup_full_bw                           [BwDemod]
% 3.20/1.00  --sup_immed_triv                        [TrivRules]
% 3.20/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.20/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/1.00  --sup_immed_bw_main                     []
% 3.20/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.20/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.20/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.20/1.00  
% 3.20/1.00  ------ Combination Options
% 3.20/1.00  
% 3.20/1.00  --comb_res_mult                         3
% 3.20/1.00  --comb_sup_mult                         2
% 3.20/1.00  --comb_inst_mult                        10
% 3.20/1.00  
% 3.20/1.00  ------ Debug Options
% 3.20/1.00  
% 3.20/1.00  --dbg_backtrace                         false
% 3.20/1.00  --dbg_dump_prop_clauses                 false
% 3.20/1.00  --dbg_dump_prop_clauses_file            -
% 3.20/1.00  --dbg_out_stat                          false
% 3.20/1.00  
% 3.20/1.00  
% 3.20/1.00  
% 3.20/1.00  
% 3.20/1.00  ------ Proving...
% 3.20/1.00  
% 3.20/1.00  
% 3.20/1.00  % SZS status Theorem for theBenchmark.p
% 3.20/1.00  
% 3.20/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.20/1.00  
% 3.20/1.00  fof(f7,conjecture,(
% 3.20/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ~(k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1))),
% 3.20/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/1.00  
% 3.20/1.00  fof(f8,negated_conjecture,(
% 3.20/1.00    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ~(k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1))),
% 3.20/1.00    inference(negated_conjecture,[],[f7])).
% 3.20/1.00  
% 3.20/1.00  fof(f13,plain,(
% 3.20/1.00    ? [X0,X1] : ((k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.20/1.00    inference(ennf_transformation,[],[f8])).
% 3.20/1.00  
% 3.20/1.00  fof(f14,plain,(
% 3.20/1.00    ? [X0,X1] : (k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.20/1.00    inference(flattening,[],[f13])).
% 3.20/1.00  
% 3.20/1.00  fof(f22,plain,(
% 3.20/1.00    ? [X0,X1] : (k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (k1_xboole_0 = k7_setfam_1(sK1,sK2) & k1_xboole_0 != sK2 & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))))),
% 3.20/1.00    introduced(choice_axiom,[])).
% 3.20/1.00  
% 3.20/1.00  fof(f23,plain,(
% 3.20/1.00    k1_xboole_0 = k7_setfam_1(sK1,sK2) & k1_xboole_0 != sK2 & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1)))),
% 3.20/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f14,f22])).
% 3.20/1.00  
% 3.20/1.00  fof(f36,plain,(
% 3.20/1.00    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1)))),
% 3.20/1.00    inference(cnf_transformation,[],[f23])).
% 3.20/1.00  
% 3.20/1.00  fof(f5,axiom,(
% 3.20/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k7_setfam_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => (r2_hidden(X3,X2) <=> r2_hidden(k3_subset_1(X0,X3),X1))))))),
% 3.20/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/1.00  
% 3.20/1.00  fof(f11,plain,(
% 3.20/1.00    ! [X0,X1] : (! [X2] : ((k7_setfam_1(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> r2_hidden(k3_subset_1(X0,X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.20/1.00    inference(ennf_transformation,[],[f5])).
% 3.20/1.00  
% 3.20/1.00  fof(f17,plain,(
% 3.20/1.00    ! [X0,X1] : (! [X2] : (((k7_setfam_1(X0,X1) = X2 | ? [X3] : (((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(k3_subset_1(X0,X3),X1)) & (r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(X0))) | k7_setfam_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.20/1.00    inference(nnf_transformation,[],[f11])).
% 3.20/1.00  
% 3.20/1.00  fof(f18,plain,(
% 3.20/1.00    ! [X0,X1] : (! [X2] : (((k7_setfam_1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2)) & m1_subset_1(X3,k1_zfmisc_1(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(k3_subset_1(X0,X3),X1)) & (r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(X0))) | k7_setfam_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.20/1.00    inference(flattening,[],[f17])).
% 3.20/1.00  
% 3.20/1.00  fof(f19,plain,(
% 3.20/1.00    ! [X0,X1] : (! [X2] : (((k7_setfam_1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2)) & m1_subset_1(X3,k1_zfmisc_1(X0)))) & (! [X4] : (((r2_hidden(X4,X2) | ~r2_hidden(k3_subset_1(X0,X4),X1)) & (r2_hidden(k3_subset_1(X0,X4),X1) | ~r2_hidden(X4,X2))) | ~m1_subset_1(X4,k1_zfmisc_1(X0))) | k7_setfam_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.20/1.00    inference(rectify,[],[f18])).
% 3.20/1.00  
% 3.20/1.00  fof(f20,plain,(
% 3.20/1.00    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2)) & m1_subset_1(X3,k1_zfmisc_1(X0))) => ((~r2_hidden(k3_subset_1(X0,sK0(X0,X1,X2)),X1) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(k3_subset_1(X0,sK0(X0,X1,X2)),X1) | r2_hidden(sK0(X0,X1,X2),X2)) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(X0))))),
% 3.20/1.00    introduced(choice_axiom,[])).
% 3.20/1.00  
% 3.20/1.00  fof(f21,plain,(
% 3.20/1.00    ! [X0,X1] : (! [X2] : (((k7_setfam_1(X0,X1) = X2 | ((~r2_hidden(k3_subset_1(X0,sK0(X0,X1,X2)),X1) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(k3_subset_1(X0,sK0(X0,X1,X2)),X1) | r2_hidden(sK0(X0,X1,X2),X2)) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(X0)))) & (! [X4] : (((r2_hidden(X4,X2) | ~r2_hidden(k3_subset_1(X0,X4),X1)) & (r2_hidden(k3_subset_1(X0,X4),X1) | ~r2_hidden(X4,X2))) | ~m1_subset_1(X4,k1_zfmisc_1(X0))) | k7_setfam_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.20/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).
% 3.20/1.00  
% 3.20/1.00  fof(f32,plain,(
% 3.20/1.00    ( ! [X2,X0,X1] : (k7_setfam_1(X0,X1) = X2 | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.20/1.00    inference(cnf_transformation,[],[f21])).
% 3.20/1.00  
% 3.20/1.00  fof(f4,axiom,(
% 3.20/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 3.20/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/1.00  
% 3.20/1.00  fof(f10,plain,(
% 3.20/1.00    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.20/1.00    inference(ennf_transformation,[],[f4])).
% 3.20/1.00  
% 3.20/1.00  fof(f29,plain,(
% 3.20/1.00    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.20/1.00    inference(cnf_transformation,[],[f10])).
% 3.20/1.00  
% 3.20/1.00  fof(f38,plain,(
% 3.20/1.00    k1_xboole_0 = k7_setfam_1(sK1,sK2)),
% 3.20/1.00    inference(cnf_transformation,[],[f23])).
% 3.20/1.00  
% 3.20/1.00  fof(f37,plain,(
% 3.20/1.00    k1_xboole_0 != sK2),
% 3.20/1.00    inference(cnf_transformation,[],[f23])).
% 3.20/1.00  
% 3.20/1.00  fof(f3,axiom,(
% 3.20/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 3.20/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/1.00  
% 3.20/1.00  fof(f9,plain,(
% 3.20/1.00    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.20/1.00    inference(ennf_transformation,[],[f3])).
% 3.20/1.00  
% 3.20/1.00  fof(f28,plain,(
% 3.20/1.00    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.20/1.00    inference(cnf_transformation,[],[f9])).
% 3.20/1.00  
% 3.20/1.00  fof(f33,plain,(
% 3.20/1.00    ( ! [X2,X0,X1] : (k7_setfam_1(X0,X1) = X2 | r2_hidden(k3_subset_1(X0,sK0(X0,X1,X2)),X1) | r2_hidden(sK0(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.20/1.00    inference(cnf_transformation,[],[f21])).
% 3.20/1.00  
% 3.20/1.00  fof(f31,plain,(
% 3.20/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(k3_subset_1(X0,X4),X1) | ~m1_subset_1(X4,k1_zfmisc_1(X0)) | k7_setfam_1(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.20/1.00    inference(cnf_transformation,[],[f21])).
% 3.20/1.00  
% 3.20/1.00  fof(f41,plain,(
% 3.20/1.00    ( ! [X4,X0,X1] : (r2_hidden(X4,k7_setfam_1(X0,X1)) | ~r2_hidden(k3_subset_1(X0,X4),X1) | ~m1_subset_1(X4,k1_zfmisc_1(X0)) | ~m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.20/1.00    inference(equality_resolution,[],[f31])).
% 3.20/1.00  
% 3.20/1.00  fof(f6,axiom,(
% 3.20/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.20/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/1.00  
% 3.20/1.00  fof(f12,plain,(
% 3.20/1.00    ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.20/1.00    inference(ennf_transformation,[],[f6])).
% 3.20/1.00  
% 3.20/1.00  fof(f35,plain,(
% 3.20/1.00    ( ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.20/1.00    inference(cnf_transformation,[],[f12])).
% 3.20/1.00  
% 3.20/1.00  fof(f1,axiom,(
% 3.20/1.00    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.20/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/1.00  
% 3.20/1.00  fof(f15,plain,(
% 3.20/1.00    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 3.20/1.00    inference(nnf_transformation,[],[f1])).
% 3.20/1.00  
% 3.20/1.00  fof(f16,plain,(
% 3.20/1.00    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 3.20/1.00    inference(flattening,[],[f15])).
% 3.20/1.00  
% 3.20/1.00  fof(f26,plain,(
% 3.20/1.00    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 3.20/1.00    inference(cnf_transformation,[],[f16])).
% 3.20/1.00  
% 3.20/1.00  fof(f39,plain,(
% 3.20/1.00    ( ! [X0] : (k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0) )),
% 3.20/1.00    inference(equality_resolution,[],[f26])).
% 3.20/1.00  
% 3.20/1.00  fof(f2,axiom,(
% 3.20/1.00    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 3.20/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/1.00  
% 3.20/1.00  fof(f27,plain,(
% 3.20/1.00    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 3.20/1.00    inference(cnf_transformation,[],[f2])).
% 3.20/1.00  
% 3.20/1.00  fof(f25,plain,(
% 3.20/1.00    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 3.20/1.00    inference(cnf_transformation,[],[f16])).
% 3.20/1.00  
% 3.20/1.00  fof(f40,plain,(
% 3.20/1.00    ( ! [X1] : (k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0) )),
% 3.20/1.00    inference(equality_resolution,[],[f25])).
% 3.20/1.00  
% 3.20/1.00  fof(f24,plain,(
% 3.20/1.00    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0) )),
% 3.20/1.00    inference(cnf_transformation,[],[f16])).
% 3.20/1.00  
% 3.20/1.00  cnf(c_14,negated_conjecture,
% 3.20/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
% 3.20/1.00      inference(cnf_transformation,[],[f36]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_316,plain,
% 3.20/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
% 3.20/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_8,plain,
% 3.20/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.20/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.20/1.00      | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(X1))
% 3.20/1.00      | k7_setfam_1(X1,X2) = X0 ),
% 3.20/1.00      inference(cnf_transformation,[],[f32]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_320,plain,
% 3.20/1.00      ( k7_setfam_1(X0,X1) = X2
% 3.20/1.00      | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top
% 3.20/1.00      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top
% 3.20/1.00      | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(X0)) = iProver_top ),
% 3.20/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_5,plain,
% 3.20/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.20/1.00      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 3.20/1.00      inference(cnf_transformation,[],[f29]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_323,plain,
% 3.20/1.00      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 3.20/1.00      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.20/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_1707,plain,
% 3.20/1.00      ( k7_setfam_1(X0,X1) = X2
% 3.20/1.00      | k3_subset_1(X0,k3_subset_1(X0,sK0(X0,X1,X2))) = sK0(X0,X1,X2)
% 3.20/1.00      | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top
% 3.20/1.00      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 3.20/1.00      inference(superposition,[status(thm)],[c_320,c_323]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_8438,plain,
% 3.20/1.00      ( k7_setfam_1(sK1,X0) = sK2
% 3.20/1.00      | k3_subset_1(sK1,k3_subset_1(sK1,sK0(sK1,X0,sK2))) = sK0(sK1,X0,sK2)
% 3.20/1.00      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top ),
% 3.20/1.00      inference(superposition,[status(thm)],[c_316,c_1707]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_8577,plain,
% 3.20/1.00      ( k7_setfam_1(sK1,sK2) = sK2
% 3.20/1.00      | k3_subset_1(sK1,k3_subset_1(sK1,sK0(sK1,sK2,sK2))) = sK0(sK1,sK2,sK2) ),
% 3.20/1.00      inference(superposition,[status(thm)],[c_316,c_8438]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_12,negated_conjecture,
% 3.20/1.00      ( k1_xboole_0 = k7_setfam_1(sK1,sK2) ),
% 3.20/1.00      inference(cnf_transformation,[],[f38]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_8596,plain,
% 3.20/1.00      ( k3_subset_1(sK1,k3_subset_1(sK1,sK0(sK1,sK2,sK2))) = sK0(sK1,sK2,sK2)
% 3.20/1.00      | sK2 = k1_xboole_0 ),
% 3.20/1.00      inference(light_normalisation,[status(thm)],[c_8577,c_12]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_15,plain,
% 3.20/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
% 3.20/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_13,negated_conjecture,
% 3.20/1.00      ( k1_xboole_0 != sK2 ),
% 3.20/1.00      inference(cnf_transformation,[],[f37]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_447,plain,
% 3.20/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK1)))
% 3.20/1.00      | m1_subset_1(sK0(sK1,X0,sK2),k1_zfmisc_1(sK1))
% 3.20/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1)))
% 3.20/1.00      | k7_setfam_1(sK1,X0) = sK2 ),
% 3.20/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_574,plain,
% 3.20/1.00      ( m1_subset_1(sK0(sK1,sK2,sK2),k1_zfmisc_1(sK1))
% 3.20/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1)))
% 3.20/1.00      | k7_setfam_1(sK1,sK2) = sK2 ),
% 3.20/1.00      inference(instantiation,[status(thm)],[c_447]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_575,plain,
% 3.20/1.00      ( k7_setfam_1(sK1,sK2) = sK2
% 3.20/1.00      | m1_subset_1(sK0(sK1,sK2,sK2),k1_zfmisc_1(sK1)) = iProver_top
% 3.20/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top ),
% 3.20/1.00      inference(predicate_to_equality,[status(thm)],[c_574]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_128,plain,( X0 = X0 ),theory(equality) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_598,plain,
% 3.20/1.00      ( sK2 = sK2 ),
% 3.20/1.00      inference(instantiation,[status(thm)],[c_128]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_129,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_572,plain,
% 3.20/1.00      ( X0 != X1 | sK2 != X1 | sK2 = X0 ),
% 3.20/1.00      inference(instantiation,[status(thm)],[c_129]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_938,plain,
% 3.20/1.00      ( X0 != sK2 | sK2 = X0 | sK2 != sK2 ),
% 3.20/1.00      inference(instantiation,[status(thm)],[c_572]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_2296,plain,
% 3.20/1.00      ( k7_setfam_1(sK1,X0) != sK2
% 3.20/1.00      | sK2 = k7_setfam_1(sK1,X0)
% 3.20/1.00      | sK2 != sK2 ),
% 3.20/1.00      inference(instantiation,[status(thm)],[c_938]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_3126,plain,
% 3.20/1.00      ( k7_setfam_1(sK1,sK2) != sK2
% 3.20/1.00      | sK2 = k7_setfam_1(sK1,sK2)
% 3.20/1.00      | sK2 != sK2 ),
% 3.20/1.00      inference(instantiation,[status(thm)],[c_2296]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_3139,plain,
% 3.20/1.00      ( ~ m1_subset_1(sK0(sK1,X0,sK2),k1_zfmisc_1(sK1))
% 3.20/1.00      | k3_subset_1(sK1,k3_subset_1(sK1,sK0(sK1,X0,sK2))) = sK0(sK1,X0,sK2) ),
% 3.20/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_5321,plain,
% 3.20/1.00      ( ~ m1_subset_1(sK0(sK1,sK2,sK2),k1_zfmisc_1(sK1))
% 3.20/1.00      | k3_subset_1(sK1,k3_subset_1(sK1,sK0(sK1,sK2,sK2))) = sK0(sK1,sK2,sK2) ),
% 3.20/1.00      inference(instantiation,[status(thm)],[c_3139]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_5322,plain,
% 3.20/1.00      ( k3_subset_1(sK1,k3_subset_1(sK1,sK0(sK1,sK2,sK2))) = sK0(sK1,sK2,sK2)
% 3.20/1.00      | m1_subset_1(sK0(sK1,sK2,sK2),k1_zfmisc_1(sK1)) != iProver_top ),
% 3.20/1.00      inference(predicate_to_equality,[status(thm)],[c_5321]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_442,plain,
% 3.20/1.00      ( sK2 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK2 ),
% 3.20/1.00      inference(instantiation,[status(thm)],[c_129]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_5308,plain,
% 3.20/1.00      ( sK2 != k7_setfam_1(sK1,X0)
% 3.20/1.00      | k1_xboole_0 != k7_setfam_1(sK1,X0)
% 3.20/1.00      | k1_xboole_0 = sK2 ),
% 3.20/1.00      inference(instantiation,[status(thm)],[c_442]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_7856,plain,
% 3.20/1.00      ( sK2 != k7_setfam_1(sK1,sK2)
% 3.20/1.00      | k1_xboole_0 != k7_setfam_1(sK1,sK2)
% 3.20/1.00      | k1_xboole_0 = sK2 ),
% 3.20/1.00      inference(instantiation,[status(thm)],[c_5308]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_8630,plain,
% 3.20/1.00      ( k3_subset_1(sK1,k3_subset_1(sK1,sK0(sK1,sK2,sK2))) = sK0(sK1,sK2,sK2) ),
% 3.20/1.00      inference(global_propositional_subsumption,
% 3.20/1.00                [status(thm)],
% 3.20/1.00                [c_8596,c_15,c_13,c_12,c_575,c_598,c_3126,c_5322,c_7856]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_4,plain,
% 3.20/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.20/1.00      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 3.20/1.00      inference(cnf_transformation,[],[f28]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_324,plain,
% 3.20/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.20/1.00      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 3.20/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_8634,plain,
% 3.20/1.00      ( m1_subset_1(sK0(sK1,sK2,sK2),k1_zfmisc_1(sK1)) = iProver_top
% 3.20/1.00      | m1_subset_1(k3_subset_1(sK1,sK0(sK1,sK2,sK2)),k1_zfmisc_1(sK1)) != iProver_top ),
% 3.20/1.00      inference(superposition,[status(thm)],[c_8630,c_324]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_8716,plain,
% 3.20/1.00      ( m1_subset_1(sK0(sK1,sK2,sK2),k1_zfmisc_1(sK1)) = iProver_top ),
% 3.20/1.00      inference(global_propositional_subsumption,
% 3.20/1.00                [status(thm)],
% 3.20/1.00                [c_8634,c_15,c_13,c_12,c_575,c_598,c_3126,c_7856]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_7,plain,
% 3.20/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.20/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.20/1.00      | r2_hidden(sK0(X1,X2,X0),X0)
% 3.20/1.00      | r2_hidden(k3_subset_1(X1,sK0(X1,X2,X0)),X2)
% 3.20/1.00      | k7_setfam_1(X1,X2) = X0 ),
% 3.20/1.00      inference(cnf_transformation,[],[f33]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_321,plain,
% 3.20/1.00      ( k7_setfam_1(X0,X1) = X2
% 3.20/1.00      | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top
% 3.20/1.00      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top
% 3.20/1.00      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
% 3.20/1.00      | r2_hidden(k3_subset_1(X0,sK0(X0,X1,X2)),X1) = iProver_top ),
% 3.20/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_9,plain,
% 3.20/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.20/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.20/1.00      | ~ m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.20/1.00      | r2_hidden(X0,k7_setfam_1(X1,X2))
% 3.20/1.00      | ~ r2_hidden(k3_subset_1(X1,X0),X2) ),
% 3.20/1.00      inference(cnf_transformation,[],[f41]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_319,plain,
% 3.20/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.20/1.00      | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 3.20/1.00      | m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 3.20/1.00      | r2_hidden(X0,k7_setfam_1(X1,X2)) = iProver_top
% 3.20/1.00      | r2_hidden(k3_subset_1(X1,X0),X2) != iProver_top ),
% 3.20/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_11,plain,
% 3.20/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.20/1.00      | m1_subset_1(k7_setfam_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
% 3.20/1.00      inference(cnf_transformation,[],[f35]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_317,plain,
% 3.20/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 3.20/1.00      | m1_subset_1(k7_setfam_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1))) = iProver_top ),
% 3.20/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_389,plain,
% 3.20/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.20/1.00      | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 3.20/1.00      | r2_hidden(X0,k7_setfam_1(X1,X2)) = iProver_top
% 3.20/1.00      | r2_hidden(k3_subset_1(X1,X0),X2) != iProver_top ),
% 3.20/1.00      inference(forward_subsumption_resolution,
% 3.20/1.00                [status(thm)],
% 3.20/1.00                [c_319,c_317]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_2239,plain,
% 3.20/1.00      ( m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top
% 3.20/1.00      | r2_hidden(X0,k7_setfam_1(sK1,sK2)) = iProver_top
% 3.20/1.00      | r2_hidden(k3_subset_1(sK1,X0),sK2) != iProver_top ),
% 3.20/1.00      inference(superposition,[status(thm)],[c_316,c_389]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_2247,plain,
% 3.20/1.00      ( m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top
% 3.20/1.00      | r2_hidden(X0,k1_xboole_0) = iProver_top
% 3.20/1.00      | r2_hidden(k3_subset_1(sK1,X0),sK2) != iProver_top ),
% 3.20/1.00      inference(light_normalisation,[status(thm)],[c_2239,c_12]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_0,plain,
% 3.20/1.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.20/1.00      inference(cnf_transformation,[],[f39]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_3,plain,
% 3.20/1.00      ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
% 3.20/1.00      inference(cnf_transformation,[],[f27]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_325,plain,
% 3.20/1.00      ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 3.20/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_586,plain,
% 3.20/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.20/1.00      inference(superposition,[status(thm)],[c_0,c_325]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_2318,plain,
% 3.20/1.00      ( m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top
% 3.20/1.00      | r2_hidden(k3_subset_1(sK1,X0),sK2) != iProver_top ),
% 3.20/1.00      inference(global_propositional_subsumption,
% 3.20/1.00                [status(thm)],
% 3.20/1.00                [c_2247,c_586]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_2326,plain,
% 3.20/1.00      ( k7_setfam_1(sK1,sK2) = X0
% 3.20/1.00      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
% 3.20/1.00      | m1_subset_1(sK0(sK1,sK2,X0),k1_zfmisc_1(sK1)) != iProver_top
% 3.20/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
% 3.20/1.00      | r2_hidden(sK0(sK1,sK2,X0),X0) = iProver_top ),
% 3.20/1.00      inference(superposition,[status(thm)],[c_321,c_2318]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_2342,plain,
% 3.20/1.00      ( k1_xboole_0 = X0
% 3.20/1.00      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
% 3.20/1.00      | m1_subset_1(sK0(sK1,sK2,X0),k1_zfmisc_1(sK1)) != iProver_top
% 3.20/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
% 3.20/1.00      | r2_hidden(sK0(sK1,sK2,X0),X0) = iProver_top ),
% 3.20/1.00      inference(demodulation,[status(thm)],[c_2326,c_12]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_2371,plain,
% 3.20/1.00      ( m1_subset_1(sK0(sK1,sK2,X0),k1_zfmisc_1(sK1)) != iProver_top
% 3.20/1.00      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
% 3.20/1.00      | k1_xboole_0 = X0
% 3.20/1.00      | r2_hidden(sK0(sK1,sK2,X0),X0) = iProver_top ),
% 3.20/1.00      inference(global_propositional_subsumption,
% 3.20/1.00                [status(thm)],
% 3.20/1.00                [c_2342,c_15]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_2372,plain,
% 3.20/1.00      ( k1_xboole_0 = X0
% 3.20/1.00      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
% 3.20/1.00      | m1_subset_1(sK0(sK1,sK2,X0),k1_zfmisc_1(sK1)) != iProver_top
% 3.20/1.00      | r2_hidden(sK0(sK1,sK2,X0),X0) = iProver_top ),
% 3.20/1.00      inference(renaming,[status(thm)],[c_2371]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_8727,plain,
% 3.20/1.00      ( sK2 = k1_xboole_0
% 3.20/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
% 3.20/1.00      | r2_hidden(sK0(sK1,sK2,sK2),sK2) = iProver_top ),
% 3.20/1.00      inference(superposition,[status(thm)],[c_8716,c_2372]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_8636,plain,
% 3.20/1.00      ( m1_subset_1(k3_subset_1(sK1,sK0(sK1,sK2,sK2)),k1_zfmisc_1(sK1)) != iProver_top
% 3.20/1.00      | r2_hidden(sK0(sK1,sK2,sK2),sK2) != iProver_top ),
% 3.20/1.00      inference(superposition,[status(thm)],[c_8630,c_2318]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_3140,plain,
% 3.20/1.00      ( ~ m1_subset_1(sK0(sK1,X0,sK2),k1_zfmisc_1(sK1))
% 3.20/1.00      | m1_subset_1(k3_subset_1(sK1,sK0(sK1,X0,sK2)),k1_zfmisc_1(sK1)) ),
% 3.20/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_5301,plain,
% 3.20/1.00      ( ~ m1_subset_1(sK0(sK1,sK2,sK2),k1_zfmisc_1(sK1))
% 3.20/1.00      | m1_subset_1(k3_subset_1(sK1,sK0(sK1,sK2,sK2)),k1_zfmisc_1(sK1)) ),
% 3.20/1.00      inference(instantiation,[status(thm)],[c_3140]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_5302,plain,
% 3.20/1.00      ( m1_subset_1(sK0(sK1,sK2,sK2),k1_zfmisc_1(sK1)) != iProver_top
% 3.20/1.00      | m1_subset_1(k3_subset_1(sK1,sK0(sK1,sK2,sK2)),k1_zfmisc_1(sK1)) = iProver_top ),
% 3.20/1.00      inference(predicate_to_equality,[status(thm)],[c_5301]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_443,plain,
% 3.20/1.00      ( sK2 != k1_xboole_0
% 3.20/1.00      | k1_xboole_0 = sK2
% 3.20/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.20/1.00      inference(instantiation,[status(thm)],[c_442]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_1,plain,
% 3.20/1.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.20/1.00      inference(cnf_transformation,[],[f40]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_44,plain,
% 3.20/1.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.20/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_2,plain,
% 3.20/1.00      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.20/1.00      | k1_xboole_0 = X1
% 3.20/1.00      | k1_xboole_0 = X0 ),
% 3.20/1.00      inference(cnf_transformation,[],[f24]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_43,plain,
% 3.20/1.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.20/1.00      | k1_xboole_0 = k1_xboole_0 ),
% 3.20/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(contradiction,plain,
% 3.20/1.00      ( $false ),
% 3.20/1.00      inference(minisat,
% 3.20/1.00                [status(thm)],
% 3.20/1.00                [c_8727,c_8636,c_7856,c_5302,c_3126,c_598,c_575,c_443,
% 3.20/1.00                 c_44,c_43,c_12,c_13,c_15]) ).
% 3.20/1.00  
% 3.20/1.00  
% 3.20/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.20/1.00  
% 3.20/1.00  ------                               Statistics
% 3.20/1.00  
% 3.20/1.00  ------ General
% 3.20/1.00  
% 3.20/1.00  abstr_ref_over_cycles:                  0
% 3.20/1.00  abstr_ref_under_cycles:                 0
% 3.20/1.00  gc_basic_clause_elim:                   0
% 3.20/1.00  forced_gc_time:                         0
% 3.20/1.00  parsing_time:                           0.008
% 3.20/1.00  unif_index_cands_time:                  0.
% 3.20/1.00  unif_index_add_time:                    0.
% 3.20/1.00  orderings_time:                         0.
% 3.20/1.00  out_proof_time:                         0.009
% 3.20/1.00  total_time:                             0.336
% 3.20/1.00  num_of_symbols:                         41
% 3.20/1.00  num_of_terms:                           9404
% 3.20/1.00  
% 3.20/1.00  ------ Preprocessing
% 3.20/1.00  
% 3.20/1.00  num_of_splits:                          0
% 3.20/1.00  num_of_split_atoms:                     0
% 3.20/1.00  num_of_reused_defs:                     0
% 3.20/1.00  num_eq_ax_congr_red:                    8
% 3.20/1.00  num_of_sem_filtered_clauses:            1
% 3.20/1.00  num_of_subtypes:                        0
% 3.20/1.00  monotx_restored_types:                  0
% 3.20/1.00  sat_num_of_epr_types:                   0
% 3.20/1.00  sat_num_of_non_cyclic_types:            0
% 3.20/1.00  sat_guarded_non_collapsed_types:        0
% 3.20/1.00  num_pure_diseq_elim:                    0
% 3.20/1.00  simp_replaced_by:                       0
% 3.20/1.00  res_preprocessed:                       62
% 3.20/1.00  prep_upred:                             0
% 3.20/1.00  prep_unflattend:                        0
% 3.20/1.00  smt_new_axioms:                         0
% 3.20/1.00  pred_elim_cands:                        2
% 3.20/1.00  pred_elim:                              0
% 3.20/1.00  pred_elim_cl:                           0
% 3.20/1.00  pred_elim_cycles:                       1
% 3.20/1.00  merged_defs:                            0
% 3.20/1.00  merged_defs_ncl:                        0
% 3.20/1.00  bin_hyper_res:                          0
% 3.20/1.00  prep_cycles:                            3
% 3.20/1.00  pred_elim_time:                         0.
% 3.20/1.00  splitting_time:                         0.
% 3.20/1.00  sem_filter_time:                        0.
% 3.20/1.00  monotx_time:                            0.
% 3.20/1.00  subtype_inf_time:                       0.
% 3.20/1.00  
% 3.20/1.00  ------ Problem properties
% 3.20/1.00  
% 3.20/1.00  clauses:                                15
% 3.20/1.00  conjectures:                            3
% 3.20/1.00  epr:                                    1
% 3.20/1.00  horn:                                   12
% 3.20/1.00  ground:                                 3
% 3.20/1.00  unary:                                  6
% 3.20/1.00  binary:                                 3
% 3.20/1.00  lits:                                   39
% 3.20/1.00  lits_eq:                                11
% 3.20/1.00  fd_pure:                                0
% 3.20/1.00  fd_pseudo:                              0
% 3.20/1.00  fd_cond:                                1
% 3.20/1.00  fd_pseudo_cond:                         3
% 3.20/1.00  ac_symbols:                             0
% 3.20/1.00  
% 3.20/1.00  ------ Propositional Solver
% 3.20/1.00  
% 3.20/1.00  prop_solver_calls:                      25
% 3.20/1.00  prop_fast_solver_calls:                 799
% 3.20/1.00  smt_solver_calls:                       0
% 3.20/1.00  smt_fast_solver_calls:                  0
% 3.20/1.00  prop_num_of_clauses:                    2928
% 3.20/1.00  prop_preprocess_simplified:             4756
% 3.20/1.00  prop_fo_subsumed:                       27
% 3.20/1.00  prop_solver_time:                       0.
% 3.20/1.00  smt_solver_time:                        0.
% 3.20/1.00  smt_fast_solver_time:                   0.
% 3.20/1.00  prop_fast_solver_time:                  0.
% 3.20/1.00  prop_unsat_core_time:                   0.
% 3.20/1.00  
% 3.20/1.00  ------ QBF
% 3.20/1.00  
% 3.20/1.00  qbf_q_res:                              0
% 3.20/1.00  qbf_num_tautologies:                    0
% 3.20/1.00  qbf_prep_cycles:                        0
% 3.20/1.00  
% 3.20/1.00  ------ BMC1
% 3.20/1.00  
% 3.20/1.00  bmc1_current_bound:                     -1
% 3.20/1.00  bmc1_last_solved_bound:                 -1
% 3.20/1.00  bmc1_unsat_core_size:                   -1
% 3.20/1.00  bmc1_unsat_core_parents_size:           -1
% 3.20/1.00  bmc1_merge_next_fun:                    0
% 3.20/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.20/1.00  
% 3.20/1.00  ------ Instantiation
% 3.20/1.00  
% 3.20/1.00  inst_num_of_clauses:                    799
% 3.20/1.00  inst_num_in_passive:                    235
% 3.20/1.00  inst_num_in_active:                     520
% 3.20/1.00  inst_num_in_unprocessed:                44
% 3.20/1.00  inst_num_of_loops:                      590
% 3.20/1.00  inst_num_of_learning_restarts:          0
% 3.20/1.00  inst_num_moves_active_passive:          66
% 3.20/1.00  inst_lit_activity:                      0
% 3.20/1.00  inst_lit_activity_moves:                0
% 3.20/1.00  inst_num_tautologies:                   0
% 3.20/1.00  inst_num_prop_implied:                  0
% 3.20/1.00  inst_num_existing_simplified:           0
% 3.20/1.00  inst_num_eq_res_simplified:             0
% 3.20/1.00  inst_num_child_elim:                    0
% 3.20/1.00  inst_num_of_dismatching_blockings:      419
% 3.20/1.00  inst_num_of_non_proper_insts:           799
% 3.20/1.00  inst_num_of_duplicates:                 0
% 3.20/1.00  inst_inst_num_from_inst_to_res:         0
% 3.20/1.00  inst_dismatching_checking_time:         0.
% 3.20/1.00  
% 3.20/1.00  ------ Resolution
% 3.20/1.00  
% 3.20/1.00  res_num_of_clauses:                     0
% 3.20/1.00  res_num_in_passive:                     0
% 3.20/1.00  res_num_in_active:                      0
% 3.20/1.00  res_num_of_loops:                       65
% 3.20/1.00  res_forward_subset_subsumed:            33
% 3.20/1.00  res_backward_subset_subsumed:           2
% 3.20/1.00  res_forward_subsumed:                   0
% 3.20/1.00  res_backward_subsumed:                  0
% 3.20/1.00  res_forward_subsumption_resolution:     0
% 3.20/1.00  res_backward_subsumption_resolution:    0
% 3.20/1.00  res_clause_to_clause_subsumption:       1288
% 3.20/1.00  res_orphan_elimination:                 0
% 3.20/1.00  res_tautology_del:                      14
% 3.20/1.00  res_num_eq_res_simplified:              0
% 3.20/1.00  res_num_sel_changes:                    0
% 3.20/1.00  res_moves_from_active_to_pass:          0
% 3.20/1.00  
% 3.20/1.00  ------ Superposition
% 3.20/1.00  
% 3.20/1.00  sup_time_total:                         0.
% 3.20/1.00  sup_time_generating:                    0.
% 3.20/1.00  sup_time_sim_full:                      0.
% 3.20/1.00  sup_time_sim_immed:                     0.
% 3.20/1.00  
% 3.20/1.00  sup_num_of_clauses:                     292
% 3.20/1.00  sup_num_in_active:                      106
% 3.20/1.00  sup_num_in_passive:                     186
% 3.20/1.00  sup_num_of_loops:                       116
% 3.20/1.00  sup_fw_superposition:                   317
% 3.20/1.00  sup_bw_superposition:                   136
% 3.20/1.00  sup_immediate_simplified:               157
% 3.20/1.00  sup_given_eliminated:                   0
% 3.20/1.00  comparisons_done:                       0
% 3.20/1.00  comparisons_avoided:                    11
% 3.20/1.00  
% 3.20/1.00  ------ Simplifications
% 3.20/1.00  
% 3.20/1.00  
% 3.20/1.00  sim_fw_subset_subsumed:                 5
% 3.20/1.00  sim_bw_subset_subsumed:                 2
% 3.20/1.00  sim_fw_subsumed:                        21
% 3.20/1.00  sim_bw_subsumed:                        1
% 3.20/1.00  sim_fw_subsumption_res:                 12
% 3.20/1.00  sim_bw_subsumption_res:                 0
% 3.20/1.00  sim_tautology_del:                      5
% 3.20/1.00  sim_eq_tautology_del:                   72
% 3.20/1.00  sim_eq_res_simp:                        0
% 3.20/1.00  sim_fw_demodulated:                     4
% 3.20/1.00  sim_bw_demodulated:                     9
% 3.20/1.00  sim_light_normalised:                   137
% 3.20/1.00  sim_joinable_taut:                      0
% 3.20/1.00  sim_joinable_simp:                      0
% 3.20/1.00  sim_ac_normalised:                      0
% 3.20/1.00  sim_smt_subsumption:                    0
% 3.20/1.00  
%------------------------------------------------------------------------------
