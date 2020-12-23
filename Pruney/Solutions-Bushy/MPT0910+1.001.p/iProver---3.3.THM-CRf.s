%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0910+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:24 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 102 expanded)
%              Number of clauses        :   28 (  31 expanded)
%              Number of leaves         :    6 (  21 expanded)
%              Depth                    :   11
%              Number of atoms          :  188 ( 702 expanded)
%              Number of equality atoms :  113 ( 423 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
     => ( ! [X5] :
            ( m1_subset_1(X5,X0)
           => ! [X6] :
                ( m1_subset_1(X6,X1)
               => ! [X7] :
                    ( m1_subset_1(X7,X2)
                   => ( k3_mcart_1(X5,X6,X7) = X4
                     => X3 = X6 ) ) ) )
       => ( k6_mcart_1(X0,X1,X2,X4) = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
       => ( ! [X5] :
              ( m1_subset_1(X5,X0)
             => ! [X6] :
                  ( m1_subset_1(X6,X1)
                 => ! [X7] :
                      ( m1_subset_1(X7,X2)
                     => ( k3_mcart_1(X5,X6,X7) = X4
                       => X3 = X6 ) ) ) )
         => ( k6_mcart_1(X0,X1,X2,X4) = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f11,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k6_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X6
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f12,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k6_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X6
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(flattening,[],[f11])).

fof(f13,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( k6_mcart_1(X0,X1,X2,X4) != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & ! [X5] :
            ( ! [X6] :
                ( ! [X7] :
                    ( X3 = X6
                    | k3_mcart_1(X5,X6,X7) != X4
                    | ~ m1_subset_1(X7,X2) )
                | ~ m1_subset_1(X6,X1) )
            | ~ m1_subset_1(X5,X0) )
        & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) )
   => ( k6_mcart_1(sK0,sK1,sK2,sK4) != sK3
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( sK3 = X6
                  | k3_mcart_1(X5,X6,X7) != sK4
                  | ~ m1_subset_1(X7,sK2) )
              | ~ m1_subset_1(X6,sK1) )
          | ~ m1_subset_1(X5,sK0) )
      & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK4) != sK3
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & ! [X5] :
        ( ! [X6] :
            ( ! [X7] :
                ( sK3 = X6
                | k3_mcart_1(X5,X6,X7) != sK4
                | ~ m1_subset_1(X7,sK2) )
            | ~ m1_subset_1(X6,sK1) )
        | ~ m1_subset_1(X5,sK0) )
    & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f12,f13])).

fof(f19,plain,(
    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f21,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f14])).

fof(f22,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f14])).

fof(f23,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f14])).

fof(f20,plain,(
    ! [X6,X7,X5] :
      ( sK3 = X6
      | k3_mcart_1(X5,X6,X7) != sK4
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f17,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f16,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f15,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f24,plain,(
    k6_mcart_1(sK0,sK1,sK2,sK4) != sK3 ),
    inference(cnf_transformation,[],[f14])).

cnf(c_9,negated_conjecture,
    ( m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_194,plain,
    ( m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k3_zfmisc_1(X1,X2,X3))
    | k3_mcart_1(k5_mcart_1(X1,X2,X3,X0),k6_mcart_1(X1,X2,X3,X0),k7_mcart_1(X1,X2,X3,X0)) = X0
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f18])).

cnf(c_196,plain,
    ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_539,plain,
    ( k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK4),k6_mcart_1(sK0,sK1,sK2,sK4),k7_mcart_1(sK0,sK1,sK2,sK4)) = sK4
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_194,c_196])).

cnf(c_7,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_6,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_5,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_279,plain,
    ( ~ m1_subset_1(X0,k3_zfmisc_1(X1,X2,sK2))
    | k3_mcart_1(k5_mcart_1(X1,X2,sK2,X0),k6_mcart_1(X1,X2,sK2,X0),k7_mcart_1(X1,X2,sK2,X0)) = X0
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_338,plain,
    ( ~ m1_subset_1(X0,k3_zfmisc_1(X1,sK1,sK2))
    | k3_mcart_1(k5_mcart_1(X1,sK1,sK2,X0),k6_mcart_1(X1,sK1,sK2,X0),k7_mcart_1(X1,sK1,sK2,X0)) = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_279])).

cnf(c_443,plain,
    ( ~ m1_subset_1(X0,k3_zfmisc_1(sK0,sK1,sK2))
    | k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,X0),k6_mcart_1(sK0,sK1,sK2,X0),k7_mcart_1(sK0,sK1,sK2,X0)) = X0
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_338])).

cnf(c_488,plain,
    ( ~ m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))
    | k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK4),k6_mcart_1(sK0,sK1,sK2,sK4),k7_mcart_1(sK0,sK1,sK2,sK4)) = sK4
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_443])).

cnf(c_744,plain,
    ( k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK4),k6_mcart_1(sK0,sK1,sK2,sK4),k7_mcart_1(sK0,sK1,sK2,sK4)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_539,c_9,c_7,c_6,c_5,c_488])).

cnf(c_8,negated_conjecture,
    ( ~ m1_subset_1(X0,sK2)
    | ~ m1_subset_1(X1,sK1)
    | ~ m1_subset_1(X2,sK0)
    | k3_mcart_1(X2,X1,X0) != sK4
    | sK3 = X1 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_195,plain,
    ( k3_mcart_1(X0,X1,X2) != sK4
    | sK3 = X1
    | m1_subset_1(X2,sK2) != iProver_top
    | m1_subset_1(X1,sK1) != iProver_top
    | m1_subset_1(X0,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_747,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK4) = sK3
    | m1_subset_1(k7_mcart_1(sK0,sK1,sK2,sK4),sK2) != iProver_top
    | m1_subset_1(k6_mcart_1(sK0,sK1,sK2,sK4),sK1) != iProver_top
    | m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK4),sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_744,c_195])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k3_zfmisc_1(X1,X2,X3))
    | m1_subset_1(k7_mcart_1(X1,X2,X3,X0),X3) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_276,plain,
    ( m1_subset_1(k7_mcart_1(sK0,sK1,sK2,sK4),sK2)
    | ~ m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_277,plain,
    ( m1_subset_1(k7_mcart_1(sK0,sK1,sK2,sK4),sK2) = iProver_top
    | m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_276])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k3_zfmisc_1(X1,X2,X3))
    | m1_subset_1(k6_mcart_1(X1,X2,X3,X0),X2) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_273,plain,
    ( m1_subset_1(k6_mcart_1(sK0,sK1,sK2,sK4),sK1)
    | ~ m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_274,plain,
    ( m1_subset_1(k6_mcart_1(sK0,sK1,sK2,sK4),sK1) = iProver_top
    | m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_273])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k3_zfmisc_1(X1,X2,X3))
    | m1_subset_1(k5_mcart_1(X1,X2,X3,X0),X1) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_268,plain,
    ( m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK4),sK0)
    | ~ m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_269,plain,
    ( m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK4),sK0) = iProver_top
    | m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_268])).

cnf(c_4,negated_conjecture,
    ( k6_mcart_1(sK0,sK1,sK2,sK4) != sK3 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_10,plain,
    ( m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_747,c_277,c_274,c_269,c_4,c_10])).


%------------------------------------------------------------------------------
