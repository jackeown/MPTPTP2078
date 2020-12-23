%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0919+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:25 EST 2020

% Result     : Theorem 1.43s
% Output     : CNFRefutation 1.43s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 114 expanded)
%              Number of clauses        :   39 (  43 expanded)
%              Number of leaves         :    9 (  26 expanded)
%              Depth                    :   11
%              Number of atoms          :  235 ( 834 expanded)
%              Number of equality atoms :  145 ( 497 expanded)
%              Maximal formula depth    :   24 (   6 average)
%              Maximal clause size      :   24 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))
     => ( ! [X6] :
            ( m1_subset_1(X6,X0)
           => ! [X7] :
                ( m1_subset_1(X7,X1)
               => ! [X8] :
                    ( m1_subset_1(X8,X2)
                   => ! [X9] :
                        ( m1_subset_1(X9,X3)
                       => ( k4_mcart_1(X6,X7,X8,X9) = X5
                         => X4 = X6 ) ) ) ) )
       => ( k8_mcart_1(X0,X1,X2,X3,X5) = X4
          | k1_xboole_0 = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))
       => ( ! [X6] :
              ( m1_subset_1(X6,X0)
             => ! [X7] :
                  ( m1_subset_1(X7,X1)
                 => ! [X8] :
                      ( m1_subset_1(X8,X2)
                     => ! [X9] :
                          ( m1_subset_1(X9,X3)
                         => ( k4_mcart_1(X6,X7,X8,X9) = X5
                           => X4 = X6 ) ) ) ) )
         => ( k8_mcart_1(X0,X1,X2,X3,X5) = X4
            | k1_xboole_0 = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f13,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( k8_mcart_1(X0,X1,X2,X3,X5) != X4
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( X4 = X6
                      | k4_mcart_1(X6,X7,X8,X9) != X5
                      | ~ m1_subset_1(X9,X3) )
                  | ~ m1_subset_1(X8,X2) )
              | ~ m1_subset_1(X7,X1) )
          | ~ m1_subset_1(X6,X0) )
      & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f14,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( k8_mcart_1(X0,X1,X2,X3,X5) != X4
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( X4 = X6
                      | k4_mcart_1(X6,X7,X8,X9) != X5
                      | ~ m1_subset_1(X9,X3) )
                  | ~ m1_subset_1(X8,X2) )
              | ~ m1_subset_1(X7,X1) )
          | ~ m1_subset_1(X6,X0) )
      & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(flattening,[],[f13])).

fof(f15,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( k8_mcart_1(X0,X1,X2,X3,X5) != X4
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & ! [X6] :
            ( ! [X7] :
                ( ! [X8] :
                    ( ! [X9] :
                        ( X4 = X6
                        | k4_mcart_1(X6,X7,X8,X9) != X5
                        | ~ m1_subset_1(X9,X3) )
                    | ~ m1_subset_1(X8,X2) )
                | ~ m1_subset_1(X7,X1) )
            | ~ m1_subset_1(X6,X0) )
        & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) )
   => ( k8_mcart_1(sK0,sK1,sK2,sK3,sK5) != sK4
      & k1_xboole_0 != sK3
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( sK4 = X6
                      | k4_mcart_1(X6,X7,X8,X9) != sK5
                      | ~ m1_subset_1(X9,sK3) )
                  | ~ m1_subset_1(X8,sK2) )
              | ~ m1_subset_1(X7,sK1) )
          | ~ m1_subset_1(X6,sK0) )
      & m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK5) != sK4
    & k1_xboole_0 != sK3
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & ! [X6] :
        ( ! [X7] :
            ( ! [X8] :
                ( ! [X9] :
                    ( sK4 = X6
                    | k4_mcart_1(X6,X7,X8,X9) != sK5
                    | ~ m1_subset_1(X9,sK3) )
                | ~ m1_subset_1(X8,sK2) )
            | ~ m1_subset_1(X7,sK1) )
        | ~ m1_subset_1(X6,sK0) )
    & m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f14,f15])).

fof(f22,plain,(
    m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f16])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ~ ! [X4] :
              ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
             => k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4 )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f24,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f16])).

fof(f25,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f16])).

fof(f26,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f16])).

fof(f27,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f16])).

fof(f23,plain,(
    ! [X6,X8,X7,X9] :
      ( sK4 = X6
      | k4_mcart_1(X6,X7,X8,X9) != sK5
      | ~ m1_subset_1(X9,sK3)
      | ~ m1_subset_1(X8,sK2)
      | ~ m1_subset_1(X7,sK1)
      | ~ m1_subset_1(X6,sK0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f20,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f19,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f18,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f17,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f28,plain,(
    k8_mcart_1(sK0,sK1,sK2,sK3,sK5) != sK4 ),
    inference(cnf_transformation,[],[f16])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_223,plain,
    ( m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k4_zfmisc_1(X1,X2,X3,X4))
    | k4_mcart_1(k8_mcart_1(X1,X2,X3,X4,X0),k9_mcart_1(X1,X2,X3,X4,X0),k10_mcart_1(X1,X2,X3,X4,X0),k11_mcart_1(X1,X2,X3,X4,X0)) = X0
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_225,plain,
    ( k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X3
    | m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_730,plain,
    ( k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),k9_mcart_1(sK0,sK1,sK2,sK3,sK5),k10_mcart_1(sK0,sK1,sK2,sK3,sK5),k11_mcart_1(sK0,sK1,sK2,sK3,sK5)) = sK5
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_223,c_225])).

cnf(c_9,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_8,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_7,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_6,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_92,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_103,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_92])).

cnf(c_93,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_299,plain,
    ( sK3 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_93])).

cnf(c_300,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_299])).

cnf(c_301,plain,
    ( sK2 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_93])).

cnf(c_302,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_301])).

cnf(c_303,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_93])).

cnf(c_304,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_303])).

cnf(c_305,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_93])).

cnf(c_306,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_305])).

cnf(c_1381,plain,
    ( k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),k9_mcart_1(sK0,sK1,sK2,sK3,sK5),k10_mcart_1(sK0,sK1,sK2,sK3,sK5),k11_mcart_1(sK0,sK1,sK2,sK3,sK5)) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_730,c_9,c_8,c_7,c_6,c_103,c_300,c_302,c_304,c_306])).

cnf(c_10,negated_conjecture,
    ( ~ m1_subset_1(X0,sK3)
    | ~ m1_subset_1(X1,sK2)
    | ~ m1_subset_1(X2,sK1)
    | ~ m1_subset_1(X3,sK0)
    | k4_mcart_1(X3,X2,X1,X0) != sK5
    | sK4 = X3 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_224,plain,
    ( k4_mcart_1(X0,X1,X2,X3) != sK5
    | sK4 = X0
    | m1_subset_1(X3,sK3) != iProver_top
    | m1_subset_1(X2,sK2) != iProver_top
    | m1_subset_1(X1,sK1) != iProver_top
    | m1_subset_1(X0,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1384,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = sK4
    | m1_subset_1(k9_mcart_1(sK0,sK1,sK2,sK3,sK5),sK1) != iProver_top
    | m1_subset_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),sK0) != iProver_top
    | m1_subset_1(k11_mcart_1(sK0,sK1,sK2,sK3,sK5),sK3) != iProver_top
    | m1_subset_1(k10_mcart_1(sK0,sK1,sK2,sK3,sK5),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1381,c_224])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k4_zfmisc_1(X1,X2,X3,X4))
    | m1_subset_1(k9_mcart_1(X1,X2,X3,X4,X0),X2) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_323,plain,
    ( m1_subset_1(k9_mcart_1(sK0,sK1,sK2,sK3,sK5),sK1)
    | ~ m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_324,plain,
    ( m1_subset_1(k9_mcart_1(sK0,sK1,sK2,sK3,sK5),sK1) = iProver_top
    | m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_323])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k4_zfmisc_1(X1,X2,X3,X4))
    | m1_subset_1(k8_mcart_1(X1,X2,X3,X4,X0),X1) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_320,plain,
    ( m1_subset_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),sK0)
    | ~ m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_321,plain,
    ( m1_subset_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),sK0) = iProver_top
    | m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_320])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k4_zfmisc_1(X1,X2,X3,X4))
    | m1_subset_1(k11_mcart_1(X1,X2,X3,X4,X0),X4) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_317,plain,
    ( m1_subset_1(k11_mcart_1(sK0,sK1,sK2,sK3,sK5),sK3)
    | ~ m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_318,plain,
    ( m1_subset_1(k11_mcart_1(sK0,sK1,sK2,sK3,sK5),sK3) = iProver_top
    | m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_317])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k4_zfmisc_1(X1,X2,X3,X4))
    | m1_subset_1(k10_mcart_1(X1,X2,X3,X4,X0),X3) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_314,plain,
    ( m1_subset_1(k10_mcart_1(sK0,sK1,sK2,sK3,sK5),sK2)
    | ~ m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_315,plain,
    ( m1_subset_1(k10_mcart_1(sK0,sK1,sK2,sK3,sK5),sK2) = iProver_top
    | m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_314])).

cnf(c_5,negated_conjecture,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK5) != sK4 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_12,plain,
    ( m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1384,c_324,c_321,c_318,c_315,c_5,c_12])).


%------------------------------------------------------------------------------
