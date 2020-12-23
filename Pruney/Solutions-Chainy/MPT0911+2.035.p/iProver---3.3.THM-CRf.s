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
% DateTime   : Thu Dec  3 11:59:07 EST 2020

% Result     : Theorem 3.64s
% Output     : CNFRefutation 3.93s
% Verified   : 
% Statistics : Number of formulae       :  124 (1521 expanded)
%              Number of clauses        :   74 ( 532 expanded)
%              Number of leaves         :   15 ( 329 expanded)
%              Depth                    :   19
%              Number of atoms          :  343 (7477 expanded)
%              Number of equality atoms :  246 (4720 expanded)
%              Maximal formula depth    :   20 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
     => ( ! [X5] :
            ( m1_subset_1(X5,X0)
           => ! [X6] :
                ( m1_subset_1(X6,X1)
               => ! [X7] :
                    ( m1_subset_1(X7,X2)
                   => ( k3_mcart_1(X5,X6,X7) = X4
                     => X3 = X7 ) ) ) )
       => ( k7_mcart_1(X0,X1,X2,X4) = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
       => ( ! [X5] :
              ( m1_subset_1(X5,X0)
             => ! [X6] :
                  ( m1_subset_1(X6,X1)
                 => ! [X7] :
                      ( m1_subset_1(X7,X2)
                     => ( k3_mcart_1(X5,X6,X7) = X4
                       => X3 = X7 ) ) ) )
         => ( k7_mcart_1(X0,X1,X2,X4) = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f20,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k7_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X7
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f21,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k7_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X7
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(flattening,[],[f20])).

fof(f26,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( k7_mcart_1(X0,X1,X2,X4) != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & ! [X5] :
            ( ! [X6] :
                ( ! [X7] :
                    ( X3 = X7
                    | k3_mcart_1(X5,X6,X7) != X4
                    | ~ m1_subset_1(X7,X2) )
                | ~ m1_subset_1(X6,X1) )
            | ~ m1_subset_1(X5,X0) )
        & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) )
   => ( k7_mcart_1(sK2,sK3,sK4,sK6) != sK5
      & k1_xboole_0 != sK4
      & k1_xboole_0 != sK3
      & k1_xboole_0 != sK2
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( sK5 = X7
                  | k3_mcart_1(X5,X6,X7) != sK6
                  | ~ m1_subset_1(X7,sK4) )
              | ~ m1_subset_1(X6,sK3) )
          | ~ m1_subset_1(X5,sK2) )
      & m1_subset_1(sK6,k3_zfmisc_1(sK2,sK3,sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( k7_mcart_1(sK2,sK3,sK4,sK6) != sK5
    & k1_xboole_0 != sK4
    & k1_xboole_0 != sK3
    & k1_xboole_0 != sK2
    & ! [X5] :
        ( ! [X6] :
            ( ! [X7] :
                ( sK5 = X7
                | k3_mcart_1(X5,X6,X7) != sK6
                | ~ m1_subset_1(X7,sK4) )
            | ~ m1_subset_1(X6,sK3) )
        | ~ m1_subset_1(X5,sK2) )
    & m1_subset_1(sK6,k3_zfmisc_1(sK2,sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f21,f26])).

fof(f44,plain,(
    m1_subset_1(sK6,k3_zfmisc_1(sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f27])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f54,plain,(
    m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) ),
    inference(definition_unfolding,[],[f44,f36])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ~ ( ! [X3,X4] : k4_tarski(X3,X4) != X0
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
     => k4_tarski(sK0(X0),sK1(X0)) = X0 ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k4_tarski(sK0(X0),sK1(X0)) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f22])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(sK0(X0),sK1(X0)) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f46,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f27])).

fof(f47,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f27])).

fof(f48,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f24])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f43,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f10])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f45,plain,(
    ! [X6,X7,X5] :
      ( sK5 = X7
      | k3_mcart_1(X5,X6,X7) != sK6
      | ~ m1_subset_1(X7,sK4)
      | ~ m1_subset_1(X6,sK3)
      | ~ m1_subset_1(X5,sK2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X2,X0,X1] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f53,plain,(
    ! [X6,X7,X5] :
      ( sK5 = X7
      | k4_tarski(k4_tarski(X5,X6),X7) != sK6
      | ~ m1_subset_1(X7,sK4)
      | ~ m1_subset_1(X6,sK3)
      | ~ m1_subset_1(X5,sK2) ) ),
    inference(definition_unfolding,[],[f45,f35])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
                & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
                & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
            & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
            & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f41,f36])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f56,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f31])).

fof(f49,plain,(
    k7_mcart_1(sK2,sK3,sK4,sK6) != sK5 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_446,plain,
    ( m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_147,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | X1 != X2
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_6])).

cnf(c_148,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_147])).

cnf(c_445,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X1,X0) != iProver_top
    | r2_hidden(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_148])).

cnf(c_714,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
    | r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_446,c_445])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | k4_tarski(sK0(X0),sK1(X0)) = X0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_454,plain,
    ( k4_tarski(sK0(X0),sK1(X0)) = X0
    | r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2517,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
    | k4_tarski(sK0(sK6),sK1(sK6)) = sK6 ),
    inference(superposition,[status(thm)],[c_714,c_454])).

cnf(c_17,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_16,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_15,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_590,plain,
    ( k2_zfmisc_1(X0,sK3) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_644,plain,
    ( k2_zfmisc_1(sK2,sK3) != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_590])).

cnf(c_772,plain,
    ( ~ r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))
    | k4_tarski(sK0(sK6),sK1(sK6)) = sK6 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_779,plain,
    ( k4_tarski(sK0(sK6),sK1(sK6)) = sK6
    | r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_772])).

cnf(c_242,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_706,plain,
    ( k2_zfmisc_1(sK2,sK3) != X0
    | k2_zfmisc_1(sK2,sK3) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_242])).

cnf(c_978,plain,
    ( k2_zfmisc_1(sK2,sK3) != k2_zfmisc_1(sK2,sK3)
    | k2_zfmisc_1(sK2,sK3) = k1_xboole_0
    | k1_xboole_0 != k2_zfmisc_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_706])).

cnf(c_241,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_979,plain,
    ( k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_241])).

cnf(c_589,plain,
    ( k2_zfmisc_1(X0,sK4) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2009,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) != k1_xboole_0
    | k1_xboole_0 = k2_zfmisc_1(sK2,sK3)
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_589])).

cnf(c_2716,plain,
    ( k4_tarski(sK0(sK6),sK1(sK6)) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2517,c_17,c_16,c_15,c_644,c_714,c_779,c_978,c_979,c_2009])).

cnf(c_13,plain,
    ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_2720,plain,
    ( k1_mcart_1(sK6) = sK0(sK6) ),
    inference(superposition,[status(thm)],[c_2716,c_13])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k1_mcart_1(X0),X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_451,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_988,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
    | r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_714,c_451])).

cnf(c_2940,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
    | r2_hidden(sK0(sK6),k2_zfmisc_1(sK2,sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2720,c_988])).

cnf(c_3985,plain,
    ( r2_hidden(sK0(sK6),k2_zfmisc_1(sK2,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2940,c_17,c_16,c_15,c_644,c_978,c_979,c_2009])).

cnf(c_3990,plain,
    ( k4_tarski(sK0(sK0(sK6)),sK1(sK0(sK6))) = sK0(sK6) ),
    inference(superposition,[status(thm)],[c_3985,c_454])).

cnf(c_12,plain,
    ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_4806,plain,
    ( k2_mcart_1(sK0(sK6)) = sK1(sK0(sK6)) ),
    inference(superposition,[status(thm)],[c_3990,c_12])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k2_mcart_1(X0),X2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_452,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k2_mcart_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3991,plain,
    ( r2_hidden(k2_mcart_1(sK0(sK6)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3985,c_452])).

cnf(c_5,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_453,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4063,plain,
    ( m1_subset_1(k2_mcart_1(sK0(sK6)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3991,c_453])).

cnf(c_5454,plain,
    ( m1_subset_1(sK1(sK0(sK6)),sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4806,c_4063])).

cnf(c_4805,plain,
    ( k1_mcart_1(sK0(sK6)) = sK0(sK0(sK6)) ),
    inference(superposition,[status(thm)],[c_3990,c_13])).

cnf(c_3992,plain,
    ( r2_hidden(k1_mcart_1(sK0(sK6)),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3985,c_451])).

cnf(c_4251,plain,
    ( m1_subset_1(k1_mcart_1(sK0(sK6)),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3992,c_453])).

cnf(c_5422,plain,
    ( m1_subset_1(sK0(sK0(sK6)),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4805,c_4251])).

cnf(c_18,negated_conjecture,
    ( ~ m1_subset_1(X0,sK4)
    | ~ m1_subset_1(X1,sK3)
    | ~ m1_subset_1(X2,sK2)
    | k4_tarski(k4_tarski(X2,X1),X0) != sK6
    | sK5 = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_447,plain,
    ( k4_tarski(k4_tarski(X0,X1),X2) != sK6
    | sK5 = X2
    | m1_subset_1(X2,sK4) != iProver_top
    | m1_subset_1(X1,sK3) != iProver_top
    | m1_subset_1(X0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4807,plain,
    ( k4_tarski(sK0(sK6),X0) != sK6
    | sK5 = X0
    | m1_subset_1(X0,sK4) != iProver_top
    | m1_subset_1(sK1(sK0(sK6)),sK3) != iProver_top
    | m1_subset_1(sK0(sK0(sK6)),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3990,c_447])).

cnf(c_4877,plain,
    ( sK1(sK6) = sK5
    | m1_subset_1(sK1(sK0(sK6)),sK3) != iProver_top
    | m1_subset_1(sK1(sK6),sK4) != iProver_top
    | m1_subset_1(sK0(sK0(sK6)),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2716,c_4807])).

cnf(c_2721,plain,
    ( k2_mcart_1(sK6) = sK1(sK6) ),
    inference(superposition,[status(thm)],[c_2716,c_12])).

cnf(c_1435,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
    | r2_hidden(k2_mcart_1(sK6),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_714,c_452])).

cnf(c_1791,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
    | m1_subset_1(k2_mcart_1(sK6),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1435,c_453])).

cnf(c_3232,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
    | m1_subset_1(sK1(sK6),sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2721,c_1791])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_450,plain,
    ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3401,plain,
    ( k7_mcart_1(sK2,sK3,sK4,sK6) = k2_mcart_1(sK6)
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_446,c_450])).

cnf(c_3442,plain,
    ( k7_mcart_1(sK2,sK3,sK4,sK6) = sK1(sK6)
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3401,c_2721])).

cnf(c_47,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_48,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_597,plain,
    ( sK4 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_242])).

cnf(c_598,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_597])).

cnf(c_599,plain,
    ( sK3 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_242])).

cnf(c_600,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_599])).

cnf(c_601,plain,
    ( sK2 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_242])).

cnf(c_602,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_601])).

cnf(c_3804,plain,
    ( k7_mcart_1(sK2,sK3,sK4,sK6) = sK1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3442,c_17,c_16,c_15,c_47,c_48,c_598,c_600,c_602])).

cnf(c_14,negated_conjecture,
    ( k7_mcart_1(sK2,sK3,sK4,sK6) != sK5 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_3807,plain,
    ( sK1(sK6) != sK5 ),
    inference(demodulation,[status(thm)],[c_3804,c_14])).

cnf(c_4957,plain,
    ( m1_subset_1(sK1(sK0(sK6)),sK3) != iProver_top
    | m1_subset_1(sK0(sK0(sK6)),sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4877,c_17,c_16,c_15,c_644,c_978,c_979,c_2009,c_3232,c_3807])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5454,c_5422,c_4957])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.33  % Computer   : n011.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 20:52:12 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running in FOF mode
% 3.64/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.64/0.98  
% 3.64/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.64/0.98  
% 3.64/0.98  ------  iProver source info
% 3.64/0.98  
% 3.64/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.64/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.64/0.98  git: non_committed_changes: false
% 3.64/0.98  git: last_make_outside_of_git: false
% 3.64/0.98  
% 3.64/0.98  ------ 
% 3.64/0.98  ------ Parsing...
% 3.64/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.64/0.98  
% 3.64/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.64/0.98  
% 3.64/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.64/0.98  
% 3.64/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.64/0.98  ------ Proving...
% 3.64/0.98  ------ Problem Properties 
% 3.64/0.98  
% 3.64/0.98  
% 3.64/0.98  clauses                                 19
% 3.64/0.98  conjectures                             6
% 3.64/0.98  EPR                                     5
% 3.64/0.98  Horn                                    14
% 3.64/0.98  unary                                   9
% 3.64/0.98  binary                                  4
% 3.64/0.98  lits                                    43
% 3.64/0.98  lits eq                                 27
% 3.64/0.98  fd_pure                                 0
% 3.64/0.98  fd_pseudo                               0
% 3.64/0.98  fd_cond                                 6
% 3.64/0.98  fd_pseudo_cond                          0
% 3.64/0.98  AC symbols                              0
% 3.64/0.98  
% 3.64/0.98  ------ Input Options Time Limit: Unbounded
% 3.64/0.98  
% 3.64/0.98  
% 3.64/0.98  ------ 
% 3.64/0.98  Current options:
% 3.64/0.98  ------ 
% 3.64/0.98  
% 3.64/0.98  
% 3.64/0.98  
% 3.64/0.98  
% 3.64/0.98  ------ Proving...
% 3.64/0.98  
% 3.64/0.98  
% 3.64/0.98  % SZS status Theorem for theBenchmark.p
% 3.64/0.98  
% 3.64/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.64/0.98  
% 3.64/0.98  fof(f11,conjecture,(
% 3.64/0.98    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 3.64/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.64/0.98  
% 3.64/0.98  fof(f12,negated_conjecture,(
% 3.64/0.98    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 3.64/0.98    inference(negated_conjecture,[],[f11])).
% 3.64/0.98  
% 3.64/0.98  fof(f20,plain,(
% 3.64/0.98    ? [X0,X1,X2,X3,X4] : (((k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X7 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 3.64/0.98    inference(ennf_transformation,[],[f12])).
% 3.64/0.98  
% 3.64/0.98  fof(f21,plain,(
% 3.64/0.98    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 3.64/0.98    inference(flattening,[],[f20])).
% 3.64/0.98  
% 3.64/0.98  fof(f26,plain,(
% 3.64/0.98    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) => (k7_mcart_1(sK2,sK3,sK4,sK6) != sK5 & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & ! [X5] : (! [X6] : (! [X7] : (sK5 = X7 | k3_mcart_1(X5,X6,X7) != sK6 | ~m1_subset_1(X7,sK4)) | ~m1_subset_1(X6,sK3)) | ~m1_subset_1(X5,sK2)) & m1_subset_1(sK6,k3_zfmisc_1(sK2,sK3,sK4)))),
% 3.64/0.98    introduced(choice_axiom,[])).
% 3.64/0.98  
% 3.64/0.98  fof(f27,plain,(
% 3.64/0.98    k7_mcart_1(sK2,sK3,sK4,sK6) != sK5 & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & ! [X5] : (! [X6] : (! [X7] : (sK5 = X7 | k3_mcart_1(X5,X6,X7) != sK6 | ~m1_subset_1(X7,sK4)) | ~m1_subset_1(X6,sK3)) | ~m1_subset_1(X5,sK2)) & m1_subset_1(sK6,k3_zfmisc_1(sK2,sK3,sK4))),
% 3.64/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f21,f26])).
% 3.64/0.98  
% 3.64/0.98  fof(f44,plain,(
% 3.64/0.98    m1_subset_1(sK6,k3_zfmisc_1(sK2,sK3,sK4))),
% 3.64/0.98    inference(cnf_transformation,[],[f27])).
% 3.64/0.98  
% 3.64/0.98  fof(f7,axiom,(
% 3.64/0.98    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)),
% 3.64/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.64/0.98  
% 3.64/0.98  fof(f36,plain,(
% 3.64/0.98    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)) )),
% 3.64/0.98    inference(cnf_transformation,[],[f7])).
% 3.64/0.98  
% 3.64/0.98  fof(f54,plain,(
% 3.64/0.98    m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))),
% 3.64/0.98    inference(definition_unfolding,[],[f44,f36])).
% 3.64/0.98  
% 3.64/0.98  fof(f1,axiom,(
% 3.64/0.98    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.64/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.64/0.98  
% 3.64/0.98  fof(f13,plain,(
% 3.64/0.98    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.64/0.98    inference(ennf_transformation,[],[f1])).
% 3.64/0.98  
% 3.64/0.98  fof(f28,plain,(
% 3.64/0.98    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.64/0.98    inference(cnf_transformation,[],[f13])).
% 3.64/0.98  
% 3.64/0.98  fof(f5,axiom,(
% 3.64/0.98    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.64/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.64/0.98  
% 3.64/0.98  fof(f16,plain,(
% 3.64/0.98    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.64/0.98    inference(ennf_transformation,[],[f5])).
% 3.64/0.98  
% 3.64/0.98  fof(f17,plain,(
% 3.64/0.98    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.64/0.98    inference(flattening,[],[f16])).
% 3.64/0.98  
% 3.64/0.98  fof(f34,plain,(
% 3.64/0.98    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.64/0.98    inference(cnf_transformation,[],[f17])).
% 3.64/0.98  
% 3.64/0.98  fof(f2,axiom,(
% 3.64/0.98    ! [X0,X1,X2] : ~(! [X3,X4] : k4_tarski(X3,X4) != X0 & r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 3.64/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.64/0.98  
% 3.64/0.98  fof(f14,plain,(
% 3.64/0.98    ! [X0,X1,X2] : (? [X3,X4] : k4_tarski(X3,X4) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 3.64/0.98    inference(ennf_transformation,[],[f2])).
% 3.64/0.98  
% 3.64/0.98  fof(f22,plain,(
% 3.64/0.98    ! [X0] : (? [X3,X4] : k4_tarski(X3,X4) = X0 => k4_tarski(sK0(X0),sK1(X0)) = X0)),
% 3.64/0.98    introduced(choice_axiom,[])).
% 3.64/0.98  
% 3.64/0.98  fof(f23,plain,(
% 3.64/0.98    ! [X0,X1,X2] : (k4_tarski(sK0(X0),sK1(X0)) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 3.64/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f22])).
% 3.64/0.98  
% 3.64/0.98  fof(f29,plain,(
% 3.64/0.98    ( ! [X2,X0,X1] : (k4_tarski(sK0(X0),sK1(X0)) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 3.64/0.98    inference(cnf_transformation,[],[f23])).
% 3.64/0.98  
% 3.64/0.98  fof(f46,plain,(
% 3.64/0.98    k1_xboole_0 != sK2),
% 3.64/0.98    inference(cnf_transformation,[],[f27])).
% 3.64/0.98  
% 3.64/0.98  fof(f47,plain,(
% 3.64/0.98    k1_xboole_0 != sK3),
% 3.64/0.98    inference(cnf_transformation,[],[f27])).
% 3.64/0.98  
% 3.64/0.98  fof(f48,plain,(
% 3.64/0.98    k1_xboole_0 != sK4),
% 3.64/0.98    inference(cnf_transformation,[],[f27])).
% 3.64/0.98  
% 3.64/0.98  fof(f3,axiom,(
% 3.64/0.98    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.64/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.64/0.98  
% 3.64/0.98  fof(f24,plain,(
% 3.64/0.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.64/0.98    inference(nnf_transformation,[],[f3])).
% 3.64/0.98  
% 3.64/0.98  fof(f25,plain,(
% 3.64/0.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.64/0.98    inference(flattening,[],[f24])).
% 3.64/0.98  
% 3.64/0.98  fof(f30,plain,(
% 3.64/0.98    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.64/0.98    inference(cnf_transformation,[],[f25])).
% 3.64/0.98  
% 3.64/0.98  fof(f10,axiom,(
% 3.64/0.98    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 3.64/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.64/0.98  
% 3.64/0.98  fof(f42,plain,(
% 3.64/0.98    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 3.64/0.98    inference(cnf_transformation,[],[f10])).
% 3.64/0.98  
% 3.64/0.98  fof(f8,axiom,(
% 3.64/0.98    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 3.64/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.64/0.98  
% 3.64/0.98  fof(f18,plain,(
% 3.64/0.98    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 3.64/0.98    inference(ennf_transformation,[],[f8])).
% 3.64/0.98  
% 3.64/0.98  fof(f37,plain,(
% 3.64/0.98    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 3.64/0.98    inference(cnf_transformation,[],[f18])).
% 3.64/0.98  
% 3.64/0.98  fof(f43,plain,(
% 3.64/0.98    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 3.64/0.98    inference(cnf_transformation,[],[f10])).
% 3.64/0.98  
% 3.64/0.98  fof(f38,plain,(
% 3.64/0.98    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 3.64/0.98    inference(cnf_transformation,[],[f18])).
% 3.64/0.98  
% 3.64/0.98  fof(f4,axiom,(
% 3.64/0.98    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 3.64/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.64/0.98  
% 3.64/0.98  fof(f15,plain,(
% 3.64/0.98    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 3.64/0.98    inference(ennf_transformation,[],[f4])).
% 3.64/0.98  
% 3.64/0.98  fof(f33,plain,(
% 3.64/0.98    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 3.64/0.98    inference(cnf_transformation,[],[f15])).
% 3.64/0.98  
% 3.64/0.98  fof(f45,plain,(
% 3.64/0.98    ( ! [X6,X7,X5] : (sK5 = X7 | k3_mcart_1(X5,X6,X7) != sK6 | ~m1_subset_1(X7,sK4) | ~m1_subset_1(X6,sK3) | ~m1_subset_1(X5,sK2)) )),
% 3.64/0.98    inference(cnf_transformation,[],[f27])).
% 3.64/0.98  
% 3.64/0.98  fof(f6,axiom,(
% 3.64/0.98    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2)),
% 3.64/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.64/0.98  
% 3.64/0.98  fof(f35,plain,(
% 3.64/0.98    ( ! [X2,X0,X1] : (k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2)) )),
% 3.64/0.98    inference(cnf_transformation,[],[f6])).
% 3.64/0.98  
% 3.64/0.98  fof(f53,plain,(
% 3.64/0.98    ( ! [X6,X7,X5] : (sK5 = X7 | k4_tarski(k4_tarski(X5,X6),X7) != sK6 | ~m1_subset_1(X7,sK4) | ~m1_subset_1(X6,sK3) | ~m1_subset_1(X5,sK2)) )),
% 3.64/0.98    inference(definition_unfolding,[],[f45,f35])).
% 3.64/0.98  
% 3.64/0.98  fof(f9,axiom,(
% 3.64/0.98    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 3.64/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.64/0.98  
% 3.64/0.98  fof(f19,plain,(
% 3.64/0.98    ! [X0,X1,X2] : (! [X3] : ((k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 3.64/0.98    inference(ennf_transformation,[],[f9])).
% 3.64/0.98  
% 3.64/0.98  fof(f41,plain,(
% 3.64/0.98    ( ! [X2,X0,X3,X1] : (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.64/0.98    inference(cnf_transformation,[],[f19])).
% 3.64/0.98  
% 3.64/0.98  fof(f50,plain,(
% 3.64/0.98    ( ! [X2,X0,X3,X1] : (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.64/0.98    inference(definition_unfolding,[],[f41,f36])).
% 3.64/0.98  
% 3.64/0.98  fof(f31,plain,(
% 3.64/0.98    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.64/0.98    inference(cnf_transformation,[],[f25])).
% 3.64/0.98  
% 3.64/0.98  fof(f56,plain,(
% 3.64/0.98    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.64/0.98    inference(equality_resolution,[],[f31])).
% 3.64/0.98  
% 3.64/0.98  fof(f49,plain,(
% 3.64/0.98    k7_mcart_1(sK2,sK3,sK4,sK6) != sK5),
% 3.64/0.98    inference(cnf_transformation,[],[f27])).
% 3.64/0.98  
% 3.64/0.98  cnf(c_19,negated_conjecture,
% 3.64/0.98      ( m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) ),
% 3.64/0.98      inference(cnf_transformation,[],[f54]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_446,plain,
% 3.64/0.98      ( m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
% 3.64/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_0,plain,
% 3.93/0.98      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.93/0.98      inference(cnf_transformation,[],[f28]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_6,plain,
% 3.93/0.98      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.93/0.98      inference(cnf_transformation,[],[f34]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_147,plain,
% 3.93/0.98      ( ~ m1_subset_1(X0,X1)
% 3.93/0.98      | r2_hidden(X0,X1)
% 3.93/0.98      | X1 != X2
% 3.93/0.98      | k1_xboole_0 = X2 ),
% 3.93/0.98      inference(resolution_lifted,[status(thm)],[c_0,c_6]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_148,plain,
% 3.93/0.98      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | k1_xboole_0 = X1 ),
% 3.93/0.98      inference(unflattening,[status(thm)],[c_147]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_445,plain,
% 3.93/0.98      ( k1_xboole_0 = X0
% 3.93/0.98      | m1_subset_1(X1,X0) != iProver_top
% 3.93/0.98      | r2_hidden(X1,X0) = iProver_top ),
% 3.93/0.98      inference(predicate_to_equality,[status(thm)],[c_148]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_714,plain,
% 3.93/0.98      ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
% 3.93/0.98      | r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
% 3.93/0.98      inference(superposition,[status(thm)],[c_446,c_445]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_1,plain,
% 3.93/0.98      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 3.93/0.98      | k4_tarski(sK0(X0),sK1(X0)) = X0 ),
% 3.93/0.98      inference(cnf_transformation,[],[f29]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_454,plain,
% 3.93/0.98      ( k4_tarski(sK0(X0),sK1(X0)) = X0
% 3.93/0.98      | r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
% 3.93/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_2517,plain,
% 3.93/0.98      ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
% 3.93/0.98      | k4_tarski(sK0(sK6),sK1(sK6)) = sK6 ),
% 3.93/0.98      inference(superposition,[status(thm)],[c_714,c_454]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_17,negated_conjecture,
% 3.93/0.98      ( k1_xboole_0 != sK2 ),
% 3.93/0.98      inference(cnf_transformation,[],[f46]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_16,negated_conjecture,
% 3.93/0.98      ( k1_xboole_0 != sK3 ),
% 3.93/0.98      inference(cnf_transformation,[],[f47]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_15,negated_conjecture,
% 3.93/0.98      ( k1_xboole_0 != sK4 ),
% 3.93/0.98      inference(cnf_transformation,[],[f48]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_4,plain,
% 3.93/0.98      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.93/0.98      | k1_xboole_0 = X0
% 3.93/0.98      | k1_xboole_0 = X1 ),
% 3.93/0.98      inference(cnf_transformation,[],[f30]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_590,plain,
% 3.93/0.98      ( k2_zfmisc_1(X0,sK3) != k1_xboole_0
% 3.93/0.98      | k1_xboole_0 = X0
% 3.93/0.98      | k1_xboole_0 = sK3 ),
% 3.93/0.98      inference(instantiation,[status(thm)],[c_4]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_644,plain,
% 3.93/0.98      ( k2_zfmisc_1(sK2,sK3) != k1_xboole_0
% 3.93/0.98      | k1_xboole_0 = sK3
% 3.93/0.98      | k1_xboole_0 = sK2 ),
% 3.93/0.98      inference(instantiation,[status(thm)],[c_590]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_772,plain,
% 3.93/0.98      ( ~ r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))
% 3.93/0.98      | k4_tarski(sK0(sK6),sK1(sK6)) = sK6 ),
% 3.93/0.98      inference(instantiation,[status(thm)],[c_1]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_779,plain,
% 3.93/0.98      ( k4_tarski(sK0(sK6),sK1(sK6)) = sK6
% 3.93/0.98      | r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) != iProver_top ),
% 3.93/0.98      inference(predicate_to_equality,[status(thm)],[c_772]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_242,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_706,plain,
% 3.93/0.98      ( k2_zfmisc_1(sK2,sK3) != X0
% 3.93/0.98      | k2_zfmisc_1(sK2,sK3) = k1_xboole_0
% 3.93/0.98      | k1_xboole_0 != X0 ),
% 3.93/0.98      inference(instantiation,[status(thm)],[c_242]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_978,plain,
% 3.93/0.98      ( k2_zfmisc_1(sK2,sK3) != k2_zfmisc_1(sK2,sK3)
% 3.93/0.98      | k2_zfmisc_1(sK2,sK3) = k1_xboole_0
% 3.93/0.98      | k1_xboole_0 != k2_zfmisc_1(sK2,sK3) ),
% 3.93/0.98      inference(instantiation,[status(thm)],[c_706]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_241,plain,( X0 = X0 ),theory(equality) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_979,plain,
% 3.93/0.98      ( k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK2,sK3) ),
% 3.93/0.98      inference(instantiation,[status(thm)],[c_241]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_589,plain,
% 3.93/0.98      ( k2_zfmisc_1(X0,sK4) != k1_xboole_0
% 3.93/0.98      | k1_xboole_0 = X0
% 3.93/0.98      | k1_xboole_0 = sK4 ),
% 3.93/0.98      inference(instantiation,[status(thm)],[c_4]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_2009,plain,
% 3.93/0.98      ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) != k1_xboole_0
% 3.93/0.98      | k1_xboole_0 = k2_zfmisc_1(sK2,sK3)
% 3.93/0.98      | k1_xboole_0 = sK4 ),
% 3.93/0.98      inference(instantiation,[status(thm)],[c_589]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_2716,plain,
% 3.93/0.98      ( k4_tarski(sK0(sK6),sK1(sK6)) = sK6 ),
% 3.93/0.98      inference(global_propositional_subsumption,
% 3.93/0.98                [status(thm)],
% 3.93/0.98                [c_2517,c_17,c_16,c_15,c_644,c_714,c_779,c_978,c_979,
% 3.93/0.98                 c_2009]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_13,plain,
% 3.93/0.98      ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
% 3.93/0.98      inference(cnf_transformation,[],[f42]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_2720,plain,
% 3.93/0.98      ( k1_mcart_1(sK6) = sK0(sK6) ),
% 3.93/0.98      inference(superposition,[status(thm)],[c_2716,c_13]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_8,plain,
% 3.93/0.98      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 3.93/0.98      | r2_hidden(k1_mcart_1(X0),X1) ),
% 3.93/0.98      inference(cnf_transformation,[],[f37]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_451,plain,
% 3.93/0.98      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.93/0.98      | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
% 3.93/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_988,plain,
% 3.93/0.98      ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
% 3.93/0.98      | r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK2,sK3)) = iProver_top ),
% 3.93/0.98      inference(superposition,[status(thm)],[c_714,c_451]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_2940,plain,
% 3.93/0.98      ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
% 3.93/0.98      | r2_hidden(sK0(sK6),k2_zfmisc_1(sK2,sK3)) = iProver_top ),
% 3.93/0.98      inference(demodulation,[status(thm)],[c_2720,c_988]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_3985,plain,
% 3.93/0.98      ( r2_hidden(sK0(sK6),k2_zfmisc_1(sK2,sK3)) = iProver_top ),
% 3.93/0.98      inference(global_propositional_subsumption,
% 3.93/0.98                [status(thm)],
% 3.93/0.98                [c_2940,c_17,c_16,c_15,c_644,c_978,c_979,c_2009]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_3990,plain,
% 3.93/0.98      ( k4_tarski(sK0(sK0(sK6)),sK1(sK0(sK6))) = sK0(sK6) ),
% 3.93/0.98      inference(superposition,[status(thm)],[c_3985,c_454]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_12,plain,
% 3.93/0.98      ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
% 3.93/0.98      inference(cnf_transformation,[],[f43]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_4806,plain,
% 3.93/0.98      ( k2_mcart_1(sK0(sK6)) = sK1(sK0(sK6)) ),
% 3.93/0.98      inference(superposition,[status(thm)],[c_3990,c_12]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_7,plain,
% 3.93/0.98      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 3.93/0.98      | r2_hidden(k2_mcart_1(X0),X2) ),
% 3.93/0.98      inference(cnf_transformation,[],[f38]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_452,plain,
% 3.93/0.98      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.93/0.98      | r2_hidden(k2_mcart_1(X0),X2) = iProver_top ),
% 3.93/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_3991,plain,
% 3.93/0.98      ( r2_hidden(k2_mcart_1(sK0(sK6)),sK3) = iProver_top ),
% 3.93/0.98      inference(superposition,[status(thm)],[c_3985,c_452]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_5,plain,
% 3.93/0.98      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 3.93/0.98      inference(cnf_transformation,[],[f33]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_453,plain,
% 3.93/0.98      ( m1_subset_1(X0,X1) = iProver_top
% 3.93/0.98      | r2_hidden(X0,X1) != iProver_top ),
% 3.93/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_4063,plain,
% 3.93/0.98      ( m1_subset_1(k2_mcart_1(sK0(sK6)),sK3) = iProver_top ),
% 3.93/0.98      inference(superposition,[status(thm)],[c_3991,c_453]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_5454,plain,
% 3.93/0.98      ( m1_subset_1(sK1(sK0(sK6)),sK3) = iProver_top ),
% 3.93/0.98      inference(demodulation,[status(thm)],[c_4806,c_4063]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_4805,plain,
% 3.93/0.98      ( k1_mcart_1(sK0(sK6)) = sK0(sK0(sK6)) ),
% 3.93/0.98      inference(superposition,[status(thm)],[c_3990,c_13]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_3992,plain,
% 3.93/0.98      ( r2_hidden(k1_mcart_1(sK0(sK6)),sK2) = iProver_top ),
% 3.93/0.98      inference(superposition,[status(thm)],[c_3985,c_451]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_4251,plain,
% 3.93/0.98      ( m1_subset_1(k1_mcart_1(sK0(sK6)),sK2) = iProver_top ),
% 3.93/0.98      inference(superposition,[status(thm)],[c_3992,c_453]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_5422,plain,
% 3.93/0.98      ( m1_subset_1(sK0(sK0(sK6)),sK2) = iProver_top ),
% 3.93/0.98      inference(demodulation,[status(thm)],[c_4805,c_4251]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_18,negated_conjecture,
% 3.93/0.98      ( ~ m1_subset_1(X0,sK4)
% 3.93/0.98      | ~ m1_subset_1(X1,sK3)
% 3.93/0.98      | ~ m1_subset_1(X2,sK2)
% 3.93/0.98      | k4_tarski(k4_tarski(X2,X1),X0) != sK6
% 3.93/0.98      | sK5 = X0 ),
% 3.93/0.98      inference(cnf_transformation,[],[f53]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_447,plain,
% 3.93/0.98      ( k4_tarski(k4_tarski(X0,X1),X2) != sK6
% 3.93/0.98      | sK5 = X2
% 3.93/0.98      | m1_subset_1(X2,sK4) != iProver_top
% 3.93/0.98      | m1_subset_1(X1,sK3) != iProver_top
% 3.93/0.98      | m1_subset_1(X0,sK2) != iProver_top ),
% 3.93/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_4807,plain,
% 3.93/0.98      ( k4_tarski(sK0(sK6),X0) != sK6
% 3.93/0.98      | sK5 = X0
% 3.93/0.98      | m1_subset_1(X0,sK4) != iProver_top
% 3.93/0.98      | m1_subset_1(sK1(sK0(sK6)),sK3) != iProver_top
% 3.93/0.98      | m1_subset_1(sK0(sK0(sK6)),sK2) != iProver_top ),
% 3.93/0.98      inference(superposition,[status(thm)],[c_3990,c_447]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_4877,plain,
% 3.93/0.98      ( sK1(sK6) = sK5
% 3.93/0.98      | m1_subset_1(sK1(sK0(sK6)),sK3) != iProver_top
% 3.93/0.98      | m1_subset_1(sK1(sK6),sK4) != iProver_top
% 3.93/0.98      | m1_subset_1(sK0(sK0(sK6)),sK2) != iProver_top ),
% 3.93/0.98      inference(superposition,[status(thm)],[c_2716,c_4807]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_2721,plain,
% 3.93/0.98      ( k2_mcart_1(sK6) = sK1(sK6) ),
% 3.93/0.98      inference(superposition,[status(thm)],[c_2716,c_12]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_1435,plain,
% 3.93/0.98      ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
% 3.93/0.98      | r2_hidden(k2_mcart_1(sK6),sK4) = iProver_top ),
% 3.93/0.98      inference(superposition,[status(thm)],[c_714,c_452]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_1791,plain,
% 3.93/0.98      ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
% 3.93/0.98      | m1_subset_1(k2_mcart_1(sK6),sK4) = iProver_top ),
% 3.93/0.98      inference(superposition,[status(thm)],[c_1435,c_453]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_3232,plain,
% 3.93/0.98      ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
% 3.93/0.98      | m1_subset_1(sK1(sK6),sK4) = iProver_top ),
% 3.93/0.98      inference(demodulation,[status(thm)],[c_2721,c_1791]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_9,plain,
% 3.93/0.98      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 3.93/0.98      | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
% 3.93/0.98      | k1_xboole_0 = X1
% 3.93/0.98      | k1_xboole_0 = X2
% 3.93/0.98      | k1_xboole_0 = X3 ),
% 3.93/0.98      inference(cnf_transformation,[],[f50]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_450,plain,
% 3.93/0.98      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
% 3.93/0.98      | k1_xboole_0 = X0
% 3.93/0.98      | k1_xboole_0 = X1
% 3.93/0.98      | k1_xboole_0 = X2
% 3.93/0.98      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 3.93/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_3401,plain,
% 3.93/0.98      ( k7_mcart_1(sK2,sK3,sK4,sK6) = k2_mcart_1(sK6)
% 3.93/0.98      | sK4 = k1_xboole_0
% 3.93/0.98      | sK3 = k1_xboole_0
% 3.93/0.98      | sK2 = k1_xboole_0 ),
% 3.93/0.98      inference(superposition,[status(thm)],[c_446,c_450]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_3442,plain,
% 3.93/0.98      ( k7_mcart_1(sK2,sK3,sK4,sK6) = sK1(sK6)
% 3.93/0.98      | sK4 = k1_xboole_0
% 3.93/0.98      | sK3 = k1_xboole_0
% 3.93/0.98      | sK2 = k1_xboole_0 ),
% 3.93/0.98      inference(light_normalisation,[status(thm)],[c_3401,c_2721]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_47,plain,
% 3.93/0.98      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.93/0.98      | k1_xboole_0 = k1_xboole_0 ),
% 3.93/0.98      inference(instantiation,[status(thm)],[c_4]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_3,plain,
% 3.93/0.98      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.93/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_48,plain,
% 3.93/0.98      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.93/0.98      inference(instantiation,[status(thm)],[c_3]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_597,plain,
% 3.93/0.98      ( sK4 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK4 ),
% 3.93/0.98      inference(instantiation,[status(thm)],[c_242]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_598,plain,
% 3.93/0.98      ( sK4 != k1_xboole_0
% 3.93/0.98      | k1_xboole_0 = sK4
% 3.93/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 3.93/0.98      inference(instantiation,[status(thm)],[c_597]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_599,plain,
% 3.93/0.98      ( sK3 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK3 ),
% 3.93/0.98      inference(instantiation,[status(thm)],[c_242]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_600,plain,
% 3.93/0.98      ( sK3 != k1_xboole_0
% 3.93/0.98      | k1_xboole_0 = sK3
% 3.93/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 3.93/0.98      inference(instantiation,[status(thm)],[c_599]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_601,plain,
% 3.93/0.98      ( sK2 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK2 ),
% 3.93/0.98      inference(instantiation,[status(thm)],[c_242]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_602,plain,
% 3.93/0.98      ( sK2 != k1_xboole_0
% 3.93/0.98      | k1_xboole_0 = sK2
% 3.93/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 3.93/0.98      inference(instantiation,[status(thm)],[c_601]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_3804,plain,
% 3.93/0.98      ( k7_mcart_1(sK2,sK3,sK4,sK6) = sK1(sK6) ),
% 3.93/0.98      inference(global_propositional_subsumption,
% 3.93/0.98                [status(thm)],
% 3.93/0.98                [c_3442,c_17,c_16,c_15,c_47,c_48,c_598,c_600,c_602]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_14,negated_conjecture,
% 3.93/0.98      ( k7_mcart_1(sK2,sK3,sK4,sK6) != sK5 ),
% 3.93/0.98      inference(cnf_transformation,[],[f49]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_3807,plain,
% 3.93/0.98      ( sK1(sK6) != sK5 ),
% 3.93/0.98      inference(demodulation,[status(thm)],[c_3804,c_14]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_4957,plain,
% 3.93/0.98      ( m1_subset_1(sK1(sK0(sK6)),sK3) != iProver_top
% 3.93/0.98      | m1_subset_1(sK0(sK0(sK6)),sK2) != iProver_top ),
% 3.93/0.98      inference(global_propositional_subsumption,
% 3.93/0.98                [status(thm)],
% 3.93/0.98                [c_4877,c_17,c_16,c_15,c_644,c_978,c_979,c_2009,c_3232,
% 3.93/0.98                 c_3807]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(contradiction,plain,
% 3.93/0.98      ( $false ),
% 3.93/0.98      inference(minisat,[status(thm)],[c_5454,c_5422,c_4957]) ).
% 3.93/0.98  
% 3.93/0.98  
% 3.93/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.93/0.98  
% 3.93/0.98  ------                               Statistics
% 3.93/0.98  
% 3.93/0.98  ------ Selected
% 3.93/0.98  
% 3.93/0.98  total_time:                             0.343
% 3.93/0.98  
%------------------------------------------------------------------------------
