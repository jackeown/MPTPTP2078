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
% DateTime   : Thu Dec  3 11:58:58 EST 2020

% Result     : Theorem 2.80s
% Output     : CNFRefutation 2.80s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 496 expanded)
%              Number of clauses        :   54 ( 152 expanded)
%              Number of leaves         :   13 ( 104 expanded)
%              Depth                    :   16
%              Number of atoms          :  324 (2701 expanded)
%              Number of equality atoms :  209 (1646 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
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

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f28,plain,
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

fof(f29,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f25,f28])).

fof(f48,plain,(
    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f63,plain,(
    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f48,f36])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f50,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f29])).

fof(f51,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f29])).

fof(f52,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f29])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) )
      & ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) )
      & ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f26])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f41,f36])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f49,plain,(
    ! [X6,X7,X5] :
      ( sK3 = X6
      | k3_mcart_1(X5,X6,X7) != sK4
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f62,plain,(
    ! [X6,X7,X5] :
      ( sK3 = X6
      | k4_tarski(k4_tarski(X5,X6),X7) != sK4
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(definition_unfolding,[],[f49,f35])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
                & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
                & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
            & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f46,f36])).

fof(f53,plain,(
    k6_mcart_1(sK0,sK1,sK2,sK4) != sK3 ),
    inference(cnf_transformation,[],[f29])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_538,plain,
    ( m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_546,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2205,plain,
    ( r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_538,c_546])).

cnf(c_19,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_18,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_17,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_61,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_12,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k1_xboole_0
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_691,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),sK2) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_841,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,X0),sK2) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_691])).

cnf(c_1059,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_841])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_1110,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ v1_xboole_0(k1_xboole_0)
    | k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1111,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k1_xboole_0
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1110])).

cnf(c_2302,plain,
    ( r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2205,c_19,c_18,c_17,c_61,c_1059,c_1111])).

cnf(c_4,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_relat_1(X1)
    | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_176,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
    | k2_zfmisc_1(X2,X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_8])).

cnf(c_177,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_176])).

cnf(c_537,plain,
    ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
    | r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_177])).

cnf(c_2310,plain,
    ( k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) = sK4 ),
    inference(superposition,[status(thm)],[c_2302,c_537])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k1_mcart_1(X0),X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_543,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2309,plain,
    ( r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2302,c_543])).

cnf(c_2357,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) = k1_mcart_1(sK4) ),
    inference(superposition,[status(thm)],[c_2309,c_537])).

cnf(c_20,negated_conjecture,
    ( ~ m1_subset_1(X0,sK2)
    | ~ m1_subset_1(X1,sK1)
    | ~ m1_subset_1(X2,sK0)
    | k4_tarski(k4_tarski(X2,X1),X0) != sK4
    | sK3 = X1 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_539,plain,
    ( k4_tarski(k4_tarski(X0,X1),X2) != sK4
    | sK3 = X1
    | m1_subset_1(X2,sK2) != iProver_top
    | m1_subset_1(X1,sK1) != iProver_top
    | m1_subset_1(X0,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2843,plain,
    ( k4_tarski(k1_mcart_1(sK4),X0) != sK4
    | k2_mcart_1(k1_mcart_1(sK4)) = sK3
    | m1_subset_1(X0,sK2) != iProver_top
    | m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) != iProver_top
    | m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2357,c_539])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k6_mcart_1(X1,X2,X3,X0) = k2_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_541,plain,
    ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2385,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4))
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_538,c_541])).

cnf(c_721,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),sK2))
    | k6_mcart_1(X1,X2,sK2,X0) = k2_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_903,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,sK1),sK2))
    | k6_mcart_1(X1,sK1,sK2,X0) = k2_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_721])).

cnf(c_1424,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k6_mcart_1(sK0,sK1,sK2,X0) = k2_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_903])).

cnf(c_2376,plain,
    ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1424])).

cnf(c_2773,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2385,c_21,c_19,c_18,c_17,c_2376])).

cnf(c_16,negated_conjecture,
    ( k6_mcart_1(sK0,sK1,sK2,sK4) != sK3 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2776,plain,
    ( k2_mcart_1(k1_mcart_1(sK4)) != sK3 ),
    inference(demodulation,[status(thm)],[c_2773,c_16])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k2_mcart_1(X0),X2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_544,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k2_mcart_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2355,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK4)),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2309,c_544])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_547,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2786,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2355,c_547])).

cnf(c_2356,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2309,c_543])).

cnf(c_2797,plain,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2356,c_547])).

cnf(c_2848,plain,
    ( k4_tarski(k1_mcart_1(sK4),X0) != sK4
    | m1_subset_1(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2843,c_2776,c_2786,c_2797])).

cnf(c_2856,plain,
    ( m1_subset_1(k2_mcart_1(sK4),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2310,c_2848])).

cnf(c_2308,plain,
    ( r2_hidden(k2_mcart_1(sK4),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2302,c_544])).

cnf(c_2327,plain,
    ( m1_subset_1(k2_mcart_1(sK4),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2308,c_547])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2856,c_2327])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:42:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.80/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.80/1.01  
% 2.80/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.80/1.01  
% 2.80/1.01  ------  iProver source info
% 2.80/1.01  
% 2.80/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.80/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.80/1.01  git: non_committed_changes: false
% 2.80/1.01  git: last_make_outside_of_git: false
% 2.80/1.01  
% 2.80/1.01  ------ 
% 2.80/1.01  
% 2.80/1.01  ------ Input Options
% 2.80/1.01  
% 2.80/1.01  --out_options                           all
% 2.80/1.01  --tptp_safe_out                         true
% 2.80/1.01  --problem_path                          ""
% 2.80/1.01  --include_path                          ""
% 2.80/1.01  --clausifier                            res/vclausify_rel
% 2.80/1.01  --clausifier_options                    --mode clausify
% 2.80/1.01  --stdin                                 false
% 2.80/1.01  --stats_out                             all
% 2.80/1.01  
% 2.80/1.01  ------ General Options
% 2.80/1.01  
% 2.80/1.01  --fof                                   false
% 2.80/1.01  --time_out_real                         305.
% 2.80/1.01  --time_out_virtual                      -1.
% 2.80/1.01  --symbol_type_check                     false
% 2.80/1.01  --clausify_out                          false
% 2.80/1.01  --sig_cnt_out                           false
% 2.80/1.01  --trig_cnt_out                          false
% 2.80/1.01  --trig_cnt_out_tolerance                1.
% 2.80/1.01  --trig_cnt_out_sk_spl                   false
% 2.80/1.01  --abstr_cl_out                          false
% 2.80/1.01  
% 2.80/1.01  ------ Global Options
% 2.80/1.01  
% 2.80/1.01  --schedule                              default
% 2.80/1.01  --add_important_lit                     false
% 2.80/1.01  --prop_solver_per_cl                    1000
% 2.80/1.01  --min_unsat_core                        false
% 2.80/1.01  --soft_assumptions                      false
% 2.80/1.01  --soft_lemma_size                       3
% 2.80/1.01  --prop_impl_unit_size                   0
% 2.80/1.01  --prop_impl_unit                        []
% 2.80/1.01  --share_sel_clauses                     true
% 2.80/1.01  --reset_solvers                         false
% 2.80/1.01  --bc_imp_inh                            [conj_cone]
% 2.80/1.01  --conj_cone_tolerance                   3.
% 2.80/1.01  --extra_neg_conj                        none
% 2.80/1.01  --large_theory_mode                     true
% 2.80/1.01  --prolific_symb_bound                   200
% 2.80/1.01  --lt_threshold                          2000
% 2.80/1.01  --clause_weak_htbl                      true
% 2.80/1.01  --gc_record_bc_elim                     false
% 2.80/1.01  
% 2.80/1.01  ------ Preprocessing Options
% 2.80/1.01  
% 2.80/1.01  --preprocessing_flag                    true
% 2.80/1.01  --time_out_prep_mult                    0.1
% 2.80/1.01  --splitting_mode                        input
% 2.80/1.01  --splitting_grd                         true
% 2.80/1.01  --splitting_cvd                         false
% 2.80/1.01  --splitting_cvd_svl                     false
% 2.80/1.01  --splitting_nvd                         32
% 2.80/1.01  --sub_typing                            true
% 2.80/1.01  --prep_gs_sim                           true
% 2.80/1.01  --prep_unflatten                        true
% 2.80/1.01  --prep_res_sim                          true
% 2.80/1.01  --prep_upred                            true
% 2.80/1.01  --prep_sem_filter                       exhaustive
% 2.80/1.01  --prep_sem_filter_out                   false
% 2.80/1.01  --pred_elim                             true
% 2.80/1.01  --res_sim_input                         true
% 2.80/1.01  --eq_ax_congr_red                       true
% 2.80/1.01  --pure_diseq_elim                       true
% 2.80/1.01  --brand_transform                       false
% 2.80/1.01  --non_eq_to_eq                          false
% 2.80/1.01  --prep_def_merge                        true
% 2.80/1.01  --prep_def_merge_prop_impl              false
% 2.80/1.01  --prep_def_merge_mbd                    true
% 2.80/1.01  --prep_def_merge_tr_red                 false
% 2.80/1.01  --prep_def_merge_tr_cl                  false
% 2.80/1.01  --smt_preprocessing                     true
% 2.80/1.01  --smt_ac_axioms                         fast
% 2.80/1.01  --preprocessed_out                      false
% 2.80/1.01  --preprocessed_stats                    false
% 2.80/1.01  
% 2.80/1.01  ------ Abstraction refinement Options
% 2.80/1.01  
% 2.80/1.01  --abstr_ref                             []
% 2.80/1.01  --abstr_ref_prep                        false
% 2.80/1.01  --abstr_ref_until_sat                   false
% 2.80/1.01  --abstr_ref_sig_restrict                funpre
% 2.80/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.80/1.01  --abstr_ref_under                       []
% 2.80/1.01  
% 2.80/1.01  ------ SAT Options
% 2.80/1.01  
% 2.80/1.01  --sat_mode                              false
% 2.80/1.01  --sat_fm_restart_options                ""
% 2.80/1.01  --sat_gr_def                            false
% 2.80/1.01  --sat_epr_types                         true
% 2.80/1.01  --sat_non_cyclic_types                  false
% 2.80/1.01  --sat_finite_models                     false
% 2.80/1.01  --sat_fm_lemmas                         false
% 2.80/1.01  --sat_fm_prep                           false
% 2.80/1.01  --sat_fm_uc_incr                        true
% 2.80/1.01  --sat_out_model                         small
% 2.80/1.01  --sat_out_clauses                       false
% 2.80/1.01  
% 2.80/1.01  ------ QBF Options
% 2.80/1.01  
% 2.80/1.01  --qbf_mode                              false
% 2.80/1.01  --qbf_elim_univ                         false
% 2.80/1.01  --qbf_dom_inst                          none
% 2.80/1.01  --qbf_dom_pre_inst                      false
% 2.80/1.01  --qbf_sk_in                             false
% 2.80/1.01  --qbf_pred_elim                         true
% 2.80/1.01  --qbf_split                             512
% 2.80/1.01  
% 2.80/1.01  ------ BMC1 Options
% 2.80/1.01  
% 2.80/1.01  --bmc1_incremental                      false
% 2.80/1.01  --bmc1_axioms                           reachable_all
% 2.80/1.01  --bmc1_min_bound                        0
% 2.80/1.01  --bmc1_max_bound                        -1
% 2.80/1.01  --bmc1_max_bound_default                -1
% 2.80/1.01  --bmc1_symbol_reachability              true
% 2.80/1.01  --bmc1_property_lemmas                  false
% 2.80/1.01  --bmc1_k_induction                      false
% 2.80/1.01  --bmc1_non_equiv_states                 false
% 2.80/1.01  --bmc1_deadlock                         false
% 2.80/1.01  --bmc1_ucm                              false
% 2.80/1.01  --bmc1_add_unsat_core                   none
% 2.80/1.01  --bmc1_unsat_core_children              false
% 2.80/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.80/1.01  --bmc1_out_stat                         full
% 2.80/1.01  --bmc1_ground_init                      false
% 2.80/1.01  --bmc1_pre_inst_next_state              false
% 2.80/1.01  --bmc1_pre_inst_state                   false
% 2.80/1.01  --bmc1_pre_inst_reach_state             false
% 2.80/1.01  --bmc1_out_unsat_core                   false
% 2.80/1.01  --bmc1_aig_witness_out                  false
% 2.80/1.01  --bmc1_verbose                          false
% 2.80/1.01  --bmc1_dump_clauses_tptp                false
% 2.80/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.80/1.01  --bmc1_dump_file                        -
% 2.80/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.80/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.80/1.01  --bmc1_ucm_extend_mode                  1
% 2.80/1.01  --bmc1_ucm_init_mode                    2
% 2.80/1.01  --bmc1_ucm_cone_mode                    none
% 2.80/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.80/1.01  --bmc1_ucm_relax_model                  4
% 2.80/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.80/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.80/1.01  --bmc1_ucm_layered_model                none
% 2.80/1.01  --bmc1_ucm_max_lemma_size               10
% 2.80/1.01  
% 2.80/1.01  ------ AIG Options
% 2.80/1.01  
% 2.80/1.01  --aig_mode                              false
% 2.80/1.01  
% 2.80/1.01  ------ Instantiation Options
% 2.80/1.01  
% 2.80/1.01  --instantiation_flag                    true
% 2.80/1.01  --inst_sos_flag                         false
% 2.80/1.01  --inst_sos_phase                        true
% 2.80/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.80/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.80/1.01  --inst_lit_sel_side                     num_symb
% 2.80/1.01  --inst_solver_per_active                1400
% 2.80/1.01  --inst_solver_calls_frac                1.
% 2.80/1.01  --inst_passive_queue_type               priority_queues
% 2.80/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.80/1.01  --inst_passive_queues_freq              [25;2]
% 2.80/1.01  --inst_dismatching                      true
% 2.80/1.01  --inst_eager_unprocessed_to_passive     true
% 2.80/1.01  --inst_prop_sim_given                   true
% 2.80/1.01  --inst_prop_sim_new                     false
% 2.80/1.01  --inst_subs_new                         false
% 2.80/1.01  --inst_eq_res_simp                      false
% 2.80/1.01  --inst_subs_given                       false
% 2.80/1.01  --inst_orphan_elimination               true
% 2.80/1.01  --inst_learning_loop_flag               true
% 2.80/1.01  --inst_learning_start                   3000
% 2.80/1.01  --inst_learning_factor                  2
% 2.80/1.01  --inst_start_prop_sim_after_learn       3
% 2.80/1.01  --inst_sel_renew                        solver
% 2.80/1.01  --inst_lit_activity_flag                true
% 2.80/1.01  --inst_restr_to_given                   false
% 2.80/1.01  --inst_activity_threshold               500
% 2.80/1.01  --inst_out_proof                        true
% 2.80/1.01  
% 2.80/1.01  ------ Resolution Options
% 2.80/1.01  
% 2.80/1.01  --resolution_flag                       true
% 2.80/1.01  --res_lit_sel                           adaptive
% 2.80/1.01  --res_lit_sel_side                      none
% 2.80/1.01  --res_ordering                          kbo
% 2.80/1.01  --res_to_prop_solver                    active
% 2.80/1.01  --res_prop_simpl_new                    false
% 2.80/1.01  --res_prop_simpl_given                  true
% 2.80/1.01  --res_passive_queue_type                priority_queues
% 2.80/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.80/1.01  --res_passive_queues_freq               [15;5]
% 2.80/1.01  --res_forward_subs                      full
% 2.80/1.01  --res_backward_subs                     full
% 2.80/1.01  --res_forward_subs_resolution           true
% 2.80/1.01  --res_backward_subs_resolution          true
% 2.80/1.01  --res_orphan_elimination                true
% 2.80/1.01  --res_time_limit                        2.
% 2.80/1.01  --res_out_proof                         true
% 2.80/1.01  
% 2.80/1.01  ------ Superposition Options
% 2.80/1.01  
% 2.80/1.01  --superposition_flag                    true
% 2.80/1.01  --sup_passive_queue_type                priority_queues
% 2.80/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.80/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.80/1.01  --demod_completeness_check              fast
% 2.80/1.01  --demod_use_ground                      true
% 2.80/1.01  --sup_to_prop_solver                    passive
% 2.80/1.01  --sup_prop_simpl_new                    true
% 2.80/1.01  --sup_prop_simpl_given                  true
% 2.80/1.01  --sup_fun_splitting                     false
% 2.80/1.01  --sup_smt_interval                      50000
% 2.80/1.01  
% 2.80/1.01  ------ Superposition Simplification Setup
% 2.80/1.01  
% 2.80/1.01  --sup_indices_passive                   []
% 2.80/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.80/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.80/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.80/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.80/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.80/1.01  --sup_full_bw                           [BwDemod]
% 2.80/1.01  --sup_immed_triv                        [TrivRules]
% 2.80/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.80/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.80/1.01  --sup_immed_bw_main                     []
% 2.80/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.80/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.80/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.80/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.80/1.01  
% 2.80/1.01  ------ Combination Options
% 2.80/1.01  
% 2.80/1.01  --comb_res_mult                         3
% 2.80/1.01  --comb_sup_mult                         2
% 2.80/1.01  --comb_inst_mult                        10
% 2.80/1.01  
% 2.80/1.01  ------ Debug Options
% 2.80/1.01  
% 2.80/1.01  --dbg_backtrace                         false
% 2.80/1.01  --dbg_dump_prop_clauses                 false
% 2.80/1.01  --dbg_dump_prop_clauses_file            -
% 2.80/1.01  --dbg_out_stat                          false
% 2.80/1.01  ------ Parsing...
% 2.80/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.80/1.01  
% 2.80/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.80/1.01  
% 2.80/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.80/1.01  
% 2.80/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.80/1.01  ------ Proving...
% 2.80/1.01  ------ Problem Properties 
% 2.80/1.01  
% 2.80/1.01  
% 2.80/1.01  clauses                                 21
% 2.80/1.01  conjectures                             6
% 2.80/1.01  EPR                                     7
% 2.80/1.01  Horn                                    16
% 2.80/1.01  unary                                   9
% 2.80/1.01  binary                                  5
% 2.80/1.01  lits                                    49
% 2.80/1.01  lits eq                                 27
% 2.80/1.01  fd_pure                                 0
% 2.80/1.01  fd_pseudo                               0
% 2.80/1.01  fd_cond                                 5
% 2.80/1.01  fd_pseudo_cond                          1
% 2.80/1.01  AC symbols                              0
% 2.80/1.01  
% 2.80/1.01  ------ Schedule dynamic 5 is on 
% 2.80/1.01  
% 2.80/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.80/1.01  
% 2.80/1.01  
% 2.80/1.01  ------ 
% 2.80/1.01  Current options:
% 2.80/1.01  ------ 
% 2.80/1.01  
% 2.80/1.01  ------ Input Options
% 2.80/1.01  
% 2.80/1.01  --out_options                           all
% 2.80/1.01  --tptp_safe_out                         true
% 2.80/1.01  --problem_path                          ""
% 2.80/1.01  --include_path                          ""
% 2.80/1.01  --clausifier                            res/vclausify_rel
% 2.80/1.01  --clausifier_options                    --mode clausify
% 2.80/1.01  --stdin                                 false
% 2.80/1.01  --stats_out                             all
% 2.80/1.01  
% 2.80/1.01  ------ General Options
% 2.80/1.01  
% 2.80/1.01  --fof                                   false
% 2.80/1.01  --time_out_real                         305.
% 2.80/1.01  --time_out_virtual                      -1.
% 2.80/1.01  --symbol_type_check                     false
% 2.80/1.01  --clausify_out                          false
% 2.80/1.01  --sig_cnt_out                           false
% 2.80/1.01  --trig_cnt_out                          false
% 2.80/1.01  --trig_cnt_out_tolerance                1.
% 2.80/1.01  --trig_cnt_out_sk_spl                   false
% 2.80/1.01  --abstr_cl_out                          false
% 2.80/1.01  
% 2.80/1.01  ------ Global Options
% 2.80/1.01  
% 2.80/1.01  --schedule                              default
% 2.80/1.01  --add_important_lit                     false
% 2.80/1.01  --prop_solver_per_cl                    1000
% 2.80/1.01  --min_unsat_core                        false
% 2.80/1.01  --soft_assumptions                      false
% 2.80/1.01  --soft_lemma_size                       3
% 2.80/1.01  --prop_impl_unit_size                   0
% 2.80/1.01  --prop_impl_unit                        []
% 2.80/1.01  --share_sel_clauses                     true
% 2.80/1.01  --reset_solvers                         false
% 2.80/1.01  --bc_imp_inh                            [conj_cone]
% 2.80/1.01  --conj_cone_tolerance                   3.
% 2.80/1.01  --extra_neg_conj                        none
% 2.80/1.01  --large_theory_mode                     true
% 2.80/1.01  --prolific_symb_bound                   200
% 2.80/1.01  --lt_threshold                          2000
% 2.80/1.01  --clause_weak_htbl                      true
% 2.80/1.01  --gc_record_bc_elim                     false
% 2.80/1.01  
% 2.80/1.01  ------ Preprocessing Options
% 2.80/1.01  
% 2.80/1.01  --preprocessing_flag                    true
% 2.80/1.01  --time_out_prep_mult                    0.1
% 2.80/1.01  --splitting_mode                        input
% 2.80/1.01  --splitting_grd                         true
% 2.80/1.01  --splitting_cvd                         false
% 2.80/1.01  --splitting_cvd_svl                     false
% 2.80/1.01  --splitting_nvd                         32
% 2.80/1.01  --sub_typing                            true
% 2.80/1.01  --prep_gs_sim                           true
% 2.80/1.01  --prep_unflatten                        true
% 2.80/1.01  --prep_res_sim                          true
% 2.80/1.01  --prep_upred                            true
% 2.80/1.01  --prep_sem_filter                       exhaustive
% 2.80/1.01  --prep_sem_filter_out                   false
% 2.80/1.01  --pred_elim                             true
% 2.80/1.01  --res_sim_input                         true
% 2.80/1.01  --eq_ax_congr_red                       true
% 2.80/1.01  --pure_diseq_elim                       true
% 2.80/1.01  --brand_transform                       false
% 2.80/1.01  --non_eq_to_eq                          false
% 2.80/1.01  --prep_def_merge                        true
% 2.80/1.01  --prep_def_merge_prop_impl              false
% 2.80/1.01  --prep_def_merge_mbd                    true
% 2.80/1.01  --prep_def_merge_tr_red                 false
% 2.80/1.01  --prep_def_merge_tr_cl                  false
% 2.80/1.01  --smt_preprocessing                     true
% 2.80/1.01  --smt_ac_axioms                         fast
% 2.80/1.01  --preprocessed_out                      false
% 2.80/1.01  --preprocessed_stats                    false
% 2.80/1.01  
% 2.80/1.01  ------ Abstraction refinement Options
% 2.80/1.01  
% 2.80/1.01  --abstr_ref                             []
% 2.80/1.01  --abstr_ref_prep                        false
% 2.80/1.01  --abstr_ref_until_sat                   false
% 2.80/1.01  --abstr_ref_sig_restrict                funpre
% 2.80/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.80/1.01  --abstr_ref_under                       []
% 2.80/1.01  
% 2.80/1.01  ------ SAT Options
% 2.80/1.01  
% 2.80/1.01  --sat_mode                              false
% 2.80/1.01  --sat_fm_restart_options                ""
% 2.80/1.01  --sat_gr_def                            false
% 2.80/1.01  --sat_epr_types                         true
% 2.80/1.01  --sat_non_cyclic_types                  false
% 2.80/1.01  --sat_finite_models                     false
% 2.80/1.01  --sat_fm_lemmas                         false
% 2.80/1.01  --sat_fm_prep                           false
% 2.80/1.01  --sat_fm_uc_incr                        true
% 2.80/1.01  --sat_out_model                         small
% 2.80/1.01  --sat_out_clauses                       false
% 2.80/1.01  
% 2.80/1.01  ------ QBF Options
% 2.80/1.01  
% 2.80/1.01  --qbf_mode                              false
% 2.80/1.01  --qbf_elim_univ                         false
% 2.80/1.01  --qbf_dom_inst                          none
% 2.80/1.01  --qbf_dom_pre_inst                      false
% 2.80/1.01  --qbf_sk_in                             false
% 2.80/1.01  --qbf_pred_elim                         true
% 2.80/1.01  --qbf_split                             512
% 2.80/1.01  
% 2.80/1.01  ------ BMC1 Options
% 2.80/1.01  
% 2.80/1.01  --bmc1_incremental                      false
% 2.80/1.01  --bmc1_axioms                           reachable_all
% 2.80/1.01  --bmc1_min_bound                        0
% 2.80/1.01  --bmc1_max_bound                        -1
% 2.80/1.01  --bmc1_max_bound_default                -1
% 2.80/1.01  --bmc1_symbol_reachability              true
% 2.80/1.01  --bmc1_property_lemmas                  false
% 2.80/1.01  --bmc1_k_induction                      false
% 2.80/1.01  --bmc1_non_equiv_states                 false
% 2.80/1.01  --bmc1_deadlock                         false
% 2.80/1.01  --bmc1_ucm                              false
% 2.80/1.01  --bmc1_add_unsat_core                   none
% 2.80/1.01  --bmc1_unsat_core_children              false
% 2.80/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.80/1.01  --bmc1_out_stat                         full
% 2.80/1.01  --bmc1_ground_init                      false
% 2.80/1.01  --bmc1_pre_inst_next_state              false
% 2.80/1.01  --bmc1_pre_inst_state                   false
% 2.80/1.01  --bmc1_pre_inst_reach_state             false
% 2.80/1.01  --bmc1_out_unsat_core                   false
% 2.80/1.01  --bmc1_aig_witness_out                  false
% 2.80/1.01  --bmc1_verbose                          false
% 2.80/1.01  --bmc1_dump_clauses_tptp                false
% 2.80/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.80/1.01  --bmc1_dump_file                        -
% 2.80/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.80/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.80/1.01  --bmc1_ucm_extend_mode                  1
% 2.80/1.01  --bmc1_ucm_init_mode                    2
% 2.80/1.01  --bmc1_ucm_cone_mode                    none
% 2.80/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.80/1.01  --bmc1_ucm_relax_model                  4
% 2.80/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.80/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.80/1.01  --bmc1_ucm_layered_model                none
% 2.80/1.01  --bmc1_ucm_max_lemma_size               10
% 2.80/1.01  
% 2.80/1.01  ------ AIG Options
% 2.80/1.01  
% 2.80/1.01  --aig_mode                              false
% 2.80/1.01  
% 2.80/1.01  ------ Instantiation Options
% 2.80/1.01  
% 2.80/1.01  --instantiation_flag                    true
% 2.80/1.01  --inst_sos_flag                         false
% 2.80/1.01  --inst_sos_phase                        true
% 2.80/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.80/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.80/1.01  --inst_lit_sel_side                     none
% 2.80/1.01  --inst_solver_per_active                1400
% 2.80/1.01  --inst_solver_calls_frac                1.
% 2.80/1.01  --inst_passive_queue_type               priority_queues
% 2.80/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.80/1.01  --inst_passive_queues_freq              [25;2]
% 2.80/1.01  --inst_dismatching                      true
% 2.80/1.01  --inst_eager_unprocessed_to_passive     true
% 2.80/1.01  --inst_prop_sim_given                   true
% 2.80/1.01  --inst_prop_sim_new                     false
% 2.80/1.01  --inst_subs_new                         false
% 2.80/1.01  --inst_eq_res_simp                      false
% 2.80/1.01  --inst_subs_given                       false
% 2.80/1.01  --inst_orphan_elimination               true
% 2.80/1.01  --inst_learning_loop_flag               true
% 2.80/1.01  --inst_learning_start                   3000
% 2.80/1.01  --inst_learning_factor                  2
% 2.80/1.01  --inst_start_prop_sim_after_learn       3
% 2.80/1.01  --inst_sel_renew                        solver
% 2.80/1.01  --inst_lit_activity_flag                true
% 2.80/1.01  --inst_restr_to_given                   false
% 2.80/1.01  --inst_activity_threshold               500
% 2.80/1.01  --inst_out_proof                        true
% 2.80/1.01  
% 2.80/1.01  ------ Resolution Options
% 2.80/1.01  
% 2.80/1.01  --resolution_flag                       false
% 2.80/1.01  --res_lit_sel                           adaptive
% 2.80/1.01  --res_lit_sel_side                      none
% 2.80/1.01  --res_ordering                          kbo
% 2.80/1.01  --res_to_prop_solver                    active
% 2.80/1.01  --res_prop_simpl_new                    false
% 2.80/1.01  --res_prop_simpl_given                  true
% 2.80/1.01  --res_passive_queue_type                priority_queues
% 2.80/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.80/1.01  --res_passive_queues_freq               [15;5]
% 2.80/1.01  --res_forward_subs                      full
% 2.80/1.01  --res_backward_subs                     full
% 2.80/1.01  --res_forward_subs_resolution           true
% 2.80/1.01  --res_backward_subs_resolution          true
% 2.80/1.01  --res_orphan_elimination                true
% 2.80/1.01  --res_time_limit                        2.
% 2.80/1.01  --res_out_proof                         true
% 2.80/1.01  
% 2.80/1.01  ------ Superposition Options
% 2.80/1.01  
% 2.80/1.01  --superposition_flag                    true
% 2.80/1.01  --sup_passive_queue_type                priority_queues
% 2.80/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.80/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.80/1.01  --demod_completeness_check              fast
% 2.80/1.01  --demod_use_ground                      true
% 2.80/1.01  --sup_to_prop_solver                    passive
% 2.80/1.01  --sup_prop_simpl_new                    true
% 2.80/1.01  --sup_prop_simpl_given                  true
% 2.80/1.01  --sup_fun_splitting                     false
% 2.80/1.01  --sup_smt_interval                      50000
% 2.80/1.01  
% 2.80/1.01  ------ Superposition Simplification Setup
% 2.80/1.01  
% 2.80/1.01  --sup_indices_passive                   []
% 2.80/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.80/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.80/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.80/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.80/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.80/1.01  --sup_full_bw                           [BwDemod]
% 2.80/1.01  --sup_immed_triv                        [TrivRules]
% 2.80/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.80/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.80/1.01  --sup_immed_bw_main                     []
% 2.80/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.80/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.80/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.80/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.80/1.01  
% 2.80/1.01  ------ Combination Options
% 2.80/1.01  
% 2.80/1.01  --comb_res_mult                         3
% 2.80/1.01  --comb_sup_mult                         2
% 2.80/1.01  --comb_inst_mult                        10
% 2.80/1.01  
% 2.80/1.01  ------ Debug Options
% 2.80/1.01  
% 2.80/1.01  --dbg_backtrace                         false
% 2.80/1.01  --dbg_dump_prop_clauses                 false
% 2.80/1.01  --dbg_dump_prop_clauses_file            -
% 2.80/1.01  --dbg_out_stat                          false
% 2.80/1.01  
% 2.80/1.01  
% 2.80/1.01  
% 2.80/1.01  
% 2.80/1.01  ------ Proving...
% 2.80/1.01  
% 2.80/1.01  
% 2.80/1.01  % SZS status Theorem for theBenchmark.p
% 2.80/1.01  
% 2.80/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.80/1.01  
% 2.80/1.01  fof(f13,conjecture,(
% 2.80/1.01    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X6)))) => (k6_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 2.80/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/1.02  
% 2.80/1.02  fof(f14,negated_conjecture,(
% 2.80/1.02    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X6)))) => (k6_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 2.80/1.02    inference(negated_conjecture,[],[f13])).
% 2.80/1.02  
% 2.80/1.02  fof(f24,plain,(
% 2.80/1.02    ? [X0,X1,X2,X3,X4] : (((k6_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X6 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 2.80/1.02    inference(ennf_transformation,[],[f14])).
% 2.80/1.02  
% 2.80/1.02  fof(f25,plain,(
% 2.80/1.02    ? [X0,X1,X2,X3,X4] : (k6_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X6 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 2.80/1.02    inference(flattening,[],[f24])).
% 2.80/1.02  
% 2.80/1.02  fof(f28,plain,(
% 2.80/1.02    ? [X0,X1,X2,X3,X4] : (k6_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X6 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) => (k6_mcart_1(sK0,sK1,sK2,sK4) != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5] : (! [X6] : (! [X7] : (sK3 = X6 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2)) | ~m1_subset_1(X6,sK1)) | ~m1_subset_1(X5,sK0)) & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)))),
% 2.80/1.02    introduced(choice_axiom,[])).
% 2.80/1.02  
% 2.80/1.02  fof(f29,plain,(
% 2.80/1.02    k6_mcart_1(sK0,sK1,sK2,sK4) != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5] : (! [X6] : (! [X7] : (sK3 = X6 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2)) | ~m1_subset_1(X6,sK1)) | ~m1_subset_1(X5,sK0)) & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 2.80/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f25,f28])).
% 2.80/1.02  
% 2.80/1.02  fof(f48,plain,(
% 2.80/1.02    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 2.80/1.02    inference(cnf_transformation,[],[f29])).
% 2.80/1.02  
% 2.80/1.02  fof(f7,axiom,(
% 2.80/1.02    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)),
% 2.80/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/1.02  
% 2.80/1.02  fof(f36,plain,(
% 2.80/1.02    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)) )),
% 2.80/1.02    inference(cnf_transformation,[],[f7])).
% 2.80/1.02  
% 2.80/1.02  fof(f63,plain,(
% 2.80/1.02    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 2.80/1.02    inference(definition_unfolding,[],[f48,f36])).
% 2.80/1.02  
% 2.80/1.02  fof(f4,axiom,(
% 2.80/1.02    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.80/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/1.02  
% 2.80/1.02  fof(f17,plain,(
% 2.80/1.02    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.80/1.02    inference(ennf_transformation,[],[f4])).
% 2.80/1.02  
% 2.80/1.02  fof(f18,plain,(
% 2.80/1.02    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.80/1.02    inference(flattening,[],[f17])).
% 2.80/1.02  
% 2.80/1.02  fof(f33,plain,(
% 2.80/1.02    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.80/1.02    inference(cnf_transformation,[],[f18])).
% 2.80/1.02  
% 2.80/1.02  fof(f50,plain,(
% 2.80/1.02    k1_xboole_0 != sK0),
% 2.80/1.02    inference(cnf_transformation,[],[f29])).
% 2.80/1.02  
% 2.80/1.02  fof(f51,plain,(
% 2.80/1.02    k1_xboole_0 != sK1),
% 2.80/1.02    inference(cnf_transformation,[],[f29])).
% 2.80/1.02  
% 2.80/1.02  fof(f52,plain,(
% 2.80/1.02    k1_xboole_0 != sK2),
% 2.80/1.02    inference(cnf_transformation,[],[f29])).
% 2.80/1.02  
% 2.80/1.02  fof(f1,axiom,(
% 2.80/1.02    v1_xboole_0(k1_xboole_0)),
% 2.80/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/1.02  
% 2.80/1.02  fof(f30,plain,(
% 2.80/1.02    v1_xboole_0(k1_xboole_0)),
% 2.80/1.02    inference(cnf_transformation,[],[f1])).
% 2.80/1.02  
% 2.80/1.02  fof(f11,axiom,(
% 2.80/1.02    ! [X0,X1,X2] : ((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2))),
% 2.80/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/1.02  
% 2.80/1.02  fof(f26,plain,(
% 2.80/1.02    ! [X0,X1,X2] : (((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) & (k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) | (k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 2.80/1.02    inference(nnf_transformation,[],[f11])).
% 2.80/1.02  
% 2.80/1.02  fof(f27,plain,(
% 2.80/1.02    ! [X0,X1,X2] : (((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) & (k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.80/1.02    inference(flattening,[],[f26])).
% 2.80/1.02  
% 2.80/1.02  fof(f41,plain,(
% 2.80/1.02    ( ! [X2,X0,X1] : (k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.80/1.02    inference(cnf_transformation,[],[f27])).
% 2.80/1.02  
% 2.80/1.02  fof(f58,plain,(
% 2.80/1.02    ( ! [X2,X0,X1] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.80/1.02    inference(definition_unfolding,[],[f41,f36])).
% 2.80/1.02  
% 2.80/1.02  fof(f2,axiom,(
% 2.80/1.02    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 2.80/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/1.02  
% 2.80/1.02  fof(f15,plain,(
% 2.80/1.02    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 2.80/1.02    inference(ennf_transformation,[],[f2])).
% 2.80/1.02  
% 2.80/1.02  fof(f31,plain,(
% 2.80/1.02    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 2.80/1.02    inference(cnf_transformation,[],[f15])).
% 2.80/1.02  
% 2.80/1.02  fof(f5,axiom,(
% 2.80/1.02    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.80/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/1.02  
% 2.80/1.02  fof(f34,plain,(
% 2.80/1.02    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.80/1.02    inference(cnf_transformation,[],[f5])).
% 2.80/1.02  
% 2.80/1.02  fof(f10,axiom,(
% 2.80/1.02    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,X1) => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0))),
% 2.80/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/1.02  
% 2.80/1.02  fof(f21,plain,(
% 2.80/1.02    ! [X0,X1] : ((k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1)) | ~v1_relat_1(X1))),
% 2.80/1.02    inference(ennf_transformation,[],[f10])).
% 2.80/1.02  
% 2.80/1.02  fof(f22,plain,(
% 2.80/1.02    ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1))),
% 2.80/1.02    inference(flattening,[],[f21])).
% 2.80/1.02  
% 2.80/1.02  fof(f40,plain,(
% 2.80/1.02    ( ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1)) )),
% 2.80/1.02    inference(cnf_transformation,[],[f22])).
% 2.80/1.02  
% 2.80/1.02  fof(f9,axiom,(
% 2.80/1.02    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 2.80/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/1.02  
% 2.80/1.02  fof(f20,plain,(
% 2.80/1.02    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 2.80/1.02    inference(ennf_transformation,[],[f9])).
% 2.80/1.02  
% 2.80/1.02  fof(f38,plain,(
% 2.80/1.02    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 2.80/1.02    inference(cnf_transformation,[],[f20])).
% 2.80/1.02  
% 2.80/1.02  fof(f49,plain,(
% 2.80/1.02    ( ! [X6,X7,X5] : (sK3 = X6 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X5,sK0)) )),
% 2.80/1.02    inference(cnf_transformation,[],[f29])).
% 2.80/1.02  
% 2.80/1.02  fof(f6,axiom,(
% 2.80/1.02    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 2.80/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/1.02  
% 2.80/1.02  fof(f35,plain,(
% 2.80/1.02    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 2.80/1.02    inference(cnf_transformation,[],[f6])).
% 2.80/1.02  
% 2.80/1.02  fof(f62,plain,(
% 2.80/1.02    ( ! [X6,X7,X5] : (sK3 = X6 | k4_tarski(k4_tarski(X5,X6),X7) != sK4 | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X5,sK0)) )),
% 2.80/1.02    inference(definition_unfolding,[],[f49,f35])).
% 2.80/1.02  
% 2.80/1.02  fof(f12,axiom,(
% 2.80/1.02    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.80/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/1.02  
% 2.80/1.02  fof(f23,plain,(
% 2.80/1.02    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.80/1.02    inference(ennf_transformation,[],[f12])).
% 2.80/1.02  
% 2.80/1.02  fof(f46,plain,(
% 2.80/1.02    ( ! [X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.80/1.02    inference(cnf_transformation,[],[f23])).
% 2.80/1.02  
% 2.80/1.02  fof(f60,plain,(
% 2.80/1.02    ( ! [X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.80/1.02    inference(definition_unfolding,[],[f46,f36])).
% 2.80/1.02  
% 2.80/1.02  fof(f53,plain,(
% 2.80/1.02    k6_mcart_1(sK0,sK1,sK2,sK4) != sK3),
% 2.80/1.02    inference(cnf_transformation,[],[f29])).
% 2.80/1.02  
% 2.80/1.02  fof(f39,plain,(
% 2.80/1.02    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 2.80/1.02    inference(cnf_transformation,[],[f20])).
% 2.80/1.02  
% 2.80/1.02  fof(f3,axiom,(
% 2.80/1.02    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 2.80/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/1.02  
% 2.80/1.02  fof(f16,plain,(
% 2.80/1.02    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 2.80/1.02    inference(ennf_transformation,[],[f3])).
% 2.80/1.02  
% 2.80/1.02  fof(f32,plain,(
% 2.80/1.02    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 2.80/1.02    inference(cnf_transformation,[],[f16])).
% 2.80/1.02  
% 2.80/1.02  cnf(c_21,negated_conjecture,
% 2.80/1.02      ( m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
% 2.80/1.02      inference(cnf_transformation,[],[f63]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_538,plain,
% 2.80/1.02      ( m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) = iProver_top ),
% 2.80/1.02      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_3,plain,
% 2.80/1.02      ( r2_hidden(X0,X1) | ~ m1_subset_1(X0,X1) | v1_xboole_0(X1) ),
% 2.80/1.02      inference(cnf_transformation,[],[f33]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_546,plain,
% 2.80/1.02      ( r2_hidden(X0,X1) = iProver_top
% 2.80/1.02      | m1_subset_1(X0,X1) != iProver_top
% 2.80/1.02      | v1_xboole_0(X1) = iProver_top ),
% 2.80/1.02      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_2205,plain,
% 2.80/1.02      ( r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) = iProver_top
% 2.80/1.02      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) = iProver_top ),
% 2.80/1.02      inference(superposition,[status(thm)],[c_538,c_546]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_19,negated_conjecture,
% 2.80/1.02      ( k1_xboole_0 != sK0 ),
% 2.80/1.02      inference(cnf_transformation,[],[f50]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_18,negated_conjecture,
% 2.80/1.02      ( k1_xboole_0 != sK1 ),
% 2.80/1.02      inference(cnf_transformation,[],[f51]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_17,negated_conjecture,
% 2.80/1.02      ( k1_xboole_0 != sK2 ),
% 2.80/1.02      inference(cnf_transformation,[],[f52]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_0,plain,
% 2.80/1.02      ( v1_xboole_0(k1_xboole_0) ),
% 2.80/1.02      inference(cnf_transformation,[],[f30]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_61,plain,
% 2.80/1.02      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.80/1.02      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_12,plain,
% 2.80/1.02      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k1_xboole_0
% 2.80/1.02      | k1_xboole_0 = X2
% 2.80/1.02      | k1_xboole_0 = X1
% 2.80/1.02      | k1_xboole_0 = X0 ),
% 2.80/1.02      inference(cnf_transformation,[],[f58]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_691,plain,
% 2.80/1.02      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),sK2) != k1_xboole_0
% 2.80/1.02      | k1_xboole_0 = X0
% 2.80/1.02      | k1_xboole_0 = X1
% 2.80/1.02      | k1_xboole_0 = sK2 ),
% 2.80/1.02      inference(instantiation,[status(thm)],[c_12]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_841,plain,
% 2.80/1.02      ( k2_zfmisc_1(k2_zfmisc_1(sK0,X0),sK2) != k1_xboole_0
% 2.80/1.02      | k1_xboole_0 = X0
% 2.80/1.02      | k1_xboole_0 = sK2
% 2.80/1.02      | k1_xboole_0 = sK0 ),
% 2.80/1.02      inference(instantiation,[status(thm)],[c_691]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_1059,plain,
% 2.80/1.02      ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) != k1_xboole_0
% 2.80/1.02      | k1_xboole_0 = sK2
% 2.80/1.02      | k1_xboole_0 = sK1
% 2.80/1.02      | k1_xboole_0 = sK0 ),
% 2.80/1.02      inference(instantiation,[status(thm)],[c_841]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_1,plain,
% 2.80/1.02      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X1 = X0 ),
% 2.80/1.02      inference(cnf_transformation,[],[f31]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_1110,plain,
% 2.80/1.02      ( ~ v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
% 2.80/1.02      | ~ v1_xboole_0(k1_xboole_0)
% 2.80/1.02      | k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k1_xboole_0 ),
% 2.80/1.02      inference(instantiation,[status(thm)],[c_1]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_1111,plain,
% 2.80/1.02      ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k1_xboole_0
% 2.80/1.02      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) != iProver_top
% 2.80/1.02      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.80/1.02      inference(predicate_to_equality,[status(thm)],[c_1110]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_2302,plain,
% 2.80/1.02      ( r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) = iProver_top ),
% 2.80/1.02      inference(global_propositional_subsumption,
% 2.80/1.02                [status(thm)],
% 2.80/1.02                [c_2205,c_19,c_18,c_17,c_61,c_1059,c_1111]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_4,plain,
% 2.80/1.02      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.80/1.02      inference(cnf_transformation,[],[f34]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_8,plain,
% 2.80/1.02      ( ~ r2_hidden(X0,X1)
% 2.80/1.02      | ~ v1_relat_1(X1)
% 2.80/1.02      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ),
% 2.80/1.02      inference(cnf_transformation,[],[f40]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_176,plain,
% 2.80/1.02      ( ~ r2_hidden(X0,X1)
% 2.80/1.02      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
% 2.80/1.02      | k2_zfmisc_1(X2,X3) != X1 ),
% 2.80/1.02      inference(resolution_lifted,[status(thm)],[c_4,c_8]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_177,plain,
% 2.80/1.02      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 2.80/1.02      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ),
% 2.80/1.02      inference(unflattening,[status(thm)],[c_176]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_537,plain,
% 2.80/1.02      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
% 2.80/1.02      | r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
% 2.80/1.02      inference(predicate_to_equality,[status(thm)],[c_177]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_2310,plain,
% 2.80/1.02      ( k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) = sK4 ),
% 2.80/1.02      inference(superposition,[status(thm)],[c_2302,c_537]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_7,plain,
% 2.80/1.02      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 2.80/1.02      | r2_hidden(k1_mcart_1(X0),X1) ),
% 2.80/1.02      inference(cnf_transformation,[],[f38]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_543,plain,
% 2.80/1.02      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 2.80/1.02      | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
% 2.80/1.02      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_2309,plain,
% 2.80/1.02      ( r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 2.80/1.02      inference(superposition,[status(thm)],[c_2302,c_543]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_2357,plain,
% 2.80/1.02      ( k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) = k1_mcart_1(sK4) ),
% 2.80/1.02      inference(superposition,[status(thm)],[c_2309,c_537]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_20,negated_conjecture,
% 2.80/1.02      ( ~ m1_subset_1(X0,sK2)
% 2.80/1.02      | ~ m1_subset_1(X1,sK1)
% 2.80/1.02      | ~ m1_subset_1(X2,sK0)
% 2.80/1.02      | k4_tarski(k4_tarski(X2,X1),X0) != sK4
% 2.80/1.02      | sK3 = X1 ),
% 2.80/1.02      inference(cnf_transformation,[],[f62]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_539,plain,
% 2.80/1.02      ( k4_tarski(k4_tarski(X0,X1),X2) != sK4
% 2.80/1.02      | sK3 = X1
% 2.80/1.02      | m1_subset_1(X2,sK2) != iProver_top
% 2.80/1.02      | m1_subset_1(X1,sK1) != iProver_top
% 2.80/1.02      | m1_subset_1(X0,sK0) != iProver_top ),
% 2.80/1.02      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_2843,plain,
% 2.80/1.02      ( k4_tarski(k1_mcart_1(sK4),X0) != sK4
% 2.80/1.02      | k2_mcart_1(k1_mcart_1(sK4)) = sK3
% 2.80/1.02      | m1_subset_1(X0,sK2) != iProver_top
% 2.80/1.02      | m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) != iProver_top
% 2.80/1.02      | m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) != iProver_top ),
% 2.80/1.02      inference(superposition,[status(thm)],[c_2357,c_539]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_14,plain,
% 2.80/1.02      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 2.80/1.02      | k6_mcart_1(X1,X2,X3,X0) = k2_mcart_1(k1_mcart_1(X0))
% 2.80/1.02      | k1_xboole_0 = X3
% 2.80/1.02      | k1_xboole_0 = X2
% 2.80/1.02      | k1_xboole_0 = X1 ),
% 2.80/1.02      inference(cnf_transformation,[],[f60]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_541,plain,
% 2.80/1.02      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
% 2.80/1.02      | k1_xboole_0 = X1
% 2.80/1.02      | k1_xboole_0 = X0
% 2.80/1.02      | k1_xboole_0 = X2
% 2.80/1.02      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 2.80/1.02      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_2385,plain,
% 2.80/1.02      ( k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4))
% 2.80/1.02      | sK2 = k1_xboole_0
% 2.80/1.02      | sK1 = k1_xboole_0
% 2.80/1.02      | sK0 = k1_xboole_0 ),
% 2.80/1.02      inference(superposition,[status(thm)],[c_538,c_541]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_721,plain,
% 2.80/1.02      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),sK2))
% 2.80/1.02      | k6_mcart_1(X1,X2,sK2,X0) = k2_mcart_1(k1_mcart_1(X0))
% 2.80/1.02      | k1_xboole_0 = X2
% 2.80/1.02      | k1_xboole_0 = X1
% 2.80/1.02      | k1_xboole_0 = sK2 ),
% 2.80/1.02      inference(instantiation,[status(thm)],[c_14]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_903,plain,
% 2.80/1.02      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,sK1),sK2))
% 2.80/1.02      | k6_mcart_1(X1,sK1,sK2,X0) = k2_mcart_1(k1_mcart_1(X0))
% 2.80/1.02      | k1_xboole_0 = X1
% 2.80/1.02      | k1_xboole_0 = sK2
% 2.80/1.02      | k1_xboole_0 = sK1 ),
% 2.80/1.02      inference(instantiation,[status(thm)],[c_721]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_1424,plain,
% 2.80/1.02      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
% 2.80/1.02      | k6_mcart_1(sK0,sK1,sK2,X0) = k2_mcart_1(k1_mcart_1(X0))
% 2.80/1.02      | k1_xboole_0 = sK2
% 2.80/1.02      | k1_xboole_0 = sK1
% 2.80/1.02      | k1_xboole_0 = sK0 ),
% 2.80/1.02      inference(instantiation,[status(thm)],[c_903]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_2376,plain,
% 2.80/1.02      ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
% 2.80/1.02      | k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4))
% 2.80/1.02      | k1_xboole_0 = sK2
% 2.80/1.02      | k1_xboole_0 = sK1
% 2.80/1.02      | k1_xboole_0 = sK0 ),
% 2.80/1.02      inference(instantiation,[status(thm)],[c_1424]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_2773,plain,
% 2.80/1.02      ( k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4)) ),
% 2.80/1.02      inference(global_propositional_subsumption,
% 2.80/1.02                [status(thm)],
% 2.80/1.02                [c_2385,c_21,c_19,c_18,c_17,c_2376]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_16,negated_conjecture,
% 2.80/1.02      ( k6_mcart_1(sK0,sK1,sK2,sK4) != sK3 ),
% 2.80/1.02      inference(cnf_transformation,[],[f53]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_2776,plain,
% 2.80/1.02      ( k2_mcart_1(k1_mcart_1(sK4)) != sK3 ),
% 2.80/1.02      inference(demodulation,[status(thm)],[c_2773,c_16]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_6,plain,
% 2.80/1.02      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 2.80/1.02      | r2_hidden(k2_mcart_1(X0),X2) ),
% 2.80/1.02      inference(cnf_transformation,[],[f39]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_544,plain,
% 2.80/1.02      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 2.80/1.02      | r2_hidden(k2_mcart_1(X0),X2) = iProver_top ),
% 2.80/1.02      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_2355,plain,
% 2.80/1.02      ( r2_hidden(k2_mcart_1(k1_mcart_1(sK4)),sK1) = iProver_top ),
% 2.80/1.02      inference(superposition,[status(thm)],[c_2309,c_544]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_2,plain,
% 2.80/1.02      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 2.80/1.02      inference(cnf_transformation,[],[f32]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_547,plain,
% 2.80/1.02      ( r2_hidden(X0,X1) != iProver_top
% 2.80/1.02      | m1_subset_1(X0,X1) = iProver_top ),
% 2.80/1.02      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_2786,plain,
% 2.80/1.02      ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) = iProver_top ),
% 2.80/1.02      inference(superposition,[status(thm)],[c_2355,c_547]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_2356,plain,
% 2.80/1.02      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0) = iProver_top ),
% 2.80/1.02      inference(superposition,[status(thm)],[c_2309,c_543]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_2797,plain,
% 2.80/1.02      ( m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) = iProver_top ),
% 2.80/1.02      inference(superposition,[status(thm)],[c_2356,c_547]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_2848,plain,
% 2.80/1.02      ( k4_tarski(k1_mcart_1(sK4),X0) != sK4
% 2.80/1.02      | m1_subset_1(X0,sK2) != iProver_top ),
% 2.80/1.02      inference(global_propositional_subsumption,
% 2.80/1.02                [status(thm)],
% 2.80/1.02                [c_2843,c_2776,c_2786,c_2797]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_2856,plain,
% 2.80/1.02      ( m1_subset_1(k2_mcart_1(sK4),sK2) != iProver_top ),
% 2.80/1.02      inference(superposition,[status(thm)],[c_2310,c_2848]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_2308,plain,
% 2.80/1.02      ( r2_hidden(k2_mcart_1(sK4),sK2) = iProver_top ),
% 2.80/1.02      inference(superposition,[status(thm)],[c_2302,c_544]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_2327,plain,
% 2.80/1.02      ( m1_subset_1(k2_mcart_1(sK4),sK2) = iProver_top ),
% 2.80/1.02      inference(superposition,[status(thm)],[c_2308,c_547]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(contradiction,plain,
% 2.80/1.02      ( $false ),
% 2.80/1.02      inference(minisat,[status(thm)],[c_2856,c_2327]) ).
% 2.80/1.02  
% 2.80/1.02  
% 2.80/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 2.80/1.02  
% 2.80/1.02  ------                               Statistics
% 2.80/1.02  
% 2.80/1.02  ------ General
% 2.80/1.02  
% 2.80/1.02  abstr_ref_over_cycles:                  0
% 2.80/1.02  abstr_ref_under_cycles:                 0
% 2.80/1.02  gc_basic_clause_elim:                   0
% 2.80/1.02  forced_gc_time:                         0
% 2.80/1.02  parsing_time:                           0.008
% 2.80/1.02  unif_index_cands_time:                  0.
% 2.80/1.02  unif_index_add_time:                    0.
% 2.80/1.02  orderings_time:                         0.
% 2.80/1.02  out_proof_time:                         0.017
% 2.80/1.02  total_time:                             0.126
% 2.80/1.02  num_of_symbols:                         48
% 2.80/1.02  num_of_terms:                           3417
% 2.80/1.02  
% 2.80/1.02  ------ Preprocessing
% 2.80/1.02  
% 2.80/1.02  num_of_splits:                          0
% 2.80/1.02  num_of_split_atoms:                     0
% 2.80/1.02  num_of_reused_defs:                     0
% 2.80/1.02  num_eq_ax_congr_red:                    24
% 2.80/1.02  num_of_sem_filtered_clauses:            1
% 2.80/1.02  num_of_subtypes:                        0
% 2.80/1.02  monotx_restored_types:                  0
% 2.80/1.02  sat_num_of_epr_types:                   0
% 2.80/1.02  sat_num_of_non_cyclic_types:            0
% 2.80/1.02  sat_guarded_non_collapsed_types:        0
% 2.80/1.02  num_pure_diseq_elim:                    0
% 2.80/1.02  simp_replaced_by:                       0
% 2.80/1.02  res_preprocessed:                       106
% 2.80/1.02  prep_upred:                             0
% 2.80/1.02  prep_unflattend:                        1
% 2.80/1.02  smt_new_axioms:                         0
% 2.80/1.02  pred_elim_cands:                        3
% 2.80/1.02  pred_elim:                              1
% 2.80/1.02  pred_elim_cl:                           1
% 2.80/1.02  pred_elim_cycles:                       3
% 2.80/1.02  merged_defs:                            0
% 2.80/1.02  merged_defs_ncl:                        0
% 2.80/1.02  bin_hyper_res:                          0
% 2.80/1.02  prep_cycles:                            4
% 2.80/1.02  pred_elim_time:                         0.
% 2.80/1.02  splitting_time:                         0.
% 2.80/1.02  sem_filter_time:                        0.
% 2.80/1.02  monotx_time:                            0.
% 2.80/1.02  subtype_inf_time:                       0.
% 2.80/1.02  
% 2.80/1.02  ------ Problem properties
% 2.80/1.02  
% 2.80/1.02  clauses:                                21
% 2.80/1.02  conjectures:                            6
% 2.80/1.02  epr:                                    7
% 2.80/1.02  horn:                                   16
% 2.80/1.02  ground:                                 6
% 2.80/1.02  unary:                                  9
% 2.80/1.02  binary:                                 5
% 2.80/1.02  lits:                                   49
% 2.80/1.02  lits_eq:                                27
% 2.80/1.02  fd_pure:                                0
% 2.80/1.02  fd_pseudo:                              0
% 2.80/1.02  fd_cond:                                5
% 2.80/1.02  fd_pseudo_cond:                         1
% 2.80/1.02  ac_symbols:                             0
% 2.80/1.02  
% 2.80/1.02  ------ Propositional Solver
% 2.80/1.02  
% 2.80/1.02  prop_solver_calls:                      26
% 2.80/1.02  prop_fast_solver_calls:                 633
% 2.80/1.02  smt_solver_calls:                       0
% 2.80/1.02  smt_fast_solver_calls:                  0
% 2.80/1.02  prop_num_of_clauses:                    1081
% 2.80/1.02  prop_preprocess_simplified:             4263
% 2.80/1.02  prop_fo_subsumed:                       14
% 2.80/1.02  prop_solver_time:                       0.
% 2.80/1.02  smt_solver_time:                        0.
% 2.80/1.02  smt_fast_solver_time:                   0.
% 2.80/1.02  prop_fast_solver_time:                  0.
% 2.80/1.02  prop_unsat_core_time:                   0.
% 2.80/1.02  
% 2.80/1.02  ------ QBF
% 2.80/1.02  
% 2.80/1.02  qbf_q_res:                              0
% 2.80/1.02  qbf_num_tautologies:                    0
% 2.80/1.02  qbf_prep_cycles:                        0
% 2.80/1.02  
% 2.80/1.02  ------ BMC1
% 2.80/1.02  
% 2.80/1.02  bmc1_current_bound:                     -1
% 2.80/1.02  bmc1_last_solved_bound:                 -1
% 2.80/1.02  bmc1_unsat_core_size:                   -1
% 2.80/1.02  bmc1_unsat_core_parents_size:           -1
% 2.80/1.02  bmc1_merge_next_fun:                    0
% 2.80/1.02  bmc1_unsat_core_clauses_time:           0.
% 2.80/1.02  
% 2.80/1.02  ------ Instantiation
% 2.80/1.02  
% 2.80/1.02  inst_num_of_clauses:                    374
% 2.80/1.02  inst_num_in_passive:                    79
% 2.80/1.02  inst_num_in_active:                     228
% 2.80/1.02  inst_num_in_unprocessed:                67
% 2.80/1.02  inst_num_of_loops:                      230
% 2.80/1.02  inst_num_of_learning_restarts:          0
% 2.80/1.02  inst_num_moves_active_passive:          0
% 2.80/1.02  inst_lit_activity:                      0
% 2.80/1.02  inst_lit_activity_moves:                0
% 2.80/1.02  inst_num_tautologies:                   0
% 2.80/1.02  inst_num_prop_implied:                  0
% 2.80/1.02  inst_num_existing_simplified:           0
% 2.80/1.02  inst_num_eq_res_simplified:             0
% 2.80/1.02  inst_num_child_elim:                    0
% 2.80/1.02  inst_num_of_dismatching_blockings:      2
% 2.80/1.02  inst_num_of_non_proper_insts:           288
% 2.80/1.02  inst_num_of_duplicates:                 0
% 2.80/1.02  inst_inst_num_from_inst_to_res:         0
% 2.80/1.02  inst_dismatching_checking_time:         0.
% 2.80/1.02  
% 2.80/1.02  ------ Resolution
% 2.80/1.02  
% 2.80/1.02  res_num_of_clauses:                     0
% 2.80/1.02  res_num_in_passive:                     0
% 2.80/1.02  res_num_in_active:                      0
% 2.80/1.02  res_num_of_loops:                       110
% 2.80/1.02  res_forward_subset_subsumed:            10
% 2.80/1.02  res_backward_subset_subsumed:           0
% 2.80/1.02  res_forward_subsumed:                   0
% 2.80/1.02  res_backward_subsumed:                  0
% 2.80/1.02  res_forward_subsumption_resolution:     0
% 2.80/1.02  res_backward_subsumption_resolution:    0
% 2.80/1.02  res_clause_to_clause_subsumption:       125
% 2.80/1.02  res_orphan_elimination:                 0
% 2.80/1.02  res_tautology_del:                      8
% 2.80/1.02  res_num_eq_res_simplified:              0
% 2.80/1.02  res_num_sel_changes:                    0
% 2.80/1.02  res_moves_from_active_to_pass:          0
% 2.80/1.02  
% 2.80/1.02  ------ Superposition
% 2.80/1.02  
% 2.80/1.02  sup_time_total:                         0.
% 2.80/1.02  sup_time_generating:                    0.
% 2.80/1.02  sup_time_sim_full:                      0.
% 2.80/1.02  sup_time_sim_immed:                     0.
% 2.80/1.02  
% 2.80/1.02  sup_num_of_clauses:                     67
% 2.80/1.02  sup_num_in_active:                      43
% 2.80/1.02  sup_num_in_passive:                     24
% 2.80/1.02  sup_num_of_loops:                       45
% 2.80/1.02  sup_fw_superposition:                   53
% 2.80/1.02  sup_bw_superposition:                   241
% 2.80/1.02  sup_immediate_simplified:               98
% 2.80/1.02  sup_given_eliminated:                   0
% 2.80/1.02  comparisons_done:                       0
% 2.80/1.02  comparisons_avoided:                    6
% 2.80/1.02  
% 2.80/1.02  ------ Simplifications
% 2.80/1.02  
% 2.80/1.02  
% 2.80/1.02  sim_fw_subset_subsumed:                 64
% 2.80/1.02  sim_bw_subset_subsumed:                 2
% 2.80/1.02  sim_fw_subsumed:                        26
% 2.80/1.02  sim_bw_subsumed:                        4
% 2.80/1.02  sim_fw_subsumption_res:                 0
% 2.80/1.02  sim_bw_subsumption_res:                 0
% 2.80/1.02  sim_tautology_del:                      2
% 2.80/1.02  sim_eq_tautology_del:                   20
% 2.80/1.02  sim_eq_res_simp:                        5
% 2.80/1.02  sim_fw_demodulated:                     8
% 2.80/1.02  sim_bw_demodulated:                     2
% 2.80/1.02  sim_light_normalised:                   0
% 2.80/1.02  sim_joinable_taut:                      0
% 2.80/1.02  sim_joinable_simp:                      0
% 2.80/1.02  sim_ac_normalised:                      0
% 2.80/1.02  sim_smt_subsumption:                    0
% 2.80/1.02  
%------------------------------------------------------------------------------
