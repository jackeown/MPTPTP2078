%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:42:26 EST 2020

% Result     : Theorem 2.50s
% Output     : CNFRefutation 2.50s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 842 expanded)
%              Number of clauses        :   53 ( 215 expanded)
%              Number of leaves         :   12 ( 194 expanded)
%              Depth                    :   27
%              Number of atoms          :  347 (5004 expanded)
%              Number of equality atoms :  155 (1031 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = X0
       => ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 ) )
      & ( k1_xboole_0 != X0
       => ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X3,X0)
                 => r2_hidden(X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 )
        | k1_xboole_0 != X0 )
      & ( ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X2,X3)
                  | ~ r2_hidden(X3,X0) ) ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ? [X2] :
                ( ( ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) )
                & ( ! [X3] :
                      ( r2_hidden(X2,X3)
                      | ~ r2_hidden(X3,X0) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) ) )
                & ( ! [X3] :
                      ( r2_hidden(X2,X3)
                      | ~ r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ? [X2] :
                ( ( ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) )
                & ( ! [X4] :
                      ( r2_hidden(X2,X4)
                      | ~ r2_hidden(X4,X0) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ? [X6] :
                      ( ~ r2_hidden(X5,X6)
                      & r2_hidden(X6,X0) ) )
                & ( ! [X7] :
                      ( r2_hidden(X5,X7)
                      | ~ r2_hidden(X7,X0) )
                  | ~ r2_hidden(X5,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(rectify,[],[f18])).

fof(f22,plain,(
    ! [X5,X0] :
      ( ? [X6] :
          ( ~ r2_hidden(X5,X6)
          & r2_hidden(X6,X0) )
     => ( ~ r2_hidden(X5,sK2(X0,X5))
        & r2_hidden(sK2(X0,X5),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X2,X3)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(X2,sK1(X0,X1))
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( ~ r2_hidden(X2,X3)
                & r2_hidden(X3,X0) )
            | ~ r2_hidden(X2,X1) )
          & ( ! [X4] :
                ( r2_hidden(X2,X4)
                | ~ r2_hidden(X4,X0) )
            | r2_hidden(X2,X1) ) )
     => ( ( ? [X3] :
              ( ~ r2_hidden(sK0(X0,X1),X3)
              & r2_hidden(X3,X0) )
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( ! [X4] :
              ( r2_hidden(sK0(X0,X1),X4)
              | ~ r2_hidden(X4,X0) )
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ( ( ( ~ r2_hidden(sK0(X0,X1),sK1(X0,X1))
                  & r2_hidden(sK1(X0,X1),X0) )
                | ~ r2_hidden(sK0(X0,X1),X1) )
              & ( ! [X4] :
                    ( r2_hidden(sK0(X0,X1),X4)
                    | ~ r2_hidden(X4,X0) )
                | r2_hidden(sK0(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ( ~ r2_hidden(X5,sK2(X0,X5))
                    & r2_hidden(sK2(X0,X5),X0) ) )
                & ( ! [X7] :
                      ( r2_hidden(X5,X7)
                      | ~ r2_hidden(X7,X0) )
                  | ~ r2_hidden(X5,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f22,f21,f20])).

fof(f36,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | r2_hidden(sK2(X0,X5),X0)
      | k1_setfam_1(X0) != X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f56,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,k1_setfam_1(X0))
      | r2_hidden(sK2(X0,X5),X0)
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f36])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( r2_hidden(X1,X0)
       => ( r2_hidden(X1,k8_setfam_1(X0,X2))
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
             => r2_hidden(X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ( r2_hidden(X1,X0)
         => ( r2_hidden(X1,k8_setfam_1(X0,X2))
          <=> ! [X3] :
                ( r2_hidden(X3,X2)
               => r2_hidden(X1,X3) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,k8_setfam_1(X0,X2))
      <~> ! [X3] :
            ( r2_hidden(X1,X3)
            | ~ r2_hidden(X3,X2) ) )
      & r2_hidden(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,k8_setfam_1(X0,X2))
      <~> ! [X3] :
            ( r2_hidden(X1,X3)
            | ~ r2_hidden(X3,X2) ) )
      & r2_hidden(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f16])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ( ? [X3] :
            ( ~ r2_hidden(X1,X3)
            & r2_hidden(X3,X2) )
        | ~ r2_hidden(X1,k8_setfam_1(X0,X2)) )
      & ( ! [X3] :
            ( r2_hidden(X1,X3)
            | ~ r2_hidden(X3,X2) )
        | r2_hidden(X1,k8_setfam_1(X0,X2)) )
      & r2_hidden(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ( ? [X3] :
            ( ~ r2_hidden(X1,X3)
            & r2_hidden(X3,X2) )
        | ~ r2_hidden(X1,k8_setfam_1(X0,X2)) )
      & ( ! [X3] :
            ( r2_hidden(X1,X3)
            | ~ r2_hidden(X3,X2) )
        | r2_hidden(X1,k8_setfam_1(X0,X2)) )
      & r2_hidden(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f24])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ( ? [X3] :
            ( ~ r2_hidden(X1,X3)
            & r2_hidden(X3,X2) )
        | ~ r2_hidden(X1,k8_setfam_1(X0,X2)) )
      & ( ! [X4] :
            ( r2_hidden(X1,X4)
            | ~ r2_hidden(X4,X2) )
        | r2_hidden(X1,k8_setfam_1(X0,X2)) )
      & r2_hidden(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(rectify,[],[f25])).

fof(f28,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( ~ r2_hidden(X1,X3)
          & r2_hidden(X3,X2) )
     => ( ~ r2_hidden(X1,sK6)
        & r2_hidden(sK6,X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X0,X1,X2] :
        ( ( ? [X3] :
              ( ~ r2_hidden(X1,X3)
              & r2_hidden(X3,X2) )
          | ~ r2_hidden(X1,k8_setfam_1(X0,X2)) )
        & ( ! [X4] :
              ( r2_hidden(X1,X4)
              | ~ r2_hidden(X4,X2) )
          | r2_hidden(X1,k8_setfam_1(X0,X2)) )
        & r2_hidden(X1,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ( ? [X3] :
            ( ~ r2_hidden(sK4,X3)
            & r2_hidden(X3,sK5) )
        | ~ r2_hidden(sK4,k8_setfam_1(sK3,sK5)) )
      & ( ! [X4] :
            ( r2_hidden(sK4,X4)
            | ~ r2_hidden(X4,sK5) )
        | r2_hidden(sK4,k8_setfam_1(sK3,sK5)) )
      & r2_hidden(sK4,sK3)
      & m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK3))) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ( ( ~ r2_hidden(sK4,sK6)
        & r2_hidden(sK6,sK5) )
      | ~ r2_hidden(sK4,k8_setfam_1(sK3,sK5)) )
    & ( ! [X4] :
          ( r2_hidden(sK4,X4)
          | ~ r2_hidden(X4,sK5) )
      | r2_hidden(sK4,k8_setfam_1(sK3,sK5)) )
    & r2_hidden(sK4,sK3)
    & m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK3))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f26,f28,f27])).

fof(f45,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK3))) ),
    inference(cnf_transformation,[],[f29])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f48,plain,
    ( r2_hidden(sK6,sK5)
    | ~ r2_hidden(sK4,k8_setfam_1(sK3,sK5)) ),
    inference(cnf_transformation,[],[f29])).

fof(f47,plain,(
    ! [X4] :
      ( r2_hidden(sK4,X4)
      | ~ r2_hidden(X4,sK5)
      | r2_hidden(sK4,k8_setfam_1(sK3,sK5)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f37,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X5,sK2(X0,X5))
      | k1_setfam_1(X0) != X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f55,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,k1_setfam_1(X0))
      | ~ r2_hidden(X5,sK2(X0,X5))
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f37])).

fof(f49,plain,
    ( ~ r2_hidden(sK4,sK6)
    | ~ r2_hidden(sK4,k8_setfam_1(sK3,sK5)) ),
    inference(cnf_transformation,[],[f29])).

fof(f35,plain,(
    ! [X0,X7,X5,X1] :
      ( r2_hidden(X5,X7)
      | ~ r2_hidden(X7,X0)
      | ~ r2_hidden(X5,X1)
      | k1_setfam_1(X0) != X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f57,plain,(
    ! [X0,X7,X5] :
      ( r2_hidden(X5,X7)
      | ~ r2_hidden(X7,X0)
      | ~ r2_hidden(X5,k1_setfam_1(X0))
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f35])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f50,plain,(
    ! [X0] :
      ( k8_setfam_1(X0,k1_xboole_0) = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f34])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f46,plain,(
    r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

cnf(c_11,plain,
    ( r2_hidden(X0,k1_setfam_1(X1))
    | r2_hidden(sK2(X1,X0),X1)
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_610,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(X1,k1_setfam_1(X0)) = iProver_top
    | r2_hidden(sK2(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK3))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_602,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k6_setfam_1(X1,X0) = k8_setfam_1(X1,X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_615,plain,
    ( k6_setfam_1(X0,X1) = k8_setfam_1(X0,X1)
    | k1_xboole_0 = X1
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1657,plain,
    ( k6_setfam_1(sK3,sK5) = k8_setfam_1(sK3,sK5)
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_602,c_615])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k6_setfam_1(X1,X0) = k1_setfam_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_608,plain,
    ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1152,plain,
    ( k6_setfam_1(sK3,sK5) = k1_setfam_1(sK5) ),
    inference(superposition,[status(thm)],[c_602,c_608])).

cnf(c_1660,plain,
    ( k8_setfam_1(sK3,sK5) = k1_setfam_1(sK5)
    | sK5 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1657,c_1152])).

cnf(c_16,negated_conjecture,
    ( r2_hidden(sK6,sK5)
    | ~ r2_hidden(sK4,k8_setfam_1(sK3,sK5)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_605,plain,
    ( r2_hidden(sK6,sK5) = iProver_top
    | r2_hidden(sK4,k8_setfam_1(sK3,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1810,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK6,sK5) = iProver_top
    | r2_hidden(sK4,k1_setfam_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1660,c_605])).

cnf(c_25,plain,
    ( r2_hidden(sK6,sK5) = iProver_top
    | r2_hidden(sK4,k8_setfam_1(sK3,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_17,negated_conjecture,
    ( ~ r2_hidden(X0,sK5)
    | r2_hidden(sK4,X0)
    | r2_hidden(sK4,k8_setfam_1(sK3,sK5)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_604,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(sK4,X0) = iProver_top
    | r2_hidden(sK4,k8_setfam_1(sK3,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1568,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(X0,k1_setfam_1(sK5)) = iProver_top
    | r2_hidden(sK4,sK2(sK5,X0)) = iProver_top
    | r2_hidden(sK4,k8_setfam_1(sK3,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_610,c_604])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,sK2(X1,X0))
    | r2_hidden(X0,k1_setfam_1(X1))
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_611,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(X1,sK2(X0,X1)) != iProver_top
    | r2_hidden(X1,k1_setfam_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1775,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK4,k8_setfam_1(sK3,sK5)) = iProver_top
    | r2_hidden(sK4,k1_setfam_1(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1568,c_611])).

cnf(c_1960,plain,
    ( r2_hidden(sK6,sK5) = iProver_top
    | sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1810,c_25,c_1775])).

cnf(c_1961,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK6,sK5) = iProver_top ),
    inference(renaming,[status(thm)],[c_1960])).

cnf(c_1968,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK4,k8_setfam_1(sK3,sK5)) = iProver_top
    | r2_hidden(sK4,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1961,c_604])).

cnf(c_15,negated_conjecture,
    ( ~ r2_hidden(sK4,k8_setfam_1(sK3,sK5))
    | ~ r2_hidden(sK4,sK6) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_606,plain,
    ( r2_hidden(sK4,k8_setfam_1(sK3,sK5)) != iProver_top
    | r2_hidden(sK4,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1809,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK4,k1_setfam_1(sK5)) != iProver_top
    | r2_hidden(sK4,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1660,c_606])).

cnf(c_26,plain,
    ( r2_hidden(sK4,k8_setfam_1(sK3,sK5)) != iProver_top
    | r2_hidden(sK4,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1953,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK4,sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1809,c_26,c_1775])).

cnf(c_2056,plain,
    ( r2_hidden(sK4,k8_setfam_1(sK3,sK5)) = iProver_top
    | sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1968,c_1953])).

cnf(c_2057,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK4,k8_setfam_1(sK3,sK5)) = iProver_top ),
    inference(renaming,[status(thm)],[c_2056])).

cnf(c_2062,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK4,k1_setfam_1(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1660,c_2057])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X0)
    | ~ r2_hidden(X2,k1_setfam_1(X1))
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_609,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(X1,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top
    | r2_hidden(X2,k1_setfam_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2149,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(sK4,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2062,c_609])).

cnf(c_3079,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(X0,k1_setfam_1(sK5)) = iProver_top
    | r2_hidden(sK4,sK2(sK5,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_610,c_2149])).

cnf(c_3078,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK4,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1961,c_2149])).

cnf(c_3128,plain,
    ( sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3079,c_1953,c_3078])).

cnf(c_3147,plain,
    ( r2_hidden(sK6,k1_xboole_0) = iProver_top
    | r2_hidden(sK4,k8_setfam_1(sK3,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3128,c_605])).

cnf(c_3,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
    | k8_setfam_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_616,plain,
    ( k8_setfam_1(X0,k1_xboole_0) = X0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_617,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_639,plain,
    ( k8_setfam_1(X0,k1_xboole_0) = X0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_616,c_617])).

cnf(c_3152,plain,
    ( r2_hidden(sK6,k1_xboole_0) = iProver_top
    | r2_hidden(sK4,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3147,c_639])).

cnf(c_18,negated_conjecture,
    ( r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_21,plain,
    ( r2_hidden(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3487,plain,
    ( r2_hidden(sK6,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3152,c_21])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | k2_xboole_0(k1_tarski(X0),X1) = X1 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_618,plain,
    ( k2_xboole_0(k1_tarski(X0),X1) = X1
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3492,plain,
    ( k2_xboole_0(k1_tarski(sK6),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3487,c_618])).

cnf(c_1,plain,
    ( k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_3774,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3492,c_1])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 09:39:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.50/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.50/0.99  
% 2.50/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.50/0.99  
% 2.50/0.99  ------  iProver source info
% 2.50/0.99  
% 2.50/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.50/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.50/0.99  git: non_committed_changes: false
% 2.50/0.99  git: last_make_outside_of_git: false
% 2.50/0.99  
% 2.50/0.99  ------ 
% 2.50/0.99  
% 2.50/0.99  ------ Input Options
% 2.50/0.99  
% 2.50/0.99  --out_options                           all
% 2.50/0.99  --tptp_safe_out                         true
% 2.50/0.99  --problem_path                          ""
% 2.50/0.99  --include_path                          ""
% 2.50/0.99  --clausifier                            res/vclausify_rel
% 2.50/0.99  --clausifier_options                    --mode clausify
% 2.50/0.99  --stdin                                 false
% 2.50/0.99  --stats_out                             all
% 2.50/0.99  
% 2.50/0.99  ------ General Options
% 2.50/0.99  
% 2.50/0.99  --fof                                   false
% 2.50/0.99  --time_out_real                         305.
% 2.50/0.99  --time_out_virtual                      -1.
% 2.50/0.99  --symbol_type_check                     false
% 2.50/0.99  --clausify_out                          false
% 2.50/0.99  --sig_cnt_out                           false
% 2.50/0.99  --trig_cnt_out                          false
% 2.50/0.99  --trig_cnt_out_tolerance                1.
% 2.50/0.99  --trig_cnt_out_sk_spl                   false
% 2.50/0.99  --abstr_cl_out                          false
% 2.50/0.99  
% 2.50/0.99  ------ Global Options
% 2.50/0.99  
% 2.50/0.99  --schedule                              default
% 2.50/0.99  --add_important_lit                     false
% 2.50/0.99  --prop_solver_per_cl                    1000
% 2.50/0.99  --min_unsat_core                        false
% 2.50/0.99  --soft_assumptions                      false
% 2.50/0.99  --soft_lemma_size                       3
% 2.50/0.99  --prop_impl_unit_size                   0
% 2.50/0.99  --prop_impl_unit                        []
% 2.50/0.99  --share_sel_clauses                     true
% 2.50/0.99  --reset_solvers                         false
% 2.50/0.99  --bc_imp_inh                            [conj_cone]
% 2.50/0.99  --conj_cone_tolerance                   3.
% 2.50/0.99  --extra_neg_conj                        none
% 2.50/0.99  --large_theory_mode                     true
% 2.50/0.99  --prolific_symb_bound                   200
% 2.50/0.99  --lt_threshold                          2000
% 2.50/0.99  --clause_weak_htbl                      true
% 2.50/0.99  --gc_record_bc_elim                     false
% 2.50/0.99  
% 2.50/0.99  ------ Preprocessing Options
% 2.50/0.99  
% 2.50/0.99  --preprocessing_flag                    true
% 2.50/0.99  --time_out_prep_mult                    0.1
% 2.50/0.99  --splitting_mode                        input
% 2.50/0.99  --splitting_grd                         true
% 2.50/0.99  --splitting_cvd                         false
% 2.50/0.99  --splitting_cvd_svl                     false
% 2.50/0.99  --splitting_nvd                         32
% 2.50/0.99  --sub_typing                            true
% 2.50/0.99  --prep_gs_sim                           true
% 2.50/0.99  --prep_unflatten                        true
% 2.50/0.99  --prep_res_sim                          true
% 2.50/0.99  --prep_upred                            true
% 2.50/0.99  --prep_sem_filter                       exhaustive
% 2.50/0.99  --prep_sem_filter_out                   false
% 2.50/0.99  --pred_elim                             true
% 2.50/0.99  --res_sim_input                         true
% 2.50/0.99  --eq_ax_congr_red                       true
% 2.50/0.99  --pure_diseq_elim                       true
% 2.50/0.99  --brand_transform                       false
% 2.50/0.99  --non_eq_to_eq                          false
% 2.50/0.99  --prep_def_merge                        true
% 2.50/0.99  --prep_def_merge_prop_impl              false
% 2.50/0.99  --prep_def_merge_mbd                    true
% 2.50/0.99  --prep_def_merge_tr_red                 false
% 2.50/0.99  --prep_def_merge_tr_cl                  false
% 2.50/0.99  --smt_preprocessing                     true
% 2.50/0.99  --smt_ac_axioms                         fast
% 2.50/0.99  --preprocessed_out                      false
% 2.50/0.99  --preprocessed_stats                    false
% 2.50/0.99  
% 2.50/0.99  ------ Abstraction refinement Options
% 2.50/0.99  
% 2.50/0.99  --abstr_ref                             []
% 2.50/0.99  --abstr_ref_prep                        false
% 2.50/0.99  --abstr_ref_until_sat                   false
% 2.50/0.99  --abstr_ref_sig_restrict                funpre
% 2.50/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.50/0.99  --abstr_ref_under                       []
% 2.50/0.99  
% 2.50/0.99  ------ SAT Options
% 2.50/0.99  
% 2.50/0.99  --sat_mode                              false
% 2.50/0.99  --sat_fm_restart_options                ""
% 2.50/0.99  --sat_gr_def                            false
% 2.50/0.99  --sat_epr_types                         true
% 2.50/0.99  --sat_non_cyclic_types                  false
% 2.50/0.99  --sat_finite_models                     false
% 2.50/0.99  --sat_fm_lemmas                         false
% 2.50/0.99  --sat_fm_prep                           false
% 2.50/0.99  --sat_fm_uc_incr                        true
% 2.50/0.99  --sat_out_model                         small
% 2.50/0.99  --sat_out_clauses                       false
% 2.50/0.99  
% 2.50/0.99  ------ QBF Options
% 2.50/0.99  
% 2.50/0.99  --qbf_mode                              false
% 2.50/0.99  --qbf_elim_univ                         false
% 2.50/0.99  --qbf_dom_inst                          none
% 2.50/0.99  --qbf_dom_pre_inst                      false
% 2.50/0.99  --qbf_sk_in                             false
% 2.50/0.99  --qbf_pred_elim                         true
% 2.50/0.99  --qbf_split                             512
% 2.50/0.99  
% 2.50/0.99  ------ BMC1 Options
% 2.50/0.99  
% 2.50/0.99  --bmc1_incremental                      false
% 2.50/0.99  --bmc1_axioms                           reachable_all
% 2.50/0.99  --bmc1_min_bound                        0
% 2.50/0.99  --bmc1_max_bound                        -1
% 2.50/0.99  --bmc1_max_bound_default                -1
% 2.50/0.99  --bmc1_symbol_reachability              true
% 2.50/0.99  --bmc1_property_lemmas                  false
% 2.50/0.99  --bmc1_k_induction                      false
% 2.50/0.99  --bmc1_non_equiv_states                 false
% 2.50/0.99  --bmc1_deadlock                         false
% 2.50/0.99  --bmc1_ucm                              false
% 2.50/0.99  --bmc1_add_unsat_core                   none
% 2.50/0.99  --bmc1_unsat_core_children              false
% 2.50/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.50/0.99  --bmc1_out_stat                         full
% 2.50/0.99  --bmc1_ground_init                      false
% 2.50/0.99  --bmc1_pre_inst_next_state              false
% 2.50/0.99  --bmc1_pre_inst_state                   false
% 2.50/0.99  --bmc1_pre_inst_reach_state             false
% 2.50/0.99  --bmc1_out_unsat_core                   false
% 2.50/0.99  --bmc1_aig_witness_out                  false
% 2.50/0.99  --bmc1_verbose                          false
% 2.50/0.99  --bmc1_dump_clauses_tptp                false
% 2.50/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.50/0.99  --bmc1_dump_file                        -
% 2.50/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.50/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.50/0.99  --bmc1_ucm_extend_mode                  1
% 2.50/0.99  --bmc1_ucm_init_mode                    2
% 2.50/0.99  --bmc1_ucm_cone_mode                    none
% 2.50/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.50/0.99  --bmc1_ucm_relax_model                  4
% 2.50/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.50/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.50/0.99  --bmc1_ucm_layered_model                none
% 2.50/0.99  --bmc1_ucm_max_lemma_size               10
% 2.50/0.99  
% 2.50/0.99  ------ AIG Options
% 2.50/0.99  
% 2.50/0.99  --aig_mode                              false
% 2.50/0.99  
% 2.50/0.99  ------ Instantiation Options
% 2.50/0.99  
% 2.50/0.99  --instantiation_flag                    true
% 2.50/0.99  --inst_sos_flag                         false
% 2.50/0.99  --inst_sos_phase                        true
% 2.50/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.50/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.50/0.99  --inst_lit_sel_side                     num_symb
% 2.50/0.99  --inst_solver_per_active                1400
% 2.50/0.99  --inst_solver_calls_frac                1.
% 2.50/0.99  --inst_passive_queue_type               priority_queues
% 2.50/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.50/0.99  --inst_passive_queues_freq              [25;2]
% 2.50/0.99  --inst_dismatching                      true
% 2.50/0.99  --inst_eager_unprocessed_to_passive     true
% 2.50/0.99  --inst_prop_sim_given                   true
% 2.50/0.99  --inst_prop_sim_new                     false
% 2.50/0.99  --inst_subs_new                         false
% 2.50/0.99  --inst_eq_res_simp                      false
% 2.50/0.99  --inst_subs_given                       false
% 2.50/0.99  --inst_orphan_elimination               true
% 2.50/0.99  --inst_learning_loop_flag               true
% 2.50/0.99  --inst_learning_start                   3000
% 2.50/0.99  --inst_learning_factor                  2
% 2.50/0.99  --inst_start_prop_sim_after_learn       3
% 2.50/0.99  --inst_sel_renew                        solver
% 2.50/0.99  --inst_lit_activity_flag                true
% 2.50/0.99  --inst_restr_to_given                   false
% 2.50/0.99  --inst_activity_threshold               500
% 2.50/0.99  --inst_out_proof                        true
% 2.50/0.99  
% 2.50/0.99  ------ Resolution Options
% 2.50/0.99  
% 2.50/0.99  --resolution_flag                       true
% 2.50/0.99  --res_lit_sel                           adaptive
% 2.50/0.99  --res_lit_sel_side                      none
% 2.50/0.99  --res_ordering                          kbo
% 2.50/0.99  --res_to_prop_solver                    active
% 2.50/0.99  --res_prop_simpl_new                    false
% 2.50/0.99  --res_prop_simpl_given                  true
% 2.50/0.99  --res_passive_queue_type                priority_queues
% 2.50/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.50/0.99  --res_passive_queues_freq               [15;5]
% 2.50/0.99  --res_forward_subs                      full
% 2.50/0.99  --res_backward_subs                     full
% 2.50/0.99  --res_forward_subs_resolution           true
% 2.50/0.99  --res_backward_subs_resolution          true
% 2.50/0.99  --res_orphan_elimination                true
% 2.50/0.99  --res_time_limit                        2.
% 2.50/0.99  --res_out_proof                         true
% 2.50/0.99  
% 2.50/0.99  ------ Superposition Options
% 2.50/0.99  
% 2.50/0.99  --superposition_flag                    true
% 2.50/0.99  --sup_passive_queue_type                priority_queues
% 2.50/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.50/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.50/0.99  --demod_completeness_check              fast
% 2.50/0.99  --demod_use_ground                      true
% 2.50/0.99  --sup_to_prop_solver                    passive
% 2.50/0.99  --sup_prop_simpl_new                    true
% 2.50/0.99  --sup_prop_simpl_given                  true
% 2.50/0.99  --sup_fun_splitting                     false
% 2.50/0.99  --sup_smt_interval                      50000
% 2.50/0.99  
% 2.50/0.99  ------ Superposition Simplification Setup
% 2.50/0.99  
% 2.50/0.99  --sup_indices_passive                   []
% 2.50/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.50/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.50/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.50/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.50/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.50/0.99  --sup_full_bw                           [BwDemod]
% 2.50/0.99  --sup_immed_triv                        [TrivRules]
% 2.50/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.50/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.50/0.99  --sup_immed_bw_main                     []
% 2.50/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.50/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.50/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.50/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.50/0.99  
% 2.50/0.99  ------ Combination Options
% 2.50/0.99  
% 2.50/0.99  --comb_res_mult                         3
% 2.50/0.99  --comb_sup_mult                         2
% 2.50/0.99  --comb_inst_mult                        10
% 2.50/0.99  
% 2.50/0.99  ------ Debug Options
% 2.50/0.99  
% 2.50/0.99  --dbg_backtrace                         false
% 2.50/0.99  --dbg_dump_prop_clauses                 false
% 2.50/0.99  --dbg_dump_prop_clauses_file            -
% 2.50/0.99  --dbg_out_stat                          false
% 2.50/0.99  ------ Parsing...
% 2.50/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.50/0.99  
% 2.50/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.50/0.99  
% 2.50/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.50/0.99  
% 2.50/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.50/0.99  ------ Proving...
% 2.50/0.99  ------ Problem Properties 
% 2.50/0.99  
% 2.50/0.99  
% 2.50/0.99  clauses                                 19
% 2.50/0.99  conjectures                             5
% 2.50/0.99  EPR                                     1
% 2.50/0.99  Horn                                    11
% 2.50/0.99  unary                                   5
% 2.50/0.99  binary                                  5
% 2.50/0.99  lits                                    47
% 2.50/0.99  lits eq                                 16
% 2.50/0.99  fd_pure                                 0
% 2.50/0.99  fd_pseudo                               0
% 2.50/0.99  fd_cond                                 4
% 2.50/0.99  fd_pseudo_cond                          3
% 2.50/0.99  AC symbols                              0
% 2.50/0.99  
% 2.50/0.99  ------ Schedule dynamic 5 is on 
% 2.50/0.99  
% 2.50/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.50/0.99  
% 2.50/0.99  
% 2.50/0.99  ------ 
% 2.50/0.99  Current options:
% 2.50/0.99  ------ 
% 2.50/0.99  
% 2.50/0.99  ------ Input Options
% 2.50/0.99  
% 2.50/0.99  --out_options                           all
% 2.50/0.99  --tptp_safe_out                         true
% 2.50/0.99  --problem_path                          ""
% 2.50/0.99  --include_path                          ""
% 2.50/0.99  --clausifier                            res/vclausify_rel
% 2.50/0.99  --clausifier_options                    --mode clausify
% 2.50/0.99  --stdin                                 false
% 2.50/0.99  --stats_out                             all
% 2.50/0.99  
% 2.50/0.99  ------ General Options
% 2.50/0.99  
% 2.50/0.99  --fof                                   false
% 2.50/0.99  --time_out_real                         305.
% 2.50/0.99  --time_out_virtual                      -1.
% 2.50/0.99  --symbol_type_check                     false
% 2.50/0.99  --clausify_out                          false
% 2.50/0.99  --sig_cnt_out                           false
% 2.50/0.99  --trig_cnt_out                          false
% 2.50/0.99  --trig_cnt_out_tolerance                1.
% 2.50/0.99  --trig_cnt_out_sk_spl                   false
% 2.50/0.99  --abstr_cl_out                          false
% 2.50/0.99  
% 2.50/0.99  ------ Global Options
% 2.50/0.99  
% 2.50/0.99  --schedule                              default
% 2.50/0.99  --add_important_lit                     false
% 2.50/0.99  --prop_solver_per_cl                    1000
% 2.50/0.99  --min_unsat_core                        false
% 2.50/0.99  --soft_assumptions                      false
% 2.50/0.99  --soft_lemma_size                       3
% 2.50/0.99  --prop_impl_unit_size                   0
% 2.50/0.99  --prop_impl_unit                        []
% 2.50/0.99  --share_sel_clauses                     true
% 2.50/0.99  --reset_solvers                         false
% 2.50/0.99  --bc_imp_inh                            [conj_cone]
% 2.50/0.99  --conj_cone_tolerance                   3.
% 2.50/0.99  --extra_neg_conj                        none
% 2.50/0.99  --large_theory_mode                     true
% 2.50/0.99  --prolific_symb_bound                   200
% 2.50/0.99  --lt_threshold                          2000
% 2.50/0.99  --clause_weak_htbl                      true
% 2.50/0.99  --gc_record_bc_elim                     false
% 2.50/0.99  
% 2.50/0.99  ------ Preprocessing Options
% 2.50/0.99  
% 2.50/0.99  --preprocessing_flag                    true
% 2.50/0.99  --time_out_prep_mult                    0.1
% 2.50/0.99  --splitting_mode                        input
% 2.50/0.99  --splitting_grd                         true
% 2.50/0.99  --splitting_cvd                         false
% 2.50/0.99  --splitting_cvd_svl                     false
% 2.50/0.99  --splitting_nvd                         32
% 2.50/0.99  --sub_typing                            true
% 2.50/0.99  --prep_gs_sim                           true
% 2.50/0.99  --prep_unflatten                        true
% 2.50/0.99  --prep_res_sim                          true
% 2.50/0.99  --prep_upred                            true
% 2.50/0.99  --prep_sem_filter                       exhaustive
% 2.50/0.99  --prep_sem_filter_out                   false
% 2.50/0.99  --pred_elim                             true
% 2.50/0.99  --res_sim_input                         true
% 2.50/0.99  --eq_ax_congr_red                       true
% 2.50/0.99  --pure_diseq_elim                       true
% 2.50/0.99  --brand_transform                       false
% 2.50/0.99  --non_eq_to_eq                          false
% 2.50/0.99  --prep_def_merge                        true
% 2.50/0.99  --prep_def_merge_prop_impl              false
% 2.50/0.99  --prep_def_merge_mbd                    true
% 2.50/0.99  --prep_def_merge_tr_red                 false
% 2.50/0.99  --prep_def_merge_tr_cl                  false
% 2.50/0.99  --smt_preprocessing                     true
% 2.50/0.99  --smt_ac_axioms                         fast
% 2.50/0.99  --preprocessed_out                      false
% 2.50/0.99  --preprocessed_stats                    false
% 2.50/0.99  
% 2.50/0.99  ------ Abstraction refinement Options
% 2.50/0.99  
% 2.50/0.99  --abstr_ref                             []
% 2.50/0.99  --abstr_ref_prep                        false
% 2.50/0.99  --abstr_ref_until_sat                   false
% 2.50/0.99  --abstr_ref_sig_restrict                funpre
% 2.50/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.50/0.99  --abstr_ref_under                       []
% 2.50/0.99  
% 2.50/0.99  ------ SAT Options
% 2.50/0.99  
% 2.50/0.99  --sat_mode                              false
% 2.50/0.99  --sat_fm_restart_options                ""
% 2.50/0.99  --sat_gr_def                            false
% 2.50/0.99  --sat_epr_types                         true
% 2.50/0.99  --sat_non_cyclic_types                  false
% 2.50/0.99  --sat_finite_models                     false
% 2.50/0.99  --sat_fm_lemmas                         false
% 2.50/0.99  --sat_fm_prep                           false
% 2.50/0.99  --sat_fm_uc_incr                        true
% 2.50/0.99  --sat_out_model                         small
% 2.50/0.99  --sat_out_clauses                       false
% 2.50/0.99  
% 2.50/0.99  ------ QBF Options
% 2.50/0.99  
% 2.50/0.99  --qbf_mode                              false
% 2.50/0.99  --qbf_elim_univ                         false
% 2.50/0.99  --qbf_dom_inst                          none
% 2.50/0.99  --qbf_dom_pre_inst                      false
% 2.50/0.99  --qbf_sk_in                             false
% 2.50/0.99  --qbf_pred_elim                         true
% 2.50/0.99  --qbf_split                             512
% 2.50/0.99  
% 2.50/0.99  ------ BMC1 Options
% 2.50/0.99  
% 2.50/0.99  --bmc1_incremental                      false
% 2.50/0.99  --bmc1_axioms                           reachable_all
% 2.50/0.99  --bmc1_min_bound                        0
% 2.50/0.99  --bmc1_max_bound                        -1
% 2.50/0.99  --bmc1_max_bound_default                -1
% 2.50/0.99  --bmc1_symbol_reachability              true
% 2.50/0.99  --bmc1_property_lemmas                  false
% 2.50/0.99  --bmc1_k_induction                      false
% 2.50/0.99  --bmc1_non_equiv_states                 false
% 2.50/0.99  --bmc1_deadlock                         false
% 2.50/0.99  --bmc1_ucm                              false
% 2.50/0.99  --bmc1_add_unsat_core                   none
% 2.50/0.99  --bmc1_unsat_core_children              false
% 2.50/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.50/0.99  --bmc1_out_stat                         full
% 2.50/0.99  --bmc1_ground_init                      false
% 2.50/0.99  --bmc1_pre_inst_next_state              false
% 2.50/0.99  --bmc1_pre_inst_state                   false
% 2.50/0.99  --bmc1_pre_inst_reach_state             false
% 2.50/0.99  --bmc1_out_unsat_core                   false
% 2.50/0.99  --bmc1_aig_witness_out                  false
% 2.50/0.99  --bmc1_verbose                          false
% 2.50/0.99  --bmc1_dump_clauses_tptp                false
% 2.50/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.50/0.99  --bmc1_dump_file                        -
% 2.50/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.50/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.50/0.99  --bmc1_ucm_extend_mode                  1
% 2.50/0.99  --bmc1_ucm_init_mode                    2
% 2.50/0.99  --bmc1_ucm_cone_mode                    none
% 2.50/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.50/0.99  --bmc1_ucm_relax_model                  4
% 2.50/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.50/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.50/0.99  --bmc1_ucm_layered_model                none
% 2.50/0.99  --bmc1_ucm_max_lemma_size               10
% 2.50/0.99  
% 2.50/0.99  ------ AIG Options
% 2.50/0.99  
% 2.50/0.99  --aig_mode                              false
% 2.50/0.99  
% 2.50/0.99  ------ Instantiation Options
% 2.50/0.99  
% 2.50/0.99  --instantiation_flag                    true
% 2.50/0.99  --inst_sos_flag                         false
% 2.50/0.99  --inst_sos_phase                        true
% 2.50/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.50/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.50/0.99  --inst_lit_sel_side                     none
% 2.50/0.99  --inst_solver_per_active                1400
% 2.50/0.99  --inst_solver_calls_frac                1.
% 2.50/0.99  --inst_passive_queue_type               priority_queues
% 2.50/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.50/0.99  --inst_passive_queues_freq              [25;2]
% 2.50/0.99  --inst_dismatching                      true
% 2.50/0.99  --inst_eager_unprocessed_to_passive     true
% 2.50/0.99  --inst_prop_sim_given                   true
% 2.50/0.99  --inst_prop_sim_new                     false
% 2.50/0.99  --inst_subs_new                         false
% 2.50/0.99  --inst_eq_res_simp                      false
% 2.50/0.99  --inst_subs_given                       false
% 2.50/0.99  --inst_orphan_elimination               true
% 2.50/0.99  --inst_learning_loop_flag               true
% 2.50/0.99  --inst_learning_start                   3000
% 2.50/0.99  --inst_learning_factor                  2
% 2.50/0.99  --inst_start_prop_sim_after_learn       3
% 2.50/0.99  --inst_sel_renew                        solver
% 2.50/0.99  --inst_lit_activity_flag                true
% 2.50/0.99  --inst_restr_to_given                   false
% 2.50/0.99  --inst_activity_threshold               500
% 2.50/0.99  --inst_out_proof                        true
% 2.50/0.99  
% 2.50/0.99  ------ Resolution Options
% 2.50/0.99  
% 2.50/0.99  --resolution_flag                       false
% 2.50/0.99  --res_lit_sel                           adaptive
% 2.50/0.99  --res_lit_sel_side                      none
% 2.50/0.99  --res_ordering                          kbo
% 2.50/0.99  --res_to_prop_solver                    active
% 2.50/0.99  --res_prop_simpl_new                    false
% 2.50/0.99  --res_prop_simpl_given                  true
% 2.50/0.99  --res_passive_queue_type                priority_queues
% 2.50/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.50/0.99  --res_passive_queues_freq               [15;5]
% 2.50/0.99  --res_forward_subs                      full
% 2.50/0.99  --res_backward_subs                     full
% 2.50/0.99  --res_forward_subs_resolution           true
% 2.50/0.99  --res_backward_subs_resolution          true
% 2.50/0.99  --res_orphan_elimination                true
% 2.50/0.99  --res_time_limit                        2.
% 2.50/0.99  --res_out_proof                         true
% 2.50/0.99  
% 2.50/0.99  ------ Superposition Options
% 2.50/0.99  
% 2.50/0.99  --superposition_flag                    true
% 2.50/0.99  --sup_passive_queue_type                priority_queues
% 2.50/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.50/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.50/0.99  --demod_completeness_check              fast
% 2.50/0.99  --demod_use_ground                      true
% 2.50/0.99  --sup_to_prop_solver                    passive
% 2.50/0.99  --sup_prop_simpl_new                    true
% 2.50/0.99  --sup_prop_simpl_given                  true
% 2.50/0.99  --sup_fun_splitting                     false
% 2.50/0.99  --sup_smt_interval                      50000
% 2.50/0.99  
% 2.50/0.99  ------ Superposition Simplification Setup
% 2.50/0.99  
% 2.50/0.99  --sup_indices_passive                   []
% 2.50/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.50/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.50/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.50/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.50/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.50/0.99  --sup_full_bw                           [BwDemod]
% 2.50/0.99  --sup_immed_triv                        [TrivRules]
% 2.50/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.50/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.50/0.99  --sup_immed_bw_main                     []
% 2.50/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.50/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.50/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.50/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.50/0.99  
% 2.50/0.99  ------ Combination Options
% 2.50/0.99  
% 2.50/0.99  --comb_res_mult                         3
% 2.50/0.99  --comb_sup_mult                         2
% 2.50/0.99  --comb_inst_mult                        10
% 2.50/0.99  
% 2.50/0.99  ------ Debug Options
% 2.50/0.99  
% 2.50/0.99  --dbg_backtrace                         false
% 2.50/0.99  --dbg_dump_prop_clauses                 false
% 2.50/0.99  --dbg_dump_prop_clauses_file            -
% 2.50/0.99  --dbg_out_stat                          false
% 2.50/0.99  
% 2.50/0.99  
% 2.50/0.99  
% 2.50/0.99  
% 2.50/0.99  ------ Proving...
% 2.50/0.99  
% 2.50/0.99  
% 2.50/0.99  % SZS status Theorem for theBenchmark.p
% 2.50/0.99  
% 2.50/0.99   Resolution empty clause
% 2.50/0.99  
% 2.50/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.50/0.99  
% 2.50/0.99  fof(f5,axiom,(
% 2.50/0.99    ! [X0,X1] : ((k1_xboole_0 = X0 => (k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1)) & (k1_xboole_0 != X0 => (k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X3,X0) => r2_hidden(X2,X3))))))),
% 2.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.50/0.99  
% 2.50/0.99  fof(f12,plain,(
% 2.50/0.99    ! [X0,X1] : (((k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1) | k1_xboole_0 != X0) & ((k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)))) | k1_xboole_0 = X0))),
% 2.50/0.99    inference(ennf_transformation,[],[f5])).
% 2.50/0.99  
% 2.50/0.99  fof(f18,plain,(
% 2.50/0.99    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | ? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0))) & (! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)) | ~r2_hidden(X2,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 2.50/0.99    inference(nnf_transformation,[],[f12])).
% 2.50/0.99  
% 2.50/0.99  fof(f19,plain,(
% 2.50/0.99    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | ? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X4] : (r2_hidden(X2,X4) | ~r2_hidden(X4,X0)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ? [X6] : (~r2_hidden(X5,X6) & r2_hidden(X6,X0))) & (! [X7] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0)) | ~r2_hidden(X5,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 2.50/0.99    inference(rectify,[],[f18])).
% 2.50/0.99  
% 2.50/0.99  fof(f22,plain,(
% 2.50/0.99    ! [X5,X0] : (? [X6] : (~r2_hidden(X5,X6) & r2_hidden(X6,X0)) => (~r2_hidden(X5,sK2(X0,X5)) & r2_hidden(sK2(X0,X5),X0)))),
% 2.50/0.99    introduced(choice_axiom,[])).
% 2.50/0.99  
% 2.50/0.99  fof(f21,plain,(
% 2.50/0.99    ( ! [X2] : (! [X1,X0] : (? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) => (~r2_hidden(X2,sK1(X0,X1)) & r2_hidden(sK1(X0,X1),X0)))) )),
% 2.50/0.99    introduced(choice_axiom,[])).
% 2.50/0.99  
% 2.50/0.99  fof(f20,plain,(
% 2.50/0.99    ! [X1,X0] : (? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X4] : (r2_hidden(X2,X4) | ~r2_hidden(X4,X0)) | r2_hidden(X2,X1))) => ((? [X3] : (~r2_hidden(sK0(X0,X1),X3) & r2_hidden(X3,X0)) | ~r2_hidden(sK0(X0,X1),X1)) & (! [X4] : (r2_hidden(sK0(X0,X1),X4) | ~r2_hidden(X4,X0)) | r2_hidden(sK0(X0,X1),X1))))),
% 2.50/0.99    introduced(choice_axiom,[])).
% 2.50/0.99  
% 2.50/0.99  fof(f23,plain,(
% 2.50/0.99    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | (((~r2_hidden(sK0(X0,X1),sK1(X0,X1)) & r2_hidden(sK1(X0,X1),X0)) | ~r2_hidden(sK0(X0,X1),X1)) & (! [X4] : (r2_hidden(sK0(X0,X1),X4) | ~r2_hidden(X4,X0)) | r2_hidden(sK0(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | (~r2_hidden(X5,sK2(X0,X5)) & r2_hidden(sK2(X0,X5),X0))) & (! [X7] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0)) | ~r2_hidden(X5,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 2.50/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f22,f21,f20])).
% 2.50/0.99  
% 2.50/0.99  fof(f36,plain,(
% 2.50/0.99    ( ! [X0,X5,X1] : (r2_hidden(X5,X1) | r2_hidden(sK2(X0,X5),X0) | k1_setfam_1(X0) != X1 | k1_xboole_0 = X0) )),
% 2.50/0.99    inference(cnf_transformation,[],[f23])).
% 2.50/0.99  
% 2.50/0.99  fof(f56,plain,(
% 2.50/0.99    ( ! [X0,X5] : (r2_hidden(X5,k1_setfam_1(X0)) | r2_hidden(sK2(X0,X5),X0) | k1_xboole_0 = X0) )),
% 2.50/0.99    inference(equality_resolution,[],[f36])).
% 2.50/0.99  
% 2.50/0.99  fof(f8,conjecture,(
% 2.50/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r2_hidden(X1,X0) => (r2_hidden(X1,k8_setfam_1(X0,X2)) <=> ! [X3] : (r2_hidden(X3,X2) => r2_hidden(X1,X3)))))),
% 2.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.50/0.99  
% 2.50/0.99  fof(f9,negated_conjecture,(
% 2.50/0.99    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r2_hidden(X1,X0) => (r2_hidden(X1,k8_setfam_1(X0,X2)) <=> ! [X3] : (r2_hidden(X3,X2) => r2_hidden(X1,X3)))))),
% 2.50/0.99    inference(negated_conjecture,[],[f8])).
% 2.50/0.99  
% 2.50/0.99  fof(f16,plain,(
% 2.50/0.99    ? [X0,X1,X2] : (((r2_hidden(X1,k8_setfam_1(X0,X2)) <~> ! [X3] : (r2_hidden(X1,X3) | ~r2_hidden(X3,X2))) & r2_hidden(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.50/0.99    inference(ennf_transformation,[],[f9])).
% 2.50/0.99  
% 2.50/0.99  fof(f17,plain,(
% 2.50/0.99    ? [X0,X1,X2] : ((r2_hidden(X1,k8_setfam_1(X0,X2)) <~> ! [X3] : (r2_hidden(X1,X3) | ~r2_hidden(X3,X2))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.50/0.99    inference(flattening,[],[f16])).
% 2.50/0.99  
% 2.50/0.99  fof(f24,plain,(
% 2.50/0.99    ? [X0,X1,X2] : (((? [X3] : (~r2_hidden(X1,X3) & r2_hidden(X3,X2)) | ~r2_hidden(X1,k8_setfam_1(X0,X2))) & (! [X3] : (r2_hidden(X1,X3) | ~r2_hidden(X3,X2)) | r2_hidden(X1,k8_setfam_1(X0,X2)))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.50/0.99    inference(nnf_transformation,[],[f17])).
% 2.50/0.99  
% 2.50/0.99  fof(f25,plain,(
% 2.50/0.99    ? [X0,X1,X2] : ((? [X3] : (~r2_hidden(X1,X3) & r2_hidden(X3,X2)) | ~r2_hidden(X1,k8_setfam_1(X0,X2))) & (! [X3] : (r2_hidden(X1,X3) | ~r2_hidden(X3,X2)) | r2_hidden(X1,k8_setfam_1(X0,X2))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.50/0.99    inference(flattening,[],[f24])).
% 2.50/0.99  
% 2.50/0.99  fof(f26,plain,(
% 2.50/0.99    ? [X0,X1,X2] : ((? [X3] : (~r2_hidden(X1,X3) & r2_hidden(X3,X2)) | ~r2_hidden(X1,k8_setfam_1(X0,X2))) & (! [X4] : (r2_hidden(X1,X4) | ~r2_hidden(X4,X2)) | r2_hidden(X1,k8_setfam_1(X0,X2))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.50/0.99    inference(rectify,[],[f25])).
% 2.50/0.99  
% 2.50/0.99  fof(f28,plain,(
% 2.50/0.99    ( ! [X2,X1] : (? [X3] : (~r2_hidden(X1,X3) & r2_hidden(X3,X2)) => (~r2_hidden(X1,sK6) & r2_hidden(sK6,X2))) )),
% 2.50/0.99    introduced(choice_axiom,[])).
% 2.50/0.99  
% 2.50/0.99  fof(f27,plain,(
% 2.50/0.99    ? [X0,X1,X2] : ((? [X3] : (~r2_hidden(X1,X3) & r2_hidden(X3,X2)) | ~r2_hidden(X1,k8_setfam_1(X0,X2))) & (! [X4] : (r2_hidden(X1,X4) | ~r2_hidden(X4,X2)) | r2_hidden(X1,k8_setfam_1(X0,X2))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) => ((? [X3] : (~r2_hidden(sK4,X3) & r2_hidden(X3,sK5)) | ~r2_hidden(sK4,k8_setfam_1(sK3,sK5))) & (! [X4] : (r2_hidden(sK4,X4) | ~r2_hidden(X4,sK5)) | r2_hidden(sK4,k8_setfam_1(sK3,sK5))) & r2_hidden(sK4,sK3) & m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK3))))),
% 2.50/0.99    introduced(choice_axiom,[])).
% 2.50/0.99  
% 2.50/0.99  fof(f29,plain,(
% 2.50/0.99    ((~r2_hidden(sK4,sK6) & r2_hidden(sK6,sK5)) | ~r2_hidden(sK4,k8_setfam_1(sK3,sK5))) & (! [X4] : (r2_hidden(sK4,X4) | ~r2_hidden(X4,sK5)) | r2_hidden(sK4,k8_setfam_1(sK3,sK5))) & r2_hidden(sK4,sK3) & m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK3)))),
% 2.50/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f26,f28,f27])).
% 2.50/0.99  
% 2.50/0.99  fof(f45,plain,(
% 2.50/0.99    m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK3)))),
% 2.50/0.99    inference(cnf_transformation,[],[f29])).
% 2.50/0.99  
% 2.50/0.99  fof(f4,axiom,(
% 2.50/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 2.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.50/0.99  
% 2.50/0.99  fof(f11,plain,(
% 2.50/0.99    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.50/0.99    inference(ennf_transformation,[],[f4])).
% 2.50/0.99  
% 2.50/0.99  fof(f33,plain,(
% 2.50/0.99    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.50/0.99    inference(cnf_transformation,[],[f11])).
% 2.50/0.99  
% 2.50/0.99  fof(f6,axiom,(
% 2.50/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 2.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.50/0.99  
% 2.50/0.99  fof(f13,plain,(
% 2.50/0.99    ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.50/0.99    inference(ennf_transformation,[],[f6])).
% 2.50/0.99  
% 2.50/0.99  fof(f43,plain,(
% 2.50/0.99    ( ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.50/0.99    inference(cnf_transformation,[],[f13])).
% 2.50/0.99  
% 2.50/0.99  fof(f48,plain,(
% 2.50/0.99    r2_hidden(sK6,sK5) | ~r2_hidden(sK4,k8_setfam_1(sK3,sK5))),
% 2.50/0.99    inference(cnf_transformation,[],[f29])).
% 2.50/0.99  
% 2.50/0.99  fof(f47,plain,(
% 2.50/0.99    ( ! [X4] : (r2_hidden(sK4,X4) | ~r2_hidden(X4,sK5) | r2_hidden(sK4,k8_setfam_1(sK3,sK5))) )),
% 2.50/0.99    inference(cnf_transformation,[],[f29])).
% 2.50/0.99  
% 2.50/0.99  fof(f37,plain,(
% 2.50/0.99    ( ! [X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(X5,sK2(X0,X5)) | k1_setfam_1(X0) != X1 | k1_xboole_0 = X0) )),
% 2.50/0.99    inference(cnf_transformation,[],[f23])).
% 2.50/0.99  
% 2.50/0.99  fof(f55,plain,(
% 2.50/0.99    ( ! [X0,X5] : (r2_hidden(X5,k1_setfam_1(X0)) | ~r2_hidden(X5,sK2(X0,X5)) | k1_xboole_0 = X0) )),
% 2.50/0.99    inference(equality_resolution,[],[f37])).
% 2.50/0.99  
% 2.50/0.99  fof(f49,plain,(
% 2.50/0.99    ~r2_hidden(sK4,sK6) | ~r2_hidden(sK4,k8_setfam_1(sK3,sK5))),
% 2.50/0.99    inference(cnf_transformation,[],[f29])).
% 2.50/0.99  
% 2.50/0.99  fof(f35,plain,(
% 2.50/0.99    ( ! [X0,X7,X5,X1] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0) | ~r2_hidden(X5,X1) | k1_setfam_1(X0) != X1 | k1_xboole_0 = X0) )),
% 2.50/0.99    inference(cnf_transformation,[],[f23])).
% 2.50/0.99  
% 2.50/0.99  fof(f57,plain,(
% 2.50/0.99    ( ! [X0,X7,X5] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0) | ~r2_hidden(X5,k1_setfam_1(X0)) | k1_xboole_0 = X0) )),
% 2.50/0.99    inference(equality_resolution,[],[f35])).
% 2.50/0.99  
% 2.50/0.99  fof(f34,plain,(
% 2.50/0.99    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.50/0.99    inference(cnf_transformation,[],[f11])).
% 2.50/0.99  
% 2.50/0.99  fof(f50,plain,(
% 2.50/0.99    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.50/0.99    inference(equality_resolution,[],[f34])).
% 2.50/0.99  
% 2.50/0.99  fof(f3,axiom,(
% 2.50/0.99    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.50/0.99  
% 2.50/0.99  fof(f32,plain,(
% 2.50/0.99    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.50/0.99    inference(cnf_transformation,[],[f3])).
% 2.50/0.99  
% 2.50/0.99  fof(f46,plain,(
% 2.50/0.99    r2_hidden(sK4,sK3)),
% 2.50/0.99    inference(cnf_transformation,[],[f29])).
% 2.50/0.99  
% 2.50/0.99  fof(f1,axiom,(
% 2.50/0.99    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 2.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.50/0.99  
% 2.50/0.99  fof(f10,plain,(
% 2.50/0.99    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1))),
% 2.50/0.99    inference(ennf_transformation,[],[f1])).
% 2.50/0.99  
% 2.50/0.99  fof(f30,plain,(
% 2.50/0.99    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1)) )),
% 2.50/0.99    inference(cnf_transformation,[],[f10])).
% 2.50/0.99  
% 2.50/0.99  fof(f2,axiom,(
% 2.50/0.99    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0),
% 2.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.50/0.99  
% 2.50/0.99  fof(f31,plain,(
% 2.50/0.99    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0) )),
% 2.50/0.99    inference(cnf_transformation,[],[f2])).
% 2.50/0.99  
% 2.50/0.99  cnf(c_11,plain,
% 2.50/0.99      ( r2_hidden(X0,k1_setfam_1(X1))
% 2.50/0.99      | r2_hidden(sK2(X1,X0),X1)
% 2.50/0.99      | k1_xboole_0 = X1 ),
% 2.50/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_610,plain,
% 2.50/0.99      ( k1_xboole_0 = X0
% 2.50/0.99      | r2_hidden(X1,k1_setfam_1(X0)) = iProver_top
% 2.50/0.99      | r2_hidden(sK2(X0,X1),X0) = iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_19,negated_conjecture,
% 2.50/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK3))) ),
% 2.50/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_602,plain,
% 2.50/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK3))) = iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_4,plain,
% 2.50/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.50/0.99      | k6_setfam_1(X1,X0) = k8_setfam_1(X1,X0)
% 2.50/0.99      | k1_xboole_0 = X0 ),
% 2.50/0.99      inference(cnf_transformation,[],[f33]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_615,plain,
% 2.50/0.99      ( k6_setfam_1(X0,X1) = k8_setfam_1(X0,X1)
% 2.50/0.99      | k1_xboole_0 = X1
% 2.50/0.99      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1657,plain,
% 2.50/0.99      ( k6_setfam_1(sK3,sK5) = k8_setfam_1(sK3,sK5) | sK5 = k1_xboole_0 ),
% 2.50/0.99      inference(superposition,[status(thm)],[c_602,c_615]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_13,plain,
% 2.50/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.50/0.99      | k6_setfam_1(X1,X0) = k1_setfam_1(X0) ),
% 2.50/0.99      inference(cnf_transformation,[],[f43]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_608,plain,
% 2.50/0.99      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
% 2.50/0.99      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1152,plain,
% 2.50/0.99      ( k6_setfam_1(sK3,sK5) = k1_setfam_1(sK5) ),
% 2.50/0.99      inference(superposition,[status(thm)],[c_602,c_608]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1660,plain,
% 2.50/0.99      ( k8_setfam_1(sK3,sK5) = k1_setfam_1(sK5) | sK5 = k1_xboole_0 ),
% 2.50/0.99      inference(light_normalisation,[status(thm)],[c_1657,c_1152]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_16,negated_conjecture,
% 2.50/0.99      ( r2_hidden(sK6,sK5) | ~ r2_hidden(sK4,k8_setfam_1(sK3,sK5)) ),
% 2.50/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_605,plain,
% 2.50/0.99      ( r2_hidden(sK6,sK5) = iProver_top
% 2.50/0.99      | r2_hidden(sK4,k8_setfam_1(sK3,sK5)) != iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1810,plain,
% 2.50/0.99      ( sK5 = k1_xboole_0
% 2.50/0.99      | r2_hidden(sK6,sK5) = iProver_top
% 2.50/0.99      | r2_hidden(sK4,k1_setfam_1(sK5)) != iProver_top ),
% 2.50/0.99      inference(superposition,[status(thm)],[c_1660,c_605]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_25,plain,
% 2.50/0.99      ( r2_hidden(sK6,sK5) = iProver_top
% 2.50/0.99      | r2_hidden(sK4,k8_setfam_1(sK3,sK5)) != iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_17,negated_conjecture,
% 2.50/0.99      ( ~ r2_hidden(X0,sK5)
% 2.50/0.99      | r2_hidden(sK4,X0)
% 2.50/0.99      | r2_hidden(sK4,k8_setfam_1(sK3,sK5)) ),
% 2.50/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_604,plain,
% 2.50/0.99      ( r2_hidden(X0,sK5) != iProver_top
% 2.50/0.99      | r2_hidden(sK4,X0) = iProver_top
% 2.50/0.99      | r2_hidden(sK4,k8_setfam_1(sK3,sK5)) = iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1568,plain,
% 2.50/0.99      ( sK5 = k1_xboole_0
% 2.50/0.99      | r2_hidden(X0,k1_setfam_1(sK5)) = iProver_top
% 2.50/0.99      | r2_hidden(sK4,sK2(sK5,X0)) = iProver_top
% 2.50/0.99      | r2_hidden(sK4,k8_setfam_1(sK3,sK5)) = iProver_top ),
% 2.50/0.99      inference(superposition,[status(thm)],[c_610,c_604]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_10,plain,
% 2.50/0.99      ( ~ r2_hidden(X0,sK2(X1,X0))
% 2.50/0.99      | r2_hidden(X0,k1_setfam_1(X1))
% 2.50/0.99      | k1_xboole_0 = X1 ),
% 2.50/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_611,plain,
% 2.50/0.99      ( k1_xboole_0 = X0
% 2.50/0.99      | r2_hidden(X1,sK2(X0,X1)) != iProver_top
% 2.50/0.99      | r2_hidden(X1,k1_setfam_1(X0)) = iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1775,plain,
% 2.50/0.99      ( sK5 = k1_xboole_0
% 2.50/0.99      | r2_hidden(sK4,k8_setfam_1(sK3,sK5)) = iProver_top
% 2.50/0.99      | r2_hidden(sK4,k1_setfam_1(sK5)) = iProver_top ),
% 2.50/0.99      inference(superposition,[status(thm)],[c_1568,c_611]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1960,plain,
% 2.50/0.99      ( r2_hidden(sK6,sK5) = iProver_top | sK5 = k1_xboole_0 ),
% 2.50/0.99      inference(global_propositional_subsumption,
% 2.50/0.99                [status(thm)],
% 2.50/0.99                [c_1810,c_25,c_1775]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1961,plain,
% 2.50/0.99      ( sK5 = k1_xboole_0 | r2_hidden(sK6,sK5) = iProver_top ),
% 2.50/0.99      inference(renaming,[status(thm)],[c_1960]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1968,plain,
% 2.50/0.99      ( sK5 = k1_xboole_0
% 2.50/0.99      | r2_hidden(sK4,k8_setfam_1(sK3,sK5)) = iProver_top
% 2.50/0.99      | r2_hidden(sK4,sK6) = iProver_top ),
% 2.50/0.99      inference(superposition,[status(thm)],[c_1961,c_604]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_15,negated_conjecture,
% 2.50/0.99      ( ~ r2_hidden(sK4,k8_setfam_1(sK3,sK5)) | ~ r2_hidden(sK4,sK6) ),
% 2.50/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_606,plain,
% 2.50/0.99      ( r2_hidden(sK4,k8_setfam_1(sK3,sK5)) != iProver_top
% 2.50/0.99      | r2_hidden(sK4,sK6) != iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1809,plain,
% 2.50/0.99      ( sK5 = k1_xboole_0
% 2.50/0.99      | r2_hidden(sK4,k1_setfam_1(sK5)) != iProver_top
% 2.50/0.99      | r2_hidden(sK4,sK6) != iProver_top ),
% 2.50/0.99      inference(superposition,[status(thm)],[c_1660,c_606]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_26,plain,
% 2.50/0.99      ( r2_hidden(sK4,k8_setfam_1(sK3,sK5)) != iProver_top
% 2.50/0.99      | r2_hidden(sK4,sK6) != iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1953,plain,
% 2.50/0.99      ( sK5 = k1_xboole_0 | r2_hidden(sK4,sK6) != iProver_top ),
% 2.50/0.99      inference(global_propositional_subsumption,
% 2.50/0.99                [status(thm)],
% 2.50/0.99                [c_1809,c_26,c_1775]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_2056,plain,
% 2.50/0.99      ( r2_hidden(sK4,k8_setfam_1(sK3,sK5)) = iProver_top | sK5 = k1_xboole_0 ),
% 2.50/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1968,c_1953]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_2057,plain,
% 2.50/0.99      ( sK5 = k1_xboole_0 | r2_hidden(sK4,k8_setfam_1(sK3,sK5)) = iProver_top ),
% 2.50/0.99      inference(renaming,[status(thm)],[c_2056]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_2062,plain,
% 2.50/0.99      ( sK5 = k1_xboole_0 | r2_hidden(sK4,k1_setfam_1(sK5)) = iProver_top ),
% 2.50/0.99      inference(superposition,[status(thm)],[c_1660,c_2057]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_12,plain,
% 2.50/0.99      ( ~ r2_hidden(X0,X1)
% 2.50/0.99      | r2_hidden(X2,X0)
% 2.50/0.99      | ~ r2_hidden(X2,k1_setfam_1(X1))
% 2.50/0.99      | k1_xboole_0 = X1 ),
% 2.50/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_609,plain,
% 2.50/0.99      ( k1_xboole_0 = X0
% 2.50/0.99      | r2_hidden(X1,X0) != iProver_top
% 2.50/0.99      | r2_hidden(X2,X1) = iProver_top
% 2.50/0.99      | r2_hidden(X2,k1_setfam_1(X0)) != iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_2149,plain,
% 2.50/0.99      ( sK5 = k1_xboole_0
% 2.50/0.99      | r2_hidden(X0,sK5) != iProver_top
% 2.50/0.99      | r2_hidden(sK4,X0) = iProver_top ),
% 2.50/0.99      inference(superposition,[status(thm)],[c_2062,c_609]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_3079,plain,
% 2.50/0.99      ( sK5 = k1_xboole_0
% 2.50/0.99      | r2_hidden(X0,k1_setfam_1(sK5)) = iProver_top
% 2.50/0.99      | r2_hidden(sK4,sK2(sK5,X0)) = iProver_top ),
% 2.50/0.99      inference(superposition,[status(thm)],[c_610,c_2149]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_3078,plain,
% 2.50/0.99      ( sK5 = k1_xboole_0 | r2_hidden(sK4,sK6) = iProver_top ),
% 2.50/0.99      inference(superposition,[status(thm)],[c_1961,c_2149]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_3128,plain,
% 2.50/0.99      ( sK5 = k1_xboole_0 ),
% 2.50/0.99      inference(global_propositional_subsumption,
% 2.50/0.99                [status(thm)],
% 2.50/0.99                [c_3079,c_1953,c_3078]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_3147,plain,
% 2.50/0.99      ( r2_hidden(sK6,k1_xboole_0) = iProver_top
% 2.50/0.99      | r2_hidden(sK4,k8_setfam_1(sK3,k1_xboole_0)) != iProver_top ),
% 2.50/0.99      inference(demodulation,[status(thm)],[c_3128,c_605]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_3,plain,
% 2.50/0.99      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
% 2.50/0.99      | k8_setfam_1(X0,k1_xboole_0) = X0 ),
% 2.50/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_616,plain,
% 2.50/0.99      ( k8_setfam_1(X0,k1_xboole_0) = X0
% 2.50/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_2,plain,
% 2.50/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.50/0.99      inference(cnf_transformation,[],[f32]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_617,plain,
% 2.50/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_639,plain,
% 2.50/0.99      ( k8_setfam_1(X0,k1_xboole_0) = X0 ),
% 2.50/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_616,c_617]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_3152,plain,
% 2.50/0.99      ( r2_hidden(sK6,k1_xboole_0) = iProver_top
% 2.50/0.99      | r2_hidden(sK4,sK3) != iProver_top ),
% 2.50/0.99      inference(demodulation,[status(thm)],[c_3147,c_639]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_18,negated_conjecture,
% 2.50/0.99      ( r2_hidden(sK4,sK3) ),
% 2.50/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_21,plain,
% 2.50/0.99      ( r2_hidden(sK4,sK3) = iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_3487,plain,
% 2.50/0.99      ( r2_hidden(sK6,k1_xboole_0) = iProver_top ),
% 2.50/0.99      inference(global_propositional_subsumption,[status(thm)],[c_3152,c_21]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_0,plain,
% 2.50/0.99      ( ~ r2_hidden(X0,X1) | k2_xboole_0(k1_tarski(X0),X1) = X1 ),
% 2.50/0.99      inference(cnf_transformation,[],[f30]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_618,plain,
% 2.50/0.99      ( k2_xboole_0(k1_tarski(X0),X1) = X1 | r2_hidden(X0,X1) != iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_3492,plain,
% 2.50/0.99      ( k2_xboole_0(k1_tarski(sK6),k1_xboole_0) = k1_xboole_0 ),
% 2.50/0.99      inference(superposition,[status(thm)],[c_3487,c_618]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1,plain,
% 2.50/0.99      ( k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
% 2.50/0.99      inference(cnf_transformation,[],[f31]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_3774,plain,
% 2.50/0.99      ( $false ),
% 2.50/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_3492,c_1]) ).
% 2.50/0.99  
% 2.50/0.99  
% 2.50/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.50/0.99  
% 2.50/0.99  ------                               Statistics
% 2.50/0.99  
% 2.50/0.99  ------ General
% 2.50/0.99  
% 2.50/0.99  abstr_ref_over_cycles:                  0
% 2.50/0.99  abstr_ref_under_cycles:                 0
% 2.50/0.99  gc_basic_clause_elim:                   0
% 2.50/0.99  forced_gc_time:                         0
% 2.50/0.99  parsing_time:                           0.04
% 2.50/0.99  unif_index_cands_time:                  0.
% 2.50/0.99  unif_index_add_time:                    0.
% 2.50/0.99  orderings_time:                         0.
% 2.50/0.99  out_proof_time:                         0.007
% 2.50/0.99  total_time:                             0.159
% 2.50/0.99  num_of_symbols:                         47
% 2.50/0.99  num_of_terms:                           3210
% 2.50/0.99  
% 2.50/0.99  ------ Preprocessing
% 2.50/0.99  
% 2.50/0.99  num_of_splits:                          0
% 2.50/0.99  num_of_split_atoms:                     0
% 2.50/0.99  num_of_reused_defs:                     0
% 2.50/0.99  num_eq_ax_congr_red:                    30
% 2.50/0.99  num_of_sem_filtered_clauses:            1
% 2.50/0.99  num_of_subtypes:                        0
% 2.50/0.99  monotx_restored_types:                  0
% 2.50/0.99  sat_num_of_epr_types:                   0
% 2.50/0.99  sat_num_of_non_cyclic_types:            0
% 2.50/0.99  sat_guarded_non_collapsed_types:        0
% 2.50/0.99  num_pure_diseq_elim:                    0
% 2.50/0.99  simp_replaced_by:                       0
% 2.50/0.99  res_preprocessed:                       93
% 2.50/0.99  prep_upred:                             0
% 2.50/0.99  prep_unflattend:                        0
% 2.50/0.99  smt_new_axioms:                         0
% 2.50/0.99  pred_elim_cands:                        2
% 2.50/0.99  pred_elim:                              0
% 2.50/0.99  pred_elim_cl:                           0
% 2.50/0.99  pred_elim_cycles:                       2
% 2.50/0.99  merged_defs:                            0
% 2.50/0.99  merged_defs_ncl:                        0
% 2.50/0.99  bin_hyper_res:                          0
% 2.50/0.99  prep_cycles:                            4
% 2.50/0.99  pred_elim_time:                         0.
% 2.50/0.99  splitting_time:                         0.
% 2.50/0.99  sem_filter_time:                        0.
% 2.50/0.99  monotx_time:                            0.
% 2.50/0.99  subtype_inf_time:                       0.
% 2.50/0.99  
% 2.50/0.99  ------ Problem properties
% 2.50/0.99  
% 2.50/0.99  clauses:                                19
% 2.50/0.99  conjectures:                            5
% 2.50/0.99  epr:                                    1
% 2.50/0.99  horn:                                   11
% 2.50/0.99  ground:                                 5
% 2.50/0.99  unary:                                  5
% 2.50/0.99  binary:                                 5
% 2.50/0.99  lits:                                   47
% 2.50/0.99  lits_eq:                                16
% 2.50/0.99  fd_pure:                                0
% 2.50/0.99  fd_pseudo:                              0
% 2.50/0.99  fd_cond:                                4
% 2.50/0.99  fd_pseudo_cond:                         3
% 2.50/0.99  ac_symbols:                             0
% 2.50/0.99  
% 2.50/0.99  ------ Propositional Solver
% 2.50/0.99  
% 2.50/0.99  prop_solver_calls:                      27
% 2.50/0.99  prop_fast_solver_calls:                 645
% 2.50/0.99  smt_solver_calls:                       0
% 2.50/0.99  smt_fast_solver_calls:                  0
% 2.50/0.99  prop_num_of_clauses:                    1192
% 2.50/0.99  prop_preprocess_simplified:             3735
% 2.50/0.99  prop_fo_subsumed:                       12
% 2.50/0.99  prop_solver_time:                       0.
% 2.50/0.99  smt_solver_time:                        0.
% 2.50/0.99  smt_fast_solver_time:                   0.
% 2.50/0.99  prop_fast_solver_time:                  0.
% 2.50/0.99  prop_unsat_core_time:                   0.
% 2.50/0.99  
% 2.50/0.99  ------ QBF
% 2.50/0.99  
% 2.50/0.99  qbf_q_res:                              0
% 2.50/0.99  qbf_num_tautologies:                    0
% 2.50/0.99  qbf_prep_cycles:                        0
% 2.50/0.99  
% 2.50/0.99  ------ BMC1
% 2.50/0.99  
% 2.50/0.99  bmc1_current_bound:                     -1
% 2.50/0.99  bmc1_last_solved_bound:                 -1
% 2.50/0.99  bmc1_unsat_core_size:                   -1
% 2.50/0.99  bmc1_unsat_core_parents_size:           -1
% 2.50/0.99  bmc1_merge_next_fun:                    0
% 2.50/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.50/0.99  
% 2.50/0.99  ------ Instantiation
% 2.50/0.99  
% 2.50/0.99  inst_num_of_clauses:                    400
% 2.50/0.99  inst_num_in_passive:                    43
% 2.50/0.99  inst_num_in_active:                     203
% 2.50/0.99  inst_num_in_unprocessed:                154
% 2.50/0.99  inst_num_of_loops:                      270
% 2.50/0.99  inst_num_of_learning_restarts:          0
% 2.50/0.99  inst_num_moves_active_passive:          64
% 2.50/0.99  inst_lit_activity:                      0
% 2.50/0.99  inst_lit_activity_moves:                0
% 2.50/0.99  inst_num_tautologies:                   0
% 2.50/0.99  inst_num_prop_implied:                  0
% 2.50/0.99  inst_num_existing_simplified:           0
% 2.50/0.99  inst_num_eq_res_simplified:             0
% 2.50/0.99  inst_num_child_elim:                    0
% 2.50/0.99  inst_num_of_dismatching_blockings:      102
% 2.50/0.99  inst_num_of_non_proper_insts:           335
% 2.50/0.99  inst_num_of_duplicates:                 0
% 2.50/0.99  inst_inst_num_from_inst_to_res:         0
% 2.50/0.99  inst_dismatching_checking_time:         0.
% 2.50/0.99  
% 2.50/0.99  ------ Resolution
% 2.50/0.99  
% 2.50/0.99  res_num_of_clauses:                     0
% 2.50/0.99  res_num_in_passive:                     0
% 2.50/0.99  res_num_in_active:                      0
% 2.50/0.99  res_num_of_loops:                       97
% 2.50/0.99  res_forward_subset_subsumed:            55
% 2.50/0.99  res_backward_subset_subsumed:           0
% 2.50/0.99  res_forward_subsumed:                   0
% 2.50/0.99  res_backward_subsumed:                  0
% 2.50/0.99  res_forward_subsumption_resolution:     0
% 2.50/0.99  res_backward_subsumption_resolution:    0
% 2.50/0.99  res_clause_to_clause_subsumption:       347
% 2.50/0.99  res_orphan_elimination:                 0
% 2.50/0.99  res_tautology_del:                      33
% 2.50/0.99  res_num_eq_res_simplified:              0
% 2.50/0.99  res_num_sel_changes:                    0
% 2.50/0.99  res_moves_from_active_to_pass:          0
% 2.50/0.99  
% 2.50/0.99  ------ Superposition
% 2.50/0.99  
% 2.50/0.99  sup_time_total:                         0.
% 2.50/0.99  sup_time_generating:                    0.
% 2.50/0.99  sup_time_sim_full:                      0.
% 2.50/0.99  sup_time_sim_immed:                     0.
% 2.50/0.99  
% 2.50/0.99  sup_num_of_clauses:                     64
% 2.50/0.99  sup_num_in_active:                      26
% 2.50/0.99  sup_num_in_passive:                     38
% 2.50/0.99  sup_num_of_loops:                       52
% 2.50/0.99  sup_fw_superposition:                   22
% 2.50/0.99  sup_bw_superposition:                   64
% 2.50/0.99  sup_immediate_simplified:               15
% 2.50/0.99  sup_given_eliminated:                   0
% 2.50/0.99  comparisons_done:                       0
% 2.50/0.99  comparisons_avoided:                    21
% 2.50/0.99  
% 2.50/0.99  ------ Simplifications
% 2.50/0.99  
% 2.50/0.99  
% 2.50/0.99  sim_fw_subset_subsumed:                 0
% 2.50/0.99  sim_bw_subset_subsumed:                 11
% 2.50/0.99  sim_fw_subsumed:                        15
% 2.50/0.99  sim_bw_subsumed:                        0
% 2.50/0.99  sim_fw_subsumption_res:                 2
% 2.50/0.99  sim_bw_subsumption_res:                 0
% 2.50/0.99  sim_tautology_del:                      3
% 2.50/0.99  sim_eq_tautology_del:                   11
% 2.50/0.99  sim_eq_res_simp:                        1
% 2.50/0.99  sim_fw_demodulated:                     10
% 2.50/0.99  sim_bw_demodulated:                     18
% 2.50/0.99  sim_light_normalised:                   7
% 2.50/0.99  sim_joinable_taut:                      0
% 2.50/0.99  sim_joinable_simp:                      0
% 2.50/0.99  sim_ac_normalised:                      0
% 2.50/0.99  sim_smt_subsumption:                    0
% 2.50/0.99  
%------------------------------------------------------------------------------
