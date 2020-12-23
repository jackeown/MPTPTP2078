%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:42:25 EST 2020

% Result     : Theorem 2.78s
% Output     : CNFRefutation 2.78s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 759 expanded)
%              Number of clauses        :   68 ( 218 expanded)
%              Number of leaves         :   15 ( 181 expanded)
%              Depth                    :   22
%              Number of atoms          :  392 (4505 expanded)
%              Number of equality atoms :  175 (1076 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
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

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f4])).

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
    inference(nnf_transformation,[],[f11])).

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

fof(f35,plain,(
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
    inference(equality_resolution,[],[f35])).

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

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f47,plain,(
    ! [X4] :
      ( r2_hidden(sK4,X4)
      | ~ r2_hidden(X4,sK5)
      | r2_hidden(sK4,k8_setfam_1(sK3,sK5)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f36,plain,(
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
    inference(equality_resolution,[],[f36])).

fof(f34,plain,(
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
    inference(equality_resolution,[],[f34])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f48,plain,
    ( r2_hidden(sK6,sK5)
    | ~ r2_hidden(sK4,k8_setfam_1(sK3,sK5)) ),
    inference(cnf_transformation,[],[f29])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f49,plain,
    ( ~ r2_hidden(sK4,sK6)
    | ~ r2_hidden(sK4,k8_setfam_1(sK3,sK5)) ),
    inference(cnf_transformation,[],[f29])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f50,plain,(
    ! [X0] :
      ( k8_setfam_1(X0,k1_xboole_0) = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f33])).

fof(f46,plain,(
    r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_10,plain,
    ( r2_hidden(X0,k1_setfam_1(X1))
    | r2_hidden(sK2(X1,X0),X1)
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_629,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(X1,k1_setfam_1(X0)) = iProver_top
    | r2_hidden(sK2(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK3))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_621,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k6_setfam_1(X1,X0) = k8_setfam_1(X1,X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_634,plain,
    ( k6_setfam_1(X0,X1) = k8_setfam_1(X0,X1)
    | k1_xboole_0 = X1
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1602,plain,
    ( k6_setfam_1(sK3,sK5) = k8_setfam_1(sK3,sK5)
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_621,c_634])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k6_setfam_1(X1,X0) = k1_setfam_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_627,plain,
    ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1104,plain,
    ( k6_setfam_1(sK3,sK5) = k1_setfam_1(sK5) ),
    inference(superposition,[status(thm)],[c_621,c_627])).

cnf(c_1605,plain,
    ( k8_setfam_1(sK3,sK5) = k1_setfam_1(sK5)
    | sK5 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1602,c_1104])).

cnf(c_17,negated_conjecture,
    ( ~ r2_hidden(X0,sK5)
    | r2_hidden(sK4,X0)
    | r2_hidden(sK4,k8_setfam_1(sK3,sK5)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_623,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(sK4,X0) = iProver_top
    | r2_hidden(sK4,k8_setfam_1(sK3,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1176,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(X0,k1_setfam_1(sK5)) = iProver_top
    | r2_hidden(sK4,sK2(sK5,X0)) = iProver_top
    | r2_hidden(sK4,k8_setfam_1(sK3,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_629,c_623])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,sK2(X1,X0))
    | r2_hidden(X0,k1_setfam_1(X1))
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_630,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(X1,sK2(X0,X1)) != iProver_top
    | r2_hidden(X1,k1_setfam_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1373,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK4,k8_setfam_1(sK3,sK5)) = iProver_top
    | r2_hidden(sK4,k1_setfam_1(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1176,c_630])).

cnf(c_2231,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK4,k1_setfam_1(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1605,c_1373])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X0)
    | ~ r2_hidden(X2,k1_setfam_1(X1))
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_628,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(X1,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top
    | r2_hidden(X2,k1_setfam_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_19019,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(sK4,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2231,c_628])).

cnf(c_1,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_58,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_60,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_58])).

cnf(c_334,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_339,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_334])).

cnf(c_332,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_345,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_332])).

cnf(c_16,negated_conjecture,
    ( r2_hidden(sK6,sK5)
    | ~ r2_hidden(sK4,k8_setfam_1(sK3,sK5)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_624,plain,
    ( r2_hidden(sK6,sK5) = iProver_top
    | r2_hidden(sK4,k8_setfam_1(sK3,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1380,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK6,sK5) = iProver_top
    | r2_hidden(sK4,k1_setfam_1(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1373,c_624])).

cnf(c_1530,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(sK6,sK5) = iProver_top
    | r2_hidden(sK4,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1380,c_628])).

cnf(c_22,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(sK4,X0) = iProver_top
    | r2_hidden(sK4,k8_setfam_1(sK3,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_25,plain,
    ( r2_hidden(sK6,sK5) = iProver_top
    | r2_hidden(sK4,k8_setfam_1(sK3,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2666,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(sK6,sK5) = iProver_top
    | r2_hidden(sK4,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1530,c_22,c_25])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_201,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_14])).

cnf(c_202,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(unflattening,[status(thm)],[c_201])).

cnf(c_2915,plain,
    ( ~ r2_hidden(sK6,sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_202])).

cnf(c_2916,plain,
    ( r2_hidden(sK6,sK5) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2915])).

cnf(c_335,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_786,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | X1 != k1_zfmisc_1(X2)
    | X0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_335])).

cnf(c_1149,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | X0 != k1_xboole_0
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_786])).

cnf(c_5057,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0)
    | sK5 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1149])).

cnf(c_5059,plain,
    ( k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0)
    | sK5 != k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5057])).

cnf(c_19082,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(sK4,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19019,c_60,c_339,c_345,c_2666,c_2916,c_5059])).

cnf(c_19105,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(X0,k1_setfam_1(sK5)) = iProver_top
    | r2_hidden(sK4,sK2(sK5,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_629,c_19082])).

cnf(c_15,negated_conjecture,
    ( ~ r2_hidden(sK4,k8_setfam_1(sK3,sK5))
    | ~ r2_hidden(sK4,sK6) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_625,plain,
    ( r2_hidden(sK4,k8_setfam_1(sK3,sK5)) != iProver_top
    | r2_hidden(sK4,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2232,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK4,k1_setfam_1(sK5)) != iProver_top
    | r2_hidden(sK4,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1605,c_625])).

cnf(c_2251,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK4,sK6) != iProver_top ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2231,c_2232])).

cnf(c_2233,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK6,sK5) = iProver_top
    | r2_hidden(sK4,k1_setfam_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1605,c_624])).

cnf(c_2250,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK6,sK5) = iProver_top ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2231,c_2233])).

cnf(c_19104,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK4,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_2250,c_19082])).

cnf(c_19462,plain,
    ( sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_19105,c_2251,c_19104])).

cnf(c_19534,plain,
    ( r2_hidden(sK6,k1_xboole_0) = iProver_top
    | r2_hidden(sK4,k8_setfam_1(sK3,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_19462,c_624])).

cnf(c_2,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
    | k8_setfam_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_635,plain,
    ( k8_setfam_1(X0,k1_xboole_0) = X0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_636,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_655,plain,
    ( k8_setfam_1(X0,k1_xboole_0) = X0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_635,c_636])).

cnf(c_19539,plain,
    ( r2_hidden(sK6,k1_xboole_0) = iProver_top
    | r2_hidden(sK4,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_19534,c_655])).

cnf(c_18,negated_conjecture,
    ( r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_21,plain,
    ( r2_hidden(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_20031,plain,
    ( r2_hidden(sK6,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19539,c_21])).

cnf(c_620,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_202])).

cnf(c_1096,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_636,c_620])).

cnf(c_20036,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_20031,c_1096])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:19:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.78/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/0.99  
% 2.78/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.78/0.99  
% 2.78/0.99  ------  iProver source info
% 2.78/0.99  
% 2.78/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.78/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.78/0.99  git: non_committed_changes: false
% 2.78/0.99  git: last_make_outside_of_git: false
% 2.78/0.99  
% 2.78/0.99  ------ 
% 2.78/0.99  
% 2.78/0.99  ------ Input Options
% 2.78/0.99  
% 2.78/0.99  --out_options                           all
% 2.78/0.99  --tptp_safe_out                         true
% 2.78/0.99  --problem_path                          ""
% 2.78/0.99  --include_path                          ""
% 2.78/0.99  --clausifier                            res/vclausify_rel
% 2.78/0.99  --clausifier_options                    --mode clausify
% 2.78/0.99  --stdin                                 false
% 2.78/0.99  --stats_out                             all
% 2.78/0.99  
% 2.78/0.99  ------ General Options
% 2.78/0.99  
% 2.78/0.99  --fof                                   false
% 2.78/0.99  --time_out_real                         305.
% 2.78/0.99  --time_out_virtual                      -1.
% 2.78/0.99  --symbol_type_check                     false
% 2.78/0.99  --clausify_out                          false
% 2.78/0.99  --sig_cnt_out                           false
% 2.78/0.99  --trig_cnt_out                          false
% 2.78/0.99  --trig_cnt_out_tolerance                1.
% 2.78/0.99  --trig_cnt_out_sk_spl                   false
% 2.78/0.99  --abstr_cl_out                          false
% 2.78/0.99  
% 2.78/0.99  ------ Global Options
% 2.78/0.99  
% 2.78/0.99  --schedule                              default
% 2.78/0.99  --add_important_lit                     false
% 2.78/0.99  --prop_solver_per_cl                    1000
% 2.78/0.99  --min_unsat_core                        false
% 2.78/0.99  --soft_assumptions                      false
% 2.78/0.99  --soft_lemma_size                       3
% 2.78/0.99  --prop_impl_unit_size                   0
% 2.78/0.99  --prop_impl_unit                        []
% 2.78/0.99  --share_sel_clauses                     true
% 2.78/0.99  --reset_solvers                         false
% 2.78/0.99  --bc_imp_inh                            [conj_cone]
% 2.78/0.99  --conj_cone_tolerance                   3.
% 2.78/0.99  --extra_neg_conj                        none
% 2.78/0.99  --large_theory_mode                     true
% 2.78/0.99  --prolific_symb_bound                   200
% 2.78/0.99  --lt_threshold                          2000
% 2.78/0.99  --clause_weak_htbl                      true
% 2.78/0.99  --gc_record_bc_elim                     false
% 2.78/0.99  
% 2.78/0.99  ------ Preprocessing Options
% 2.78/0.99  
% 2.78/0.99  --preprocessing_flag                    true
% 2.78/0.99  --time_out_prep_mult                    0.1
% 2.78/0.99  --splitting_mode                        input
% 2.78/0.99  --splitting_grd                         true
% 2.78/0.99  --splitting_cvd                         false
% 2.78/0.99  --splitting_cvd_svl                     false
% 2.78/0.99  --splitting_nvd                         32
% 2.78/0.99  --sub_typing                            true
% 2.78/0.99  --prep_gs_sim                           true
% 2.78/0.99  --prep_unflatten                        true
% 2.78/0.99  --prep_res_sim                          true
% 2.78/0.99  --prep_upred                            true
% 2.78/0.99  --prep_sem_filter                       exhaustive
% 2.78/0.99  --prep_sem_filter_out                   false
% 2.78/0.99  --pred_elim                             true
% 2.78/0.99  --res_sim_input                         true
% 2.78/0.99  --eq_ax_congr_red                       true
% 2.78/0.99  --pure_diseq_elim                       true
% 2.78/0.99  --brand_transform                       false
% 2.78/0.99  --non_eq_to_eq                          false
% 2.78/0.99  --prep_def_merge                        true
% 2.78/0.99  --prep_def_merge_prop_impl              false
% 2.78/0.99  --prep_def_merge_mbd                    true
% 2.78/0.99  --prep_def_merge_tr_red                 false
% 2.78/0.99  --prep_def_merge_tr_cl                  false
% 2.78/0.99  --smt_preprocessing                     true
% 2.78/0.99  --smt_ac_axioms                         fast
% 2.78/0.99  --preprocessed_out                      false
% 2.78/0.99  --preprocessed_stats                    false
% 2.78/0.99  
% 2.78/0.99  ------ Abstraction refinement Options
% 2.78/0.99  
% 2.78/0.99  --abstr_ref                             []
% 2.78/0.99  --abstr_ref_prep                        false
% 2.78/0.99  --abstr_ref_until_sat                   false
% 2.78/0.99  --abstr_ref_sig_restrict                funpre
% 2.78/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.78/0.99  --abstr_ref_under                       []
% 2.78/0.99  
% 2.78/0.99  ------ SAT Options
% 2.78/0.99  
% 2.78/0.99  --sat_mode                              false
% 2.78/0.99  --sat_fm_restart_options                ""
% 2.78/0.99  --sat_gr_def                            false
% 2.78/0.99  --sat_epr_types                         true
% 2.78/0.99  --sat_non_cyclic_types                  false
% 2.78/0.99  --sat_finite_models                     false
% 2.78/0.99  --sat_fm_lemmas                         false
% 2.78/0.99  --sat_fm_prep                           false
% 2.78/0.99  --sat_fm_uc_incr                        true
% 2.78/0.99  --sat_out_model                         small
% 2.78/0.99  --sat_out_clauses                       false
% 2.78/0.99  
% 2.78/0.99  ------ QBF Options
% 2.78/0.99  
% 2.78/0.99  --qbf_mode                              false
% 2.78/0.99  --qbf_elim_univ                         false
% 2.78/0.99  --qbf_dom_inst                          none
% 2.78/0.99  --qbf_dom_pre_inst                      false
% 2.78/0.99  --qbf_sk_in                             false
% 2.78/0.99  --qbf_pred_elim                         true
% 2.78/0.99  --qbf_split                             512
% 2.78/0.99  
% 2.78/0.99  ------ BMC1 Options
% 2.78/0.99  
% 2.78/0.99  --bmc1_incremental                      false
% 2.78/0.99  --bmc1_axioms                           reachable_all
% 2.78/0.99  --bmc1_min_bound                        0
% 2.78/0.99  --bmc1_max_bound                        -1
% 2.78/0.99  --bmc1_max_bound_default                -1
% 2.78/0.99  --bmc1_symbol_reachability              true
% 2.78/0.99  --bmc1_property_lemmas                  false
% 2.78/0.99  --bmc1_k_induction                      false
% 2.78/0.99  --bmc1_non_equiv_states                 false
% 2.78/0.99  --bmc1_deadlock                         false
% 2.78/0.99  --bmc1_ucm                              false
% 2.78/0.99  --bmc1_add_unsat_core                   none
% 2.78/0.99  --bmc1_unsat_core_children              false
% 2.78/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.78/0.99  --bmc1_out_stat                         full
% 2.78/0.99  --bmc1_ground_init                      false
% 2.78/0.99  --bmc1_pre_inst_next_state              false
% 2.78/0.99  --bmc1_pre_inst_state                   false
% 2.78/0.99  --bmc1_pre_inst_reach_state             false
% 2.78/0.99  --bmc1_out_unsat_core                   false
% 2.78/0.99  --bmc1_aig_witness_out                  false
% 2.78/0.99  --bmc1_verbose                          false
% 2.78/0.99  --bmc1_dump_clauses_tptp                false
% 2.78/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.78/0.99  --bmc1_dump_file                        -
% 2.78/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.78/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.78/0.99  --bmc1_ucm_extend_mode                  1
% 2.78/0.99  --bmc1_ucm_init_mode                    2
% 2.78/0.99  --bmc1_ucm_cone_mode                    none
% 2.78/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.78/0.99  --bmc1_ucm_relax_model                  4
% 2.78/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.78/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.78/0.99  --bmc1_ucm_layered_model                none
% 2.78/0.99  --bmc1_ucm_max_lemma_size               10
% 2.78/0.99  
% 2.78/0.99  ------ AIG Options
% 2.78/0.99  
% 2.78/0.99  --aig_mode                              false
% 2.78/0.99  
% 2.78/0.99  ------ Instantiation Options
% 2.78/0.99  
% 2.78/0.99  --instantiation_flag                    true
% 2.78/0.99  --inst_sos_flag                         false
% 2.78/0.99  --inst_sos_phase                        true
% 2.78/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.78/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.78/0.99  --inst_lit_sel_side                     num_symb
% 2.78/0.99  --inst_solver_per_active                1400
% 2.78/0.99  --inst_solver_calls_frac                1.
% 2.78/0.99  --inst_passive_queue_type               priority_queues
% 2.78/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.78/0.99  --inst_passive_queues_freq              [25;2]
% 2.78/0.99  --inst_dismatching                      true
% 2.78/0.99  --inst_eager_unprocessed_to_passive     true
% 2.78/0.99  --inst_prop_sim_given                   true
% 2.78/0.99  --inst_prop_sim_new                     false
% 2.78/0.99  --inst_subs_new                         false
% 2.78/0.99  --inst_eq_res_simp                      false
% 2.78/0.99  --inst_subs_given                       false
% 2.78/0.99  --inst_orphan_elimination               true
% 2.78/0.99  --inst_learning_loop_flag               true
% 2.78/0.99  --inst_learning_start                   3000
% 2.78/0.99  --inst_learning_factor                  2
% 2.78/0.99  --inst_start_prop_sim_after_learn       3
% 2.78/0.99  --inst_sel_renew                        solver
% 2.78/0.99  --inst_lit_activity_flag                true
% 2.78/0.99  --inst_restr_to_given                   false
% 2.78/0.99  --inst_activity_threshold               500
% 2.78/0.99  --inst_out_proof                        true
% 2.78/0.99  
% 2.78/0.99  ------ Resolution Options
% 2.78/0.99  
% 2.78/0.99  --resolution_flag                       true
% 2.78/0.99  --res_lit_sel                           adaptive
% 2.78/0.99  --res_lit_sel_side                      none
% 2.78/0.99  --res_ordering                          kbo
% 2.78/0.99  --res_to_prop_solver                    active
% 2.78/0.99  --res_prop_simpl_new                    false
% 2.78/0.99  --res_prop_simpl_given                  true
% 2.78/0.99  --res_passive_queue_type                priority_queues
% 2.78/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.78/0.99  --res_passive_queues_freq               [15;5]
% 2.78/0.99  --res_forward_subs                      full
% 2.78/0.99  --res_backward_subs                     full
% 2.78/0.99  --res_forward_subs_resolution           true
% 2.78/0.99  --res_backward_subs_resolution          true
% 2.78/0.99  --res_orphan_elimination                true
% 2.78/0.99  --res_time_limit                        2.
% 2.78/0.99  --res_out_proof                         true
% 2.78/0.99  
% 2.78/0.99  ------ Superposition Options
% 2.78/0.99  
% 2.78/0.99  --superposition_flag                    true
% 2.78/0.99  --sup_passive_queue_type                priority_queues
% 2.78/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.78/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.78/0.99  --demod_completeness_check              fast
% 2.78/0.99  --demod_use_ground                      true
% 2.78/0.99  --sup_to_prop_solver                    passive
% 2.78/0.99  --sup_prop_simpl_new                    true
% 2.78/0.99  --sup_prop_simpl_given                  true
% 2.78/0.99  --sup_fun_splitting                     false
% 2.78/0.99  --sup_smt_interval                      50000
% 2.78/0.99  
% 2.78/0.99  ------ Superposition Simplification Setup
% 2.78/0.99  
% 2.78/0.99  --sup_indices_passive                   []
% 2.78/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.78/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/0.99  --sup_full_bw                           [BwDemod]
% 2.78/0.99  --sup_immed_triv                        [TrivRules]
% 2.78/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.78/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/0.99  --sup_immed_bw_main                     []
% 2.78/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.78/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.78/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.78/0.99  
% 2.78/0.99  ------ Combination Options
% 2.78/0.99  
% 2.78/0.99  --comb_res_mult                         3
% 2.78/0.99  --comb_sup_mult                         2
% 2.78/0.99  --comb_inst_mult                        10
% 2.78/0.99  
% 2.78/0.99  ------ Debug Options
% 2.78/0.99  
% 2.78/0.99  --dbg_backtrace                         false
% 2.78/0.99  --dbg_dump_prop_clauses                 false
% 2.78/0.99  --dbg_dump_prop_clauses_file            -
% 2.78/0.99  --dbg_out_stat                          false
% 2.78/0.99  ------ Parsing...
% 2.78/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.78/0.99  
% 2.78/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.78/0.99  
% 2.78/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.78/0.99  
% 2.78/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.78/0.99  ------ Proving...
% 2.78/0.99  ------ Problem Properties 
% 2.78/0.99  
% 2.78/0.99  
% 2.78/0.99  clauses                                 18
% 2.78/0.99  conjectures                             5
% 2.78/0.99  EPR                                     1
% 2.78/0.99  Horn                                    10
% 2.78/0.99  unary                                   4
% 2.78/0.99  binary                                  5
% 2.78/0.99  lits                                    46
% 2.78/0.99  lits eq                                 14
% 2.78/0.99  fd_pure                                 0
% 2.78/0.99  fd_pseudo                               0
% 2.78/0.99  fd_cond                                 4
% 2.78/0.99  fd_pseudo_cond                          3
% 2.78/0.99  AC symbols                              0
% 2.78/0.99  
% 2.78/0.99  ------ Schedule dynamic 5 is on 
% 2.78/0.99  
% 2.78/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.78/0.99  
% 2.78/0.99  
% 2.78/0.99  ------ 
% 2.78/0.99  Current options:
% 2.78/0.99  ------ 
% 2.78/0.99  
% 2.78/0.99  ------ Input Options
% 2.78/0.99  
% 2.78/0.99  --out_options                           all
% 2.78/0.99  --tptp_safe_out                         true
% 2.78/0.99  --problem_path                          ""
% 2.78/0.99  --include_path                          ""
% 2.78/0.99  --clausifier                            res/vclausify_rel
% 2.78/0.99  --clausifier_options                    --mode clausify
% 2.78/0.99  --stdin                                 false
% 2.78/0.99  --stats_out                             all
% 2.78/0.99  
% 2.78/0.99  ------ General Options
% 2.78/0.99  
% 2.78/0.99  --fof                                   false
% 2.78/0.99  --time_out_real                         305.
% 2.78/0.99  --time_out_virtual                      -1.
% 2.78/0.99  --symbol_type_check                     false
% 2.78/0.99  --clausify_out                          false
% 2.78/0.99  --sig_cnt_out                           false
% 2.78/0.99  --trig_cnt_out                          false
% 2.78/0.99  --trig_cnt_out_tolerance                1.
% 2.78/0.99  --trig_cnt_out_sk_spl                   false
% 2.78/0.99  --abstr_cl_out                          false
% 2.78/0.99  
% 2.78/0.99  ------ Global Options
% 2.78/0.99  
% 2.78/0.99  --schedule                              default
% 2.78/0.99  --add_important_lit                     false
% 2.78/0.99  --prop_solver_per_cl                    1000
% 2.78/0.99  --min_unsat_core                        false
% 2.78/0.99  --soft_assumptions                      false
% 2.78/0.99  --soft_lemma_size                       3
% 2.78/0.99  --prop_impl_unit_size                   0
% 2.78/0.99  --prop_impl_unit                        []
% 2.78/0.99  --share_sel_clauses                     true
% 2.78/0.99  --reset_solvers                         false
% 2.78/0.99  --bc_imp_inh                            [conj_cone]
% 2.78/0.99  --conj_cone_tolerance                   3.
% 2.78/0.99  --extra_neg_conj                        none
% 2.78/0.99  --large_theory_mode                     true
% 2.78/0.99  --prolific_symb_bound                   200
% 2.78/0.99  --lt_threshold                          2000
% 2.78/0.99  --clause_weak_htbl                      true
% 2.78/0.99  --gc_record_bc_elim                     false
% 2.78/0.99  
% 2.78/0.99  ------ Preprocessing Options
% 2.78/0.99  
% 2.78/0.99  --preprocessing_flag                    true
% 2.78/0.99  --time_out_prep_mult                    0.1
% 2.78/0.99  --splitting_mode                        input
% 2.78/0.99  --splitting_grd                         true
% 2.78/0.99  --splitting_cvd                         false
% 2.78/0.99  --splitting_cvd_svl                     false
% 2.78/0.99  --splitting_nvd                         32
% 2.78/0.99  --sub_typing                            true
% 2.78/0.99  --prep_gs_sim                           true
% 2.78/0.99  --prep_unflatten                        true
% 2.78/0.99  --prep_res_sim                          true
% 2.78/0.99  --prep_upred                            true
% 2.78/0.99  --prep_sem_filter                       exhaustive
% 2.78/0.99  --prep_sem_filter_out                   false
% 2.78/0.99  --pred_elim                             true
% 2.78/0.99  --res_sim_input                         true
% 2.78/0.99  --eq_ax_congr_red                       true
% 2.78/0.99  --pure_diseq_elim                       true
% 2.78/0.99  --brand_transform                       false
% 2.78/0.99  --non_eq_to_eq                          false
% 2.78/0.99  --prep_def_merge                        true
% 2.78/0.99  --prep_def_merge_prop_impl              false
% 2.78/0.99  --prep_def_merge_mbd                    true
% 2.78/0.99  --prep_def_merge_tr_red                 false
% 2.78/0.99  --prep_def_merge_tr_cl                  false
% 2.78/0.99  --smt_preprocessing                     true
% 2.78/0.99  --smt_ac_axioms                         fast
% 2.78/0.99  --preprocessed_out                      false
% 2.78/0.99  --preprocessed_stats                    false
% 2.78/0.99  
% 2.78/0.99  ------ Abstraction refinement Options
% 2.78/0.99  
% 2.78/0.99  --abstr_ref                             []
% 2.78/0.99  --abstr_ref_prep                        false
% 2.78/0.99  --abstr_ref_until_sat                   false
% 2.78/0.99  --abstr_ref_sig_restrict                funpre
% 2.78/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.78/0.99  --abstr_ref_under                       []
% 2.78/0.99  
% 2.78/0.99  ------ SAT Options
% 2.78/0.99  
% 2.78/0.99  --sat_mode                              false
% 2.78/0.99  --sat_fm_restart_options                ""
% 2.78/0.99  --sat_gr_def                            false
% 2.78/0.99  --sat_epr_types                         true
% 2.78/0.99  --sat_non_cyclic_types                  false
% 2.78/0.99  --sat_finite_models                     false
% 2.78/0.99  --sat_fm_lemmas                         false
% 2.78/0.99  --sat_fm_prep                           false
% 2.78/0.99  --sat_fm_uc_incr                        true
% 2.78/0.99  --sat_out_model                         small
% 2.78/0.99  --sat_out_clauses                       false
% 2.78/0.99  
% 2.78/0.99  ------ QBF Options
% 2.78/0.99  
% 2.78/0.99  --qbf_mode                              false
% 2.78/0.99  --qbf_elim_univ                         false
% 2.78/0.99  --qbf_dom_inst                          none
% 2.78/0.99  --qbf_dom_pre_inst                      false
% 2.78/0.99  --qbf_sk_in                             false
% 2.78/0.99  --qbf_pred_elim                         true
% 2.78/0.99  --qbf_split                             512
% 2.78/0.99  
% 2.78/0.99  ------ BMC1 Options
% 2.78/0.99  
% 2.78/0.99  --bmc1_incremental                      false
% 2.78/0.99  --bmc1_axioms                           reachable_all
% 2.78/0.99  --bmc1_min_bound                        0
% 2.78/0.99  --bmc1_max_bound                        -1
% 2.78/0.99  --bmc1_max_bound_default                -1
% 2.78/0.99  --bmc1_symbol_reachability              true
% 2.78/0.99  --bmc1_property_lemmas                  false
% 2.78/0.99  --bmc1_k_induction                      false
% 2.78/0.99  --bmc1_non_equiv_states                 false
% 2.78/0.99  --bmc1_deadlock                         false
% 2.78/0.99  --bmc1_ucm                              false
% 2.78/0.99  --bmc1_add_unsat_core                   none
% 2.78/0.99  --bmc1_unsat_core_children              false
% 2.78/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.78/0.99  --bmc1_out_stat                         full
% 2.78/0.99  --bmc1_ground_init                      false
% 2.78/0.99  --bmc1_pre_inst_next_state              false
% 2.78/0.99  --bmc1_pre_inst_state                   false
% 2.78/0.99  --bmc1_pre_inst_reach_state             false
% 2.78/0.99  --bmc1_out_unsat_core                   false
% 2.78/0.99  --bmc1_aig_witness_out                  false
% 2.78/0.99  --bmc1_verbose                          false
% 2.78/0.99  --bmc1_dump_clauses_tptp                false
% 2.78/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.78/0.99  --bmc1_dump_file                        -
% 2.78/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.78/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.78/0.99  --bmc1_ucm_extend_mode                  1
% 2.78/0.99  --bmc1_ucm_init_mode                    2
% 2.78/0.99  --bmc1_ucm_cone_mode                    none
% 2.78/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.78/0.99  --bmc1_ucm_relax_model                  4
% 2.78/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.78/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.78/0.99  --bmc1_ucm_layered_model                none
% 2.78/0.99  --bmc1_ucm_max_lemma_size               10
% 2.78/0.99  
% 2.78/0.99  ------ AIG Options
% 2.78/0.99  
% 2.78/0.99  --aig_mode                              false
% 2.78/0.99  
% 2.78/0.99  ------ Instantiation Options
% 2.78/0.99  
% 2.78/0.99  --instantiation_flag                    true
% 2.78/0.99  --inst_sos_flag                         false
% 2.78/0.99  --inst_sos_phase                        true
% 2.78/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.78/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.78/0.99  --inst_lit_sel_side                     none
% 2.78/0.99  --inst_solver_per_active                1400
% 2.78/0.99  --inst_solver_calls_frac                1.
% 2.78/0.99  --inst_passive_queue_type               priority_queues
% 2.78/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.78/0.99  --inst_passive_queues_freq              [25;2]
% 2.78/0.99  --inst_dismatching                      true
% 2.78/0.99  --inst_eager_unprocessed_to_passive     true
% 2.78/0.99  --inst_prop_sim_given                   true
% 2.78/0.99  --inst_prop_sim_new                     false
% 2.78/0.99  --inst_subs_new                         false
% 2.78/0.99  --inst_eq_res_simp                      false
% 2.78/0.99  --inst_subs_given                       false
% 2.78/0.99  --inst_orphan_elimination               true
% 2.78/0.99  --inst_learning_loop_flag               true
% 2.78/0.99  --inst_learning_start                   3000
% 2.78/0.99  --inst_learning_factor                  2
% 2.78/0.99  --inst_start_prop_sim_after_learn       3
% 2.78/0.99  --inst_sel_renew                        solver
% 2.78/0.99  --inst_lit_activity_flag                true
% 2.78/0.99  --inst_restr_to_given                   false
% 2.78/0.99  --inst_activity_threshold               500
% 2.78/0.99  --inst_out_proof                        true
% 2.78/0.99  
% 2.78/0.99  ------ Resolution Options
% 2.78/0.99  
% 2.78/0.99  --resolution_flag                       false
% 2.78/0.99  --res_lit_sel                           adaptive
% 2.78/0.99  --res_lit_sel_side                      none
% 2.78/0.99  --res_ordering                          kbo
% 2.78/0.99  --res_to_prop_solver                    active
% 2.78/0.99  --res_prop_simpl_new                    false
% 2.78/0.99  --res_prop_simpl_given                  true
% 2.78/0.99  --res_passive_queue_type                priority_queues
% 2.78/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.78/0.99  --res_passive_queues_freq               [15;5]
% 2.78/0.99  --res_forward_subs                      full
% 2.78/0.99  --res_backward_subs                     full
% 2.78/0.99  --res_forward_subs_resolution           true
% 2.78/0.99  --res_backward_subs_resolution          true
% 2.78/0.99  --res_orphan_elimination                true
% 2.78/0.99  --res_time_limit                        2.
% 2.78/0.99  --res_out_proof                         true
% 2.78/0.99  
% 2.78/0.99  ------ Superposition Options
% 2.78/0.99  
% 2.78/0.99  --superposition_flag                    true
% 2.78/0.99  --sup_passive_queue_type                priority_queues
% 2.78/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.78/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.78/0.99  --demod_completeness_check              fast
% 2.78/0.99  --demod_use_ground                      true
% 2.78/0.99  --sup_to_prop_solver                    passive
% 2.78/0.99  --sup_prop_simpl_new                    true
% 2.78/0.99  --sup_prop_simpl_given                  true
% 2.78/0.99  --sup_fun_splitting                     false
% 2.78/0.99  --sup_smt_interval                      50000
% 2.78/0.99  
% 2.78/0.99  ------ Superposition Simplification Setup
% 2.78/0.99  
% 2.78/0.99  --sup_indices_passive                   []
% 2.78/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.78/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/0.99  --sup_full_bw                           [BwDemod]
% 2.78/0.99  --sup_immed_triv                        [TrivRules]
% 2.78/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.78/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/0.99  --sup_immed_bw_main                     []
% 2.78/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.78/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.78/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.78/0.99  
% 2.78/0.99  ------ Combination Options
% 2.78/0.99  
% 2.78/0.99  --comb_res_mult                         3
% 2.78/0.99  --comb_sup_mult                         2
% 2.78/0.99  --comb_inst_mult                        10
% 2.78/0.99  
% 2.78/0.99  ------ Debug Options
% 2.78/0.99  
% 2.78/0.99  --dbg_backtrace                         false
% 2.78/0.99  --dbg_dump_prop_clauses                 false
% 2.78/0.99  --dbg_dump_prop_clauses_file            -
% 2.78/0.99  --dbg_out_stat                          false
% 2.78/0.99  
% 2.78/0.99  
% 2.78/0.99  
% 2.78/0.99  
% 2.78/0.99  ------ Proving...
% 2.78/0.99  
% 2.78/0.99  
% 2.78/0.99  % SZS status Theorem for theBenchmark.p
% 2.78/0.99  
% 2.78/0.99   Resolution empty clause
% 2.78/0.99  
% 2.78/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.78/0.99  
% 2.78/0.99  fof(f4,axiom,(
% 2.78/0.99    ! [X0,X1] : ((k1_xboole_0 = X0 => (k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1)) & (k1_xboole_0 != X0 => (k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X3,X0) => r2_hidden(X2,X3))))))),
% 2.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/0.99  
% 2.78/0.99  fof(f11,plain,(
% 2.78/0.99    ! [X0,X1] : (((k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1) | k1_xboole_0 != X0) & ((k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)))) | k1_xboole_0 = X0))),
% 2.78/0.99    inference(ennf_transformation,[],[f4])).
% 2.78/0.99  
% 2.78/0.99  fof(f18,plain,(
% 2.78/0.99    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | ? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0))) & (! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)) | ~r2_hidden(X2,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 2.78/0.99    inference(nnf_transformation,[],[f11])).
% 2.78/0.99  
% 2.78/0.99  fof(f19,plain,(
% 2.78/0.99    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | ? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X4] : (r2_hidden(X2,X4) | ~r2_hidden(X4,X0)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ? [X6] : (~r2_hidden(X5,X6) & r2_hidden(X6,X0))) & (! [X7] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0)) | ~r2_hidden(X5,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 2.78/0.99    inference(rectify,[],[f18])).
% 2.78/0.99  
% 2.78/0.99  fof(f22,plain,(
% 2.78/0.99    ! [X5,X0] : (? [X6] : (~r2_hidden(X5,X6) & r2_hidden(X6,X0)) => (~r2_hidden(X5,sK2(X0,X5)) & r2_hidden(sK2(X0,X5),X0)))),
% 2.78/0.99    introduced(choice_axiom,[])).
% 2.78/0.99  
% 2.78/0.99  fof(f21,plain,(
% 2.78/0.99    ( ! [X2] : (! [X1,X0] : (? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) => (~r2_hidden(X2,sK1(X0,X1)) & r2_hidden(sK1(X0,X1),X0)))) )),
% 2.78/0.99    introduced(choice_axiom,[])).
% 2.78/0.99  
% 2.78/0.99  fof(f20,plain,(
% 2.78/0.99    ! [X1,X0] : (? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X4] : (r2_hidden(X2,X4) | ~r2_hidden(X4,X0)) | r2_hidden(X2,X1))) => ((? [X3] : (~r2_hidden(sK0(X0,X1),X3) & r2_hidden(X3,X0)) | ~r2_hidden(sK0(X0,X1),X1)) & (! [X4] : (r2_hidden(sK0(X0,X1),X4) | ~r2_hidden(X4,X0)) | r2_hidden(sK0(X0,X1),X1))))),
% 2.78/0.99    introduced(choice_axiom,[])).
% 2.78/0.99  
% 2.78/0.99  fof(f23,plain,(
% 2.78/0.99    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | (((~r2_hidden(sK0(X0,X1),sK1(X0,X1)) & r2_hidden(sK1(X0,X1),X0)) | ~r2_hidden(sK0(X0,X1),X1)) & (! [X4] : (r2_hidden(sK0(X0,X1),X4) | ~r2_hidden(X4,X0)) | r2_hidden(sK0(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | (~r2_hidden(X5,sK2(X0,X5)) & r2_hidden(sK2(X0,X5),X0))) & (! [X7] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0)) | ~r2_hidden(X5,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 2.78/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f22,f21,f20])).
% 2.78/0.99  
% 2.78/0.99  fof(f35,plain,(
% 2.78/0.99    ( ! [X0,X5,X1] : (r2_hidden(X5,X1) | r2_hidden(sK2(X0,X5),X0) | k1_setfam_1(X0) != X1 | k1_xboole_0 = X0) )),
% 2.78/0.99    inference(cnf_transformation,[],[f23])).
% 2.78/0.99  
% 2.78/0.99  fof(f56,plain,(
% 2.78/0.99    ( ! [X0,X5] : (r2_hidden(X5,k1_setfam_1(X0)) | r2_hidden(sK2(X0,X5),X0) | k1_xboole_0 = X0) )),
% 2.78/0.99    inference(equality_resolution,[],[f35])).
% 2.78/0.99  
% 2.78/0.99  fof(f8,conjecture,(
% 2.78/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r2_hidden(X1,X0) => (r2_hidden(X1,k8_setfam_1(X0,X2)) <=> ! [X3] : (r2_hidden(X3,X2) => r2_hidden(X1,X3)))))),
% 2.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/0.99  
% 2.78/0.99  fof(f9,negated_conjecture,(
% 2.78/0.99    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r2_hidden(X1,X0) => (r2_hidden(X1,k8_setfam_1(X0,X2)) <=> ! [X3] : (r2_hidden(X3,X2) => r2_hidden(X1,X3)))))),
% 2.78/0.99    inference(negated_conjecture,[],[f8])).
% 2.78/0.99  
% 2.78/0.99  fof(f16,plain,(
% 2.78/0.99    ? [X0,X1,X2] : (((r2_hidden(X1,k8_setfam_1(X0,X2)) <~> ! [X3] : (r2_hidden(X1,X3) | ~r2_hidden(X3,X2))) & r2_hidden(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.78/0.99    inference(ennf_transformation,[],[f9])).
% 2.78/0.99  
% 2.78/0.99  fof(f17,plain,(
% 2.78/0.99    ? [X0,X1,X2] : ((r2_hidden(X1,k8_setfam_1(X0,X2)) <~> ! [X3] : (r2_hidden(X1,X3) | ~r2_hidden(X3,X2))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.78/0.99    inference(flattening,[],[f16])).
% 2.78/0.99  
% 2.78/0.99  fof(f24,plain,(
% 2.78/0.99    ? [X0,X1,X2] : (((? [X3] : (~r2_hidden(X1,X3) & r2_hidden(X3,X2)) | ~r2_hidden(X1,k8_setfam_1(X0,X2))) & (! [X3] : (r2_hidden(X1,X3) | ~r2_hidden(X3,X2)) | r2_hidden(X1,k8_setfam_1(X0,X2)))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.78/0.99    inference(nnf_transformation,[],[f17])).
% 2.78/0.99  
% 2.78/0.99  fof(f25,plain,(
% 2.78/0.99    ? [X0,X1,X2] : ((? [X3] : (~r2_hidden(X1,X3) & r2_hidden(X3,X2)) | ~r2_hidden(X1,k8_setfam_1(X0,X2))) & (! [X3] : (r2_hidden(X1,X3) | ~r2_hidden(X3,X2)) | r2_hidden(X1,k8_setfam_1(X0,X2))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.78/0.99    inference(flattening,[],[f24])).
% 2.78/0.99  
% 2.78/0.99  fof(f26,plain,(
% 2.78/0.99    ? [X0,X1,X2] : ((? [X3] : (~r2_hidden(X1,X3) & r2_hidden(X3,X2)) | ~r2_hidden(X1,k8_setfam_1(X0,X2))) & (! [X4] : (r2_hidden(X1,X4) | ~r2_hidden(X4,X2)) | r2_hidden(X1,k8_setfam_1(X0,X2))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.78/0.99    inference(rectify,[],[f25])).
% 2.78/0.99  
% 2.78/0.99  fof(f28,plain,(
% 2.78/0.99    ( ! [X2,X1] : (? [X3] : (~r2_hidden(X1,X3) & r2_hidden(X3,X2)) => (~r2_hidden(X1,sK6) & r2_hidden(sK6,X2))) )),
% 2.78/0.99    introduced(choice_axiom,[])).
% 2.78/0.99  
% 2.78/0.99  fof(f27,plain,(
% 2.78/0.99    ? [X0,X1,X2] : ((? [X3] : (~r2_hidden(X1,X3) & r2_hidden(X3,X2)) | ~r2_hidden(X1,k8_setfam_1(X0,X2))) & (! [X4] : (r2_hidden(X1,X4) | ~r2_hidden(X4,X2)) | r2_hidden(X1,k8_setfam_1(X0,X2))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) => ((? [X3] : (~r2_hidden(sK4,X3) & r2_hidden(X3,sK5)) | ~r2_hidden(sK4,k8_setfam_1(sK3,sK5))) & (! [X4] : (r2_hidden(sK4,X4) | ~r2_hidden(X4,sK5)) | r2_hidden(sK4,k8_setfam_1(sK3,sK5))) & r2_hidden(sK4,sK3) & m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK3))))),
% 2.78/0.99    introduced(choice_axiom,[])).
% 2.78/0.99  
% 2.78/0.99  fof(f29,plain,(
% 2.78/0.99    ((~r2_hidden(sK4,sK6) & r2_hidden(sK6,sK5)) | ~r2_hidden(sK4,k8_setfam_1(sK3,sK5))) & (! [X4] : (r2_hidden(sK4,X4) | ~r2_hidden(X4,sK5)) | r2_hidden(sK4,k8_setfam_1(sK3,sK5))) & r2_hidden(sK4,sK3) & m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK3)))),
% 2.78/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f26,f28,f27])).
% 2.78/0.99  
% 2.78/0.99  fof(f45,plain,(
% 2.78/0.99    m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK3)))),
% 2.78/0.99    inference(cnf_transformation,[],[f29])).
% 2.78/0.99  
% 2.78/0.99  fof(f3,axiom,(
% 2.78/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 2.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/0.99  
% 2.78/0.99  fof(f10,plain,(
% 2.78/0.99    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.78/0.99    inference(ennf_transformation,[],[f3])).
% 2.78/0.99  
% 2.78/0.99  fof(f32,plain,(
% 2.78/0.99    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.78/0.99    inference(cnf_transformation,[],[f10])).
% 2.78/0.99  
% 2.78/0.99  fof(f5,axiom,(
% 2.78/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 2.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/0.99  
% 2.78/0.99  fof(f12,plain,(
% 2.78/0.99    ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.78/0.99    inference(ennf_transformation,[],[f5])).
% 2.78/0.99  
% 2.78/0.99  fof(f42,plain,(
% 2.78/0.99    ( ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.78/0.99    inference(cnf_transformation,[],[f12])).
% 2.78/0.99  
% 2.78/0.99  fof(f47,plain,(
% 2.78/0.99    ( ! [X4] : (r2_hidden(sK4,X4) | ~r2_hidden(X4,sK5) | r2_hidden(sK4,k8_setfam_1(sK3,sK5))) )),
% 2.78/0.99    inference(cnf_transformation,[],[f29])).
% 2.78/0.99  
% 2.78/0.99  fof(f36,plain,(
% 2.78/0.99    ( ! [X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(X5,sK2(X0,X5)) | k1_setfam_1(X0) != X1 | k1_xboole_0 = X0) )),
% 2.78/0.99    inference(cnf_transformation,[],[f23])).
% 2.78/0.99  
% 2.78/0.99  fof(f55,plain,(
% 2.78/0.99    ( ! [X0,X5] : (r2_hidden(X5,k1_setfam_1(X0)) | ~r2_hidden(X5,sK2(X0,X5)) | k1_xboole_0 = X0) )),
% 2.78/0.99    inference(equality_resolution,[],[f36])).
% 2.78/0.99  
% 2.78/0.99  fof(f34,plain,(
% 2.78/0.99    ( ! [X0,X7,X5,X1] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0) | ~r2_hidden(X5,X1) | k1_setfam_1(X0) != X1 | k1_xboole_0 = X0) )),
% 2.78/0.99    inference(cnf_transformation,[],[f23])).
% 2.78/0.99  
% 2.78/0.99  fof(f57,plain,(
% 2.78/0.99    ( ! [X0,X7,X5] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0) | ~r2_hidden(X5,k1_setfam_1(X0)) | k1_xboole_0 = X0) )),
% 2.78/0.99    inference(equality_resolution,[],[f34])).
% 2.78/0.99  
% 2.78/0.99  fof(f2,axiom,(
% 2.78/0.99    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/0.99  
% 2.78/0.99  fof(f31,plain,(
% 2.78/0.99    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.78/0.99    inference(cnf_transformation,[],[f2])).
% 2.78/0.99  
% 2.78/0.99  fof(f48,plain,(
% 2.78/0.99    r2_hidden(sK6,sK5) | ~r2_hidden(sK4,k8_setfam_1(sK3,sK5))),
% 2.78/0.99    inference(cnf_transformation,[],[f29])).
% 2.78/0.99  
% 2.78/0.99  fof(f1,axiom,(
% 2.78/0.99    v1_xboole_0(k1_xboole_0)),
% 2.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/0.99  
% 2.78/0.99  fof(f30,plain,(
% 2.78/0.99    v1_xboole_0(k1_xboole_0)),
% 2.78/0.99    inference(cnf_transformation,[],[f1])).
% 2.78/0.99  
% 2.78/0.99  fof(f7,axiom,(
% 2.78/0.99    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/0.99  
% 2.78/0.99  fof(f15,plain,(
% 2.78/0.99    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.78/0.99    inference(ennf_transformation,[],[f7])).
% 2.78/0.99  
% 2.78/0.99  fof(f44,plain,(
% 2.78/0.99    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.78/0.99    inference(cnf_transformation,[],[f15])).
% 2.78/0.99  
% 2.78/0.99  fof(f49,plain,(
% 2.78/0.99    ~r2_hidden(sK4,sK6) | ~r2_hidden(sK4,k8_setfam_1(sK3,sK5))),
% 2.78/0.99    inference(cnf_transformation,[],[f29])).
% 2.78/0.99  
% 2.78/0.99  fof(f33,plain,(
% 2.78/0.99    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.78/0.99    inference(cnf_transformation,[],[f10])).
% 2.78/0.99  
% 2.78/0.99  fof(f50,plain,(
% 2.78/0.99    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.78/0.99    inference(equality_resolution,[],[f33])).
% 2.78/0.99  
% 2.78/0.99  fof(f46,plain,(
% 2.78/0.99    r2_hidden(sK4,sK3)),
% 2.78/0.99    inference(cnf_transformation,[],[f29])).
% 2.78/0.99  
% 2.78/0.99  cnf(c_10,plain,
% 2.78/0.99      ( r2_hidden(X0,k1_setfam_1(X1))
% 2.78/0.99      | r2_hidden(sK2(X1,X0),X1)
% 2.78/0.99      | k1_xboole_0 = X1 ),
% 2.78/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.78/0.99  
% 2.78/0.99  cnf(c_629,plain,
% 2.78/0.99      ( k1_xboole_0 = X0
% 2.78/0.99      | r2_hidden(X1,k1_setfam_1(X0)) = iProver_top
% 2.78/0.99      | r2_hidden(sK2(X0,X1),X0) = iProver_top ),
% 2.78/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.78/0.99  
% 2.78/0.99  cnf(c_19,negated_conjecture,
% 2.78/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK3))) ),
% 2.78/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.78/0.99  
% 2.78/0.99  cnf(c_621,plain,
% 2.78/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK3))) = iProver_top ),
% 2.78/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.78/0.99  
% 2.78/0.99  cnf(c_3,plain,
% 2.78/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.78/0.99      | k6_setfam_1(X1,X0) = k8_setfam_1(X1,X0)
% 2.78/0.99      | k1_xboole_0 = X0 ),
% 2.78/0.99      inference(cnf_transformation,[],[f32]) ).
% 2.78/0.99  
% 2.78/0.99  cnf(c_634,plain,
% 2.78/0.99      ( k6_setfam_1(X0,X1) = k8_setfam_1(X0,X1)
% 2.78/0.99      | k1_xboole_0 = X1
% 2.78/0.99      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.78/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.78/0.99  
% 2.78/0.99  cnf(c_1602,plain,
% 2.78/0.99      ( k6_setfam_1(sK3,sK5) = k8_setfam_1(sK3,sK5) | sK5 = k1_xboole_0 ),
% 2.78/0.99      inference(superposition,[status(thm)],[c_621,c_634]) ).
% 2.78/0.99  
% 2.78/0.99  cnf(c_12,plain,
% 2.78/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.78/0.99      | k6_setfam_1(X1,X0) = k1_setfam_1(X0) ),
% 2.78/0.99      inference(cnf_transformation,[],[f42]) ).
% 2.78/0.99  
% 2.78/0.99  cnf(c_627,plain,
% 2.78/0.99      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
% 2.78/0.99      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.78/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.78/0.99  
% 2.78/0.99  cnf(c_1104,plain,
% 2.78/0.99      ( k6_setfam_1(sK3,sK5) = k1_setfam_1(sK5) ),
% 2.78/0.99      inference(superposition,[status(thm)],[c_621,c_627]) ).
% 2.78/0.99  
% 2.78/0.99  cnf(c_1605,plain,
% 2.78/0.99      ( k8_setfam_1(sK3,sK5) = k1_setfam_1(sK5) | sK5 = k1_xboole_0 ),
% 2.78/0.99      inference(light_normalisation,[status(thm)],[c_1602,c_1104]) ).
% 2.78/0.99  
% 2.78/0.99  cnf(c_17,negated_conjecture,
% 2.78/0.99      ( ~ r2_hidden(X0,sK5)
% 2.78/0.99      | r2_hidden(sK4,X0)
% 2.78/0.99      | r2_hidden(sK4,k8_setfam_1(sK3,sK5)) ),
% 2.78/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.78/0.99  
% 2.78/0.99  cnf(c_623,plain,
% 2.78/0.99      ( r2_hidden(X0,sK5) != iProver_top
% 2.78/0.99      | r2_hidden(sK4,X0) = iProver_top
% 2.78/0.99      | r2_hidden(sK4,k8_setfam_1(sK3,sK5)) = iProver_top ),
% 2.78/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.78/0.99  
% 2.78/0.99  cnf(c_1176,plain,
% 2.78/0.99      ( sK5 = k1_xboole_0
% 2.78/0.99      | r2_hidden(X0,k1_setfam_1(sK5)) = iProver_top
% 2.78/0.99      | r2_hidden(sK4,sK2(sK5,X0)) = iProver_top
% 2.78/0.99      | r2_hidden(sK4,k8_setfam_1(sK3,sK5)) = iProver_top ),
% 2.78/0.99      inference(superposition,[status(thm)],[c_629,c_623]) ).
% 2.78/0.99  
% 2.78/0.99  cnf(c_9,plain,
% 2.78/0.99      ( ~ r2_hidden(X0,sK2(X1,X0))
% 2.78/0.99      | r2_hidden(X0,k1_setfam_1(X1))
% 2.78/0.99      | k1_xboole_0 = X1 ),
% 2.78/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.78/0.99  
% 2.78/0.99  cnf(c_630,plain,
% 2.78/0.99      ( k1_xboole_0 = X0
% 2.78/0.99      | r2_hidden(X1,sK2(X0,X1)) != iProver_top
% 2.78/0.99      | r2_hidden(X1,k1_setfam_1(X0)) = iProver_top ),
% 2.78/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.78/0.99  
% 2.78/0.99  cnf(c_1373,plain,
% 2.78/0.99      ( sK5 = k1_xboole_0
% 2.78/0.99      | r2_hidden(sK4,k8_setfam_1(sK3,sK5)) = iProver_top
% 2.78/0.99      | r2_hidden(sK4,k1_setfam_1(sK5)) = iProver_top ),
% 2.78/0.99      inference(superposition,[status(thm)],[c_1176,c_630]) ).
% 2.78/0.99  
% 2.78/0.99  cnf(c_2231,plain,
% 2.78/0.99      ( sK5 = k1_xboole_0 | r2_hidden(sK4,k1_setfam_1(sK5)) = iProver_top ),
% 2.78/0.99      inference(superposition,[status(thm)],[c_1605,c_1373]) ).
% 2.78/0.99  
% 2.78/0.99  cnf(c_11,plain,
% 2.78/0.99      ( ~ r2_hidden(X0,X1)
% 2.78/0.99      | r2_hidden(X2,X0)
% 2.78/0.99      | ~ r2_hidden(X2,k1_setfam_1(X1))
% 2.78/0.99      | k1_xboole_0 = X1 ),
% 2.78/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.78/0.99  
% 2.78/0.99  cnf(c_628,plain,
% 2.78/0.99      ( k1_xboole_0 = X0
% 2.78/0.99      | r2_hidden(X1,X0) != iProver_top
% 2.78/0.99      | r2_hidden(X2,X1) = iProver_top
% 2.78/0.99      | r2_hidden(X2,k1_setfam_1(X0)) != iProver_top ),
% 2.78/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.78/0.99  
% 2.78/0.99  cnf(c_19019,plain,
% 2.78/0.99      ( sK5 = k1_xboole_0
% 2.78/0.99      | r2_hidden(X0,sK5) != iProver_top
% 2.78/0.99      | r2_hidden(sK4,X0) = iProver_top ),
% 2.78/0.99      inference(superposition,[status(thm)],[c_2231,c_628]) ).
% 2.78/0.99  
% 2.78/0.99  cnf(c_1,plain,
% 2.78/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.78/0.99      inference(cnf_transformation,[],[f31]) ).
% 2.78/0.99  
% 2.78/0.99  cnf(c_58,plain,
% 2.78/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.78/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.78/0.99  
% 2.78/0.99  cnf(c_60,plain,
% 2.78/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.78/0.99      inference(instantiation,[status(thm)],[c_58]) ).
% 2.78/0.99  
% 2.78/0.99  cnf(c_334,plain,
% 2.78/0.99      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 2.78/0.99      theory(equality) ).
% 2.78/0.99  
% 2.78/0.99  cnf(c_339,plain,
% 2.78/0.99      ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)
% 2.78/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 2.78/0.99      inference(instantiation,[status(thm)],[c_334]) ).
% 2.78/0.99  
% 2.78/0.99  cnf(c_332,plain,( X0 = X0 ),theory(equality) ).
% 2.78/0.99  
% 2.78/0.99  cnf(c_345,plain,
% 2.78/0.99      ( k1_xboole_0 = k1_xboole_0 ),
% 2.78/0.99      inference(instantiation,[status(thm)],[c_332]) ).
% 2.78/0.99  
% 2.78/0.99  cnf(c_16,negated_conjecture,
% 2.78/0.99      ( r2_hidden(sK6,sK5) | ~ r2_hidden(sK4,k8_setfam_1(sK3,sK5)) ),
% 2.78/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.78/0.99  
% 2.78/0.99  cnf(c_624,plain,
% 2.78/0.99      ( r2_hidden(sK6,sK5) = iProver_top
% 2.78/0.99      | r2_hidden(sK4,k8_setfam_1(sK3,sK5)) != iProver_top ),
% 2.78/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.78/0.99  
% 2.78/0.99  cnf(c_1380,plain,
% 2.78/0.99      ( sK5 = k1_xboole_0
% 2.78/0.99      | r2_hidden(sK6,sK5) = iProver_top
% 2.78/0.99      | r2_hidden(sK4,k1_setfam_1(sK5)) = iProver_top ),
% 2.78/0.99      inference(superposition,[status(thm)],[c_1373,c_624]) ).
% 2.78/0.99  
% 2.78/0.99  cnf(c_1530,plain,
% 2.78/0.99      ( sK5 = k1_xboole_0
% 2.78/0.99      | r2_hidden(X0,sK5) != iProver_top
% 2.78/0.99      | r2_hidden(sK6,sK5) = iProver_top
% 2.78/0.99      | r2_hidden(sK4,X0) = iProver_top ),
% 2.78/0.99      inference(superposition,[status(thm)],[c_1380,c_628]) ).
% 2.78/0.99  
% 2.78/0.99  cnf(c_22,plain,
% 2.78/0.99      ( r2_hidden(X0,sK5) != iProver_top
% 2.78/0.99      | r2_hidden(sK4,X0) = iProver_top
% 2.78/0.99      | r2_hidden(sK4,k8_setfam_1(sK3,sK5)) = iProver_top ),
% 2.78/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.78/0.99  
% 2.78/0.99  cnf(c_25,plain,
% 2.78/0.99      ( r2_hidden(sK6,sK5) = iProver_top
% 2.78/0.99      | r2_hidden(sK4,k8_setfam_1(sK3,sK5)) != iProver_top ),
% 2.78/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.78/0.99  
% 2.78/0.99  cnf(c_2666,plain,
% 2.78/0.99      ( r2_hidden(X0,sK5) != iProver_top
% 2.78/0.99      | r2_hidden(sK6,sK5) = iProver_top
% 2.78/0.99      | r2_hidden(sK4,X0) = iProver_top ),
% 2.78/0.99      inference(global_propositional_subsumption,
% 2.78/0.99                [status(thm)],
% 2.78/0.99                [c_1530,c_22,c_25]) ).
% 2.78/0.99  
% 2.78/0.99  cnf(c_0,plain,
% 2.78/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 2.78/0.99      inference(cnf_transformation,[],[f30]) ).
% 2.78/0.99  
% 2.78/0.99  cnf(c_14,plain,
% 2.78/0.99      ( ~ r2_hidden(X0,X1)
% 2.78/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 2.78/0.99      | ~ v1_xboole_0(X2) ),
% 2.78/0.99      inference(cnf_transformation,[],[f44]) ).
% 2.78/0.99  
% 2.78/0.99  cnf(c_201,plain,
% 2.78/0.99      ( ~ r2_hidden(X0,X1)
% 2.78/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 2.78/0.99      | k1_xboole_0 != X2 ),
% 2.78/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_14]) ).
% 2.78/0.99  
% 2.78/0.99  cnf(c_202,plain,
% 2.78/0.99      ( ~ r2_hidden(X0,X1) | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
% 2.78/0.99      inference(unflattening,[status(thm)],[c_201]) ).
% 2.78/0.99  
% 2.78/0.99  cnf(c_2915,plain,
% 2.78/0.99      ( ~ r2_hidden(sK6,sK5) | ~ m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) ),
% 2.78/0.99      inference(instantiation,[status(thm)],[c_202]) ).
% 2.78/0.99  
% 2.78/0.99  cnf(c_2916,plain,
% 2.78/0.99      ( r2_hidden(sK6,sK5) != iProver_top
% 2.78/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.78/0.99      inference(predicate_to_equality,[status(thm)],[c_2915]) ).
% 2.78/0.99  
% 2.78/0.99  cnf(c_335,plain,
% 2.78/0.99      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.78/0.99      theory(equality) ).
% 2.78/0.99  
% 2.78/0.99  cnf(c_786,plain,
% 2.78/0.99      ( m1_subset_1(X0,X1)
% 2.78/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
% 2.78/0.99      | X1 != k1_zfmisc_1(X2)
% 2.78/0.99      | X0 != k1_xboole_0 ),
% 2.78/0.99      inference(instantiation,[status(thm)],[c_335]) ).
% 2.78/0.99  
% 2.78/0.99  cnf(c_1149,plain,
% 2.78/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.78/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
% 2.78/0.99      | X0 != k1_xboole_0
% 2.78/0.99      | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
% 2.78/0.99      inference(instantiation,[status(thm)],[c_786]) ).
% 2.78/0.99  
% 2.78/0.99  cnf(c_5057,plain,
% 2.78/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0))
% 2.78/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 2.78/0.99      | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0)
% 2.78/0.99      | sK5 != k1_xboole_0 ),
% 2.78/0.99      inference(instantiation,[status(thm)],[c_1149]) ).
% 2.78/0.99  
% 2.78/0.99  cnf(c_5059,plain,
% 2.78/0.99      ( k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0)
% 2.78/0.99      | sK5 != k1_xboole_0
% 2.78/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 2.78/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.78/0.99      inference(predicate_to_equality,[status(thm)],[c_5057]) ).
% 2.78/0.99  
% 2.78/0.99  cnf(c_19082,plain,
% 2.78/0.99      ( r2_hidden(X0,sK5) != iProver_top | r2_hidden(sK4,X0) = iProver_top ),
% 2.78/0.99      inference(global_propositional_subsumption,
% 2.78/0.99                [status(thm)],
% 2.78/0.99                [c_19019,c_60,c_339,c_345,c_2666,c_2916,c_5059]) ).
% 2.78/0.99  
% 2.78/0.99  cnf(c_19105,plain,
% 2.78/0.99      ( sK5 = k1_xboole_0
% 2.78/0.99      | r2_hidden(X0,k1_setfam_1(sK5)) = iProver_top
% 2.78/0.99      | r2_hidden(sK4,sK2(sK5,X0)) = iProver_top ),
% 2.78/0.99      inference(superposition,[status(thm)],[c_629,c_19082]) ).
% 2.78/0.99  
% 2.78/0.99  cnf(c_15,negated_conjecture,
% 2.78/0.99      ( ~ r2_hidden(sK4,k8_setfam_1(sK3,sK5)) | ~ r2_hidden(sK4,sK6) ),
% 2.78/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.78/0.99  
% 2.78/0.99  cnf(c_625,plain,
% 2.78/0.99      ( r2_hidden(sK4,k8_setfam_1(sK3,sK5)) != iProver_top
% 2.78/0.99      | r2_hidden(sK4,sK6) != iProver_top ),
% 2.78/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.78/0.99  
% 2.78/0.99  cnf(c_2232,plain,
% 2.78/0.99      ( sK5 = k1_xboole_0
% 2.78/0.99      | r2_hidden(sK4,k1_setfam_1(sK5)) != iProver_top
% 2.78/0.99      | r2_hidden(sK4,sK6) != iProver_top ),
% 2.78/0.99      inference(superposition,[status(thm)],[c_1605,c_625]) ).
% 2.78/0.99  
% 2.78/0.99  cnf(c_2251,plain,
% 2.78/0.99      ( sK5 = k1_xboole_0 | r2_hidden(sK4,sK6) != iProver_top ),
% 2.78/0.99      inference(backward_subsumption_resolution,[status(thm)],[c_2231,c_2232]) ).
% 2.78/0.99  
% 2.78/0.99  cnf(c_2233,plain,
% 2.78/0.99      ( sK5 = k1_xboole_0
% 2.78/0.99      | r2_hidden(sK6,sK5) = iProver_top
% 2.78/0.99      | r2_hidden(sK4,k1_setfam_1(sK5)) != iProver_top ),
% 2.78/0.99      inference(superposition,[status(thm)],[c_1605,c_624]) ).
% 2.78/0.99  
% 2.78/0.99  cnf(c_2250,plain,
% 2.78/0.99      ( sK5 = k1_xboole_0 | r2_hidden(sK6,sK5) = iProver_top ),
% 2.78/0.99      inference(backward_subsumption_resolution,[status(thm)],[c_2231,c_2233]) ).
% 2.78/0.99  
% 2.78/0.99  cnf(c_19104,plain,
% 2.78/0.99      ( sK5 = k1_xboole_0 | r2_hidden(sK4,sK6) = iProver_top ),
% 2.78/0.99      inference(superposition,[status(thm)],[c_2250,c_19082]) ).
% 2.78/0.99  
% 2.78/0.99  cnf(c_19462,plain,
% 2.78/0.99      ( sK5 = k1_xboole_0 ),
% 2.78/0.99      inference(global_propositional_subsumption,
% 2.78/0.99                [status(thm)],
% 2.78/0.99                [c_19105,c_2251,c_19104]) ).
% 2.78/0.99  
% 2.78/0.99  cnf(c_19534,plain,
% 2.78/0.99      ( r2_hidden(sK6,k1_xboole_0) = iProver_top
% 2.78/0.99      | r2_hidden(sK4,k8_setfam_1(sK3,k1_xboole_0)) != iProver_top ),
% 2.78/0.99      inference(demodulation,[status(thm)],[c_19462,c_624]) ).
% 2.78/0.99  
% 2.78/0.99  cnf(c_2,plain,
% 2.78/0.99      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
% 2.78/0.99      | k8_setfam_1(X0,k1_xboole_0) = X0 ),
% 2.78/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.78/0.99  
% 2.78/0.99  cnf(c_635,plain,
% 2.78/0.99      ( k8_setfam_1(X0,k1_xboole_0) = X0
% 2.78/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.78/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.78/0.99  
% 2.78/0.99  cnf(c_636,plain,
% 2.78/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.78/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.78/0.99  
% 2.78/0.99  cnf(c_655,plain,
% 2.78/0.99      ( k8_setfam_1(X0,k1_xboole_0) = X0 ),
% 2.78/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_635,c_636]) ).
% 2.78/0.99  
% 2.78/0.99  cnf(c_19539,plain,
% 2.78/0.99      ( r2_hidden(sK6,k1_xboole_0) = iProver_top
% 2.78/0.99      | r2_hidden(sK4,sK3) != iProver_top ),
% 2.78/0.99      inference(demodulation,[status(thm)],[c_19534,c_655]) ).
% 2.78/0.99  
% 2.78/0.99  cnf(c_18,negated_conjecture,
% 2.78/0.99      ( r2_hidden(sK4,sK3) ),
% 2.78/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.78/0.99  
% 2.78/0.99  cnf(c_21,plain,
% 2.78/0.99      ( r2_hidden(sK4,sK3) = iProver_top ),
% 2.78/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.78/0.99  
% 2.78/0.99  cnf(c_20031,plain,
% 2.78/0.99      ( r2_hidden(sK6,k1_xboole_0) = iProver_top ),
% 2.78/0.99      inference(global_propositional_subsumption,[status(thm)],[c_19539,c_21]) ).
% 2.78/0.99  
% 2.78/0.99  cnf(c_620,plain,
% 2.78/0.99      ( r2_hidden(X0,X1) != iProver_top
% 2.78/0.99      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.78/0.99      inference(predicate_to_equality,[status(thm)],[c_202]) ).
% 2.78/0.99  
% 2.78/0.99  cnf(c_1096,plain,
% 2.78/0.99      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.78/0.99      inference(superposition,[status(thm)],[c_636,c_620]) ).
% 2.78/0.99  
% 2.78/0.99  cnf(c_20036,plain,
% 2.78/0.99      ( $false ),
% 2.78/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_20031,c_1096]) ).
% 2.78/0.99  
% 2.78/0.99  
% 2.78/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.78/0.99  
% 2.78/0.99  ------                               Statistics
% 2.78/0.99  
% 2.78/0.99  ------ General
% 2.78/0.99  
% 2.78/0.99  abstr_ref_over_cycles:                  0
% 2.78/0.99  abstr_ref_under_cycles:                 0
% 2.78/0.99  gc_basic_clause_elim:                   0
% 2.78/0.99  forced_gc_time:                         0
% 2.78/0.99  parsing_time:                           0.011
% 2.78/0.99  unif_index_cands_time:                  0.
% 2.78/0.99  unif_index_add_time:                    0.
% 2.78/0.99  orderings_time:                         0.
% 2.78/0.99  out_proof_time:                         0.01
% 2.78/0.99  total_time:                             0.464
% 2.78/0.99  num_of_symbols:                         46
% 2.78/0.99  num_of_terms:                           6786
% 2.78/0.99  
% 2.78/0.99  ------ Preprocessing
% 2.78/0.99  
% 2.78/0.99  num_of_splits:                          0
% 2.78/0.99  num_of_split_atoms:                     0
% 2.78/0.99  num_of_reused_defs:                     0
% 2.78/0.99  num_eq_ax_congr_red:                    24
% 2.78/0.99  num_of_sem_filtered_clauses:            1
% 2.78/0.99  num_of_subtypes:                        0
% 2.78/0.99  monotx_restored_types:                  0
% 2.78/0.99  sat_num_of_epr_types:                   0
% 2.78/0.99  sat_num_of_non_cyclic_types:            0
% 2.78/0.99  sat_guarded_non_collapsed_types:        0
% 2.78/0.99  num_pure_diseq_elim:                    0
% 2.78/0.99  simp_replaced_by:                       0
% 2.78/0.99  res_preprocessed:                       88
% 2.78/0.99  prep_upred:                             0
% 2.78/0.99  prep_unflattend:                        1
% 2.78/0.99  smt_new_axioms:                         0
% 2.78/0.99  pred_elim_cands:                        2
% 2.78/0.99  pred_elim:                              1
% 2.78/0.99  pred_elim_cl:                           1
% 2.78/0.99  pred_elim_cycles:                       3
% 2.78/0.99  merged_defs:                            0
% 2.78/0.99  merged_defs_ncl:                        0
% 2.78/0.99  bin_hyper_res:                          0
% 2.78/0.99  prep_cycles:                            4
% 2.78/0.99  pred_elim_time:                         0.
% 2.78/0.99  splitting_time:                         0.
% 2.78/0.99  sem_filter_time:                        0.
% 2.78/0.99  monotx_time:                            0.
% 2.78/0.99  subtype_inf_time:                       0.
% 2.78/0.99  
% 2.78/0.99  ------ Problem properties
% 2.78/0.99  
% 2.78/0.99  clauses:                                18
% 2.78/0.99  conjectures:                            5
% 2.78/0.99  epr:                                    1
% 2.78/0.99  horn:                                   10
% 2.78/0.99  ground:                                 5
% 2.78/0.99  unary:                                  4
% 2.78/0.99  binary:                                 5
% 2.78/0.99  lits:                                   46
% 2.78/0.99  lits_eq:                                14
% 2.78/0.99  fd_pure:                                0
% 2.78/0.99  fd_pseudo:                              0
% 2.78/0.99  fd_cond:                                4
% 2.78/0.99  fd_pseudo_cond:                         3
% 2.78/0.99  ac_symbols:                             0
% 2.78/0.99  
% 2.78/0.99  ------ Propositional Solver
% 2.78/0.99  
% 2.78/0.99  prop_solver_calls:                      32
% 2.78/0.99  prop_fast_solver_calls:                 1269
% 2.78/0.99  smt_solver_calls:                       0
% 2.78/0.99  smt_fast_solver_calls:                  0
% 2.78/0.99  prop_num_of_clauses:                    3857
% 2.78/0.99  prop_preprocess_simplified:             7421
% 2.78/0.99  prop_fo_subsumed:                       33
% 2.78/0.99  prop_solver_time:                       0.
% 2.78/0.99  smt_solver_time:                        0.
% 2.78/0.99  smt_fast_solver_time:                   0.
% 2.78/0.99  prop_fast_solver_time:                  0.
% 2.78/0.99  prop_unsat_core_time:                   0.
% 2.78/0.99  
% 2.78/0.99  ------ QBF
% 2.78/0.99  
% 2.78/0.99  qbf_q_res:                              0
% 2.78/0.99  qbf_num_tautologies:                    0
% 2.78/0.99  qbf_prep_cycles:                        0
% 2.78/0.99  
% 2.78/0.99  ------ BMC1
% 2.78/0.99  
% 2.78/0.99  bmc1_current_bound:                     -1
% 2.78/0.99  bmc1_last_solved_bound:                 -1
% 2.78/0.99  bmc1_unsat_core_size:                   -1
% 2.78/0.99  bmc1_unsat_core_parents_size:           -1
% 2.78/0.99  bmc1_merge_next_fun:                    0
% 2.78/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.78/0.99  
% 2.78/0.99  ------ Instantiation
% 2.78/0.99  
% 2.78/0.99  inst_num_of_clauses:                    995
% 2.78/0.99  inst_num_in_passive:                    391
% 2.78/0.99  inst_num_in_active:                     522
% 2.78/0.99  inst_num_in_unprocessed:                82
% 2.78/0.99  inst_num_of_loops:                      670
% 2.78/0.99  inst_num_of_learning_restarts:          0
% 2.78/0.99  inst_num_moves_active_passive:          142
% 2.78/0.99  inst_lit_activity:                      0
% 2.78/0.99  inst_lit_activity_moves:                0
% 2.78/0.99  inst_num_tautologies:                   0
% 2.78/0.99  inst_num_prop_implied:                  0
% 2.78/0.99  inst_num_existing_simplified:           0
% 2.78/0.99  inst_num_eq_res_simplified:             0
% 2.78/0.99  inst_num_child_elim:                    0
% 2.78/0.99  inst_num_of_dismatching_blockings:      461
% 2.78/0.99  inst_num_of_non_proper_insts:           893
% 2.78/0.99  inst_num_of_duplicates:                 0
% 2.78/0.99  inst_inst_num_from_inst_to_res:         0
% 2.78/0.99  inst_dismatching_checking_time:         0.
% 2.78/0.99  
% 2.78/0.99  ------ Resolution
% 2.78/0.99  
% 2.78/0.99  res_num_of_clauses:                     0
% 2.78/0.99  res_num_in_passive:                     0
% 2.78/0.99  res_num_in_active:                      0
% 2.78/0.99  res_num_of_loops:                       92
% 2.78/0.99  res_forward_subset_subsumed:            127
% 2.78/0.99  res_backward_subset_subsumed:           2
% 2.78/0.99  res_forward_subsumed:                   0
% 2.78/0.99  res_backward_subsumed:                  0
% 2.78/0.99  res_forward_subsumption_resolution:     0
% 2.78/0.99  res_backward_subsumption_resolution:    0
% 2.78/0.99  res_clause_to_clause_subsumption:       10145
% 2.78/0.99  res_orphan_elimination:                 0
% 2.78/0.99  res_tautology_del:                      50
% 2.78/0.99  res_num_eq_res_simplified:              0
% 2.78/0.99  res_num_sel_changes:                    0
% 2.78/0.99  res_moves_from_active_to_pass:          0
% 2.78/0.99  
% 2.78/0.99  ------ Superposition
% 2.78/0.99  
% 2.78/0.99  sup_time_total:                         0.
% 2.78/0.99  sup_time_generating:                    0.
% 2.78/0.99  sup_time_sim_full:                      0.
% 2.78/0.99  sup_time_sim_immed:                     0.
% 2.78/0.99  
% 2.78/0.99  sup_num_of_clauses:                     492
% 2.78/0.99  sup_num_in_active:                      37
% 2.78/0.99  sup_num_in_passive:                     455
% 2.78/0.99  sup_num_of_loops:                       133
% 2.78/0.99  sup_fw_superposition:                   436
% 2.78/0.99  sup_bw_superposition:                   556
% 2.78/0.99  sup_immediate_simplified:               277
% 2.78/0.99  sup_given_eliminated:                   1
% 2.78/0.99  comparisons_done:                       0
% 2.78/0.99  comparisons_avoided:                    128
% 2.78/0.99  
% 2.78/0.99  ------ Simplifications
% 2.78/0.99  
% 2.78/0.99  
% 2.78/0.99  sim_fw_subset_subsumed:                 28
% 2.78/0.99  sim_bw_subset_subsumed:                 46
% 2.78/0.99  sim_fw_subsumed:                        224
% 2.78/0.99  sim_bw_subsumed:                        17
% 2.78/0.99  sim_fw_subsumption_res:                 7
% 2.78/0.99  sim_bw_subsumption_res:                 2
% 2.78/0.99  sim_tautology_del:                      3
% 2.78/0.99  sim_eq_tautology_del:                   68
% 2.78/0.99  sim_eq_res_simp:                        3
% 2.78/0.99  sim_fw_demodulated:                     22
% 2.78/0.99  sim_bw_demodulated:                     71
% 2.78/0.99  sim_light_normalised:                   4
% 2.78/0.99  sim_joinable_taut:                      0
% 2.78/0.99  sim_joinable_simp:                      0
% 2.78/0.99  sim_ac_normalised:                      0
% 2.78/0.99  sim_smt_subsumption:                    0
% 2.78/0.99  
%------------------------------------------------------------------------------
