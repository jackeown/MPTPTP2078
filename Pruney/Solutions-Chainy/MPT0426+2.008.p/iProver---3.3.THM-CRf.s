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

% Result     : Theorem 2.41s
% Output     : CNFRefutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 844 expanded)
%              Number of clauses        :   53 ( 215 expanded)
%              Number of leaves         :   12 ( 194 expanded)
%              Depth                    :   26
%              Number of atoms          :  357 (5014 expanded)
%              Number of equality atoms :  166 (1042 expanded)
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
    inference(ennf_transformation,[],[f5])).

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

fof(f20,plain,(
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
    inference(rectify,[],[f19])).

fof(f23,plain,(
    ! [X5,X0] :
      ( ? [X6] :
          ( ~ r2_hidden(X5,X6)
          & r2_hidden(X6,X0) )
     => ( ~ r2_hidden(X5,sK2(X0,X5))
        & r2_hidden(sK2(X0,X5),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X2,X3)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(X2,sK1(X0,X1))
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
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

fof(f24,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f23,f22,f21])).

fof(f39,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | r2_hidden(sK2(X0,X5),X0)
      | k1_setfam_1(X0) != X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f61,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,k1_setfam_1(X0))
      | r2_hidden(sK2(X0,X5),X0)
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f39])).

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

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,k8_setfam_1(X0,X2))
      <~> ! [X3] :
            ( r2_hidden(X1,X3)
            | ~ r2_hidden(X3,X2) ) )
      & r2_hidden(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,k8_setfam_1(X0,X2))
      <~> ! [X3] :
            ( r2_hidden(X1,X3)
            | ~ r2_hidden(X3,X2) ) )
      & r2_hidden(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f15])).

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
    inference(nnf_transformation,[],[f16])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f29,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( ~ r2_hidden(X1,X3)
          & r2_hidden(X3,X2) )
     => ( ~ r2_hidden(X1,sK6)
        & r2_hidden(sK6,X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
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

fof(f30,plain,
    ( ( ( ~ r2_hidden(sK4,sK6)
        & r2_hidden(sK6,sK5) )
      | ~ r2_hidden(sK4,k8_setfam_1(sK3,sK5)) )
    & ( ! [X4] :
          ( r2_hidden(sK4,X4)
          | ~ r2_hidden(X4,sK5) )
      | r2_hidden(sK4,k8_setfam_1(sK3,sK5)) )
    & r2_hidden(sK4,sK3)
    & m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK3))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f27,f29,f28])).

fof(f48,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK3))) ),
    inference(cnf_transformation,[],[f30])).

fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f51,plain,
    ( r2_hidden(sK6,sK5)
    | ~ r2_hidden(sK4,k8_setfam_1(sK3,sK5)) ),
    inference(cnf_transformation,[],[f30])).

fof(f50,plain,(
    ! [X4] :
      ( r2_hidden(sK4,X4)
      | ~ r2_hidden(X4,sK5)
      | r2_hidden(sK4,k8_setfam_1(sK3,sK5)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f40,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X5,sK2(X0,X5))
      | k1_setfam_1(X0) != X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f60,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,k1_setfam_1(X0))
      | ~ r2_hidden(X5,sK2(X0,X5))
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f40])).

fof(f52,plain,
    ( ~ r2_hidden(sK4,sK6)
    | ~ r2_hidden(sK4,k8_setfam_1(sK3,sK5)) ),
    inference(cnf_transformation,[],[f30])).

fof(f38,plain,(
    ! [X0,X7,X5,X1] :
      ( r2_hidden(X5,X7)
      | ~ r2_hidden(X7,X0)
      | ~ r2_hidden(X5,X1)
      | k1_setfam_1(X0) != X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f62,plain,(
    ! [X0,X7,X5] :
      ( r2_hidden(X5,X7)
      | ~ r2_hidden(X7,X0)
      | ~ r2_hidden(X5,k1_setfam_1(X0))
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f38])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f55,plain,(
    ! [X0] :
      ( k8_setfam_1(X0,k1_xboole_0) = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f37])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f49,plain,(
    r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f17])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f53,plain,(
    ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f33])).

fof(f2,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

cnf(c_13,plain,
    ( r2_hidden(X0,k1_setfam_1(X1))
    | r2_hidden(sK2(X1,X0),X1)
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_609,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(X1,k1_setfam_1(X0)) = iProver_top
    | r2_hidden(sK2(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK3))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_601,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k6_setfam_1(X1,X0) = k8_setfam_1(X1,X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_614,plain,
    ( k6_setfam_1(X0,X1) = k8_setfam_1(X0,X1)
    | k1_xboole_0 = X1
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1633,plain,
    ( k6_setfam_1(sK3,sK5) = k8_setfam_1(sK3,sK5)
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_601,c_614])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k6_setfam_1(X1,X0) = k1_setfam_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_607,plain,
    ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1407,plain,
    ( k6_setfam_1(sK3,sK5) = k1_setfam_1(sK5) ),
    inference(superposition,[status(thm)],[c_601,c_607])).

cnf(c_1636,plain,
    ( k8_setfam_1(sK3,sK5) = k1_setfam_1(sK5)
    | sK5 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1633,c_1407])).

cnf(c_18,negated_conjecture,
    ( r2_hidden(sK6,sK5)
    | ~ r2_hidden(sK4,k8_setfam_1(sK3,sK5)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_604,plain,
    ( r2_hidden(sK6,sK5) = iProver_top
    | r2_hidden(sK4,k8_setfam_1(sK3,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1702,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK6,sK5) = iProver_top
    | r2_hidden(sK4,k1_setfam_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1636,c_604])).

cnf(c_27,plain,
    ( r2_hidden(sK6,sK5) = iProver_top
    | r2_hidden(sK4,k8_setfam_1(sK3,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_19,negated_conjecture,
    ( ~ r2_hidden(X0,sK5)
    | r2_hidden(sK4,X0)
    | r2_hidden(sK4,k8_setfam_1(sK3,sK5)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_603,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(sK4,X0) = iProver_top
    | r2_hidden(sK4,k8_setfam_1(sK3,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1533,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(X0,k1_setfam_1(sK5)) = iProver_top
    | r2_hidden(sK4,sK2(sK5,X0)) = iProver_top
    | r2_hidden(sK4,k8_setfam_1(sK3,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_609,c_603])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,sK2(X1,X0))
    | r2_hidden(X0,k1_setfam_1(X1))
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_610,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(X1,sK2(X0,X1)) != iProver_top
    | r2_hidden(X1,k1_setfam_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1678,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK4,k8_setfam_1(sK3,sK5)) = iProver_top
    | r2_hidden(sK4,k1_setfam_1(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1533,c_610])).

cnf(c_1770,plain,
    ( r2_hidden(sK6,sK5) = iProver_top
    | sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1702,c_27,c_1678])).

cnf(c_1771,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK6,sK5) = iProver_top ),
    inference(renaming,[status(thm)],[c_1770])).

cnf(c_1777,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK4,k8_setfam_1(sK3,sK5)) = iProver_top
    | r2_hidden(sK4,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1771,c_603])).

cnf(c_17,negated_conjecture,
    ( ~ r2_hidden(sK4,k8_setfam_1(sK3,sK5))
    | ~ r2_hidden(sK4,sK6) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_605,plain,
    ( r2_hidden(sK4,k8_setfam_1(sK3,sK5)) != iProver_top
    | r2_hidden(sK4,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1701,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK4,k1_setfam_1(sK5)) != iProver_top
    | r2_hidden(sK4,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1636,c_605])).

cnf(c_28,plain,
    ( r2_hidden(sK4,k8_setfam_1(sK3,sK5)) != iProver_top
    | r2_hidden(sK4,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1763,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK4,sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1701,c_28,c_1678])).

cnf(c_1822,plain,
    ( r2_hidden(sK4,k8_setfam_1(sK3,sK5)) = iProver_top
    | sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1777,c_1763])).

cnf(c_1823,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK4,k8_setfam_1(sK3,sK5)) = iProver_top ),
    inference(renaming,[status(thm)],[c_1822])).

cnf(c_1828,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK4,k1_setfam_1(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1636,c_1823])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X0)
    | ~ r2_hidden(X2,k1_setfam_1(X1))
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_608,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(X1,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top
    | r2_hidden(X2,k1_setfam_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1848,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(sK4,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1828,c_608])).

cnf(c_2212,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(X0,k1_setfam_1(sK5)) = iProver_top
    | r2_hidden(sK4,sK2(sK5,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_609,c_1848])).

cnf(c_2211,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK4,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1771,c_1848])).

cnf(c_2254,plain,
    ( sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2212,c_1763,c_2211])).

cnf(c_2264,plain,
    ( r2_hidden(sK6,k1_xboole_0) = iProver_top
    | r2_hidden(sK4,k8_setfam_1(sK3,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2254,c_604])).

cnf(c_5,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
    | k8_setfam_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_615,plain,
    ( k8_setfam_1(X0,k1_xboole_0) = X0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_616,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_638,plain,
    ( k8_setfam_1(X0,k1_xboole_0) = X0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_615,c_616])).

cnf(c_2269,plain,
    ( r2_hidden(sK6,k1_xboole_0) = iProver_top
    | r2_hidden(sK4,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2264,c_638])).

cnf(c_20,negated_conjecture,
    ( r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_23,plain,
    ( r2_hidden(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2331,plain,
    ( r2_hidden(sK6,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2269,c_23])).

cnf(c_0,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_617,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1130,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_617])).

cnf(c_2336,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2331,c_1130])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:30:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.41/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.00  
% 2.41/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.41/1.00  
% 2.41/1.00  ------  iProver source info
% 2.41/1.00  
% 2.41/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.41/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.41/1.00  git: non_committed_changes: false
% 2.41/1.00  git: last_make_outside_of_git: false
% 2.41/1.00  
% 2.41/1.00  ------ 
% 2.41/1.00  
% 2.41/1.00  ------ Input Options
% 2.41/1.00  
% 2.41/1.00  --out_options                           all
% 2.41/1.00  --tptp_safe_out                         true
% 2.41/1.00  --problem_path                          ""
% 2.41/1.00  --include_path                          ""
% 2.41/1.00  --clausifier                            res/vclausify_rel
% 2.41/1.00  --clausifier_options                    --mode clausify
% 2.41/1.00  --stdin                                 false
% 2.41/1.00  --stats_out                             all
% 2.41/1.00  
% 2.41/1.00  ------ General Options
% 2.41/1.00  
% 2.41/1.00  --fof                                   false
% 2.41/1.00  --time_out_real                         305.
% 2.41/1.00  --time_out_virtual                      -1.
% 2.41/1.00  --symbol_type_check                     false
% 2.41/1.00  --clausify_out                          false
% 2.41/1.00  --sig_cnt_out                           false
% 2.41/1.00  --trig_cnt_out                          false
% 2.41/1.00  --trig_cnt_out_tolerance                1.
% 2.41/1.00  --trig_cnt_out_sk_spl                   false
% 2.41/1.00  --abstr_cl_out                          false
% 2.41/1.00  
% 2.41/1.00  ------ Global Options
% 2.41/1.00  
% 2.41/1.00  --schedule                              default
% 2.41/1.00  --add_important_lit                     false
% 2.41/1.00  --prop_solver_per_cl                    1000
% 2.41/1.00  --min_unsat_core                        false
% 2.41/1.00  --soft_assumptions                      false
% 2.41/1.00  --soft_lemma_size                       3
% 2.41/1.00  --prop_impl_unit_size                   0
% 2.41/1.00  --prop_impl_unit                        []
% 2.41/1.00  --share_sel_clauses                     true
% 2.41/1.00  --reset_solvers                         false
% 2.41/1.00  --bc_imp_inh                            [conj_cone]
% 2.41/1.00  --conj_cone_tolerance                   3.
% 2.41/1.00  --extra_neg_conj                        none
% 2.41/1.00  --large_theory_mode                     true
% 2.41/1.00  --prolific_symb_bound                   200
% 2.41/1.00  --lt_threshold                          2000
% 2.41/1.00  --clause_weak_htbl                      true
% 2.41/1.00  --gc_record_bc_elim                     false
% 2.41/1.00  
% 2.41/1.00  ------ Preprocessing Options
% 2.41/1.00  
% 2.41/1.00  --preprocessing_flag                    true
% 2.41/1.00  --time_out_prep_mult                    0.1
% 2.41/1.00  --splitting_mode                        input
% 2.41/1.00  --splitting_grd                         true
% 2.41/1.00  --splitting_cvd                         false
% 2.41/1.00  --splitting_cvd_svl                     false
% 2.41/1.00  --splitting_nvd                         32
% 2.41/1.00  --sub_typing                            true
% 2.41/1.00  --prep_gs_sim                           true
% 2.41/1.00  --prep_unflatten                        true
% 2.41/1.00  --prep_res_sim                          true
% 2.41/1.00  --prep_upred                            true
% 2.41/1.00  --prep_sem_filter                       exhaustive
% 2.41/1.00  --prep_sem_filter_out                   false
% 2.41/1.00  --pred_elim                             true
% 2.41/1.00  --res_sim_input                         true
% 2.41/1.00  --eq_ax_congr_red                       true
% 2.41/1.00  --pure_diseq_elim                       true
% 2.41/1.00  --brand_transform                       false
% 2.41/1.00  --non_eq_to_eq                          false
% 2.41/1.00  --prep_def_merge                        true
% 2.41/1.00  --prep_def_merge_prop_impl              false
% 2.41/1.00  --prep_def_merge_mbd                    true
% 2.41/1.00  --prep_def_merge_tr_red                 false
% 2.41/1.00  --prep_def_merge_tr_cl                  false
% 2.41/1.00  --smt_preprocessing                     true
% 2.41/1.00  --smt_ac_axioms                         fast
% 2.41/1.00  --preprocessed_out                      false
% 2.41/1.00  --preprocessed_stats                    false
% 2.41/1.00  
% 2.41/1.00  ------ Abstraction refinement Options
% 2.41/1.00  
% 2.41/1.00  --abstr_ref                             []
% 2.41/1.00  --abstr_ref_prep                        false
% 2.41/1.00  --abstr_ref_until_sat                   false
% 2.41/1.00  --abstr_ref_sig_restrict                funpre
% 2.41/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.41/1.00  --abstr_ref_under                       []
% 2.41/1.00  
% 2.41/1.00  ------ SAT Options
% 2.41/1.00  
% 2.41/1.00  --sat_mode                              false
% 2.41/1.00  --sat_fm_restart_options                ""
% 2.41/1.00  --sat_gr_def                            false
% 2.41/1.00  --sat_epr_types                         true
% 2.41/1.00  --sat_non_cyclic_types                  false
% 2.41/1.00  --sat_finite_models                     false
% 2.41/1.00  --sat_fm_lemmas                         false
% 2.41/1.00  --sat_fm_prep                           false
% 2.41/1.00  --sat_fm_uc_incr                        true
% 2.41/1.00  --sat_out_model                         small
% 2.41/1.00  --sat_out_clauses                       false
% 2.41/1.00  
% 2.41/1.00  ------ QBF Options
% 2.41/1.00  
% 2.41/1.00  --qbf_mode                              false
% 2.41/1.00  --qbf_elim_univ                         false
% 2.41/1.00  --qbf_dom_inst                          none
% 2.41/1.00  --qbf_dom_pre_inst                      false
% 2.41/1.00  --qbf_sk_in                             false
% 2.41/1.00  --qbf_pred_elim                         true
% 2.41/1.00  --qbf_split                             512
% 2.41/1.00  
% 2.41/1.00  ------ BMC1 Options
% 2.41/1.00  
% 2.41/1.00  --bmc1_incremental                      false
% 2.41/1.00  --bmc1_axioms                           reachable_all
% 2.41/1.00  --bmc1_min_bound                        0
% 2.41/1.00  --bmc1_max_bound                        -1
% 2.41/1.00  --bmc1_max_bound_default                -1
% 2.41/1.00  --bmc1_symbol_reachability              true
% 2.41/1.00  --bmc1_property_lemmas                  false
% 2.41/1.00  --bmc1_k_induction                      false
% 2.41/1.00  --bmc1_non_equiv_states                 false
% 2.41/1.00  --bmc1_deadlock                         false
% 2.41/1.00  --bmc1_ucm                              false
% 2.41/1.00  --bmc1_add_unsat_core                   none
% 2.41/1.00  --bmc1_unsat_core_children              false
% 2.41/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.41/1.00  --bmc1_out_stat                         full
% 2.41/1.00  --bmc1_ground_init                      false
% 2.41/1.00  --bmc1_pre_inst_next_state              false
% 2.41/1.00  --bmc1_pre_inst_state                   false
% 2.41/1.00  --bmc1_pre_inst_reach_state             false
% 2.41/1.00  --bmc1_out_unsat_core                   false
% 2.41/1.00  --bmc1_aig_witness_out                  false
% 2.41/1.00  --bmc1_verbose                          false
% 2.41/1.00  --bmc1_dump_clauses_tptp                false
% 2.41/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.41/1.00  --bmc1_dump_file                        -
% 2.41/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.41/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.41/1.00  --bmc1_ucm_extend_mode                  1
% 2.41/1.00  --bmc1_ucm_init_mode                    2
% 2.41/1.00  --bmc1_ucm_cone_mode                    none
% 2.41/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.41/1.00  --bmc1_ucm_relax_model                  4
% 2.41/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.41/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.41/1.00  --bmc1_ucm_layered_model                none
% 2.41/1.00  --bmc1_ucm_max_lemma_size               10
% 2.41/1.00  
% 2.41/1.00  ------ AIG Options
% 2.41/1.00  
% 2.41/1.00  --aig_mode                              false
% 2.41/1.00  
% 2.41/1.00  ------ Instantiation Options
% 2.41/1.00  
% 2.41/1.00  --instantiation_flag                    true
% 2.41/1.00  --inst_sos_flag                         false
% 2.41/1.00  --inst_sos_phase                        true
% 2.41/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.41/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.41/1.00  --inst_lit_sel_side                     num_symb
% 2.41/1.00  --inst_solver_per_active                1400
% 2.41/1.00  --inst_solver_calls_frac                1.
% 2.41/1.00  --inst_passive_queue_type               priority_queues
% 2.41/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.41/1.00  --inst_passive_queues_freq              [25;2]
% 2.41/1.00  --inst_dismatching                      true
% 2.41/1.00  --inst_eager_unprocessed_to_passive     true
% 2.41/1.00  --inst_prop_sim_given                   true
% 2.41/1.00  --inst_prop_sim_new                     false
% 2.41/1.00  --inst_subs_new                         false
% 2.41/1.00  --inst_eq_res_simp                      false
% 2.41/1.00  --inst_subs_given                       false
% 2.41/1.00  --inst_orphan_elimination               true
% 2.41/1.00  --inst_learning_loop_flag               true
% 2.41/1.00  --inst_learning_start                   3000
% 2.41/1.00  --inst_learning_factor                  2
% 2.41/1.00  --inst_start_prop_sim_after_learn       3
% 2.41/1.00  --inst_sel_renew                        solver
% 2.41/1.00  --inst_lit_activity_flag                true
% 2.41/1.00  --inst_restr_to_given                   false
% 2.41/1.00  --inst_activity_threshold               500
% 2.41/1.00  --inst_out_proof                        true
% 2.41/1.00  
% 2.41/1.00  ------ Resolution Options
% 2.41/1.00  
% 2.41/1.00  --resolution_flag                       true
% 2.41/1.00  --res_lit_sel                           adaptive
% 2.41/1.00  --res_lit_sel_side                      none
% 2.41/1.00  --res_ordering                          kbo
% 2.41/1.00  --res_to_prop_solver                    active
% 2.41/1.00  --res_prop_simpl_new                    false
% 2.41/1.00  --res_prop_simpl_given                  true
% 2.41/1.00  --res_passive_queue_type                priority_queues
% 2.41/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.41/1.00  --res_passive_queues_freq               [15;5]
% 2.41/1.00  --res_forward_subs                      full
% 2.41/1.00  --res_backward_subs                     full
% 2.41/1.00  --res_forward_subs_resolution           true
% 2.41/1.00  --res_backward_subs_resolution          true
% 2.41/1.00  --res_orphan_elimination                true
% 2.41/1.00  --res_time_limit                        2.
% 2.41/1.00  --res_out_proof                         true
% 2.41/1.00  
% 2.41/1.00  ------ Superposition Options
% 2.41/1.00  
% 2.41/1.00  --superposition_flag                    true
% 2.41/1.00  --sup_passive_queue_type                priority_queues
% 2.41/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.41/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.41/1.00  --demod_completeness_check              fast
% 2.41/1.00  --demod_use_ground                      true
% 2.41/1.00  --sup_to_prop_solver                    passive
% 2.41/1.00  --sup_prop_simpl_new                    true
% 2.41/1.00  --sup_prop_simpl_given                  true
% 2.41/1.00  --sup_fun_splitting                     false
% 2.41/1.00  --sup_smt_interval                      50000
% 2.41/1.00  
% 2.41/1.00  ------ Superposition Simplification Setup
% 2.41/1.00  
% 2.41/1.00  --sup_indices_passive                   []
% 2.41/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.41/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.41/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.41/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.41/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.41/1.00  --sup_full_bw                           [BwDemod]
% 2.41/1.00  --sup_immed_triv                        [TrivRules]
% 2.41/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.41/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.41/1.00  --sup_immed_bw_main                     []
% 2.41/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.41/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.41/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.41/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.41/1.00  
% 2.41/1.00  ------ Combination Options
% 2.41/1.00  
% 2.41/1.00  --comb_res_mult                         3
% 2.41/1.00  --comb_sup_mult                         2
% 2.41/1.00  --comb_inst_mult                        10
% 2.41/1.00  
% 2.41/1.00  ------ Debug Options
% 2.41/1.00  
% 2.41/1.00  --dbg_backtrace                         false
% 2.41/1.00  --dbg_dump_prop_clauses                 false
% 2.41/1.00  --dbg_dump_prop_clauses_file            -
% 2.41/1.00  --dbg_out_stat                          false
% 2.41/1.00  ------ Parsing...
% 2.41/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.41/1.00  
% 2.41/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.41/1.00  
% 2.41/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.41/1.00  
% 2.41/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.41/1.00  ------ Proving...
% 2.41/1.00  ------ Problem Properties 
% 2.41/1.00  
% 2.41/1.00  
% 2.41/1.00  clauses                                 21
% 2.41/1.00  conjectures                             5
% 2.41/1.00  EPR                                     1
% 2.41/1.00  Horn                                    12
% 2.41/1.00  unary                                   7
% 2.41/1.00  binary                                  4
% 2.41/1.00  lits                                    50
% 2.41/1.00  lits eq                                 19
% 2.41/1.00  fd_pure                                 0
% 2.41/1.00  fd_pseudo                               0
% 2.41/1.00  fd_cond                                 5
% 2.41/1.00  fd_pseudo_cond                          3
% 2.41/1.00  AC symbols                              0
% 2.41/1.00  
% 2.41/1.00  ------ Schedule dynamic 5 is on 
% 2.41/1.00  
% 2.41/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.41/1.00  
% 2.41/1.00  
% 2.41/1.00  ------ 
% 2.41/1.00  Current options:
% 2.41/1.00  ------ 
% 2.41/1.00  
% 2.41/1.00  ------ Input Options
% 2.41/1.00  
% 2.41/1.00  --out_options                           all
% 2.41/1.00  --tptp_safe_out                         true
% 2.41/1.00  --problem_path                          ""
% 2.41/1.00  --include_path                          ""
% 2.41/1.00  --clausifier                            res/vclausify_rel
% 2.41/1.00  --clausifier_options                    --mode clausify
% 2.41/1.00  --stdin                                 false
% 2.41/1.00  --stats_out                             all
% 2.41/1.00  
% 2.41/1.00  ------ General Options
% 2.41/1.00  
% 2.41/1.00  --fof                                   false
% 2.41/1.00  --time_out_real                         305.
% 2.41/1.00  --time_out_virtual                      -1.
% 2.41/1.00  --symbol_type_check                     false
% 2.41/1.00  --clausify_out                          false
% 2.41/1.00  --sig_cnt_out                           false
% 2.41/1.00  --trig_cnt_out                          false
% 2.41/1.00  --trig_cnt_out_tolerance                1.
% 2.41/1.00  --trig_cnt_out_sk_spl                   false
% 2.41/1.00  --abstr_cl_out                          false
% 2.41/1.00  
% 2.41/1.00  ------ Global Options
% 2.41/1.00  
% 2.41/1.00  --schedule                              default
% 2.41/1.00  --add_important_lit                     false
% 2.41/1.00  --prop_solver_per_cl                    1000
% 2.41/1.00  --min_unsat_core                        false
% 2.41/1.00  --soft_assumptions                      false
% 2.41/1.00  --soft_lemma_size                       3
% 2.41/1.00  --prop_impl_unit_size                   0
% 2.41/1.00  --prop_impl_unit                        []
% 2.41/1.00  --share_sel_clauses                     true
% 2.41/1.00  --reset_solvers                         false
% 2.41/1.00  --bc_imp_inh                            [conj_cone]
% 2.41/1.00  --conj_cone_tolerance                   3.
% 2.41/1.00  --extra_neg_conj                        none
% 2.41/1.00  --large_theory_mode                     true
% 2.41/1.00  --prolific_symb_bound                   200
% 2.41/1.00  --lt_threshold                          2000
% 2.41/1.00  --clause_weak_htbl                      true
% 2.41/1.00  --gc_record_bc_elim                     false
% 2.41/1.00  
% 2.41/1.00  ------ Preprocessing Options
% 2.41/1.00  
% 2.41/1.00  --preprocessing_flag                    true
% 2.41/1.00  --time_out_prep_mult                    0.1
% 2.41/1.00  --splitting_mode                        input
% 2.41/1.00  --splitting_grd                         true
% 2.41/1.00  --splitting_cvd                         false
% 2.41/1.00  --splitting_cvd_svl                     false
% 2.41/1.00  --splitting_nvd                         32
% 2.41/1.00  --sub_typing                            true
% 2.41/1.00  --prep_gs_sim                           true
% 2.41/1.00  --prep_unflatten                        true
% 2.41/1.00  --prep_res_sim                          true
% 2.41/1.00  --prep_upred                            true
% 2.41/1.00  --prep_sem_filter                       exhaustive
% 2.41/1.00  --prep_sem_filter_out                   false
% 2.41/1.00  --pred_elim                             true
% 2.41/1.00  --res_sim_input                         true
% 2.41/1.00  --eq_ax_congr_red                       true
% 2.41/1.00  --pure_diseq_elim                       true
% 2.41/1.00  --brand_transform                       false
% 2.41/1.00  --non_eq_to_eq                          false
% 2.41/1.00  --prep_def_merge                        true
% 2.41/1.00  --prep_def_merge_prop_impl              false
% 2.41/1.00  --prep_def_merge_mbd                    true
% 2.41/1.00  --prep_def_merge_tr_red                 false
% 2.41/1.00  --prep_def_merge_tr_cl                  false
% 2.41/1.00  --smt_preprocessing                     true
% 2.41/1.00  --smt_ac_axioms                         fast
% 2.41/1.00  --preprocessed_out                      false
% 2.41/1.00  --preprocessed_stats                    false
% 2.41/1.00  
% 2.41/1.00  ------ Abstraction refinement Options
% 2.41/1.00  
% 2.41/1.00  --abstr_ref                             []
% 2.41/1.00  --abstr_ref_prep                        false
% 2.41/1.00  --abstr_ref_until_sat                   false
% 2.41/1.00  --abstr_ref_sig_restrict                funpre
% 2.41/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.41/1.00  --abstr_ref_under                       []
% 2.41/1.00  
% 2.41/1.00  ------ SAT Options
% 2.41/1.00  
% 2.41/1.00  --sat_mode                              false
% 2.41/1.00  --sat_fm_restart_options                ""
% 2.41/1.00  --sat_gr_def                            false
% 2.41/1.00  --sat_epr_types                         true
% 2.41/1.00  --sat_non_cyclic_types                  false
% 2.41/1.00  --sat_finite_models                     false
% 2.41/1.00  --sat_fm_lemmas                         false
% 2.41/1.00  --sat_fm_prep                           false
% 2.41/1.00  --sat_fm_uc_incr                        true
% 2.41/1.00  --sat_out_model                         small
% 2.41/1.00  --sat_out_clauses                       false
% 2.41/1.00  
% 2.41/1.00  ------ QBF Options
% 2.41/1.00  
% 2.41/1.00  --qbf_mode                              false
% 2.41/1.00  --qbf_elim_univ                         false
% 2.41/1.00  --qbf_dom_inst                          none
% 2.41/1.00  --qbf_dom_pre_inst                      false
% 2.41/1.00  --qbf_sk_in                             false
% 2.41/1.00  --qbf_pred_elim                         true
% 2.41/1.00  --qbf_split                             512
% 2.41/1.00  
% 2.41/1.00  ------ BMC1 Options
% 2.41/1.00  
% 2.41/1.00  --bmc1_incremental                      false
% 2.41/1.00  --bmc1_axioms                           reachable_all
% 2.41/1.00  --bmc1_min_bound                        0
% 2.41/1.00  --bmc1_max_bound                        -1
% 2.41/1.00  --bmc1_max_bound_default                -1
% 2.41/1.00  --bmc1_symbol_reachability              true
% 2.41/1.00  --bmc1_property_lemmas                  false
% 2.41/1.00  --bmc1_k_induction                      false
% 2.41/1.00  --bmc1_non_equiv_states                 false
% 2.41/1.00  --bmc1_deadlock                         false
% 2.41/1.00  --bmc1_ucm                              false
% 2.41/1.00  --bmc1_add_unsat_core                   none
% 2.41/1.00  --bmc1_unsat_core_children              false
% 2.41/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.41/1.00  --bmc1_out_stat                         full
% 2.41/1.00  --bmc1_ground_init                      false
% 2.41/1.00  --bmc1_pre_inst_next_state              false
% 2.41/1.00  --bmc1_pre_inst_state                   false
% 2.41/1.00  --bmc1_pre_inst_reach_state             false
% 2.41/1.00  --bmc1_out_unsat_core                   false
% 2.41/1.00  --bmc1_aig_witness_out                  false
% 2.41/1.00  --bmc1_verbose                          false
% 2.41/1.00  --bmc1_dump_clauses_tptp                false
% 2.41/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.41/1.00  --bmc1_dump_file                        -
% 2.41/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.41/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.41/1.00  --bmc1_ucm_extend_mode                  1
% 2.41/1.00  --bmc1_ucm_init_mode                    2
% 2.41/1.00  --bmc1_ucm_cone_mode                    none
% 2.41/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.41/1.00  --bmc1_ucm_relax_model                  4
% 2.41/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.41/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.41/1.00  --bmc1_ucm_layered_model                none
% 2.41/1.00  --bmc1_ucm_max_lemma_size               10
% 2.41/1.00  
% 2.41/1.00  ------ AIG Options
% 2.41/1.00  
% 2.41/1.00  --aig_mode                              false
% 2.41/1.00  
% 2.41/1.00  ------ Instantiation Options
% 2.41/1.00  
% 2.41/1.00  --instantiation_flag                    true
% 2.41/1.00  --inst_sos_flag                         false
% 2.41/1.00  --inst_sos_phase                        true
% 2.41/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.41/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.41/1.00  --inst_lit_sel_side                     none
% 2.41/1.00  --inst_solver_per_active                1400
% 2.41/1.00  --inst_solver_calls_frac                1.
% 2.41/1.00  --inst_passive_queue_type               priority_queues
% 2.41/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.41/1.00  --inst_passive_queues_freq              [25;2]
% 2.41/1.00  --inst_dismatching                      true
% 2.41/1.00  --inst_eager_unprocessed_to_passive     true
% 2.41/1.00  --inst_prop_sim_given                   true
% 2.41/1.00  --inst_prop_sim_new                     false
% 2.41/1.00  --inst_subs_new                         false
% 2.41/1.00  --inst_eq_res_simp                      false
% 2.41/1.00  --inst_subs_given                       false
% 2.41/1.00  --inst_orphan_elimination               true
% 2.41/1.00  --inst_learning_loop_flag               true
% 2.41/1.00  --inst_learning_start                   3000
% 2.41/1.00  --inst_learning_factor                  2
% 2.41/1.00  --inst_start_prop_sim_after_learn       3
% 2.41/1.00  --inst_sel_renew                        solver
% 2.41/1.00  --inst_lit_activity_flag                true
% 2.41/1.00  --inst_restr_to_given                   false
% 2.41/1.00  --inst_activity_threshold               500
% 2.41/1.00  --inst_out_proof                        true
% 2.41/1.00  
% 2.41/1.00  ------ Resolution Options
% 2.41/1.00  
% 2.41/1.00  --resolution_flag                       false
% 2.41/1.00  --res_lit_sel                           adaptive
% 2.41/1.00  --res_lit_sel_side                      none
% 2.41/1.00  --res_ordering                          kbo
% 2.41/1.00  --res_to_prop_solver                    active
% 2.41/1.00  --res_prop_simpl_new                    false
% 2.41/1.00  --res_prop_simpl_given                  true
% 2.41/1.00  --res_passive_queue_type                priority_queues
% 2.41/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.41/1.00  --res_passive_queues_freq               [15;5]
% 2.41/1.00  --res_forward_subs                      full
% 2.41/1.00  --res_backward_subs                     full
% 2.41/1.00  --res_forward_subs_resolution           true
% 2.41/1.00  --res_backward_subs_resolution          true
% 2.41/1.00  --res_orphan_elimination                true
% 2.41/1.00  --res_time_limit                        2.
% 2.41/1.00  --res_out_proof                         true
% 2.41/1.00  
% 2.41/1.00  ------ Superposition Options
% 2.41/1.00  
% 2.41/1.00  --superposition_flag                    true
% 2.41/1.00  --sup_passive_queue_type                priority_queues
% 2.41/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.41/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.41/1.00  --demod_completeness_check              fast
% 2.41/1.00  --demod_use_ground                      true
% 2.41/1.00  --sup_to_prop_solver                    passive
% 2.41/1.00  --sup_prop_simpl_new                    true
% 2.41/1.00  --sup_prop_simpl_given                  true
% 2.41/1.00  --sup_fun_splitting                     false
% 2.41/1.00  --sup_smt_interval                      50000
% 2.41/1.00  
% 2.41/1.00  ------ Superposition Simplification Setup
% 2.41/1.00  
% 2.41/1.00  --sup_indices_passive                   []
% 2.41/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.41/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.41/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.41/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.41/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.41/1.00  --sup_full_bw                           [BwDemod]
% 2.41/1.00  --sup_immed_triv                        [TrivRules]
% 2.41/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.41/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.41/1.00  --sup_immed_bw_main                     []
% 2.41/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.41/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.41/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.41/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.41/1.00  
% 2.41/1.00  ------ Combination Options
% 2.41/1.00  
% 2.41/1.00  --comb_res_mult                         3
% 2.41/1.00  --comb_sup_mult                         2
% 2.41/1.00  --comb_inst_mult                        10
% 2.41/1.00  
% 2.41/1.00  ------ Debug Options
% 2.41/1.00  
% 2.41/1.00  --dbg_backtrace                         false
% 2.41/1.00  --dbg_dump_prop_clauses                 false
% 2.41/1.00  --dbg_dump_prop_clauses_file            -
% 2.41/1.00  --dbg_out_stat                          false
% 2.41/1.00  
% 2.41/1.00  
% 2.41/1.00  
% 2.41/1.00  
% 2.41/1.00  ------ Proving...
% 2.41/1.00  
% 2.41/1.00  
% 2.41/1.00  % SZS status Theorem for theBenchmark.p
% 2.41/1.00  
% 2.41/1.00   Resolution empty clause
% 2.41/1.00  
% 2.41/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.41/1.00  
% 2.41/1.00  fof(f5,axiom,(
% 2.41/1.00    ! [X0,X1] : ((k1_xboole_0 = X0 => (k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1)) & (k1_xboole_0 != X0 => (k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X3,X0) => r2_hidden(X2,X3))))))),
% 2.41/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.41/1.00  
% 2.41/1.00  fof(f11,plain,(
% 2.41/1.00    ! [X0,X1] : (((k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1) | k1_xboole_0 != X0) & ((k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)))) | k1_xboole_0 = X0))),
% 2.41/1.00    inference(ennf_transformation,[],[f5])).
% 2.41/1.00  
% 2.41/1.00  fof(f19,plain,(
% 2.41/1.00    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | ? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0))) & (! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)) | ~r2_hidden(X2,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 2.41/1.00    inference(nnf_transformation,[],[f11])).
% 2.41/1.00  
% 2.41/1.00  fof(f20,plain,(
% 2.41/1.00    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | ? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X4] : (r2_hidden(X2,X4) | ~r2_hidden(X4,X0)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ? [X6] : (~r2_hidden(X5,X6) & r2_hidden(X6,X0))) & (! [X7] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0)) | ~r2_hidden(X5,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 2.41/1.00    inference(rectify,[],[f19])).
% 2.41/1.00  
% 2.41/1.00  fof(f23,plain,(
% 2.41/1.00    ! [X5,X0] : (? [X6] : (~r2_hidden(X5,X6) & r2_hidden(X6,X0)) => (~r2_hidden(X5,sK2(X0,X5)) & r2_hidden(sK2(X0,X5),X0)))),
% 2.41/1.00    introduced(choice_axiom,[])).
% 2.41/1.00  
% 2.41/1.00  fof(f22,plain,(
% 2.41/1.00    ( ! [X2] : (! [X1,X0] : (? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) => (~r2_hidden(X2,sK1(X0,X1)) & r2_hidden(sK1(X0,X1),X0)))) )),
% 2.41/1.00    introduced(choice_axiom,[])).
% 2.41/1.00  
% 2.41/1.00  fof(f21,plain,(
% 2.41/1.00    ! [X1,X0] : (? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X4] : (r2_hidden(X2,X4) | ~r2_hidden(X4,X0)) | r2_hidden(X2,X1))) => ((? [X3] : (~r2_hidden(sK0(X0,X1),X3) & r2_hidden(X3,X0)) | ~r2_hidden(sK0(X0,X1),X1)) & (! [X4] : (r2_hidden(sK0(X0,X1),X4) | ~r2_hidden(X4,X0)) | r2_hidden(sK0(X0,X1),X1))))),
% 2.41/1.00    introduced(choice_axiom,[])).
% 2.41/1.00  
% 2.41/1.00  fof(f24,plain,(
% 2.41/1.00    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | (((~r2_hidden(sK0(X0,X1),sK1(X0,X1)) & r2_hidden(sK1(X0,X1),X0)) | ~r2_hidden(sK0(X0,X1),X1)) & (! [X4] : (r2_hidden(sK0(X0,X1),X4) | ~r2_hidden(X4,X0)) | r2_hidden(sK0(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | (~r2_hidden(X5,sK2(X0,X5)) & r2_hidden(sK2(X0,X5),X0))) & (! [X7] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0)) | ~r2_hidden(X5,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 2.41/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f23,f22,f21])).
% 2.41/1.00  
% 2.41/1.00  fof(f39,plain,(
% 2.41/1.00    ( ! [X0,X5,X1] : (r2_hidden(X5,X1) | r2_hidden(sK2(X0,X5),X0) | k1_setfam_1(X0) != X1 | k1_xboole_0 = X0) )),
% 2.41/1.00    inference(cnf_transformation,[],[f24])).
% 2.41/1.00  
% 2.41/1.00  fof(f61,plain,(
% 2.41/1.00    ( ! [X0,X5] : (r2_hidden(X5,k1_setfam_1(X0)) | r2_hidden(sK2(X0,X5),X0) | k1_xboole_0 = X0) )),
% 2.41/1.00    inference(equality_resolution,[],[f39])).
% 2.41/1.00  
% 2.41/1.00  fof(f8,conjecture,(
% 2.41/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r2_hidden(X1,X0) => (r2_hidden(X1,k8_setfam_1(X0,X2)) <=> ! [X3] : (r2_hidden(X3,X2) => r2_hidden(X1,X3)))))),
% 2.41/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.41/1.00  
% 2.41/1.00  fof(f9,negated_conjecture,(
% 2.41/1.00    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r2_hidden(X1,X0) => (r2_hidden(X1,k8_setfam_1(X0,X2)) <=> ! [X3] : (r2_hidden(X3,X2) => r2_hidden(X1,X3)))))),
% 2.41/1.00    inference(negated_conjecture,[],[f8])).
% 2.41/1.00  
% 2.41/1.00  fof(f15,plain,(
% 2.41/1.00    ? [X0,X1,X2] : (((r2_hidden(X1,k8_setfam_1(X0,X2)) <~> ! [X3] : (r2_hidden(X1,X3) | ~r2_hidden(X3,X2))) & r2_hidden(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.41/1.00    inference(ennf_transformation,[],[f9])).
% 2.41/1.00  
% 2.41/1.00  fof(f16,plain,(
% 2.41/1.00    ? [X0,X1,X2] : ((r2_hidden(X1,k8_setfam_1(X0,X2)) <~> ! [X3] : (r2_hidden(X1,X3) | ~r2_hidden(X3,X2))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.41/1.00    inference(flattening,[],[f15])).
% 2.41/1.00  
% 2.41/1.00  fof(f25,plain,(
% 2.41/1.00    ? [X0,X1,X2] : (((? [X3] : (~r2_hidden(X1,X3) & r2_hidden(X3,X2)) | ~r2_hidden(X1,k8_setfam_1(X0,X2))) & (! [X3] : (r2_hidden(X1,X3) | ~r2_hidden(X3,X2)) | r2_hidden(X1,k8_setfam_1(X0,X2)))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.41/1.00    inference(nnf_transformation,[],[f16])).
% 2.41/1.00  
% 2.41/1.00  fof(f26,plain,(
% 2.41/1.00    ? [X0,X1,X2] : ((? [X3] : (~r2_hidden(X1,X3) & r2_hidden(X3,X2)) | ~r2_hidden(X1,k8_setfam_1(X0,X2))) & (! [X3] : (r2_hidden(X1,X3) | ~r2_hidden(X3,X2)) | r2_hidden(X1,k8_setfam_1(X0,X2))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.41/1.00    inference(flattening,[],[f25])).
% 2.41/1.00  
% 2.41/1.00  fof(f27,plain,(
% 2.41/1.00    ? [X0,X1,X2] : ((? [X3] : (~r2_hidden(X1,X3) & r2_hidden(X3,X2)) | ~r2_hidden(X1,k8_setfam_1(X0,X2))) & (! [X4] : (r2_hidden(X1,X4) | ~r2_hidden(X4,X2)) | r2_hidden(X1,k8_setfam_1(X0,X2))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.41/1.00    inference(rectify,[],[f26])).
% 2.41/1.00  
% 2.41/1.00  fof(f29,plain,(
% 2.41/1.00    ( ! [X2,X1] : (? [X3] : (~r2_hidden(X1,X3) & r2_hidden(X3,X2)) => (~r2_hidden(X1,sK6) & r2_hidden(sK6,X2))) )),
% 2.41/1.00    introduced(choice_axiom,[])).
% 2.41/1.00  
% 2.41/1.00  fof(f28,plain,(
% 2.41/1.00    ? [X0,X1,X2] : ((? [X3] : (~r2_hidden(X1,X3) & r2_hidden(X3,X2)) | ~r2_hidden(X1,k8_setfam_1(X0,X2))) & (! [X4] : (r2_hidden(X1,X4) | ~r2_hidden(X4,X2)) | r2_hidden(X1,k8_setfam_1(X0,X2))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) => ((? [X3] : (~r2_hidden(sK4,X3) & r2_hidden(X3,sK5)) | ~r2_hidden(sK4,k8_setfam_1(sK3,sK5))) & (! [X4] : (r2_hidden(sK4,X4) | ~r2_hidden(X4,sK5)) | r2_hidden(sK4,k8_setfam_1(sK3,sK5))) & r2_hidden(sK4,sK3) & m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK3))))),
% 2.41/1.00    introduced(choice_axiom,[])).
% 2.41/1.00  
% 2.41/1.00  fof(f30,plain,(
% 2.41/1.00    ((~r2_hidden(sK4,sK6) & r2_hidden(sK6,sK5)) | ~r2_hidden(sK4,k8_setfam_1(sK3,sK5))) & (! [X4] : (r2_hidden(sK4,X4) | ~r2_hidden(X4,sK5)) | r2_hidden(sK4,k8_setfam_1(sK3,sK5))) & r2_hidden(sK4,sK3) & m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK3)))),
% 2.41/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f27,f29,f28])).
% 2.41/1.00  
% 2.41/1.00  fof(f48,plain,(
% 2.41/1.00    m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK3)))),
% 2.41/1.00    inference(cnf_transformation,[],[f30])).
% 2.41/1.00  
% 2.41/1.00  fof(f4,axiom,(
% 2.41/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 2.41/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.41/1.00  
% 2.41/1.00  fof(f10,plain,(
% 2.41/1.00    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.41/1.00    inference(ennf_transformation,[],[f4])).
% 2.41/1.00  
% 2.41/1.00  fof(f36,plain,(
% 2.41/1.00    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.41/1.00    inference(cnf_transformation,[],[f10])).
% 2.41/1.00  
% 2.41/1.00  fof(f6,axiom,(
% 2.41/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 2.41/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.41/1.00  
% 2.41/1.00  fof(f12,plain,(
% 2.41/1.00    ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.41/1.00    inference(ennf_transformation,[],[f6])).
% 2.41/1.00  
% 2.41/1.00  fof(f46,plain,(
% 2.41/1.00    ( ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.41/1.00    inference(cnf_transformation,[],[f12])).
% 2.41/1.00  
% 2.41/1.00  fof(f51,plain,(
% 2.41/1.00    r2_hidden(sK6,sK5) | ~r2_hidden(sK4,k8_setfam_1(sK3,sK5))),
% 2.41/1.00    inference(cnf_transformation,[],[f30])).
% 2.41/1.00  
% 2.41/1.00  fof(f50,plain,(
% 2.41/1.00    ( ! [X4] : (r2_hidden(sK4,X4) | ~r2_hidden(X4,sK5) | r2_hidden(sK4,k8_setfam_1(sK3,sK5))) )),
% 2.41/1.00    inference(cnf_transformation,[],[f30])).
% 2.41/1.00  
% 2.41/1.00  fof(f40,plain,(
% 2.41/1.00    ( ! [X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(X5,sK2(X0,X5)) | k1_setfam_1(X0) != X1 | k1_xboole_0 = X0) )),
% 2.41/1.00    inference(cnf_transformation,[],[f24])).
% 2.41/1.00  
% 2.41/1.00  fof(f60,plain,(
% 2.41/1.00    ( ! [X0,X5] : (r2_hidden(X5,k1_setfam_1(X0)) | ~r2_hidden(X5,sK2(X0,X5)) | k1_xboole_0 = X0) )),
% 2.41/1.00    inference(equality_resolution,[],[f40])).
% 2.41/1.00  
% 2.41/1.00  fof(f52,plain,(
% 2.41/1.00    ~r2_hidden(sK4,sK6) | ~r2_hidden(sK4,k8_setfam_1(sK3,sK5))),
% 2.41/1.00    inference(cnf_transformation,[],[f30])).
% 2.41/1.00  
% 2.41/1.00  fof(f38,plain,(
% 2.41/1.00    ( ! [X0,X7,X5,X1] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0) | ~r2_hidden(X5,X1) | k1_setfam_1(X0) != X1 | k1_xboole_0 = X0) )),
% 2.41/1.00    inference(cnf_transformation,[],[f24])).
% 2.41/1.00  
% 2.41/1.00  fof(f62,plain,(
% 2.41/1.00    ( ! [X0,X7,X5] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0) | ~r2_hidden(X5,k1_setfam_1(X0)) | k1_xboole_0 = X0) )),
% 2.41/1.00    inference(equality_resolution,[],[f38])).
% 2.41/1.00  
% 2.41/1.00  fof(f37,plain,(
% 2.41/1.00    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.41/1.00    inference(cnf_transformation,[],[f10])).
% 2.41/1.00  
% 2.41/1.00  fof(f55,plain,(
% 2.41/1.00    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.41/1.00    inference(equality_resolution,[],[f37])).
% 2.41/1.00  
% 2.41/1.00  fof(f3,axiom,(
% 2.41/1.00    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.41/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.41/1.00  
% 2.41/1.00  fof(f35,plain,(
% 2.41/1.00    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.41/1.00    inference(cnf_transformation,[],[f3])).
% 2.41/1.00  
% 2.41/1.00  fof(f49,plain,(
% 2.41/1.00    r2_hidden(sK4,sK3)),
% 2.41/1.00    inference(cnf_transformation,[],[f30])).
% 2.41/1.00  
% 2.41/1.00  fof(f1,axiom,(
% 2.41/1.00    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.41/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.41/1.00  
% 2.41/1.00  fof(f17,plain,(
% 2.41/1.00    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 2.41/1.00    inference(nnf_transformation,[],[f1])).
% 2.41/1.00  
% 2.41/1.00  fof(f18,plain,(
% 2.41/1.00    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 2.41/1.00    inference(flattening,[],[f17])).
% 2.41/1.00  
% 2.41/1.00  fof(f33,plain,(
% 2.41/1.00    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 2.41/1.00    inference(cnf_transformation,[],[f18])).
% 2.41/1.00  
% 2.41/1.00  fof(f53,plain,(
% 2.41/1.00    ( ! [X0] : (k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0) )),
% 2.41/1.00    inference(equality_resolution,[],[f33])).
% 2.41/1.00  
% 2.41/1.00  fof(f2,axiom,(
% 2.41/1.00    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 2.41/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.41/1.00  
% 2.41/1.00  fof(f34,plain,(
% 2.41/1.00    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 2.41/1.00    inference(cnf_transformation,[],[f2])).
% 2.41/1.00  
% 2.41/1.00  cnf(c_13,plain,
% 2.41/1.00      ( r2_hidden(X0,k1_setfam_1(X1))
% 2.41/1.00      | r2_hidden(sK2(X1,X0),X1)
% 2.41/1.00      | k1_xboole_0 = X1 ),
% 2.41/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.41/1.00  
% 2.41/1.00  cnf(c_609,plain,
% 2.41/1.00      ( k1_xboole_0 = X0
% 2.41/1.00      | r2_hidden(X1,k1_setfam_1(X0)) = iProver_top
% 2.41/1.00      | r2_hidden(sK2(X0,X1),X0) = iProver_top ),
% 2.41/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.41/1.00  
% 2.41/1.00  cnf(c_21,negated_conjecture,
% 2.41/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK3))) ),
% 2.41/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.41/1.00  
% 2.41/1.00  cnf(c_601,plain,
% 2.41/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK3))) = iProver_top ),
% 2.41/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.41/1.00  
% 2.41/1.00  cnf(c_6,plain,
% 2.41/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.41/1.00      | k6_setfam_1(X1,X0) = k8_setfam_1(X1,X0)
% 2.41/1.00      | k1_xboole_0 = X0 ),
% 2.41/1.00      inference(cnf_transformation,[],[f36]) ).
% 2.41/1.00  
% 2.41/1.00  cnf(c_614,plain,
% 2.41/1.00      ( k6_setfam_1(X0,X1) = k8_setfam_1(X0,X1)
% 2.41/1.00      | k1_xboole_0 = X1
% 2.41/1.00      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.41/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.41/1.00  
% 2.41/1.00  cnf(c_1633,plain,
% 2.41/1.00      ( k6_setfam_1(sK3,sK5) = k8_setfam_1(sK3,sK5) | sK5 = k1_xboole_0 ),
% 2.41/1.00      inference(superposition,[status(thm)],[c_601,c_614]) ).
% 2.41/1.00  
% 2.41/1.00  cnf(c_15,plain,
% 2.41/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.41/1.00      | k6_setfam_1(X1,X0) = k1_setfam_1(X0) ),
% 2.41/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.41/1.00  
% 2.41/1.00  cnf(c_607,plain,
% 2.41/1.00      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
% 2.41/1.00      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.41/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.41/1.00  
% 2.41/1.00  cnf(c_1407,plain,
% 2.41/1.00      ( k6_setfam_1(sK3,sK5) = k1_setfam_1(sK5) ),
% 2.41/1.00      inference(superposition,[status(thm)],[c_601,c_607]) ).
% 2.41/1.00  
% 2.41/1.00  cnf(c_1636,plain,
% 2.41/1.00      ( k8_setfam_1(sK3,sK5) = k1_setfam_1(sK5) | sK5 = k1_xboole_0 ),
% 2.41/1.00      inference(light_normalisation,[status(thm)],[c_1633,c_1407]) ).
% 2.41/1.00  
% 2.41/1.00  cnf(c_18,negated_conjecture,
% 2.41/1.00      ( r2_hidden(sK6,sK5) | ~ r2_hidden(sK4,k8_setfam_1(sK3,sK5)) ),
% 2.41/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.41/1.00  
% 2.41/1.00  cnf(c_604,plain,
% 2.41/1.00      ( r2_hidden(sK6,sK5) = iProver_top
% 2.41/1.00      | r2_hidden(sK4,k8_setfam_1(sK3,sK5)) != iProver_top ),
% 2.41/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.41/1.00  
% 2.41/1.00  cnf(c_1702,plain,
% 2.41/1.00      ( sK5 = k1_xboole_0
% 2.41/1.00      | r2_hidden(sK6,sK5) = iProver_top
% 2.41/1.00      | r2_hidden(sK4,k1_setfam_1(sK5)) != iProver_top ),
% 2.41/1.00      inference(superposition,[status(thm)],[c_1636,c_604]) ).
% 2.41/1.00  
% 2.41/1.00  cnf(c_27,plain,
% 2.41/1.00      ( r2_hidden(sK6,sK5) = iProver_top
% 2.41/1.00      | r2_hidden(sK4,k8_setfam_1(sK3,sK5)) != iProver_top ),
% 2.41/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.41/1.00  
% 2.41/1.00  cnf(c_19,negated_conjecture,
% 2.41/1.00      ( ~ r2_hidden(X0,sK5)
% 2.41/1.00      | r2_hidden(sK4,X0)
% 2.41/1.00      | r2_hidden(sK4,k8_setfam_1(sK3,sK5)) ),
% 2.41/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.41/1.00  
% 2.41/1.00  cnf(c_603,plain,
% 2.41/1.00      ( r2_hidden(X0,sK5) != iProver_top
% 2.41/1.00      | r2_hidden(sK4,X0) = iProver_top
% 2.41/1.00      | r2_hidden(sK4,k8_setfam_1(sK3,sK5)) = iProver_top ),
% 2.41/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.41/1.00  
% 2.41/1.00  cnf(c_1533,plain,
% 2.41/1.00      ( sK5 = k1_xboole_0
% 2.41/1.00      | r2_hidden(X0,k1_setfam_1(sK5)) = iProver_top
% 2.41/1.00      | r2_hidden(sK4,sK2(sK5,X0)) = iProver_top
% 2.41/1.00      | r2_hidden(sK4,k8_setfam_1(sK3,sK5)) = iProver_top ),
% 2.41/1.00      inference(superposition,[status(thm)],[c_609,c_603]) ).
% 2.41/1.00  
% 2.41/1.00  cnf(c_12,plain,
% 2.41/1.00      ( ~ r2_hidden(X0,sK2(X1,X0))
% 2.41/1.00      | r2_hidden(X0,k1_setfam_1(X1))
% 2.41/1.00      | k1_xboole_0 = X1 ),
% 2.41/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.41/1.00  
% 2.41/1.00  cnf(c_610,plain,
% 2.41/1.00      ( k1_xboole_0 = X0
% 2.41/1.00      | r2_hidden(X1,sK2(X0,X1)) != iProver_top
% 2.41/1.00      | r2_hidden(X1,k1_setfam_1(X0)) = iProver_top ),
% 2.41/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.41/1.00  
% 2.41/1.00  cnf(c_1678,plain,
% 2.41/1.00      ( sK5 = k1_xboole_0
% 2.41/1.00      | r2_hidden(sK4,k8_setfam_1(sK3,sK5)) = iProver_top
% 2.41/1.00      | r2_hidden(sK4,k1_setfam_1(sK5)) = iProver_top ),
% 2.41/1.00      inference(superposition,[status(thm)],[c_1533,c_610]) ).
% 2.41/1.00  
% 2.41/1.00  cnf(c_1770,plain,
% 2.41/1.00      ( r2_hidden(sK6,sK5) = iProver_top | sK5 = k1_xboole_0 ),
% 2.41/1.00      inference(global_propositional_subsumption,
% 2.41/1.00                [status(thm)],
% 2.41/1.00                [c_1702,c_27,c_1678]) ).
% 2.41/1.00  
% 2.41/1.00  cnf(c_1771,plain,
% 2.41/1.00      ( sK5 = k1_xboole_0 | r2_hidden(sK6,sK5) = iProver_top ),
% 2.41/1.00      inference(renaming,[status(thm)],[c_1770]) ).
% 2.41/1.00  
% 2.41/1.00  cnf(c_1777,plain,
% 2.41/1.00      ( sK5 = k1_xboole_0
% 2.41/1.00      | r2_hidden(sK4,k8_setfam_1(sK3,sK5)) = iProver_top
% 2.41/1.00      | r2_hidden(sK4,sK6) = iProver_top ),
% 2.41/1.00      inference(superposition,[status(thm)],[c_1771,c_603]) ).
% 2.41/1.00  
% 2.41/1.00  cnf(c_17,negated_conjecture,
% 2.41/1.00      ( ~ r2_hidden(sK4,k8_setfam_1(sK3,sK5)) | ~ r2_hidden(sK4,sK6) ),
% 2.41/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.41/1.00  
% 2.41/1.00  cnf(c_605,plain,
% 2.41/1.00      ( r2_hidden(sK4,k8_setfam_1(sK3,sK5)) != iProver_top
% 2.41/1.00      | r2_hidden(sK4,sK6) != iProver_top ),
% 2.41/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.41/1.00  
% 2.41/1.00  cnf(c_1701,plain,
% 2.41/1.00      ( sK5 = k1_xboole_0
% 2.41/1.00      | r2_hidden(sK4,k1_setfam_1(sK5)) != iProver_top
% 2.41/1.00      | r2_hidden(sK4,sK6) != iProver_top ),
% 2.41/1.00      inference(superposition,[status(thm)],[c_1636,c_605]) ).
% 2.41/1.00  
% 2.41/1.00  cnf(c_28,plain,
% 2.41/1.00      ( r2_hidden(sK4,k8_setfam_1(sK3,sK5)) != iProver_top
% 2.41/1.00      | r2_hidden(sK4,sK6) != iProver_top ),
% 2.41/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.41/1.00  
% 2.41/1.00  cnf(c_1763,plain,
% 2.41/1.00      ( sK5 = k1_xboole_0 | r2_hidden(sK4,sK6) != iProver_top ),
% 2.41/1.00      inference(global_propositional_subsumption,
% 2.41/1.00                [status(thm)],
% 2.41/1.00                [c_1701,c_28,c_1678]) ).
% 2.41/1.00  
% 2.41/1.00  cnf(c_1822,plain,
% 2.41/1.00      ( r2_hidden(sK4,k8_setfam_1(sK3,sK5)) = iProver_top | sK5 = k1_xboole_0 ),
% 2.41/1.00      inference(global_propositional_subsumption,[status(thm)],[c_1777,c_1763]) ).
% 2.41/1.00  
% 2.41/1.00  cnf(c_1823,plain,
% 2.41/1.00      ( sK5 = k1_xboole_0 | r2_hidden(sK4,k8_setfam_1(sK3,sK5)) = iProver_top ),
% 2.41/1.00      inference(renaming,[status(thm)],[c_1822]) ).
% 2.41/1.00  
% 2.41/1.00  cnf(c_1828,plain,
% 2.41/1.00      ( sK5 = k1_xboole_0 | r2_hidden(sK4,k1_setfam_1(sK5)) = iProver_top ),
% 2.41/1.00      inference(superposition,[status(thm)],[c_1636,c_1823]) ).
% 2.41/1.00  
% 2.41/1.00  cnf(c_14,plain,
% 2.41/1.00      ( ~ r2_hidden(X0,X1)
% 2.41/1.00      | r2_hidden(X2,X0)
% 2.41/1.00      | ~ r2_hidden(X2,k1_setfam_1(X1))
% 2.41/1.00      | k1_xboole_0 = X1 ),
% 2.41/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.41/1.00  
% 2.41/1.00  cnf(c_608,plain,
% 2.41/1.00      ( k1_xboole_0 = X0
% 2.41/1.00      | r2_hidden(X1,X0) != iProver_top
% 2.41/1.00      | r2_hidden(X2,X1) = iProver_top
% 2.41/1.00      | r2_hidden(X2,k1_setfam_1(X0)) != iProver_top ),
% 2.41/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.41/1.00  
% 2.41/1.00  cnf(c_1848,plain,
% 2.41/1.00      ( sK5 = k1_xboole_0
% 2.41/1.00      | r2_hidden(X0,sK5) != iProver_top
% 2.41/1.00      | r2_hidden(sK4,X0) = iProver_top ),
% 2.41/1.00      inference(superposition,[status(thm)],[c_1828,c_608]) ).
% 2.41/1.00  
% 2.41/1.00  cnf(c_2212,plain,
% 2.41/1.00      ( sK5 = k1_xboole_0
% 2.41/1.00      | r2_hidden(X0,k1_setfam_1(sK5)) = iProver_top
% 2.41/1.00      | r2_hidden(sK4,sK2(sK5,X0)) = iProver_top ),
% 2.41/1.00      inference(superposition,[status(thm)],[c_609,c_1848]) ).
% 2.41/1.00  
% 2.41/1.00  cnf(c_2211,plain,
% 2.41/1.00      ( sK5 = k1_xboole_0 | r2_hidden(sK4,sK6) = iProver_top ),
% 2.41/1.00      inference(superposition,[status(thm)],[c_1771,c_1848]) ).
% 2.41/1.00  
% 2.41/1.00  cnf(c_2254,plain,
% 2.41/1.00      ( sK5 = k1_xboole_0 ),
% 2.41/1.00      inference(global_propositional_subsumption,
% 2.41/1.00                [status(thm)],
% 2.41/1.00                [c_2212,c_1763,c_2211]) ).
% 2.41/1.00  
% 2.41/1.00  cnf(c_2264,plain,
% 2.41/1.00      ( r2_hidden(sK6,k1_xboole_0) = iProver_top
% 2.41/1.00      | r2_hidden(sK4,k8_setfam_1(sK3,k1_xboole_0)) != iProver_top ),
% 2.41/1.00      inference(demodulation,[status(thm)],[c_2254,c_604]) ).
% 2.41/1.00  
% 2.41/1.00  cnf(c_5,plain,
% 2.41/1.00      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
% 2.41/1.00      | k8_setfam_1(X0,k1_xboole_0) = X0 ),
% 2.41/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.41/1.00  
% 2.41/1.00  cnf(c_615,plain,
% 2.41/1.00      ( k8_setfam_1(X0,k1_xboole_0) = X0
% 2.41/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.41/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.41/1.00  
% 2.41/1.00  cnf(c_4,plain,
% 2.41/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.41/1.00      inference(cnf_transformation,[],[f35]) ).
% 2.41/1.00  
% 2.41/1.00  cnf(c_616,plain,
% 2.41/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.41/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.41/1.00  
% 2.41/1.00  cnf(c_638,plain,
% 2.41/1.00      ( k8_setfam_1(X0,k1_xboole_0) = X0 ),
% 2.41/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_615,c_616]) ).
% 2.41/1.00  
% 2.41/1.00  cnf(c_2269,plain,
% 2.41/1.00      ( r2_hidden(sK6,k1_xboole_0) = iProver_top
% 2.41/1.00      | r2_hidden(sK4,sK3) != iProver_top ),
% 2.41/1.00      inference(demodulation,[status(thm)],[c_2264,c_638]) ).
% 2.41/1.00  
% 2.41/1.00  cnf(c_20,negated_conjecture,
% 2.41/1.00      ( r2_hidden(sK4,sK3) ),
% 2.41/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.41/1.00  
% 2.41/1.00  cnf(c_23,plain,
% 2.41/1.00      ( r2_hidden(sK4,sK3) = iProver_top ),
% 2.41/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.41/1.00  
% 2.41/1.00  cnf(c_2331,plain,
% 2.41/1.00      ( r2_hidden(sK6,k1_xboole_0) = iProver_top ),
% 2.41/1.00      inference(global_propositional_subsumption,[status(thm)],[c_2269,c_23]) ).
% 2.41/1.00  
% 2.41/1.00  cnf(c_0,plain,
% 2.41/1.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.41/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.41/1.00  
% 2.41/1.00  cnf(c_3,plain,
% 2.41/1.00      ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
% 2.41/1.00      inference(cnf_transformation,[],[f34]) ).
% 2.41/1.00  
% 2.41/1.00  cnf(c_617,plain,
% 2.41/1.00      ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 2.41/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.41/1.00  
% 2.41/1.00  cnf(c_1130,plain,
% 2.41/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.41/1.00      inference(superposition,[status(thm)],[c_0,c_617]) ).
% 2.41/1.00  
% 2.41/1.00  cnf(c_2336,plain,
% 2.41/1.00      ( $false ),
% 2.41/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_2331,c_1130]) ).
% 2.41/1.00  
% 2.41/1.00  
% 2.41/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.41/1.00  
% 2.41/1.00  ------                               Statistics
% 2.41/1.00  
% 2.41/1.00  ------ General
% 2.41/1.00  
% 2.41/1.00  abstr_ref_over_cycles:                  0
% 2.41/1.00  abstr_ref_under_cycles:                 0
% 2.41/1.00  gc_basic_clause_elim:                   0
% 2.41/1.00  forced_gc_time:                         0
% 2.41/1.00  parsing_time:                           0.019
% 2.41/1.00  unif_index_cands_time:                  0.
% 2.41/1.00  unif_index_add_time:                    0.
% 2.41/1.00  orderings_time:                         0.
% 2.41/1.00  out_proof_time:                         0.01
% 2.41/1.00  total_time:                             0.111
% 2.41/1.00  num_of_symbols:                         46
% 2.41/1.00  num_of_terms:                           2053
% 2.41/1.00  
% 2.41/1.00  ------ Preprocessing
% 2.41/1.00  
% 2.41/1.00  num_of_splits:                          0
% 2.41/1.00  num_of_split_atoms:                     0
% 2.41/1.00  num_of_reused_defs:                     0
% 2.41/1.00  num_eq_ax_congr_red:                    24
% 2.41/1.00  num_of_sem_filtered_clauses:            1
% 2.41/1.00  num_of_subtypes:                        0
% 2.41/1.00  monotx_restored_types:                  0
% 2.41/1.00  sat_num_of_epr_types:                   0
% 2.41/1.00  sat_num_of_non_cyclic_types:            0
% 2.41/1.00  sat_guarded_non_collapsed_types:        0
% 2.41/1.00  num_pure_diseq_elim:                    0
% 2.41/1.00  simp_replaced_by:                       0
% 2.41/1.00  res_preprocessed:                       101
% 2.41/1.00  prep_upred:                             0
% 2.41/1.00  prep_unflattend:                        0
% 2.41/1.00  smt_new_axioms:                         0
% 2.41/1.00  pred_elim_cands:                        2
% 2.41/1.00  pred_elim:                              0
% 2.41/1.00  pred_elim_cl:                           0
% 2.41/1.00  pred_elim_cycles:                       2
% 2.41/1.00  merged_defs:                            0
% 2.41/1.00  merged_defs_ncl:                        0
% 2.41/1.00  bin_hyper_res:                          0
% 2.41/1.00  prep_cycles:                            4
% 2.41/1.00  pred_elim_time:                         0.
% 2.41/1.00  splitting_time:                         0.
% 2.41/1.00  sem_filter_time:                        0.
% 2.41/1.00  monotx_time:                            0.
% 2.41/1.00  subtype_inf_time:                       0.
% 2.41/1.00  
% 2.41/1.00  ------ Problem properties
% 2.41/1.00  
% 2.41/1.00  clauses:                                21
% 2.41/1.00  conjectures:                            5
% 2.41/1.00  epr:                                    1
% 2.41/1.00  horn:                                   12
% 2.41/1.00  ground:                                 5
% 2.41/1.00  unary:                                  7
% 2.41/1.00  binary:                                 4
% 2.41/1.00  lits:                                   50
% 2.41/1.00  lits_eq:                                19
% 2.41/1.00  fd_pure:                                0
% 2.41/1.00  fd_pseudo:                              0
% 2.41/1.00  fd_cond:                                5
% 2.41/1.00  fd_pseudo_cond:                         3
% 2.41/1.00  ac_symbols:                             0
% 2.41/1.00  
% 2.41/1.00  ------ Propositional Solver
% 2.41/1.00  
% 2.41/1.00  prop_solver_calls:                      26
% 2.41/1.00  prop_fast_solver_calls:                 601
% 2.41/1.00  smt_solver_calls:                       0
% 2.41/1.00  smt_fast_solver_calls:                  0
% 2.41/1.00  prop_num_of_clauses:                    704
% 2.41/1.00  prop_preprocess_simplified:             3235
% 2.41/1.00  prop_fo_subsumed:                       7
% 2.41/1.00  prop_solver_time:                       0.
% 2.41/1.00  smt_solver_time:                        0.
% 2.41/1.00  smt_fast_solver_time:                   0.
% 2.41/1.00  prop_fast_solver_time:                  0.
% 2.41/1.00  prop_unsat_core_time:                   0.
% 2.41/1.00  
% 2.41/1.00  ------ QBF
% 2.41/1.00  
% 2.41/1.00  qbf_q_res:                              0
% 2.41/1.00  qbf_num_tautologies:                    0
% 2.41/1.00  qbf_prep_cycles:                        0
% 2.41/1.00  
% 2.41/1.00  ------ BMC1
% 2.41/1.00  
% 2.41/1.00  bmc1_current_bound:                     -1
% 2.41/1.00  bmc1_last_solved_bound:                 -1
% 2.41/1.00  bmc1_unsat_core_size:                   -1
% 2.41/1.00  bmc1_unsat_core_parents_size:           -1
% 2.41/1.00  bmc1_merge_next_fun:                    0
% 2.41/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.41/1.00  
% 2.41/1.00  ------ Instantiation
% 2.41/1.00  
% 2.41/1.00  inst_num_of_clauses:                    221
% 2.41/1.00  inst_num_in_passive:                    57
% 2.41/1.00  inst_num_in_active:                     137
% 2.41/1.00  inst_num_in_unprocessed:                27
% 2.41/1.00  inst_num_of_loops:                      190
% 2.41/1.00  inst_num_of_learning_restarts:          0
% 2.41/1.00  inst_num_moves_active_passive:          50
% 2.41/1.00  inst_lit_activity:                      0
% 2.41/1.00  inst_lit_activity_moves:                0
% 2.41/1.00  inst_num_tautologies:                   0
% 2.41/1.00  inst_num_prop_implied:                  0
% 2.41/1.00  inst_num_existing_simplified:           0
% 2.41/1.00  inst_num_eq_res_simplified:             0
% 2.41/1.00  inst_num_child_elim:                    0
% 2.41/1.00  inst_num_of_dismatching_blockings:      52
% 2.41/1.00  inst_num_of_non_proper_insts:           170
% 2.41/1.00  inst_num_of_duplicates:                 0
% 2.41/1.00  inst_inst_num_from_inst_to_res:         0
% 2.41/1.00  inst_dismatching_checking_time:         0.
% 2.41/1.00  
% 2.41/1.00  ------ Resolution
% 2.41/1.00  
% 2.41/1.00  res_num_of_clauses:                     0
% 2.41/1.00  res_num_in_passive:                     0
% 2.41/1.00  res_num_in_active:                      0
% 2.41/1.00  res_num_of_loops:                       105
% 2.41/1.00  res_forward_subset_subsumed:            33
% 2.41/1.00  res_backward_subset_subsumed:           0
% 2.41/1.00  res_forward_subsumed:                   0
% 2.41/1.00  res_backward_subsumed:                  0
% 2.41/1.00  res_forward_subsumption_resolution:     0
% 2.41/1.00  res_backward_subsumption_resolution:    0
% 2.41/1.00  res_clause_to_clause_subsumption:       190
% 2.41/1.00  res_orphan_elimination:                 0
% 2.41/1.00  res_tautology_del:                      4
% 2.41/1.00  res_num_eq_res_simplified:              0
% 2.41/1.00  res_num_sel_changes:                    0
% 2.41/1.00  res_moves_from_active_to_pass:          0
% 2.41/1.00  
% 2.41/1.00  ------ Superposition
% 2.41/1.00  
% 2.41/1.00  sup_time_total:                         0.
% 2.41/1.00  sup_time_generating:                    0.
% 2.41/1.00  sup_time_sim_full:                      0.
% 2.41/1.00  sup_time_sim_immed:                     0.
% 2.41/1.00  
% 2.41/1.00  sup_num_of_clauses:                     40
% 2.41/1.00  sup_num_in_active:                      20
% 2.41/1.00  sup_num_in_passive:                     20
% 2.41/1.00  sup_num_of_loops:                       36
% 2.41/1.00  sup_fw_superposition:                   19
% 2.41/1.00  sup_bw_superposition:                   27
% 2.41/1.00  sup_immediate_simplified:               13
% 2.41/1.00  sup_given_eliminated:                   0
% 2.41/1.00  comparisons_done:                       0
% 2.41/1.00  comparisons_avoided:                    6
% 2.41/1.00  
% 2.41/1.00  ------ Simplifications
% 2.41/1.00  
% 2.41/1.00  
% 2.41/1.00  sim_fw_subset_subsumed:                 3
% 2.41/1.00  sim_bw_subset_subsumed:                 12
% 2.41/1.00  sim_fw_subsumed:                        6
% 2.41/1.00  sim_bw_subsumed:                        1
% 2.41/1.00  sim_fw_subsumption_res:                 3
% 2.41/1.00  sim_bw_subsumption_res:                 0
% 2.41/1.00  sim_tautology_del:                      0
% 2.41/1.00  sim_eq_tautology_del:                   4
% 2.41/1.00  sim_eq_res_simp:                        1
% 2.41/1.00  sim_fw_demodulated:                     4
% 2.41/1.00  sim_bw_demodulated:                     9
% 2.41/1.00  sim_light_normalised:                   5
% 2.41/1.00  sim_joinable_taut:                      0
% 2.41/1.00  sim_joinable_simp:                      0
% 2.41/1.00  sim_ac_normalised:                      0
% 2.41/1.00  sim_smt_subsumption:                    0
% 2.41/1.00  
%------------------------------------------------------------------------------
