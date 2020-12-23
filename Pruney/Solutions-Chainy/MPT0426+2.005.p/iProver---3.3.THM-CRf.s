%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:42:25 EST 2020

% Result     : Theorem 3.49s
% Output     : CNFRefutation 3.49s
% Verified   : 
% Statistics : Number of formulae       :  111 (3723 expanded)
%              Number of clauses        :   64 (1059 expanded)
%              Number of leaves         :   14 ( 879 expanded)
%              Depth                    :   27
%              Number of atoms          :  454 (21561 expanded)
%              Number of equality atoms :  178 (4261 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

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

fof(f9,plain,(
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
    inference(nnf_transformation,[],[f9])).

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
     => ( ~ r2_hidden(X5,sK3(X0,X5))
        & r2_hidden(sK3(X0,X5),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X2,X3)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(X2,sK2(X0,X1))
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
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
              ( ~ r2_hidden(sK1(X0,X1),X3)
              & r2_hidden(X3,X0) )
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ! [X4] :
              ( r2_hidden(sK1(X0,X1),X4)
              | ~ r2_hidden(X4,X0) )
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ( ( ( ~ r2_hidden(sK1(X0,X1),sK2(X0,X1))
                  & r2_hidden(sK2(X0,X1),X0) )
                | ~ r2_hidden(sK1(X0,X1),X1) )
              & ( ! [X4] :
                    ( r2_hidden(sK1(X0,X1),X4)
                    | ~ r2_hidden(X4,X0) )
                | r2_hidden(sK1(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ( ~ r2_hidden(X5,sK3(X0,X5))
                    & r2_hidden(sK3(X0,X5),X0) ) )
                & ( ! [X7] :
                      ( r2_hidden(X5,X7)
                      | ~ r2_hidden(X7,X0) )
                  | ~ r2_hidden(X5,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f19,f22,f21,f20])).

fof(f40,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | r2_hidden(sK3(X0,X5),X0)
      | k1_setfam_1(X0) != X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f62,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,k1_setfam_1(X0))
      | r2_hidden(sK3(X0,X5),X0)
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f40])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( r2_hidden(X1,X0)
       => ( r2_hidden(X1,k8_setfam_1(X0,X2))
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
             => r2_hidden(X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ( r2_hidden(X1,X0)
         => ( r2_hidden(X1,k8_setfam_1(X0,X2))
          <=> ! [X3] :
                ( r2_hidden(X3,X2)
               => r2_hidden(X1,X3) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,k8_setfam_1(X0,X2))
      <~> ! [X3] :
            ( r2_hidden(X1,X3)
            | ~ r2_hidden(X3,X2) ) )
      & r2_hidden(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,k8_setfam_1(X0,X2))
      <~> ! [X3] :
            ( r2_hidden(X1,X3)
            | ~ r2_hidden(X3,X2) ) )
      & r2_hidden(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f11])).

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
    inference(nnf_transformation,[],[f12])).

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
     => ( ~ r2_hidden(X1,sK7)
        & r2_hidden(sK7,X2) ) ) ),
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
            ( ~ r2_hidden(sK5,X3)
            & r2_hidden(X3,sK6) )
        | ~ r2_hidden(sK5,k8_setfam_1(sK4,sK6)) )
      & ( ! [X4] :
            ( r2_hidden(sK5,X4)
            | ~ r2_hidden(X4,sK6) )
        | r2_hidden(sK5,k8_setfam_1(sK4,sK6)) )
      & r2_hidden(sK5,sK4)
      & m1_subset_1(sK6,k1_zfmisc_1(k1_zfmisc_1(sK4))) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ( ( ~ r2_hidden(sK5,sK7)
        & r2_hidden(sK7,sK6) )
      | ~ r2_hidden(sK5,k8_setfam_1(sK4,sK6)) )
    & ( ! [X4] :
          ( r2_hidden(sK5,X4)
          | ~ r2_hidden(X4,sK6) )
      | r2_hidden(sK5,k8_setfam_1(sK4,sK6)) )
    & r2_hidden(sK5,sK4)
    & m1_subset_1(sK6,k1_zfmisc_1(k1_zfmisc_1(sK4))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f26,f28,f27])).

fof(f50,plain,(
    ! [X4] :
      ( r2_hidden(sK5,X4)
      | ~ r2_hidden(X4,sK6)
      | r2_hidden(sK5,k8_setfam_1(sK4,sK6)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f41,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X5,sK3(X0,X5))
      | k1_setfam_1(X0) != X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f61,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,k1_setfam_1(X0))
      | ~ r2_hidden(X5,sK3(X0,X5))
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f41])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f48,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k1_zfmisc_1(sK4))) ),
    inference(cnf_transformation,[],[f29])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f52,plain,
    ( ~ r2_hidden(sK5,sK7)
    | ~ r2_hidden(sK5,k8_setfam_1(sK4,sK6)) ),
    inference(cnf_transformation,[],[f29])).

fof(f51,plain,
    ( r2_hidden(sK7,sK6)
    | ~ r2_hidden(sK5,k8_setfam_1(sK4,sK6)) ),
    inference(cnf_transformation,[],[f29])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f13])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f14])).

fof(f16,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).

fof(f31,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f54,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f31])).

fof(f39,plain,(
    ! [X0,X7,X5,X1] :
      ( r2_hidden(X5,X7)
      | ~ r2_hidden(X7,X0)
      | ~ r2_hidden(X5,X1)
      | k1_setfam_1(X0) != X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f63,plain,(
    ! [X0,X7,X5] :
      ( r2_hidden(X5,X7)
      | ~ r2_hidden(X7,X0)
      | ~ r2_hidden(X5,k1_setfam_1(X0))
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f39])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f56,plain,(
    ! [X0] :
      ( k8_setfam_1(X0,k1_xboole_0) = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f38])).

fof(f49,plain,(
    r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_15,plain,
    ( r2_hidden(X0,k1_setfam_1(X1))
    | r2_hidden(sK3(X1,X0),X1)
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_654,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(X1,k1_setfam_1(X0)) = iProver_top
    | r2_hidden(sK3(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_20,negated_conjecture,
    ( ~ r2_hidden(X0,sK6)
    | r2_hidden(sK5,X0)
    | r2_hidden(sK5,k8_setfam_1(sK4,sK6)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_650,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(sK5,X0) = iProver_top
    | r2_hidden(sK5,k8_setfam_1(sK4,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1784,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(X0,k1_setfam_1(sK6)) = iProver_top
    | r2_hidden(sK5,sK3(sK6,X0)) = iProver_top
    | r2_hidden(sK5,k8_setfam_1(sK4,sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_654,c_650])).

cnf(c_372,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_894,plain,
    ( sK6 != X0
    | sK6 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_372])).

cnf(c_975,plain,
    ( sK6 != sK6
    | sK6 = k1_xboole_0
    | k1_xboole_0 != sK6 ),
    inference(instantiation,[status(thm)],[c_894])).

cnf(c_371,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_976,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_371])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,sK3(X1,X0))
    | r2_hidden(X0,k1_setfam_1(X1))
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1020,plain,
    ( r2_hidden(X0,k1_setfam_1(sK6))
    | r2_hidden(sK5,sK3(sK6,X0))
    | r2_hidden(sK5,k8_setfam_1(sK4,sK6))
    | k1_xboole_0 = sK6 ),
    inference(resolution,[status(thm)],[c_20,c_15])).

cnf(c_1563,plain,
    ( r2_hidden(sK5,k8_setfam_1(sK4,sK6))
    | r2_hidden(sK5,k1_setfam_1(sK6))
    | k1_xboole_0 = sK6 ),
    inference(resolution,[status(thm)],[c_14,c_1020])).

cnf(c_386,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_371])).

cnf(c_1100,plain,
    ( ~ r2_hidden(sK7,sK6)
    | r2_hidden(sK5,k8_setfam_1(sK4,sK6))
    | r2_hidden(sK5,sK7) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_1388,plain,
    ( sK6 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK6 ),
    inference(instantiation,[status(thm)],[c_372])).

cnf(c_1389,plain,
    ( sK6 != k1_xboole_0
    | k1_xboole_0 = sK6
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1388])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k6_setfam_1(X1,X0) = k8_setfam_1(X1,X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k1_zfmisc_1(sK4))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_241,plain,
    ( k6_setfam_1(X0,X1) = k8_setfam_1(X0,X1)
    | k1_zfmisc_1(k1_zfmisc_1(X0)) != k1_zfmisc_1(k1_zfmisc_1(sK4))
    | sK6 != X1
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_22])).

cnf(c_242,plain,
    ( k6_setfam_1(X0,sK6) = k8_setfam_1(X0,sK6)
    | k1_zfmisc_1(k1_zfmisc_1(X0)) != k1_zfmisc_1(k1_zfmisc_1(sK4))
    | k1_xboole_0 = sK6 ),
    inference(unflattening,[status(thm)],[c_241])).

cnf(c_902,plain,
    ( k6_setfam_1(sK4,sK6) = k8_setfam_1(sK4,sK6)
    | sK6 = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_242])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k6_setfam_1(X1,X0) = k1_setfam_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_232,plain,
    ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
    | k1_zfmisc_1(k1_zfmisc_1(X0)) != k1_zfmisc_1(k1_zfmisc_1(sK4))
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_22])).

cnf(c_233,plain,
    ( k6_setfam_1(X0,sK6) = k1_setfam_1(sK6)
    | k1_zfmisc_1(k1_zfmisc_1(X0)) != k1_zfmisc_1(k1_zfmisc_1(sK4)) ),
    inference(unflattening,[status(thm)],[c_232])).

cnf(c_867,plain,
    ( k6_setfam_1(sK4,sK6) = k1_setfam_1(sK6) ),
    inference(equality_resolution,[status(thm)],[c_233])).

cnf(c_1404,plain,
    ( k8_setfam_1(sK4,sK6) = k1_setfam_1(sK6)
    | sK6 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_902,c_867])).

cnf(c_18,negated_conjecture,
    ( ~ r2_hidden(sK5,k8_setfam_1(sK4,sK6))
    | ~ r2_hidden(sK5,sK7) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_652,plain,
    ( r2_hidden(sK5,k8_setfam_1(sK4,sK6)) != iProver_top
    | r2_hidden(sK5,sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1407,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(sK5,k1_setfam_1(sK6)) != iProver_top
    | r2_hidden(sK5,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1404,c_652])).

cnf(c_1421,plain,
    ( ~ r2_hidden(sK5,k1_setfam_1(sK6))
    | ~ r2_hidden(sK5,sK7)
    | sK6 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1407])).

cnf(c_19,negated_conjecture,
    ( r2_hidden(sK7,sK6)
    | ~ r2_hidden(sK5,k8_setfam_1(sK4,sK6)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_651,plain,
    ( r2_hidden(sK7,sK6) = iProver_top
    | r2_hidden(sK5,k8_setfam_1(sK4,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1408,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(sK7,sK6) = iProver_top
    | r2_hidden(sK5,k1_setfam_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1404,c_651])).

cnf(c_1422,plain,
    ( r2_hidden(sK7,sK6)
    | ~ r2_hidden(sK5,k1_setfam_1(sK6))
    | sK6 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1408])).

cnf(c_1566,plain,
    ( r2_hidden(sK5,k8_setfam_1(sK4,sK6))
    | k1_xboole_0 = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1563,c_386,c_1100,c_1389,c_1421,c_1422])).

cnf(c_1568,plain,
    ( k1_xboole_0 = sK6
    | r2_hidden(sK5,k8_setfam_1(sK4,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1566])).

cnf(c_2410,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(sK5,k8_setfam_1(sK4,sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1784,c_975,c_976,c_1568])).

cnf(c_2419,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(sK7,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_2410,c_651])).

cnf(c_6,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_660,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1540,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_660])).

cnf(c_2611,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(sK7,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2419,c_1540])).

cnf(c_2416,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(sK5,k1_setfam_1(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1404,c_2410])).

cnf(c_2418,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(sK5,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2410,c_652])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X0)
    | ~ r2_hidden(X2,k1_setfam_1(X1))
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1052,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK5,X0)
    | ~ r2_hidden(sK5,k1_setfam_1(X1))
    | k1_xboole_0 = X1 ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1370,plain,
    ( ~ r2_hidden(X0,sK6)
    | r2_hidden(sK5,X0)
    | ~ r2_hidden(sK5,k1_setfam_1(sK6))
    | k1_xboole_0 = sK6 ),
    inference(instantiation,[status(thm)],[c_1052])).

cnf(c_3374,plain,
    ( ~ r2_hidden(sK7,sK6)
    | ~ r2_hidden(sK5,k1_setfam_1(sK6))
    | r2_hidden(sK5,sK7)
    | k1_xboole_0 = sK6 ),
    inference(instantiation,[status(thm)],[c_1370])).

cnf(c_3376,plain,
    ( k1_xboole_0 = sK6
    | r2_hidden(sK7,sK6) != iProver_top
    | r2_hidden(sK5,k1_setfam_1(sK6)) != iProver_top
    | r2_hidden(sK5,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3374])).

cnf(c_3410,plain,
    ( sK6 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2611,c_975,c_976,c_2416,c_2418,c_2419,c_3376])).

cnf(c_7,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
    | k8_setfam_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_221,plain,
    ( k8_setfam_1(X0,k1_xboole_0) = X0
    | k1_zfmisc_1(k1_zfmisc_1(X0)) != k1_zfmisc_1(k1_zfmisc_1(sK4))
    | sK6 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_22])).

cnf(c_898,plain,
    ( k8_setfam_1(sK4,k1_xboole_0) = sK4
    | sK6 != k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_221])).

cnf(c_3417,plain,
    ( k8_setfam_1(sK4,k1_xboole_0) = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3410,c_898])).

cnf(c_3452,plain,
    ( k8_setfam_1(sK4,k1_xboole_0) = sK4 ),
    inference(equality_resolution_simp,[status(thm)],[c_3417])).

cnf(c_3424,plain,
    ( r2_hidden(sK7,k1_xboole_0) = iProver_top
    | r2_hidden(sK5,k8_setfam_1(sK4,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3410,c_651])).

cnf(c_3456,plain,
    ( r2_hidden(sK7,k1_xboole_0) = iProver_top
    | r2_hidden(sK5,sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3452,c_3424])).

cnf(c_21,negated_conjecture,
    ( r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_24,plain,
    ( r2_hidden(sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3482,plain,
    ( r2_hidden(sK7,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3456,c_24])).

cnf(c_3487,plain,
    ( r2_hidden(sK7,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3482,c_1540])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3487,c_3456,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:36:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.49/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.49/0.98  
% 3.49/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.49/0.98  
% 3.49/0.98  ------  iProver source info
% 3.49/0.98  
% 3.49/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.49/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.49/0.98  git: non_committed_changes: false
% 3.49/0.98  git: last_make_outside_of_git: false
% 3.49/0.98  
% 3.49/0.98  ------ 
% 3.49/0.98  ------ Parsing...
% 3.49/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.49/0.98  
% 3.49/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.49/0.98  
% 3.49/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.49/0.98  
% 3.49/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.49/0.98  ------ Proving...
% 3.49/0.98  ------ Problem Properties 
% 3.49/0.98  
% 3.49/0.98  
% 3.49/0.98  clauses                                 21
% 3.49/0.98  conjectures                             4
% 3.49/0.98  EPR                                     1
% 3.49/0.98  Horn                                    9
% 3.49/0.98  unary                                   3
% 3.49/0.98  binary                                  5
% 3.49/0.98  lits                                    58
% 3.49/0.98  lits eq                                 22
% 3.49/0.98  fd_pure                                 0
% 3.49/0.98  fd_pseudo                               0
% 3.49/0.98  fd_cond                                 3
% 3.49/0.98  fd_pseudo_cond                          6
% 3.49/0.98  AC symbols                              0
% 3.49/0.98  
% 3.49/0.98  ------ Input Options Time Limit: Unbounded
% 3.49/0.98  
% 3.49/0.98  
% 3.49/0.98  ------ 
% 3.49/0.98  Current options:
% 3.49/0.98  ------ 
% 3.49/0.98  
% 3.49/0.98  
% 3.49/0.98  
% 3.49/0.98  
% 3.49/0.98  ------ Proving...
% 3.49/0.98  
% 3.49/0.98  
% 3.49/0.98  % SZS status Theorem for theBenchmark.p
% 3.49/0.98  
% 3.49/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.49/0.98  
% 3.49/0.98  fof(f4,axiom,(
% 3.49/0.98    ! [X0,X1] : ((k1_xboole_0 = X0 => (k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1)) & (k1_xboole_0 != X0 => (k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X3,X0) => r2_hidden(X2,X3))))))),
% 3.49/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/0.98  
% 3.49/0.98  fof(f9,plain,(
% 3.49/0.98    ! [X0,X1] : (((k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1) | k1_xboole_0 != X0) & ((k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)))) | k1_xboole_0 = X0))),
% 3.49/0.98    inference(ennf_transformation,[],[f4])).
% 3.49/0.98  
% 3.49/0.98  fof(f18,plain,(
% 3.49/0.98    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | ? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0))) & (! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)) | ~r2_hidden(X2,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 3.49/0.98    inference(nnf_transformation,[],[f9])).
% 3.49/0.98  
% 3.49/0.98  fof(f19,plain,(
% 3.49/0.98    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | ? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X4] : (r2_hidden(X2,X4) | ~r2_hidden(X4,X0)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ? [X6] : (~r2_hidden(X5,X6) & r2_hidden(X6,X0))) & (! [X7] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0)) | ~r2_hidden(X5,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 3.49/0.98    inference(rectify,[],[f18])).
% 3.49/0.98  
% 3.49/0.98  fof(f22,plain,(
% 3.49/0.98    ! [X5,X0] : (? [X6] : (~r2_hidden(X5,X6) & r2_hidden(X6,X0)) => (~r2_hidden(X5,sK3(X0,X5)) & r2_hidden(sK3(X0,X5),X0)))),
% 3.49/0.98    introduced(choice_axiom,[])).
% 3.49/0.98  
% 3.49/0.98  fof(f21,plain,(
% 3.49/0.98    ( ! [X2] : (! [X1,X0] : (? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) => (~r2_hidden(X2,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),X0)))) )),
% 3.49/0.98    introduced(choice_axiom,[])).
% 3.49/0.98  
% 3.49/0.98  fof(f20,plain,(
% 3.49/0.98    ! [X1,X0] : (? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X4] : (r2_hidden(X2,X4) | ~r2_hidden(X4,X0)) | r2_hidden(X2,X1))) => ((? [X3] : (~r2_hidden(sK1(X0,X1),X3) & r2_hidden(X3,X0)) | ~r2_hidden(sK1(X0,X1),X1)) & (! [X4] : (r2_hidden(sK1(X0,X1),X4) | ~r2_hidden(X4,X0)) | r2_hidden(sK1(X0,X1),X1))))),
% 3.49/0.98    introduced(choice_axiom,[])).
% 3.49/0.98  
% 3.49/0.98  fof(f23,plain,(
% 3.49/0.98    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | (((~r2_hidden(sK1(X0,X1),sK2(X0,X1)) & r2_hidden(sK2(X0,X1),X0)) | ~r2_hidden(sK1(X0,X1),X1)) & (! [X4] : (r2_hidden(sK1(X0,X1),X4) | ~r2_hidden(X4,X0)) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | (~r2_hidden(X5,sK3(X0,X5)) & r2_hidden(sK3(X0,X5),X0))) & (! [X7] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0)) | ~r2_hidden(X5,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 3.49/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f19,f22,f21,f20])).
% 3.49/0.98  
% 3.49/0.98  fof(f40,plain,(
% 3.49/0.98    ( ! [X0,X5,X1] : (r2_hidden(X5,X1) | r2_hidden(sK3(X0,X5),X0) | k1_setfam_1(X0) != X1 | k1_xboole_0 = X0) )),
% 3.49/0.98    inference(cnf_transformation,[],[f23])).
% 3.49/0.98  
% 3.49/0.98  fof(f62,plain,(
% 3.49/0.98    ( ! [X0,X5] : (r2_hidden(X5,k1_setfam_1(X0)) | r2_hidden(sK3(X0,X5),X0) | k1_xboole_0 = X0) )),
% 3.49/0.98    inference(equality_resolution,[],[f40])).
% 3.49/0.98  
% 3.49/0.98  fof(f6,conjecture,(
% 3.49/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r2_hidden(X1,X0) => (r2_hidden(X1,k8_setfam_1(X0,X2)) <=> ! [X3] : (r2_hidden(X3,X2) => r2_hidden(X1,X3)))))),
% 3.49/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/0.98  
% 3.49/0.98  fof(f7,negated_conjecture,(
% 3.49/0.98    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r2_hidden(X1,X0) => (r2_hidden(X1,k8_setfam_1(X0,X2)) <=> ! [X3] : (r2_hidden(X3,X2) => r2_hidden(X1,X3)))))),
% 3.49/0.98    inference(negated_conjecture,[],[f6])).
% 3.49/0.98  
% 3.49/0.98  fof(f11,plain,(
% 3.49/0.98    ? [X0,X1,X2] : (((r2_hidden(X1,k8_setfam_1(X0,X2)) <~> ! [X3] : (r2_hidden(X1,X3) | ~r2_hidden(X3,X2))) & r2_hidden(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.49/0.98    inference(ennf_transformation,[],[f7])).
% 3.49/0.98  
% 3.49/0.98  fof(f12,plain,(
% 3.49/0.98    ? [X0,X1,X2] : ((r2_hidden(X1,k8_setfam_1(X0,X2)) <~> ! [X3] : (r2_hidden(X1,X3) | ~r2_hidden(X3,X2))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.49/0.98    inference(flattening,[],[f11])).
% 3.49/0.98  
% 3.49/0.98  fof(f24,plain,(
% 3.49/0.98    ? [X0,X1,X2] : (((? [X3] : (~r2_hidden(X1,X3) & r2_hidden(X3,X2)) | ~r2_hidden(X1,k8_setfam_1(X0,X2))) & (! [X3] : (r2_hidden(X1,X3) | ~r2_hidden(X3,X2)) | r2_hidden(X1,k8_setfam_1(X0,X2)))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.49/0.98    inference(nnf_transformation,[],[f12])).
% 3.49/0.98  
% 3.49/0.98  fof(f25,plain,(
% 3.49/0.98    ? [X0,X1,X2] : ((? [X3] : (~r2_hidden(X1,X3) & r2_hidden(X3,X2)) | ~r2_hidden(X1,k8_setfam_1(X0,X2))) & (! [X3] : (r2_hidden(X1,X3) | ~r2_hidden(X3,X2)) | r2_hidden(X1,k8_setfam_1(X0,X2))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.49/0.98    inference(flattening,[],[f24])).
% 3.49/0.98  
% 3.49/0.98  fof(f26,plain,(
% 3.49/0.98    ? [X0,X1,X2] : ((? [X3] : (~r2_hidden(X1,X3) & r2_hidden(X3,X2)) | ~r2_hidden(X1,k8_setfam_1(X0,X2))) & (! [X4] : (r2_hidden(X1,X4) | ~r2_hidden(X4,X2)) | r2_hidden(X1,k8_setfam_1(X0,X2))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.49/0.98    inference(rectify,[],[f25])).
% 3.49/0.98  
% 3.49/0.98  fof(f28,plain,(
% 3.49/0.98    ( ! [X2,X1] : (? [X3] : (~r2_hidden(X1,X3) & r2_hidden(X3,X2)) => (~r2_hidden(X1,sK7) & r2_hidden(sK7,X2))) )),
% 3.49/0.98    introduced(choice_axiom,[])).
% 3.49/0.98  
% 3.49/0.98  fof(f27,plain,(
% 3.49/0.98    ? [X0,X1,X2] : ((? [X3] : (~r2_hidden(X1,X3) & r2_hidden(X3,X2)) | ~r2_hidden(X1,k8_setfam_1(X0,X2))) & (! [X4] : (r2_hidden(X1,X4) | ~r2_hidden(X4,X2)) | r2_hidden(X1,k8_setfam_1(X0,X2))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) => ((? [X3] : (~r2_hidden(sK5,X3) & r2_hidden(X3,sK6)) | ~r2_hidden(sK5,k8_setfam_1(sK4,sK6))) & (! [X4] : (r2_hidden(sK5,X4) | ~r2_hidden(X4,sK6)) | r2_hidden(sK5,k8_setfam_1(sK4,sK6))) & r2_hidden(sK5,sK4) & m1_subset_1(sK6,k1_zfmisc_1(k1_zfmisc_1(sK4))))),
% 3.49/0.98    introduced(choice_axiom,[])).
% 3.49/0.98  
% 3.49/0.98  fof(f29,plain,(
% 3.49/0.98    ((~r2_hidden(sK5,sK7) & r2_hidden(sK7,sK6)) | ~r2_hidden(sK5,k8_setfam_1(sK4,sK6))) & (! [X4] : (r2_hidden(sK5,X4) | ~r2_hidden(X4,sK6)) | r2_hidden(sK5,k8_setfam_1(sK4,sK6))) & r2_hidden(sK5,sK4) & m1_subset_1(sK6,k1_zfmisc_1(k1_zfmisc_1(sK4)))),
% 3.49/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f26,f28,f27])).
% 3.49/0.98  
% 3.49/0.98  fof(f50,plain,(
% 3.49/0.98    ( ! [X4] : (r2_hidden(sK5,X4) | ~r2_hidden(X4,sK6) | r2_hidden(sK5,k8_setfam_1(sK4,sK6))) )),
% 3.49/0.98    inference(cnf_transformation,[],[f29])).
% 3.49/0.98  
% 3.49/0.98  fof(f41,plain,(
% 3.49/0.98    ( ! [X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(X5,sK3(X0,X5)) | k1_setfam_1(X0) != X1 | k1_xboole_0 = X0) )),
% 3.49/0.98    inference(cnf_transformation,[],[f23])).
% 3.49/0.98  
% 3.49/0.98  fof(f61,plain,(
% 3.49/0.98    ( ! [X0,X5] : (r2_hidden(X5,k1_setfam_1(X0)) | ~r2_hidden(X5,sK3(X0,X5)) | k1_xboole_0 = X0) )),
% 3.49/0.98    inference(equality_resolution,[],[f41])).
% 3.49/0.98  
% 3.49/0.98  fof(f3,axiom,(
% 3.49/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 3.49/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/0.98  
% 3.49/0.98  fof(f8,plain,(
% 3.49/0.98    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.49/0.98    inference(ennf_transformation,[],[f3])).
% 3.49/0.98  
% 3.49/0.98  fof(f37,plain,(
% 3.49/0.98    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.49/0.98    inference(cnf_transformation,[],[f8])).
% 3.49/0.98  
% 3.49/0.98  fof(f48,plain,(
% 3.49/0.98    m1_subset_1(sK6,k1_zfmisc_1(k1_zfmisc_1(sK4)))),
% 3.49/0.98    inference(cnf_transformation,[],[f29])).
% 3.49/0.98  
% 3.49/0.98  fof(f5,axiom,(
% 3.49/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 3.49/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/0.98  
% 3.49/0.98  fof(f10,plain,(
% 3.49/0.98    ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.49/0.98    inference(ennf_transformation,[],[f5])).
% 3.49/0.98  
% 3.49/0.98  fof(f47,plain,(
% 3.49/0.98    ( ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.49/0.98    inference(cnf_transformation,[],[f10])).
% 3.49/0.98  
% 3.49/0.98  fof(f52,plain,(
% 3.49/0.98    ~r2_hidden(sK5,sK7) | ~r2_hidden(sK5,k8_setfam_1(sK4,sK6))),
% 3.49/0.98    inference(cnf_transformation,[],[f29])).
% 3.49/0.98  
% 3.49/0.98  fof(f51,plain,(
% 3.49/0.98    r2_hidden(sK7,sK6) | ~r2_hidden(sK5,k8_setfam_1(sK4,sK6))),
% 3.49/0.98    inference(cnf_transformation,[],[f29])).
% 3.49/0.98  
% 3.49/0.98  fof(f2,axiom,(
% 3.49/0.98    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0),
% 3.49/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/0.98  
% 3.49/0.98  fof(f36,plain,(
% 3.49/0.98    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0) )),
% 3.49/0.98    inference(cnf_transformation,[],[f2])).
% 3.49/0.98  
% 3.49/0.98  fof(f1,axiom,(
% 3.49/0.98    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.49/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/0.98  
% 3.49/0.98  fof(f13,plain,(
% 3.49/0.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.49/0.98    inference(nnf_transformation,[],[f1])).
% 3.49/0.98  
% 3.49/0.98  fof(f14,plain,(
% 3.49/0.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.49/0.98    inference(flattening,[],[f13])).
% 3.49/0.98  
% 3.49/0.98  fof(f15,plain,(
% 3.49/0.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.49/0.98    inference(rectify,[],[f14])).
% 3.49/0.98  
% 3.49/0.98  fof(f16,plain,(
% 3.49/0.98    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.49/0.98    introduced(choice_axiom,[])).
% 3.49/0.98  
% 3.49/0.98  fof(f17,plain,(
% 3.49/0.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.49/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).
% 3.49/0.98  
% 3.49/0.98  fof(f31,plain,(
% 3.49/0.98    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.49/0.98    inference(cnf_transformation,[],[f17])).
% 3.49/0.98  
% 3.49/0.98  fof(f54,plain,(
% 3.49/0.98    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 3.49/0.98    inference(equality_resolution,[],[f31])).
% 3.49/0.98  
% 3.49/0.98  fof(f39,plain,(
% 3.49/0.98    ( ! [X0,X7,X5,X1] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0) | ~r2_hidden(X5,X1) | k1_setfam_1(X0) != X1 | k1_xboole_0 = X0) )),
% 3.49/0.98    inference(cnf_transformation,[],[f23])).
% 3.49/0.98  
% 3.49/0.98  fof(f63,plain,(
% 3.49/0.98    ( ! [X0,X7,X5] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0) | ~r2_hidden(X5,k1_setfam_1(X0)) | k1_xboole_0 = X0) )),
% 3.49/0.98    inference(equality_resolution,[],[f39])).
% 3.49/0.98  
% 3.49/0.98  fof(f38,plain,(
% 3.49/0.98    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.49/0.98    inference(cnf_transformation,[],[f8])).
% 3.49/0.98  
% 3.49/0.98  fof(f56,plain,(
% 3.49/0.98    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.49/0.98    inference(equality_resolution,[],[f38])).
% 3.49/0.98  
% 3.49/0.98  fof(f49,plain,(
% 3.49/0.98    r2_hidden(sK5,sK4)),
% 3.49/0.98    inference(cnf_transformation,[],[f29])).
% 3.49/0.98  
% 3.49/0.98  cnf(c_15,plain,
% 3.49/0.98      ( r2_hidden(X0,k1_setfam_1(X1))
% 3.49/0.98      | r2_hidden(sK3(X1,X0),X1)
% 3.49/0.98      | k1_xboole_0 = X1 ),
% 3.49/0.98      inference(cnf_transformation,[],[f62]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_654,plain,
% 3.49/0.98      ( k1_xboole_0 = X0
% 3.49/0.98      | r2_hidden(X1,k1_setfam_1(X0)) = iProver_top
% 3.49/0.98      | r2_hidden(sK3(X0,X1),X0) = iProver_top ),
% 3.49/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_20,negated_conjecture,
% 3.49/0.98      ( ~ r2_hidden(X0,sK6)
% 3.49/0.98      | r2_hidden(sK5,X0)
% 3.49/0.98      | r2_hidden(sK5,k8_setfam_1(sK4,sK6)) ),
% 3.49/0.98      inference(cnf_transformation,[],[f50]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_650,plain,
% 3.49/0.98      ( r2_hidden(X0,sK6) != iProver_top
% 3.49/0.98      | r2_hidden(sK5,X0) = iProver_top
% 3.49/0.98      | r2_hidden(sK5,k8_setfam_1(sK4,sK6)) = iProver_top ),
% 3.49/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_1784,plain,
% 3.49/0.98      ( sK6 = k1_xboole_0
% 3.49/0.98      | r2_hidden(X0,k1_setfam_1(sK6)) = iProver_top
% 3.49/0.98      | r2_hidden(sK5,sK3(sK6,X0)) = iProver_top
% 3.49/0.98      | r2_hidden(sK5,k8_setfam_1(sK4,sK6)) = iProver_top ),
% 3.49/0.98      inference(superposition,[status(thm)],[c_654,c_650]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_372,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_894,plain,
% 3.49/0.98      ( sK6 != X0 | sK6 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 3.49/0.98      inference(instantiation,[status(thm)],[c_372]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_975,plain,
% 3.49/0.98      ( sK6 != sK6 | sK6 = k1_xboole_0 | k1_xboole_0 != sK6 ),
% 3.49/0.98      inference(instantiation,[status(thm)],[c_894]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_371,plain,( X0 = X0 ),theory(equality) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_976,plain,
% 3.49/0.98      ( sK6 = sK6 ),
% 3.49/0.98      inference(instantiation,[status(thm)],[c_371]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_14,plain,
% 3.49/0.98      ( ~ r2_hidden(X0,sK3(X1,X0))
% 3.49/0.98      | r2_hidden(X0,k1_setfam_1(X1))
% 3.49/0.98      | k1_xboole_0 = X1 ),
% 3.49/0.98      inference(cnf_transformation,[],[f61]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_1020,plain,
% 3.49/0.98      ( r2_hidden(X0,k1_setfam_1(sK6))
% 3.49/0.98      | r2_hidden(sK5,sK3(sK6,X0))
% 3.49/0.98      | r2_hidden(sK5,k8_setfam_1(sK4,sK6))
% 3.49/0.98      | k1_xboole_0 = sK6 ),
% 3.49/0.98      inference(resolution,[status(thm)],[c_20,c_15]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_1563,plain,
% 3.49/0.98      ( r2_hidden(sK5,k8_setfam_1(sK4,sK6))
% 3.49/0.98      | r2_hidden(sK5,k1_setfam_1(sK6))
% 3.49/0.98      | k1_xboole_0 = sK6 ),
% 3.49/0.98      inference(resolution,[status(thm)],[c_14,c_1020]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_386,plain,
% 3.49/0.98      ( k1_xboole_0 = k1_xboole_0 ),
% 3.49/0.98      inference(instantiation,[status(thm)],[c_371]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_1100,plain,
% 3.49/0.98      ( ~ r2_hidden(sK7,sK6)
% 3.49/0.98      | r2_hidden(sK5,k8_setfam_1(sK4,sK6))
% 3.49/0.98      | r2_hidden(sK5,sK7) ),
% 3.49/0.98      inference(instantiation,[status(thm)],[c_20]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_1388,plain,
% 3.49/0.98      ( sK6 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK6 ),
% 3.49/0.98      inference(instantiation,[status(thm)],[c_372]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_1389,plain,
% 3.49/0.98      ( sK6 != k1_xboole_0
% 3.49/0.98      | k1_xboole_0 = sK6
% 3.49/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 3.49/0.98      inference(instantiation,[status(thm)],[c_1388]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_8,plain,
% 3.49/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.49/0.98      | k6_setfam_1(X1,X0) = k8_setfam_1(X1,X0)
% 3.49/0.98      | k1_xboole_0 = X0 ),
% 3.49/0.98      inference(cnf_transformation,[],[f37]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_22,negated_conjecture,
% 3.49/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(k1_zfmisc_1(sK4))) ),
% 3.49/0.98      inference(cnf_transformation,[],[f48]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_241,plain,
% 3.49/0.98      ( k6_setfam_1(X0,X1) = k8_setfam_1(X0,X1)
% 3.49/0.98      | k1_zfmisc_1(k1_zfmisc_1(X0)) != k1_zfmisc_1(k1_zfmisc_1(sK4))
% 3.49/0.98      | sK6 != X1
% 3.49/0.98      | k1_xboole_0 = X1 ),
% 3.49/0.98      inference(resolution_lifted,[status(thm)],[c_8,c_22]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_242,plain,
% 3.49/0.98      ( k6_setfam_1(X0,sK6) = k8_setfam_1(X0,sK6)
% 3.49/0.98      | k1_zfmisc_1(k1_zfmisc_1(X0)) != k1_zfmisc_1(k1_zfmisc_1(sK4))
% 3.49/0.98      | k1_xboole_0 = sK6 ),
% 3.49/0.98      inference(unflattening,[status(thm)],[c_241]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_902,plain,
% 3.49/0.98      ( k6_setfam_1(sK4,sK6) = k8_setfam_1(sK4,sK6) | sK6 = k1_xboole_0 ),
% 3.49/0.98      inference(equality_resolution,[status(thm)],[c_242]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_17,plain,
% 3.49/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.49/0.98      | k6_setfam_1(X1,X0) = k1_setfam_1(X0) ),
% 3.49/0.98      inference(cnf_transformation,[],[f47]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_232,plain,
% 3.49/0.98      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
% 3.49/0.98      | k1_zfmisc_1(k1_zfmisc_1(X0)) != k1_zfmisc_1(k1_zfmisc_1(sK4))
% 3.49/0.98      | sK6 != X1 ),
% 3.49/0.98      inference(resolution_lifted,[status(thm)],[c_17,c_22]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_233,plain,
% 3.49/0.98      ( k6_setfam_1(X0,sK6) = k1_setfam_1(sK6)
% 3.49/0.98      | k1_zfmisc_1(k1_zfmisc_1(X0)) != k1_zfmisc_1(k1_zfmisc_1(sK4)) ),
% 3.49/0.98      inference(unflattening,[status(thm)],[c_232]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_867,plain,
% 3.49/0.98      ( k6_setfam_1(sK4,sK6) = k1_setfam_1(sK6) ),
% 3.49/0.98      inference(equality_resolution,[status(thm)],[c_233]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_1404,plain,
% 3.49/0.98      ( k8_setfam_1(sK4,sK6) = k1_setfam_1(sK6) | sK6 = k1_xboole_0 ),
% 3.49/0.98      inference(light_normalisation,[status(thm)],[c_902,c_867]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_18,negated_conjecture,
% 3.49/0.98      ( ~ r2_hidden(sK5,k8_setfam_1(sK4,sK6)) | ~ r2_hidden(sK5,sK7) ),
% 3.49/0.98      inference(cnf_transformation,[],[f52]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_652,plain,
% 3.49/0.98      ( r2_hidden(sK5,k8_setfam_1(sK4,sK6)) != iProver_top
% 3.49/0.98      | r2_hidden(sK5,sK7) != iProver_top ),
% 3.49/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_1407,plain,
% 3.49/0.98      ( sK6 = k1_xboole_0
% 3.49/0.98      | r2_hidden(sK5,k1_setfam_1(sK6)) != iProver_top
% 3.49/0.98      | r2_hidden(sK5,sK7) != iProver_top ),
% 3.49/0.98      inference(superposition,[status(thm)],[c_1404,c_652]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_1421,plain,
% 3.49/0.98      ( ~ r2_hidden(sK5,k1_setfam_1(sK6))
% 3.49/0.98      | ~ r2_hidden(sK5,sK7)
% 3.49/0.98      | sK6 = k1_xboole_0 ),
% 3.49/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_1407]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_19,negated_conjecture,
% 3.49/0.98      ( r2_hidden(sK7,sK6) | ~ r2_hidden(sK5,k8_setfam_1(sK4,sK6)) ),
% 3.49/0.98      inference(cnf_transformation,[],[f51]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_651,plain,
% 3.49/0.98      ( r2_hidden(sK7,sK6) = iProver_top
% 3.49/0.98      | r2_hidden(sK5,k8_setfam_1(sK4,sK6)) != iProver_top ),
% 3.49/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_1408,plain,
% 3.49/0.98      ( sK6 = k1_xboole_0
% 3.49/0.98      | r2_hidden(sK7,sK6) = iProver_top
% 3.49/0.98      | r2_hidden(sK5,k1_setfam_1(sK6)) != iProver_top ),
% 3.49/0.98      inference(superposition,[status(thm)],[c_1404,c_651]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_1422,plain,
% 3.49/0.98      ( r2_hidden(sK7,sK6)
% 3.49/0.98      | ~ r2_hidden(sK5,k1_setfam_1(sK6))
% 3.49/0.98      | sK6 = k1_xboole_0 ),
% 3.49/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_1408]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_1566,plain,
% 3.49/0.98      ( r2_hidden(sK5,k8_setfam_1(sK4,sK6)) | k1_xboole_0 = sK6 ),
% 3.49/0.98      inference(global_propositional_subsumption,
% 3.49/0.98                [status(thm)],
% 3.49/0.98                [c_1563,c_386,c_1100,c_1389,c_1421,c_1422]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_1568,plain,
% 3.49/0.98      ( k1_xboole_0 = sK6
% 3.49/0.98      | r2_hidden(sK5,k8_setfam_1(sK4,sK6)) = iProver_top ),
% 3.49/0.98      inference(predicate_to_equality,[status(thm)],[c_1566]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_2410,plain,
% 3.49/0.98      ( sK6 = k1_xboole_0
% 3.49/0.98      | r2_hidden(sK5,k8_setfam_1(sK4,sK6)) = iProver_top ),
% 3.49/0.98      inference(global_propositional_subsumption,
% 3.49/0.98                [status(thm)],
% 3.49/0.98                [c_1784,c_975,c_976,c_1568]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_2419,plain,
% 3.49/0.98      ( sK6 = k1_xboole_0 | r2_hidden(sK7,sK6) = iProver_top ),
% 3.49/0.98      inference(superposition,[status(thm)],[c_2410,c_651]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_6,plain,
% 3.49/0.98      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.49/0.98      inference(cnf_transformation,[],[f36]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_4,plain,
% 3.49/0.98      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 3.49/0.98      inference(cnf_transformation,[],[f54]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_660,plain,
% 3.49/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.49/0.98      | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 3.49/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_1540,plain,
% 3.49/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.49/0.98      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.49/0.98      inference(superposition,[status(thm)],[c_6,c_660]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_2611,plain,
% 3.49/0.98      ( sK6 = k1_xboole_0 | r2_hidden(sK7,k1_xboole_0) != iProver_top ),
% 3.49/0.98      inference(superposition,[status(thm)],[c_2419,c_1540]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_2416,plain,
% 3.49/0.98      ( sK6 = k1_xboole_0
% 3.49/0.98      | r2_hidden(sK5,k1_setfam_1(sK6)) = iProver_top ),
% 3.49/0.98      inference(superposition,[status(thm)],[c_1404,c_2410]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_2418,plain,
% 3.49/0.98      ( sK6 = k1_xboole_0 | r2_hidden(sK5,sK7) != iProver_top ),
% 3.49/0.98      inference(superposition,[status(thm)],[c_2410,c_652]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_16,plain,
% 3.49/0.98      ( ~ r2_hidden(X0,X1)
% 3.49/0.98      | r2_hidden(X2,X0)
% 3.49/0.98      | ~ r2_hidden(X2,k1_setfam_1(X1))
% 3.49/0.98      | k1_xboole_0 = X1 ),
% 3.49/0.98      inference(cnf_transformation,[],[f63]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_1052,plain,
% 3.49/0.98      ( ~ r2_hidden(X0,X1)
% 3.49/0.98      | r2_hidden(sK5,X0)
% 3.49/0.98      | ~ r2_hidden(sK5,k1_setfam_1(X1))
% 3.49/0.98      | k1_xboole_0 = X1 ),
% 3.49/0.98      inference(instantiation,[status(thm)],[c_16]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_1370,plain,
% 3.49/0.98      ( ~ r2_hidden(X0,sK6)
% 3.49/0.98      | r2_hidden(sK5,X0)
% 3.49/0.98      | ~ r2_hidden(sK5,k1_setfam_1(sK6))
% 3.49/0.98      | k1_xboole_0 = sK6 ),
% 3.49/0.98      inference(instantiation,[status(thm)],[c_1052]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_3374,plain,
% 3.49/0.98      ( ~ r2_hidden(sK7,sK6)
% 3.49/0.98      | ~ r2_hidden(sK5,k1_setfam_1(sK6))
% 3.49/0.98      | r2_hidden(sK5,sK7)
% 3.49/0.98      | k1_xboole_0 = sK6 ),
% 3.49/0.98      inference(instantiation,[status(thm)],[c_1370]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_3376,plain,
% 3.49/0.98      ( k1_xboole_0 = sK6
% 3.49/0.98      | r2_hidden(sK7,sK6) != iProver_top
% 3.49/0.98      | r2_hidden(sK5,k1_setfam_1(sK6)) != iProver_top
% 3.49/0.98      | r2_hidden(sK5,sK7) = iProver_top ),
% 3.49/0.98      inference(predicate_to_equality,[status(thm)],[c_3374]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_3410,plain,
% 3.49/0.98      ( sK6 = k1_xboole_0 ),
% 3.49/0.98      inference(global_propositional_subsumption,
% 3.49/0.98                [status(thm)],
% 3.49/0.98                [c_2611,c_975,c_976,c_2416,c_2418,c_2419,c_3376]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_7,plain,
% 3.49/0.98      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
% 3.49/0.98      | k8_setfam_1(X0,k1_xboole_0) = X0 ),
% 3.49/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_221,plain,
% 3.49/0.98      ( k8_setfam_1(X0,k1_xboole_0) = X0
% 3.49/0.98      | k1_zfmisc_1(k1_zfmisc_1(X0)) != k1_zfmisc_1(k1_zfmisc_1(sK4))
% 3.49/0.98      | sK6 != k1_xboole_0 ),
% 3.49/0.98      inference(resolution_lifted,[status(thm)],[c_7,c_22]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_898,plain,
% 3.49/0.98      ( k8_setfam_1(sK4,k1_xboole_0) = sK4 | sK6 != k1_xboole_0 ),
% 3.49/0.98      inference(equality_resolution,[status(thm)],[c_221]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_3417,plain,
% 3.49/0.98      ( k8_setfam_1(sK4,k1_xboole_0) = sK4 | k1_xboole_0 != k1_xboole_0 ),
% 3.49/0.98      inference(demodulation,[status(thm)],[c_3410,c_898]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_3452,plain,
% 3.49/0.98      ( k8_setfam_1(sK4,k1_xboole_0) = sK4 ),
% 3.49/0.98      inference(equality_resolution_simp,[status(thm)],[c_3417]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_3424,plain,
% 3.49/0.98      ( r2_hidden(sK7,k1_xboole_0) = iProver_top
% 3.49/0.98      | r2_hidden(sK5,k8_setfam_1(sK4,k1_xboole_0)) != iProver_top ),
% 3.49/0.98      inference(demodulation,[status(thm)],[c_3410,c_651]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_3456,plain,
% 3.49/0.98      ( r2_hidden(sK7,k1_xboole_0) = iProver_top
% 3.49/0.98      | r2_hidden(sK5,sK4) != iProver_top ),
% 3.49/0.98      inference(demodulation,[status(thm)],[c_3452,c_3424]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_21,negated_conjecture,
% 3.49/0.98      ( r2_hidden(sK5,sK4) ),
% 3.49/0.98      inference(cnf_transformation,[],[f49]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_24,plain,
% 3.49/0.98      ( r2_hidden(sK5,sK4) = iProver_top ),
% 3.49/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_3482,plain,
% 3.49/0.98      ( r2_hidden(sK7,k1_xboole_0) = iProver_top ),
% 3.49/0.98      inference(global_propositional_subsumption,
% 3.49/0.98                [status(thm)],
% 3.49/0.98                [c_3456,c_24]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_3487,plain,
% 3.49/0.98      ( r2_hidden(sK7,k1_xboole_0) != iProver_top ),
% 3.49/0.98      inference(superposition,[status(thm)],[c_3482,c_1540]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(contradiction,plain,
% 3.49/0.98      ( $false ),
% 3.49/0.98      inference(minisat,[status(thm)],[c_3487,c_3456,c_24]) ).
% 3.49/0.98  
% 3.49/0.98  
% 3.49/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.49/0.98  
% 3.49/0.98  ------                               Statistics
% 3.49/0.98  
% 3.49/0.98  ------ Selected
% 3.49/0.98  
% 3.49/0.98  total_time:                             0.13
% 3.49/0.98  
%------------------------------------------------------------------------------
