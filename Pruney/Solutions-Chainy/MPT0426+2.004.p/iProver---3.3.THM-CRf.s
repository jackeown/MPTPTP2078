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
% DateTime   : Thu Dec  3 11:42:25 EST 2020

% Result     : Theorem 2.74s
% Output     : CNFRefutation 2.74s
% Verified   : 
% Statistics : Number of formulae       :  108 (1216 expanded)
%              Number of clauses        :   57 ( 317 expanded)
%              Number of leaves         :   13 ( 269 expanded)
%              Depth                    :   25
%              Number of atoms          :  436 (6979 expanded)
%              Number of equality atoms :  173 (1299 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

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

fof(f10,plain,(
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
    inference(nnf_transformation,[],[f10])).

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
     => ( ~ r2_hidden(X5,sK3(X0,X5))
        & r2_hidden(sK3(X0,X5),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X2,X3)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(X2,sK2(X0,X1))
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
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
              ( ~ r2_hidden(sK1(X0,X1),X3)
              & r2_hidden(X3,X0) )
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ! [X4] :
              ( r2_hidden(sK1(X0,X1),X4)
              | ~ r2_hidden(X4,X0) )
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f20,f23,f22,f21])).

fof(f42,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | r2_hidden(sK3(X0,X5),X0)
      | k1_setfam_1(X0) != X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f64,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,k1_setfam_1(X0))
      | r2_hidden(sK3(X0,X5),X0)
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f42])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( r2_hidden(X1,X0)
       => ( r2_hidden(X1,k8_setfam_1(X0,X2))
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
             => r2_hidden(X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ( r2_hidden(X1,X0)
         => ( r2_hidden(X1,k8_setfam_1(X0,X2))
          <=> ! [X3] :
                ( r2_hidden(X3,X2)
               => r2_hidden(X1,X3) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,k8_setfam_1(X0,X2))
      <~> ! [X3] :
            ( r2_hidden(X1,X3)
            | ~ r2_hidden(X3,X2) ) )
      & r2_hidden(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,k8_setfam_1(X0,X2))
      <~> ! [X3] :
            ( r2_hidden(X1,X3)
            | ~ r2_hidden(X3,X2) ) )
      & r2_hidden(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f12])).

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
    inference(nnf_transformation,[],[f13])).

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
     => ( ~ r2_hidden(X1,sK7)
        & r2_hidden(sK7,X2) ) ) ),
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

fof(f30,plain,
    ( ( ( ~ r2_hidden(sK5,sK7)
        & r2_hidden(sK7,sK6) )
      | ~ r2_hidden(sK5,k8_setfam_1(sK4,sK6)) )
    & ( ! [X4] :
          ( r2_hidden(sK5,X4)
          | ~ r2_hidden(X4,sK6) )
      | r2_hidden(sK5,k8_setfam_1(sK4,sK6)) )
    & r2_hidden(sK5,sK4)
    & m1_subset_1(sK6,k1_zfmisc_1(k1_zfmisc_1(sK4))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f27,f29,f28])).

fof(f52,plain,(
    ! [X4] :
      ( r2_hidden(sK5,X4)
      | ~ r2_hidden(X4,sK6)
      | r2_hidden(sK5,k8_setfam_1(sK4,sK6)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f43,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X5,sK3(X0,X5))
      | k1_setfam_1(X0) != X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f63,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,k1_setfam_1(X0))
      | ~ r2_hidden(X5,sK3(X0,X5))
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f43])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f50,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k1_zfmisc_1(sK4))) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f54,plain,
    ( ~ r2_hidden(sK5,sK7)
    | ~ r2_hidden(sK5,k8_setfam_1(sK4,sK6)) ),
    inference(cnf_transformation,[],[f30])).

fof(f53,plain,
    ( r2_hidden(sK7,sK6)
    | ~ r2_hidden(sK5,k8_setfam_1(sK4,sK6)) ),
    inference(cnf_transformation,[],[f30])).

fof(f41,plain,(
    ! [X0,X7,X5,X1] :
      ( r2_hidden(X5,X7)
      | ~ r2_hidden(X7,X0)
      | ~ r2_hidden(X5,X1)
      | k1_setfam_1(X0) != X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f65,plain,(
    ! [X0,X7,X5] :
      ( r2_hidden(X5,X7)
      | ~ r2_hidden(X7,X0)
      | ~ r2_hidden(X5,k1_setfam_1(X0))
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f41])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f58,plain,(
    ! [X0] :
      ( k8_setfam_1(X0,k1_xboole_0) = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f40])).

fof(f51,plain,(
    r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f1])).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f14])).

fof(f16,plain,(
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
    inference(rectify,[],[f15])).

fof(f17,plain,(
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

fof(f18,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f17])).

fof(f32,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f56,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f32])).

fof(f31,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f57,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f31])).

cnf(c_16,plain,
    ( r2_hidden(X0,k1_setfam_1(X1))
    | r2_hidden(sK3(X1,X0),X1)
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_645,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(X1,k1_setfam_1(X0)) = iProver_top
    | r2_hidden(sK3(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_21,negated_conjecture,
    ( ~ r2_hidden(X0,sK6)
    | r2_hidden(sK5,X0)
    | r2_hidden(sK5,k8_setfam_1(sK4,sK6)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_641,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(sK5,X0) = iProver_top
    | r2_hidden(sK5,k8_setfam_1(sK4,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1586,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(X0,k1_setfam_1(sK6)) = iProver_top
    | r2_hidden(sK5,sK3(sK6,X0)) = iProver_top
    | r2_hidden(sK5,k8_setfam_1(sK4,sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_645,c_641])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,sK3(X1,X0))
    | r2_hidden(X0,k1_setfam_1(X1))
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_646,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(X1,sK3(X0,X1)) != iProver_top
    | r2_hidden(X1,k1_setfam_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1894,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(sK5,k8_setfam_1(sK4,sK6)) = iProver_top
    | r2_hidden(sK5,k1_setfam_1(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1586,c_646])).

cnf(c_995,plain,
    ( ~ r2_hidden(sK7,sK6)
    | r2_hidden(sK5,k8_setfam_1(sK4,sK6))
    | r2_hidden(sK5,sK7) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_996,plain,
    ( r2_hidden(sK7,sK6) != iProver_top
    | r2_hidden(sK5,k8_setfam_1(sK4,sK6)) = iProver_top
    | r2_hidden(sK5,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_995])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k6_setfam_1(X1,X0) = k8_setfam_1(X1,X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k1_zfmisc_1(sK4))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_246,plain,
    ( k6_setfam_1(X0,X1) = k8_setfam_1(X0,X1)
    | k1_zfmisc_1(k1_zfmisc_1(X0)) != k1_zfmisc_1(k1_zfmisc_1(sK4))
    | sK6 != X1
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_23])).

cnf(c_247,plain,
    ( k6_setfam_1(X0,sK6) = k8_setfam_1(X0,sK6)
    | k1_zfmisc_1(k1_zfmisc_1(X0)) != k1_zfmisc_1(k1_zfmisc_1(sK4))
    | k1_xboole_0 = sK6 ),
    inference(unflattening,[status(thm)],[c_246])).

cnf(c_848,plain,
    ( k6_setfam_1(sK4,sK6) = k8_setfam_1(sK4,sK6)
    | sK6 = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_247])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k6_setfam_1(X1,X0) = k1_setfam_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_237,plain,
    ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
    | k1_zfmisc_1(k1_zfmisc_1(X0)) != k1_zfmisc_1(k1_zfmisc_1(sK4))
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_23])).

cnf(c_238,plain,
    ( k6_setfam_1(X0,sK6) = k1_setfam_1(sK6)
    | k1_zfmisc_1(k1_zfmisc_1(X0)) != k1_zfmisc_1(k1_zfmisc_1(sK4)) ),
    inference(unflattening,[status(thm)],[c_237])).

cnf(c_831,plain,
    ( k6_setfam_1(sK4,sK6) = k1_setfam_1(sK6) ),
    inference(equality_resolution,[status(thm)],[c_238])).

cnf(c_1233,plain,
    ( k8_setfam_1(sK4,sK6) = k1_setfam_1(sK6)
    | sK6 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_848,c_831])).

cnf(c_19,negated_conjecture,
    ( ~ r2_hidden(sK5,k8_setfam_1(sK4,sK6))
    | ~ r2_hidden(sK5,sK7) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_643,plain,
    ( r2_hidden(sK5,k8_setfam_1(sK4,sK6)) != iProver_top
    | r2_hidden(sK5,sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1236,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(sK5,k1_setfam_1(sK6)) != iProver_top
    | r2_hidden(sK5,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1233,c_643])).

cnf(c_20,negated_conjecture,
    ( r2_hidden(sK7,sK6)
    | ~ r2_hidden(sK5,k8_setfam_1(sK4,sK6)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_642,plain,
    ( r2_hidden(sK7,sK6) = iProver_top
    | r2_hidden(sK5,k8_setfam_1(sK4,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1237,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(sK7,sK6) = iProver_top
    | r2_hidden(sK5,k1_setfam_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1233,c_642])).

cnf(c_1956,plain,
    ( r2_hidden(sK5,k8_setfam_1(sK4,sK6)) = iProver_top
    | sK6 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1894,c_996,c_1236,c_1237])).

cnf(c_1957,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(sK5,k8_setfam_1(sK4,sK6)) = iProver_top ),
    inference(renaming,[status(thm)],[c_1956])).

cnf(c_1964,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(sK7,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1957,c_642])).

cnf(c_1962,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(sK5,k1_setfam_1(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1233,c_1957])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X0)
    | ~ r2_hidden(X2,k1_setfam_1(X1))
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_644,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(X1,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top
    | r2_hidden(X2,k1_setfam_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2047,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(sK5,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1962,c_644])).

cnf(c_2149,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(sK5,sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_1964,c_2047])).

cnf(c_1963,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(sK5,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1957,c_643])).

cnf(c_2166,plain,
    ( sK6 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2149,c_1963])).

cnf(c_8,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
    | k8_setfam_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_226,plain,
    ( k8_setfam_1(X0,k1_xboole_0) = X0
    | k1_zfmisc_1(k1_zfmisc_1(X0)) != k1_zfmisc_1(k1_zfmisc_1(sK4))
    | sK6 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_23])).

cnf(c_844,plain,
    ( k8_setfam_1(sK4,k1_xboole_0) = sK4
    | sK6 != k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_226])).

cnf(c_2170,plain,
    ( k8_setfam_1(sK4,k1_xboole_0) = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2166,c_844])).

cnf(c_2199,plain,
    ( k8_setfam_1(sK4,k1_xboole_0) = sK4 ),
    inference(equality_resolution_simp,[status(thm)],[c_2170])).

cnf(c_2177,plain,
    ( r2_hidden(sK7,k1_xboole_0) = iProver_top
    | r2_hidden(sK5,k8_setfam_1(sK4,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2166,c_642])).

cnf(c_2202,plain,
    ( r2_hidden(sK7,k1_xboole_0) = iProver_top
    | r2_hidden(sK5,sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2199,c_2177])).

cnf(c_22,negated_conjecture,
    ( r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_25,plain,
    ( r2_hidden(sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2311,plain,
    ( r2_hidden(sK7,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2202,c_25])).

cnf(c_6,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_7,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1176,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6,c_7])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_651,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1475,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1176,c_651])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_650,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1368,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_650])).

cnf(c_1575,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1475,c_1368])).

cnf(c_2316,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2311,c_1575])).

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
% 0.13/0.34  % DateTime   : Tue Dec  1 12:25:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.74/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/0.99  
% 2.74/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.74/0.99  
% 2.74/0.99  ------  iProver source info
% 2.74/0.99  
% 2.74/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.74/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.74/0.99  git: non_committed_changes: false
% 2.74/0.99  git: last_make_outside_of_git: false
% 2.74/0.99  
% 2.74/0.99  ------ 
% 2.74/0.99  
% 2.74/0.99  ------ Input Options
% 2.74/0.99  
% 2.74/0.99  --out_options                           all
% 2.74/0.99  --tptp_safe_out                         true
% 2.74/0.99  --problem_path                          ""
% 2.74/0.99  --include_path                          ""
% 2.74/0.99  --clausifier                            res/vclausify_rel
% 2.74/0.99  --clausifier_options                    --mode clausify
% 2.74/0.99  --stdin                                 false
% 2.74/0.99  --stats_out                             all
% 2.74/0.99  
% 2.74/0.99  ------ General Options
% 2.74/0.99  
% 2.74/0.99  --fof                                   false
% 2.74/0.99  --time_out_real                         305.
% 2.74/0.99  --time_out_virtual                      -1.
% 2.74/0.99  --symbol_type_check                     false
% 2.74/0.99  --clausify_out                          false
% 2.74/0.99  --sig_cnt_out                           false
% 2.74/0.99  --trig_cnt_out                          false
% 2.74/0.99  --trig_cnt_out_tolerance                1.
% 2.74/0.99  --trig_cnt_out_sk_spl                   false
% 2.74/0.99  --abstr_cl_out                          false
% 2.74/0.99  
% 2.74/0.99  ------ Global Options
% 2.74/0.99  
% 2.74/0.99  --schedule                              default
% 2.74/0.99  --add_important_lit                     false
% 2.74/0.99  --prop_solver_per_cl                    1000
% 2.74/0.99  --min_unsat_core                        false
% 2.74/0.99  --soft_assumptions                      false
% 2.74/0.99  --soft_lemma_size                       3
% 2.74/0.99  --prop_impl_unit_size                   0
% 2.74/0.99  --prop_impl_unit                        []
% 2.74/0.99  --share_sel_clauses                     true
% 2.74/0.99  --reset_solvers                         false
% 2.74/0.99  --bc_imp_inh                            [conj_cone]
% 2.74/0.99  --conj_cone_tolerance                   3.
% 2.74/0.99  --extra_neg_conj                        none
% 2.74/0.99  --large_theory_mode                     true
% 2.74/0.99  --prolific_symb_bound                   200
% 2.74/0.99  --lt_threshold                          2000
% 2.74/0.99  --clause_weak_htbl                      true
% 2.74/0.99  --gc_record_bc_elim                     false
% 2.74/0.99  
% 2.74/0.99  ------ Preprocessing Options
% 2.74/0.99  
% 2.74/0.99  --preprocessing_flag                    true
% 2.74/0.99  --time_out_prep_mult                    0.1
% 2.74/0.99  --splitting_mode                        input
% 2.74/0.99  --splitting_grd                         true
% 2.74/0.99  --splitting_cvd                         false
% 2.74/0.99  --splitting_cvd_svl                     false
% 2.74/0.99  --splitting_nvd                         32
% 2.74/0.99  --sub_typing                            true
% 2.74/0.99  --prep_gs_sim                           true
% 2.74/0.99  --prep_unflatten                        true
% 2.74/0.99  --prep_res_sim                          true
% 2.74/0.99  --prep_upred                            true
% 2.74/0.99  --prep_sem_filter                       exhaustive
% 2.74/0.99  --prep_sem_filter_out                   false
% 2.74/0.99  --pred_elim                             true
% 2.74/0.99  --res_sim_input                         true
% 2.74/0.99  --eq_ax_congr_red                       true
% 2.74/0.99  --pure_diseq_elim                       true
% 2.74/0.99  --brand_transform                       false
% 2.74/0.99  --non_eq_to_eq                          false
% 2.74/0.99  --prep_def_merge                        true
% 2.74/0.99  --prep_def_merge_prop_impl              false
% 2.74/0.99  --prep_def_merge_mbd                    true
% 2.74/0.99  --prep_def_merge_tr_red                 false
% 2.74/0.99  --prep_def_merge_tr_cl                  false
% 2.74/0.99  --smt_preprocessing                     true
% 2.74/0.99  --smt_ac_axioms                         fast
% 2.74/0.99  --preprocessed_out                      false
% 2.74/0.99  --preprocessed_stats                    false
% 2.74/0.99  
% 2.74/0.99  ------ Abstraction refinement Options
% 2.74/0.99  
% 2.74/0.99  --abstr_ref                             []
% 2.74/0.99  --abstr_ref_prep                        false
% 2.74/0.99  --abstr_ref_until_sat                   false
% 2.74/0.99  --abstr_ref_sig_restrict                funpre
% 2.74/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.74/0.99  --abstr_ref_under                       []
% 2.74/0.99  
% 2.74/0.99  ------ SAT Options
% 2.74/0.99  
% 2.74/0.99  --sat_mode                              false
% 2.74/0.99  --sat_fm_restart_options                ""
% 2.74/0.99  --sat_gr_def                            false
% 2.74/0.99  --sat_epr_types                         true
% 2.74/0.99  --sat_non_cyclic_types                  false
% 2.74/0.99  --sat_finite_models                     false
% 2.74/0.99  --sat_fm_lemmas                         false
% 2.74/0.99  --sat_fm_prep                           false
% 2.74/0.99  --sat_fm_uc_incr                        true
% 2.74/0.99  --sat_out_model                         small
% 2.74/0.99  --sat_out_clauses                       false
% 2.74/0.99  
% 2.74/0.99  ------ QBF Options
% 2.74/0.99  
% 2.74/0.99  --qbf_mode                              false
% 2.74/0.99  --qbf_elim_univ                         false
% 2.74/0.99  --qbf_dom_inst                          none
% 2.74/0.99  --qbf_dom_pre_inst                      false
% 2.74/0.99  --qbf_sk_in                             false
% 2.74/0.99  --qbf_pred_elim                         true
% 2.74/0.99  --qbf_split                             512
% 2.74/0.99  
% 2.74/0.99  ------ BMC1 Options
% 2.74/0.99  
% 2.74/0.99  --bmc1_incremental                      false
% 2.74/0.99  --bmc1_axioms                           reachable_all
% 2.74/0.99  --bmc1_min_bound                        0
% 2.74/0.99  --bmc1_max_bound                        -1
% 2.74/0.99  --bmc1_max_bound_default                -1
% 2.74/0.99  --bmc1_symbol_reachability              true
% 2.74/0.99  --bmc1_property_lemmas                  false
% 2.74/0.99  --bmc1_k_induction                      false
% 2.74/0.99  --bmc1_non_equiv_states                 false
% 2.74/0.99  --bmc1_deadlock                         false
% 2.74/0.99  --bmc1_ucm                              false
% 2.74/0.99  --bmc1_add_unsat_core                   none
% 2.74/0.99  --bmc1_unsat_core_children              false
% 2.74/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.74/0.99  --bmc1_out_stat                         full
% 2.74/0.99  --bmc1_ground_init                      false
% 2.74/0.99  --bmc1_pre_inst_next_state              false
% 2.74/0.99  --bmc1_pre_inst_state                   false
% 2.74/0.99  --bmc1_pre_inst_reach_state             false
% 2.74/0.99  --bmc1_out_unsat_core                   false
% 2.74/0.99  --bmc1_aig_witness_out                  false
% 2.74/0.99  --bmc1_verbose                          false
% 2.74/0.99  --bmc1_dump_clauses_tptp                false
% 2.74/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.74/0.99  --bmc1_dump_file                        -
% 2.74/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.74/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.74/0.99  --bmc1_ucm_extend_mode                  1
% 2.74/0.99  --bmc1_ucm_init_mode                    2
% 2.74/0.99  --bmc1_ucm_cone_mode                    none
% 2.74/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.74/0.99  --bmc1_ucm_relax_model                  4
% 2.74/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.74/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.74/0.99  --bmc1_ucm_layered_model                none
% 2.74/0.99  --bmc1_ucm_max_lemma_size               10
% 2.74/0.99  
% 2.74/0.99  ------ AIG Options
% 2.74/0.99  
% 2.74/0.99  --aig_mode                              false
% 2.74/0.99  
% 2.74/0.99  ------ Instantiation Options
% 2.74/0.99  
% 2.74/0.99  --instantiation_flag                    true
% 2.74/0.99  --inst_sos_flag                         false
% 2.74/0.99  --inst_sos_phase                        true
% 2.74/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.74/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.74/0.99  --inst_lit_sel_side                     num_symb
% 2.74/0.99  --inst_solver_per_active                1400
% 2.74/0.99  --inst_solver_calls_frac                1.
% 2.74/0.99  --inst_passive_queue_type               priority_queues
% 2.74/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.74/0.99  --inst_passive_queues_freq              [25;2]
% 2.74/0.99  --inst_dismatching                      true
% 2.74/0.99  --inst_eager_unprocessed_to_passive     true
% 2.74/0.99  --inst_prop_sim_given                   true
% 2.74/0.99  --inst_prop_sim_new                     false
% 2.74/0.99  --inst_subs_new                         false
% 2.74/0.99  --inst_eq_res_simp                      false
% 2.74/0.99  --inst_subs_given                       false
% 2.74/0.99  --inst_orphan_elimination               true
% 2.74/0.99  --inst_learning_loop_flag               true
% 2.74/0.99  --inst_learning_start                   3000
% 2.74/0.99  --inst_learning_factor                  2
% 2.74/0.99  --inst_start_prop_sim_after_learn       3
% 2.74/0.99  --inst_sel_renew                        solver
% 2.74/0.99  --inst_lit_activity_flag                true
% 2.74/0.99  --inst_restr_to_given                   false
% 2.74/0.99  --inst_activity_threshold               500
% 2.74/0.99  --inst_out_proof                        true
% 2.74/0.99  
% 2.74/0.99  ------ Resolution Options
% 2.74/0.99  
% 2.74/0.99  --resolution_flag                       true
% 2.74/0.99  --res_lit_sel                           adaptive
% 2.74/0.99  --res_lit_sel_side                      none
% 2.74/0.99  --res_ordering                          kbo
% 2.74/0.99  --res_to_prop_solver                    active
% 2.74/0.99  --res_prop_simpl_new                    false
% 2.74/0.99  --res_prop_simpl_given                  true
% 2.74/0.99  --res_passive_queue_type                priority_queues
% 2.74/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.74/0.99  --res_passive_queues_freq               [15;5]
% 2.74/0.99  --res_forward_subs                      full
% 2.74/0.99  --res_backward_subs                     full
% 2.74/0.99  --res_forward_subs_resolution           true
% 2.74/0.99  --res_backward_subs_resolution          true
% 2.74/0.99  --res_orphan_elimination                true
% 2.74/0.99  --res_time_limit                        2.
% 2.74/0.99  --res_out_proof                         true
% 2.74/0.99  
% 2.74/0.99  ------ Superposition Options
% 2.74/0.99  
% 2.74/0.99  --superposition_flag                    true
% 2.74/0.99  --sup_passive_queue_type                priority_queues
% 2.74/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.74/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.74/0.99  --demod_completeness_check              fast
% 2.74/0.99  --demod_use_ground                      true
% 2.74/0.99  --sup_to_prop_solver                    passive
% 2.74/0.99  --sup_prop_simpl_new                    true
% 2.74/0.99  --sup_prop_simpl_given                  true
% 2.74/0.99  --sup_fun_splitting                     false
% 2.74/0.99  --sup_smt_interval                      50000
% 2.74/0.99  
% 2.74/0.99  ------ Superposition Simplification Setup
% 2.74/0.99  
% 2.74/0.99  --sup_indices_passive                   []
% 2.74/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.74/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/0.99  --sup_full_bw                           [BwDemod]
% 2.74/0.99  --sup_immed_triv                        [TrivRules]
% 2.74/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.74/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/0.99  --sup_immed_bw_main                     []
% 2.74/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.74/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.74/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.74/0.99  
% 2.74/0.99  ------ Combination Options
% 2.74/0.99  
% 2.74/0.99  --comb_res_mult                         3
% 2.74/0.99  --comb_sup_mult                         2
% 2.74/0.99  --comb_inst_mult                        10
% 2.74/0.99  
% 2.74/0.99  ------ Debug Options
% 2.74/0.99  
% 2.74/0.99  --dbg_backtrace                         false
% 2.74/0.99  --dbg_dump_prop_clauses                 false
% 2.74/0.99  --dbg_dump_prop_clauses_file            -
% 2.74/0.99  --dbg_out_stat                          false
% 2.74/0.99  ------ Parsing...
% 2.74/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.74/0.99  
% 2.74/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.74/0.99  
% 2.74/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.74/0.99  
% 2.74/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.74/0.99  ------ Proving...
% 2.74/0.99  ------ Problem Properties 
% 2.74/0.99  
% 2.74/0.99  
% 2.74/0.99  clauses                                 22
% 2.74/0.99  conjectures                             4
% 2.74/0.99  EPR                                     1
% 2.74/0.99  Horn                                    10
% 2.74/0.99  unary                                   4
% 2.74/0.99  binary                                  5
% 2.74/0.99  lits                                    59
% 2.74/0.99  lits eq                                 23
% 2.74/0.99  fd_pure                                 0
% 2.74/0.99  fd_pseudo                               0
% 2.74/0.99  fd_cond                                 3
% 2.74/0.99  fd_pseudo_cond                          6
% 2.74/0.99  AC symbols                              0
% 2.74/0.99  
% 2.74/0.99  ------ Schedule dynamic 5 is on 
% 2.74/0.99  
% 2.74/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.74/0.99  
% 2.74/0.99  
% 2.74/0.99  ------ 
% 2.74/0.99  Current options:
% 2.74/0.99  ------ 
% 2.74/0.99  
% 2.74/0.99  ------ Input Options
% 2.74/0.99  
% 2.74/0.99  --out_options                           all
% 2.74/0.99  --tptp_safe_out                         true
% 2.74/0.99  --problem_path                          ""
% 2.74/0.99  --include_path                          ""
% 2.74/0.99  --clausifier                            res/vclausify_rel
% 2.74/0.99  --clausifier_options                    --mode clausify
% 2.74/0.99  --stdin                                 false
% 2.74/0.99  --stats_out                             all
% 2.74/0.99  
% 2.74/0.99  ------ General Options
% 2.74/0.99  
% 2.74/0.99  --fof                                   false
% 2.74/0.99  --time_out_real                         305.
% 2.74/0.99  --time_out_virtual                      -1.
% 2.74/0.99  --symbol_type_check                     false
% 2.74/0.99  --clausify_out                          false
% 2.74/0.99  --sig_cnt_out                           false
% 2.74/0.99  --trig_cnt_out                          false
% 2.74/0.99  --trig_cnt_out_tolerance                1.
% 2.74/0.99  --trig_cnt_out_sk_spl                   false
% 2.74/0.99  --abstr_cl_out                          false
% 2.74/0.99  
% 2.74/0.99  ------ Global Options
% 2.74/0.99  
% 2.74/0.99  --schedule                              default
% 2.74/0.99  --add_important_lit                     false
% 2.74/0.99  --prop_solver_per_cl                    1000
% 2.74/0.99  --min_unsat_core                        false
% 2.74/0.99  --soft_assumptions                      false
% 2.74/0.99  --soft_lemma_size                       3
% 2.74/0.99  --prop_impl_unit_size                   0
% 2.74/0.99  --prop_impl_unit                        []
% 2.74/0.99  --share_sel_clauses                     true
% 2.74/0.99  --reset_solvers                         false
% 2.74/0.99  --bc_imp_inh                            [conj_cone]
% 2.74/0.99  --conj_cone_tolerance                   3.
% 2.74/0.99  --extra_neg_conj                        none
% 2.74/0.99  --large_theory_mode                     true
% 2.74/0.99  --prolific_symb_bound                   200
% 2.74/0.99  --lt_threshold                          2000
% 2.74/0.99  --clause_weak_htbl                      true
% 2.74/0.99  --gc_record_bc_elim                     false
% 2.74/0.99  
% 2.74/0.99  ------ Preprocessing Options
% 2.74/0.99  
% 2.74/0.99  --preprocessing_flag                    true
% 2.74/0.99  --time_out_prep_mult                    0.1
% 2.74/0.99  --splitting_mode                        input
% 2.74/0.99  --splitting_grd                         true
% 2.74/0.99  --splitting_cvd                         false
% 2.74/0.99  --splitting_cvd_svl                     false
% 2.74/0.99  --splitting_nvd                         32
% 2.74/0.99  --sub_typing                            true
% 2.74/0.99  --prep_gs_sim                           true
% 2.74/0.99  --prep_unflatten                        true
% 2.74/0.99  --prep_res_sim                          true
% 2.74/0.99  --prep_upred                            true
% 2.74/0.99  --prep_sem_filter                       exhaustive
% 2.74/0.99  --prep_sem_filter_out                   false
% 2.74/0.99  --pred_elim                             true
% 2.74/0.99  --res_sim_input                         true
% 2.74/0.99  --eq_ax_congr_red                       true
% 2.74/0.99  --pure_diseq_elim                       true
% 2.74/0.99  --brand_transform                       false
% 2.74/0.99  --non_eq_to_eq                          false
% 2.74/0.99  --prep_def_merge                        true
% 2.74/0.99  --prep_def_merge_prop_impl              false
% 2.74/0.99  --prep_def_merge_mbd                    true
% 2.74/0.99  --prep_def_merge_tr_red                 false
% 2.74/0.99  --prep_def_merge_tr_cl                  false
% 2.74/0.99  --smt_preprocessing                     true
% 2.74/0.99  --smt_ac_axioms                         fast
% 2.74/0.99  --preprocessed_out                      false
% 2.74/0.99  --preprocessed_stats                    false
% 2.74/0.99  
% 2.74/0.99  ------ Abstraction refinement Options
% 2.74/0.99  
% 2.74/0.99  --abstr_ref                             []
% 2.74/0.99  --abstr_ref_prep                        false
% 2.74/0.99  --abstr_ref_until_sat                   false
% 2.74/0.99  --abstr_ref_sig_restrict                funpre
% 2.74/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.74/0.99  --abstr_ref_under                       []
% 2.74/0.99  
% 2.74/0.99  ------ SAT Options
% 2.74/0.99  
% 2.74/0.99  --sat_mode                              false
% 2.74/0.99  --sat_fm_restart_options                ""
% 2.74/0.99  --sat_gr_def                            false
% 2.74/0.99  --sat_epr_types                         true
% 2.74/0.99  --sat_non_cyclic_types                  false
% 2.74/0.99  --sat_finite_models                     false
% 2.74/0.99  --sat_fm_lemmas                         false
% 2.74/0.99  --sat_fm_prep                           false
% 2.74/0.99  --sat_fm_uc_incr                        true
% 2.74/0.99  --sat_out_model                         small
% 2.74/0.99  --sat_out_clauses                       false
% 2.74/0.99  
% 2.74/0.99  ------ QBF Options
% 2.74/0.99  
% 2.74/0.99  --qbf_mode                              false
% 2.74/0.99  --qbf_elim_univ                         false
% 2.74/0.99  --qbf_dom_inst                          none
% 2.74/0.99  --qbf_dom_pre_inst                      false
% 2.74/0.99  --qbf_sk_in                             false
% 2.74/0.99  --qbf_pred_elim                         true
% 2.74/0.99  --qbf_split                             512
% 2.74/0.99  
% 2.74/0.99  ------ BMC1 Options
% 2.74/0.99  
% 2.74/0.99  --bmc1_incremental                      false
% 2.74/0.99  --bmc1_axioms                           reachable_all
% 2.74/0.99  --bmc1_min_bound                        0
% 2.74/0.99  --bmc1_max_bound                        -1
% 2.74/0.99  --bmc1_max_bound_default                -1
% 2.74/0.99  --bmc1_symbol_reachability              true
% 2.74/0.99  --bmc1_property_lemmas                  false
% 2.74/0.99  --bmc1_k_induction                      false
% 2.74/0.99  --bmc1_non_equiv_states                 false
% 2.74/0.99  --bmc1_deadlock                         false
% 2.74/0.99  --bmc1_ucm                              false
% 2.74/0.99  --bmc1_add_unsat_core                   none
% 2.74/0.99  --bmc1_unsat_core_children              false
% 2.74/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.74/0.99  --bmc1_out_stat                         full
% 2.74/0.99  --bmc1_ground_init                      false
% 2.74/0.99  --bmc1_pre_inst_next_state              false
% 2.74/0.99  --bmc1_pre_inst_state                   false
% 2.74/0.99  --bmc1_pre_inst_reach_state             false
% 2.74/0.99  --bmc1_out_unsat_core                   false
% 2.74/0.99  --bmc1_aig_witness_out                  false
% 2.74/0.99  --bmc1_verbose                          false
% 2.74/0.99  --bmc1_dump_clauses_tptp                false
% 2.74/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.74/0.99  --bmc1_dump_file                        -
% 2.74/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.74/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.74/0.99  --bmc1_ucm_extend_mode                  1
% 2.74/0.99  --bmc1_ucm_init_mode                    2
% 2.74/0.99  --bmc1_ucm_cone_mode                    none
% 2.74/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.74/0.99  --bmc1_ucm_relax_model                  4
% 2.74/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.74/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.74/0.99  --bmc1_ucm_layered_model                none
% 2.74/0.99  --bmc1_ucm_max_lemma_size               10
% 2.74/0.99  
% 2.74/0.99  ------ AIG Options
% 2.74/0.99  
% 2.74/0.99  --aig_mode                              false
% 2.74/0.99  
% 2.74/0.99  ------ Instantiation Options
% 2.74/0.99  
% 2.74/0.99  --instantiation_flag                    true
% 2.74/0.99  --inst_sos_flag                         false
% 2.74/0.99  --inst_sos_phase                        true
% 2.74/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.74/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.74/0.99  --inst_lit_sel_side                     none
% 2.74/0.99  --inst_solver_per_active                1400
% 2.74/0.99  --inst_solver_calls_frac                1.
% 2.74/0.99  --inst_passive_queue_type               priority_queues
% 2.74/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.74/0.99  --inst_passive_queues_freq              [25;2]
% 2.74/0.99  --inst_dismatching                      true
% 2.74/0.99  --inst_eager_unprocessed_to_passive     true
% 2.74/0.99  --inst_prop_sim_given                   true
% 2.74/0.99  --inst_prop_sim_new                     false
% 2.74/0.99  --inst_subs_new                         false
% 2.74/0.99  --inst_eq_res_simp                      false
% 2.74/0.99  --inst_subs_given                       false
% 2.74/0.99  --inst_orphan_elimination               true
% 2.74/0.99  --inst_learning_loop_flag               true
% 2.74/0.99  --inst_learning_start                   3000
% 2.74/0.99  --inst_learning_factor                  2
% 2.74/0.99  --inst_start_prop_sim_after_learn       3
% 2.74/0.99  --inst_sel_renew                        solver
% 2.74/0.99  --inst_lit_activity_flag                true
% 2.74/0.99  --inst_restr_to_given                   false
% 2.74/0.99  --inst_activity_threshold               500
% 2.74/0.99  --inst_out_proof                        true
% 2.74/0.99  
% 2.74/0.99  ------ Resolution Options
% 2.74/0.99  
% 2.74/0.99  --resolution_flag                       false
% 2.74/0.99  --res_lit_sel                           adaptive
% 2.74/0.99  --res_lit_sel_side                      none
% 2.74/0.99  --res_ordering                          kbo
% 2.74/0.99  --res_to_prop_solver                    active
% 2.74/0.99  --res_prop_simpl_new                    false
% 2.74/0.99  --res_prop_simpl_given                  true
% 2.74/0.99  --res_passive_queue_type                priority_queues
% 2.74/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.74/0.99  --res_passive_queues_freq               [15;5]
% 2.74/0.99  --res_forward_subs                      full
% 2.74/0.99  --res_backward_subs                     full
% 2.74/0.99  --res_forward_subs_resolution           true
% 2.74/0.99  --res_backward_subs_resolution          true
% 2.74/0.99  --res_orphan_elimination                true
% 2.74/0.99  --res_time_limit                        2.
% 2.74/0.99  --res_out_proof                         true
% 2.74/0.99  
% 2.74/0.99  ------ Superposition Options
% 2.74/0.99  
% 2.74/0.99  --superposition_flag                    true
% 2.74/0.99  --sup_passive_queue_type                priority_queues
% 2.74/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.74/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.74/0.99  --demod_completeness_check              fast
% 2.74/0.99  --demod_use_ground                      true
% 2.74/0.99  --sup_to_prop_solver                    passive
% 2.74/0.99  --sup_prop_simpl_new                    true
% 2.74/0.99  --sup_prop_simpl_given                  true
% 2.74/0.99  --sup_fun_splitting                     false
% 2.74/0.99  --sup_smt_interval                      50000
% 2.74/0.99  
% 2.74/0.99  ------ Superposition Simplification Setup
% 2.74/0.99  
% 2.74/0.99  --sup_indices_passive                   []
% 2.74/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.74/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/0.99  --sup_full_bw                           [BwDemod]
% 2.74/0.99  --sup_immed_triv                        [TrivRules]
% 2.74/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.74/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/0.99  --sup_immed_bw_main                     []
% 2.74/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.74/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.74/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.74/0.99  
% 2.74/0.99  ------ Combination Options
% 2.74/0.99  
% 2.74/0.99  --comb_res_mult                         3
% 2.74/0.99  --comb_sup_mult                         2
% 2.74/0.99  --comb_inst_mult                        10
% 2.74/0.99  
% 2.74/0.99  ------ Debug Options
% 2.74/0.99  
% 2.74/0.99  --dbg_backtrace                         false
% 2.74/0.99  --dbg_dump_prop_clauses                 false
% 2.74/0.99  --dbg_dump_prop_clauses_file            -
% 2.74/0.99  --dbg_out_stat                          false
% 2.74/0.99  
% 2.74/0.99  
% 2.74/0.99  
% 2.74/0.99  
% 2.74/0.99  ------ Proving...
% 2.74/0.99  
% 2.74/0.99  
% 2.74/0.99  % SZS status Theorem for theBenchmark.p
% 2.74/0.99  
% 2.74/0.99   Resolution empty clause
% 2.74/0.99  
% 2.74/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.74/0.99  
% 2.74/0.99  fof(f5,axiom,(
% 2.74/0.99    ! [X0,X1] : ((k1_xboole_0 = X0 => (k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1)) & (k1_xboole_0 != X0 => (k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X3,X0) => r2_hidden(X2,X3))))))),
% 2.74/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/0.99  
% 2.74/0.99  fof(f10,plain,(
% 2.74/0.99    ! [X0,X1] : (((k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1) | k1_xboole_0 != X0) & ((k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)))) | k1_xboole_0 = X0))),
% 2.74/0.99    inference(ennf_transformation,[],[f5])).
% 2.74/0.99  
% 2.74/0.99  fof(f19,plain,(
% 2.74/0.99    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | ? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0))) & (! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)) | ~r2_hidden(X2,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 2.74/0.99    inference(nnf_transformation,[],[f10])).
% 2.74/0.99  
% 2.74/0.99  fof(f20,plain,(
% 2.74/0.99    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | ? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X4] : (r2_hidden(X2,X4) | ~r2_hidden(X4,X0)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ? [X6] : (~r2_hidden(X5,X6) & r2_hidden(X6,X0))) & (! [X7] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0)) | ~r2_hidden(X5,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 2.74/0.99    inference(rectify,[],[f19])).
% 2.74/0.99  
% 2.74/0.99  fof(f23,plain,(
% 2.74/0.99    ! [X5,X0] : (? [X6] : (~r2_hidden(X5,X6) & r2_hidden(X6,X0)) => (~r2_hidden(X5,sK3(X0,X5)) & r2_hidden(sK3(X0,X5),X0)))),
% 2.74/0.99    introduced(choice_axiom,[])).
% 2.74/0.99  
% 2.74/0.99  fof(f22,plain,(
% 2.74/0.99    ( ! [X2] : (! [X1,X0] : (? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) => (~r2_hidden(X2,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),X0)))) )),
% 2.74/0.99    introduced(choice_axiom,[])).
% 2.74/0.99  
% 2.74/0.99  fof(f21,plain,(
% 2.74/0.99    ! [X1,X0] : (? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X4] : (r2_hidden(X2,X4) | ~r2_hidden(X4,X0)) | r2_hidden(X2,X1))) => ((? [X3] : (~r2_hidden(sK1(X0,X1),X3) & r2_hidden(X3,X0)) | ~r2_hidden(sK1(X0,X1),X1)) & (! [X4] : (r2_hidden(sK1(X0,X1),X4) | ~r2_hidden(X4,X0)) | r2_hidden(sK1(X0,X1),X1))))),
% 2.74/0.99    introduced(choice_axiom,[])).
% 2.74/0.99  
% 2.74/0.99  fof(f24,plain,(
% 2.74/0.99    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | (((~r2_hidden(sK1(X0,X1),sK2(X0,X1)) & r2_hidden(sK2(X0,X1),X0)) | ~r2_hidden(sK1(X0,X1),X1)) & (! [X4] : (r2_hidden(sK1(X0,X1),X4) | ~r2_hidden(X4,X0)) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | (~r2_hidden(X5,sK3(X0,X5)) & r2_hidden(sK3(X0,X5),X0))) & (! [X7] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0)) | ~r2_hidden(X5,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 2.74/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f20,f23,f22,f21])).
% 2.74/0.99  
% 2.74/0.99  fof(f42,plain,(
% 2.74/0.99    ( ! [X0,X5,X1] : (r2_hidden(X5,X1) | r2_hidden(sK3(X0,X5),X0) | k1_setfam_1(X0) != X1 | k1_xboole_0 = X0) )),
% 2.74/0.99    inference(cnf_transformation,[],[f24])).
% 2.74/0.99  
% 2.74/0.99  fof(f64,plain,(
% 2.74/0.99    ( ! [X0,X5] : (r2_hidden(X5,k1_setfam_1(X0)) | r2_hidden(sK3(X0,X5),X0) | k1_xboole_0 = X0) )),
% 2.74/0.99    inference(equality_resolution,[],[f42])).
% 2.74/0.99  
% 2.74/0.99  fof(f7,conjecture,(
% 2.74/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r2_hidden(X1,X0) => (r2_hidden(X1,k8_setfam_1(X0,X2)) <=> ! [X3] : (r2_hidden(X3,X2) => r2_hidden(X1,X3)))))),
% 2.74/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/0.99  
% 2.74/0.99  fof(f8,negated_conjecture,(
% 2.74/0.99    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r2_hidden(X1,X0) => (r2_hidden(X1,k8_setfam_1(X0,X2)) <=> ! [X3] : (r2_hidden(X3,X2) => r2_hidden(X1,X3)))))),
% 2.74/0.99    inference(negated_conjecture,[],[f7])).
% 2.74/0.99  
% 2.74/0.99  fof(f12,plain,(
% 2.74/0.99    ? [X0,X1,X2] : (((r2_hidden(X1,k8_setfam_1(X0,X2)) <~> ! [X3] : (r2_hidden(X1,X3) | ~r2_hidden(X3,X2))) & r2_hidden(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.74/0.99    inference(ennf_transformation,[],[f8])).
% 2.74/0.99  
% 2.74/0.99  fof(f13,plain,(
% 2.74/0.99    ? [X0,X1,X2] : ((r2_hidden(X1,k8_setfam_1(X0,X2)) <~> ! [X3] : (r2_hidden(X1,X3) | ~r2_hidden(X3,X2))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.74/0.99    inference(flattening,[],[f12])).
% 2.74/0.99  
% 2.74/0.99  fof(f25,plain,(
% 2.74/0.99    ? [X0,X1,X2] : (((? [X3] : (~r2_hidden(X1,X3) & r2_hidden(X3,X2)) | ~r2_hidden(X1,k8_setfam_1(X0,X2))) & (! [X3] : (r2_hidden(X1,X3) | ~r2_hidden(X3,X2)) | r2_hidden(X1,k8_setfam_1(X0,X2)))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.74/0.99    inference(nnf_transformation,[],[f13])).
% 2.74/0.99  
% 2.74/0.99  fof(f26,plain,(
% 2.74/0.99    ? [X0,X1,X2] : ((? [X3] : (~r2_hidden(X1,X3) & r2_hidden(X3,X2)) | ~r2_hidden(X1,k8_setfam_1(X0,X2))) & (! [X3] : (r2_hidden(X1,X3) | ~r2_hidden(X3,X2)) | r2_hidden(X1,k8_setfam_1(X0,X2))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.74/0.99    inference(flattening,[],[f25])).
% 2.74/0.99  
% 2.74/0.99  fof(f27,plain,(
% 2.74/0.99    ? [X0,X1,X2] : ((? [X3] : (~r2_hidden(X1,X3) & r2_hidden(X3,X2)) | ~r2_hidden(X1,k8_setfam_1(X0,X2))) & (! [X4] : (r2_hidden(X1,X4) | ~r2_hidden(X4,X2)) | r2_hidden(X1,k8_setfam_1(X0,X2))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.74/0.99    inference(rectify,[],[f26])).
% 2.74/0.99  
% 2.74/0.99  fof(f29,plain,(
% 2.74/0.99    ( ! [X2,X1] : (? [X3] : (~r2_hidden(X1,X3) & r2_hidden(X3,X2)) => (~r2_hidden(X1,sK7) & r2_hidden(sK7,X2))) )),
% 2.74/0.99    introduced(choice_axiom,[])).
% 2.74/0.99  
% 2.74/0.99  fof(f28,plain,(
% 2.74/0.99    ? [X0,X1,X2] : ((? [X3] : (~r2_hidden(X1,X3) & r2_hidden(X3,X2)) | ~r2_hidden(X1,k8_setfam_1(X0,X2))) & (! [X4] : (r2_hidden(X1,X4) | ~r2_hidden(X4,X2)) | r2_hidden(X1,k8_setfam_1(X0,X2))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) => ((? [X3] : (~r2_hidden(sK5,X3) & r2_hidden(X3,sK6)) | ~r2_hidden(sK5,k8_setfam_1(sK4,sK6))) & (! [X4] : (r2_hidden(sK5,X4) | ~r2_hidden(X4,sK6)) | r2_hidden(sK5,k8_setfam_1(sK4,sK6))) & r2_hidden(sK5,sK4) & m1_subset_1(sK6,k1_zfmisc_1(k1_zfmisc_1(sK4))))),
% 2.74/0.99    introduced(choice_axiom,[])).
% 2.74/0.99  
% 2.74/0.99  fof(f30,plain,(
% 2.74/0.99    ((~r2_hidden(sK5,sK7) & r2_hidden(sK7,sK6)) | ~r2_hidden(sK5,k8_setfam_1(sK4,sK6))) & (! [X4] : (r2_hidden(sK5,X4) | ~r2_hidden(X4,sK6)) | r2_hidden(sK5,k8_setfam_1(sK4,sK6))) & r2_hidden(sK5,sK4) & m1_subset_1(sK6,k1_zfmisc_1(k1_zfmisc_1(sK4)))),
% 2.74/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f27,f29,f28])).
% 2.74/0.99  
% 2.74/0.99  fof(f52,plain,(
% 2.74/0.99    ( ! [X4] : (r2_hidden(sK5,X4) | ~r2_hidden(X4,sK6) | r2_hidden(sK5,k8_setfam_1(sK4,sK6))) )),
% 2.74/0.99    inference(cnf_transformation,[],[f30])).
% 2.74/0.99  
% 2.74/0.99  fof(f43,plain,(
% 2.74/0.99    ( ! [X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(X5,sK3(X0,X5)) | k1_setfam_1(X0) != X1 | k1_xboole_0 = X0) )),
% 2.74/0.99    inference(cnf_transformation,[],[f24])).
% 2.74/0.99  
% 2.74/0.99  fof(f63,plain,(
% 2.74/0.99    ( ! [X0,X5] : (r2_hidden(X5,k1_setfam_1(X0)) | ~r2_hidden(X5,sK3(X0,X5)) | k1_xboole_0 = X0) )),
% 2.74/0.99    inference(equality_resolution,[],[f43])).
% 2.74/0.99  
% 2.74/0.99  fof(f4,axiom,(
% 2.74/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 2.74/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/0.99  
% 2.74/0.99  fof(f9,plain,(
% 2.74/0.99    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.74/0.99    inference(ennf_transformation,[],[f4])).
% 2.74/0.99  
% 2.74/0.99  fof(f39,plain,(
% 2.74/0.99    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.74/0.99    inference(cnf_transformation,[],[f9])).
% 2.74/0.99  
% 2.74/0.99  fof(f50,plain,(
% 2.74/0.99    m1_subset_1(sK6,k1_zfmisc_1(k1_zfmisc_1(sK4)))),
% 2.74/0.99    inference(cnf_transformation,[],[f30])).
% 2.74/0.99  
% 2.74/0.99  fof(f6,axiom,(
% 2.74/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 2.74/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/0.99  
% 2.74/0.99  fof(f11,plain,(
% 2.74/0.99    ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.74/0.99    inference(ennf_transformation,[],[f6])).
% 2.74/0.99  
% 2.74/0.99  fof(f49,plain,(
% 2.74/0.99    ( ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.74/0.99    inference(cnf_transformation,[],[f11])).
% 2.74/0.99  
% 2.74/0.99  fof(f54,plain,(
% 2.74/0.99    ~r2_hidden(sK5,sK7) | ~r2_hidden(sK5,k8_setfam_1(sK4,sK6))),
% 2.74/0.99    inference(cnf_transformation,[],[f30])).
% 2.74/0.99  
% 2.74/0.99  fof(f53,plain,(
% 2.74/0.99    r2_hidden(sK7,sK6) | ~r2_hidden(sK5,k8_setfam_1(sK4,sK6))),
% 2.74/0.99    inference(cnf_transformation,[],[f30])).
% 2.74/0.99  
% 2.74/0.99  fof(f41,plain,(
% 2.74/0.99    ( ! [X0,X7,X5,X1] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0) | ~r2_hidden(X5,X1) | k1_setfam_1(X0) != X1 | k1_xboole_0 = X0) )),
% 2.74/0.99    inference(cnf_transformation,[],[f24])).
% 2.74/0.99  
% 2.74/0.99  fof(f65,plain,(
% 2.74/0.99    ( ! [X0,X7,X5] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0) | ~r2_hidden(X5,k1_setfam_1(X0)) | k1_xboole_0 = X0) )),
% 2.74/0.99    inference(equality_resolution,[],[f41])).
% 2.74/0.99  
% 2.74/0.99  fof(f40,plain,(
% 2.74/0.99    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.74/0.99    inference(cnf_transformation,[],[f9])).
% 2.74/0.99  
% 2.74/0.99  fof(f58,plain,(
% 2.74/0.99    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.74/0.99    inference(equality_resolution,[],[f40])).
% 2.74/0.99  
% 2.74/0.99  fof(f51,plain,(
% 2.74/0.99    r2_hidden(sK5,sK4)),
% 2.74/0.99    inference(cnf_transformation,[],[f30])).
% 2.74/0.99  
% 2.74/0.99  fof(f2,axiom,(
% 2.74/0.99    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.74/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/0.99  
% 2.74/0.99  fof(f37,plain,(
% 2.74/0.99    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.74/0.99    inference(cnf_transformation,[],[f2])).
% 2.74/0.99  
% 2.74/0.99  fof(f3,axiom,(
% 2.74/0.99    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 2.74/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/0.99  
% 2.74/0.99  fof(f38,plain,(
% 2.74/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 2.74/0.99    inference(cnf_transformation,[],[f3])).
% 2.74/0.99  
% 2.74/0.99  fof(f1,axiom,(
% 2.74/0.99    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.74/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/0.99  
% 2.74/0.99  fof(f14,plain,(
% 2.74/0.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.74/0.99    inference(nnf_transformation,[],[f1])).
% 2.74/0.99  
% 2.74/0.99  fof(f15,plain,(
% 2.74/0.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.74/0.99    inference(flattening,[],[f14])).
% 2.74/0.99  
% 2.74/0.99  fof(f16,plain,(
% 2.74/0.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.74/0.99    inference(rectify,[],[f15])).
% 2.74/0.99  
% 2.74/0.99  fof(f17,plain,(
% 2.74/0.99    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 2.74/0.99    introduced(choice_axiom,[])).
% 2.74/0.99  
% 2.74/0.99  fof(f18,plain,(
% 2.74/0.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.74/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f17])).
% 2.74/0.99  
% 2.74/0.99  fof(f32,plain,(
% 2.74/0.99    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.74/0.99    inference(cnf_transformation,[],[f18])).
% 2.74/0.99  
% 2.74/0.99  fof(f56,plain,(
% 2.74/0.99    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 2.74/0.99    inference(equality_resolution,[],[f32])).
% 2.74/0.99  
% 2.74/0.99  fof(f31,plain,(
% 2.74/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.74/0.99    inference(cnf_transformation,[],[f18])).
% 2.74/0.99  
% 2.74/0.99  fof(f57,plain,(
% 2.74/0.99    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 2.74/0.99    inference(equality_resolution,[],[f31])).
% 2.74/0.99  
% 2.74/0.99  cnf(c_16,plain,
% 2.74/0.99      ( r2_hidden(X0,k1_setfam_1(X1))
% 2.74/0.99      | r2_hidden(sK3(X1,X0),X1)
% 2.74/0.99      | k1_xboole_0 = X1 ),
% 2.74/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_645,plain,
% 2.74/0.99      ( k1_xboole_0 = X0
% 2.74/0.99      | r2_hidden(X1,k1_setfam_1(X0)) = iProver_top
% 2.74/0.99      | r2_hidden(sK3(X0,X1),X0) = iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_21,negated_conjecture,
% 2.74/0.99      ( ~ r2_hidden(X0,sK6)
% 2.74/0.99      | r2_hidden(sK5,X0)
% 2.74/0.99      | r2_hidden(sK5,k8_setfam_1(sK4,sK6)) ),
% 2.74/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_641,plain,
% 2.74/0.99      ( r2_hidden(X0,sK6) != iProver_top
% 2.74/0.99      | r2_hidden(sK5,X0) = iProver_top
% 2.74/0.99      | r2_hidden(sK5,k8_setfam_1(sK4,sK6)) = iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1586,plain,
% 2.74/0.99      ( sK6 = k1_xboole_0
% 2.74/0.99      | r2_hidden(X0,k1_setfam_1(sK6)) = iProver_top
% 2.74/0.99      | r2_hidden(sK5,sK3(sK6,X0)) = iProver_top
% 2.74/0.99      | r2_hidden(sK5,k8_setfam_1(sK4,sK6)) = iProver_top ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_645,c_641]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_15,plain,
% 2.74/0.99      ( ~ r2_hidden(X0,sK3(X1,X0))
% 2.74/0.99      | r2_hidden(X0,k1_setfam_1(X1))
% 2.74/0.99      | k1_xboole_0 = X1 ),
% 2.74/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_646,plain,
% 2.74/0.99      ( k1_xboole_0 = X0
% 2.74/0.99      | r2_hidden(X1,sK3(X0,X1)) != iProver_top
% 2.74/0.99      | r2_hidden(X1,k1_setfam_1(X0)) = iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1894,plain,
% 2.74/0.99      ( sK6 = k1_xboole_0
% 2.74/0.99      | r2_hidden(sK5,k8_setfam_1(sK4,sK6)) = iProver_top
% 2.74/0.99      | r2_hidden(sK5,k1_setfam_1(sK6)) = iProver_top ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_1586,c_646]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_995,plain,
% 2.74/0.99      ( ~ r2_hidden(sK7,sK6)
% 2.74/0.99      | r2_hidden(sK5,k8_setfam_1(sK4,sK6))
% 2.74/0.99      | r2_hidden(sK5,sK7) ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_21]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_996,plain,
% 2.74/0.99      ( r2_hidden(sK7,sK6) != iProver_top
% 2.74/0.99      | r2_hidden(sK5,k8_setfam_1(sK4,sK6)) = iProver_top
% 2.74/0.99      | r2_hidden(sK5,sK7) = iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_995]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_9,plain,
% 2.74/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.74/0.99      | k6_setfam_1(X1,X0) = k8_setfam_1(X1,X0)
% 2.74/0.99      | k1_xboole_0 = X0 ),
% 2.74/0.99      inference(cnf_transformation,[],[f39]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_23,negated_conjecture,
% 2.74/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k1_zfmisc_1(sK4))) ),
% 2.74/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_246,plain,
% 2.74/0.99      ( k6_setfam_1(X0,X1) = k8_setfam_1(X0,X1)
% 2.74/0.99      | k1_zfmisc_1(k1_zfmisc_1(X0)) != k1_zfmisc_1(k1_zfmisc_1(sK4))
% 2.74/0.99      | sK6 != X1
% 2.74/0.99      | k1_xboole_0 = X1 ),
% 2.74/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_23]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_247,plain,
% 2.74/0.99      ( k6_setfam_1(X0,sK6) = k8_setfam_1(X0,sK6)
% 2.74/0.99      | k1_zfmisc_1(k1_zfmisc_1(X0)) != k1_zfmisc_1(k1_zfmisc_1(sK4))
% 2.74/0.99      | k1_xboole_0 = sK6 ),
% 2.74/0.99      inference(unflattening,[status(thm)],[c_246]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_848,plain,
% 2.74/0.99      ( k6_setfam_1(sK4,sK6) = k8_setfam_1(sK4,sK6) | sK6 = k1_xboole_0 ),
% 2.74/0.99      inference(equality_resolution,[status(thm)],[c_247]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_18,plain,
% 2.74/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.74/0.99      | k6_setfam_1(X1,X0) = k1_setfam_1(X0) ),
% 2.74/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_237,plain,
% 2.74/0.99      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
% 2.74/0.99      | k1_zfmisc_1(k1_zfmisc_1(X0)) != k1_zfmisc_1(k1_zfmisc_1(sK4))
% 2.74/0.99      | sK6 != X1 ),
% 2.74/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_23]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_238,plain,
% 2.74/0.99      ( k6_setfam_1(X0,sK6) = k1_setfam_1(sK6)
% 2.74/0.99      | k1_zfmisc_1(k1_zfmisc_1(X0)) != k1_zfmisc_1(k1_zfmisc_1(sK4)) ),
% 2.74/0.99      inference(unflattening,[status(thm)],[c_237]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_831,plain,
% 2.74/0.99      ( k6_setfam_1(sK4,sK6) = k1_setfam_1(sK6) ),
% 2.74/0.99      inference(equality_resolution,[status(thm)],[c_238]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1233,plain,
% 2.74/0.99      ( k8_setfam_1(sK4,sK6) = k1_setfam_1(sK6) | sK6 = k1_xboole_0 ),
% 2.74/0.99      inference(light_normalisation,[status(thm)],[c_848,c_831]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_19,negated_conjecture,
% 2.74/0.99      ( ~ r2_hidden(sK5,k8_setfam_1(sK4,sK6)) | ~ r2_hidden(sK5,sK7) ),
% 2.74/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_643,plain,
% 2.74/0.99      ( r2_hidden(sK5,k8_setfam_1(sK4,sK6)) != iProver_top
% 2.74/0.99      | r2_hidden(sK5,sK7) != iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1236,plain,
% 2.74/0.99      ( sK6 = k1_xboole_0
% 2.74/0.99      | r2_hidden(sK5,k1_setfam_1(sK6)) != iProver_top
% 2.74/0.99      | r2_hidden(sK5,sK7) != iProver_top ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_1233,c_643]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_20,negated_conjecture,
% 2.74/0.99      ( r2_hidden(sK7,sK6) | ~ r2_hidden(sK5,k8_setfam_1(sK4,sK6)) ),
% 2.74/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_642,plain,
% 2.74/0.99      ( r2_hidden(sK7,sK6) = iProver_top
% 2.74/0.99      | r2_hidden(sK5,k8_setfam_1(sK4,sK6)) != iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1237,plain,
% 2.74/0.99      ( sK6 = k1_xboole_0
% 2.74/0.99      | r2_hidden(sK7,sK6) = iProver_top
% 2.74/0.99      | r2_hidden(sK5,k1_setfam_1(sK6)) != iProver_top ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_1233,c_642]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1956,plain,
% 2.74/0.99      ( r2_hidden(sK5,k8_setfam_1(sK4,sK6)) = iProver_top | sK6 = k1_xboole_0 ),
% 2.74/0.99      inference(global_propositional_subsumption,
% 2.74/0.99                [status(thm)],
% 2.74/0.99                [c_1894,c_996,c_1236,c_1237]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1957,plain,
% 2.74/0.99      ( sK6 = k1_xboole_0 | r2_hidden(sK5,k8_setfam_1(sK4,sK6)) = iProver_top ),
% 2.74/0.99      inference(renaming,[status(thm)],[c_1956]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1964,plain,
% 2.74/0.99      ( sK6 = k1_xboole_0 | r2_hidden(sK7,sK6) = iProver_top ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_1957,c_642]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1962,plain,
% 2.74/0.99      ( sK6 = k1_xboole_0 | r2_hidden(sK5,k1_setfam_1(sK6)) = iProver_top ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_1233,c_1957]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_17,plain,
% 2.74/0.99      ( ~ r2_hidden(X0,X1)
% 2.74/0.99      | r2_hidden(X2,X0)
% 2.74/0.99      | ~ r2_hidden(X2,k1_setfam_1(X1))
% 2.74/0.99      | k1_xboole_0 = X1 ),
% 2.74/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_644,plain,
% 2.74/0.99      ( k1_xboole_0 = X0
% 2.74/0.99      | r2_hidden(X1,X0) != iProver_top
% 2.74/0.99      | r2_hidden(X2,X1) = iProver_top
% 2.74/0.99      | r2_hidden(X2,k1_setfam_1(X0)) != iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2047,plain,
% 2.74/0.99      ( sK6 = k1_xboole_0
% 2.74/0.99      | r2_hidden(X0,sK6) != iProver_top
% 2.74/0.99      | r2_hidden(sK5,X0) = iProver_top ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_1962,c_644]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2149,plain,
% 2.74/0.99      ( sK6 = k1_xboole_0 | r2_hidden(sK5,sK7) = iProver_top ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_1964,c_2047]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1963,plain,
% 2.74/0.99      ( sK6 = k1_xboole_0 | r2_hidden(sK5,sK7) != iProver_top ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_1957,c_643]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2166,plain,
% 2.74/0.99      ( sK6 = k1_xboole_0 ),
% 2.74/0.99      inference(global_propositional_subsumption,[status(thm)],[c_2149,c_1963]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_8,plain,
% 2.74/0.99      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
% 2.74/0.99      | k8_setfam_1(X0,k1_xboole_0) = X0 ),
% 2.74/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_226,plain,
% 2.74/0.99      ( k8_setfam_1(X0,k1_xboole_0) = X0
% 2.74/0.99      | k1_zfmisc_1(k1_zfmisc_1(X0)) != k1_zfmisc_1(k1_zfmisc_1(sK4))
% 2.74/0.99      | sK6 != k1_xboole_0 ),
% 2.74/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_23]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_844,plain,
% 2.74/0.99      ( k8_setfam_1(sK4,k1_xboole_0) = sK4 | sK6 != k1_xboole_0 ),
% 2.74/0.99      inference(equality_resolution,[status(thm)],[c_226]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2170,plain,
% 2.74/0.99      ( k8_setfam_1(sK4,k1_xboole_0) = sK4 | k1_xboole_0 != k1_xboole_0 ),
% 2.74/0.99      inference(demodulation,[status(thm)],[c_2166,c_844]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2199,plain,
% 2.74/0.99      ( k8_setfam_1(sK4,k1_xboole_0) = sK4 ),
% 2.74/0.99      inference(equality_resolution_simp,[status(thm)],[c_2170]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2177,plain,
% 2.74/0.99      ( r2_hidden(sK7,k1_xboole_0) = iProver_top
% 2.74/0.99      | r2_hidden(sK5,k8_setfam_1(sK4,k1_xboole_0)) != iProver_top ),
% 2.74/0.99      inference(demodulation,[status(thm)],[c_2166,c_642]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2202,plain,
% 2.74/0.99      ( r2_hidden(sK7,k1_xboole_0) = iProver_top
% 2.74/0.99      | r2_hidden(sK5,sK4) != iProver_top ),
% 2.74/0.99      inference(demodulation,[status(thm)],[c_2199,c_2177]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_22,negated_conjecture,
% 2.74/0.99      ( r2_hidden(sK5,sK4) ),
% 2.74/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_25,plain,
% 2.74/0.99      ( r2_hidden(sK5,sK4) = iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2311,plain,
% 2.74/0.99      ( r2_hidden(sK7,k1_xboole_0) = iProver_top ),
% 2.74/0.99      inference(global_propositional_subsumption,[status(thm)],[c_2202,c_25]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_6,plain,
% 2.74/0.99      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 2.74/0.99      inference(cnf_transformation,[],[f37]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_7,plain,
% 2.74/0.99      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 2.74/0.99      inference(cnf_transformation,[],[f38]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1176,plain,
% 2.74/0.99      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_6,c_7]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_4,plain,
% 2.74/0.99      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 2.74/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_651,plain,
% 2.74/0.99      ( r2_hidden(X0,X1) != iProver_top
% 2.74/0.99      | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1475,plain,
% 2.74/0.99      ( r2_hidden(X0,X1) != iProver_top
% 2.74/0.99      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_1176,c_651]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_5,plain,
% 2.74/0.99      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 2.74/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_650,plain,
% 2.74/0.99      ( r2_hidden(X0,X1) = iProver_top
% 2.74/0.99      | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1368,plain,
% 2.74/0.99      ( r2_hidden(X0,X1) = iProver_top
% 2.74/0.99      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_7,c_650]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1575,plain,
% 2.74/0.99      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.74/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1475,c_1368]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2316,plain,
% 2.74/0.99      ( $false ),
% 2.74/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_2311,c_1575]) ).
% 2.74/0.99  
% 2.74/0.99  
% 2.74/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.74/0.99  
% 2.74/0.99  ------                               Statistics
% 2.74/0.99  
% 2.74/0.99  ------ General
% 2.74/0.99  
% 2.74/0.99  abstr_ref_over_cycles:                  0
% 2.74/0.99  abstr_ref_under_cycles:                 0
% 2.74/0.99  gc_basic_clause_elim:                   0
% 2.74/0.99  forced_gc_time:                         0
% 2.74/0.99  parsing_time:                           0.011
% 2.74/0.99  unif_index_cands_time:                  0.
% 2.74/0.99  unif_index_add_time:                    0.
% 2.74/0.99  orderings_time:                         0.
% 2.74/0.99  out_proof_time:                         0.016
% 2.74/0.99  total_time:                             0.108
% 2.74/0.99  num_of_symbols:                         48
% 2.74/0.99  num_of_terms:                           2142
% 2.74/0.99  
% 2.74/0.99  ------ Preprocessing
% 2.74/0.99  
% 2.74/0.99  num_of_splits:                          0
% 2.74/0.99  num_of_split_atoms:                     0
% 2.74/0.99  num_of_reused_defs:                     0
% 2.74/0.99  num_eq_ax_congr_red:                    37
% 2.74/0.99  num_of_sem_filtered_clauses:            1
% 2.74/0.99  num_of_subtypes:                        0
% 2.74/0.99  monotx_restored_types:                  0
% 2.74/0.99  sat_num_of_epr_types:                   0
% 2.74/0.99  sat_num_of_non_cyclic_types:            0
% 2.74/0.99  sat_guarded_non_collapsed_types:        0
% 2.74/0.99  num_pure_diseq_elim:                    0
% 2.74/0.99  simp_replaced_by:                       0
% 2.74/0.99  res_preprocessed:                       108
% 2.74/0.99  prep_upred:                             0
% 2.74/0.99  prep_unflattend:                        2
% 2.74/0.99  smt_new_axioms:                         0
% 2.74/0.99  pred_elim_cands:                        1
% 2.74/0.99  pred_elim:                              1
% 2.74/0.99  pred_elim_cl:                           1
% 2.74/0.99  pred_elim_cycles:                       3
% 2.74/0.99  merged_defs:                            0
% 2.74/0.99  merged_defs_ncl:                        0
% 2.74/0.99  bin_hyper_res:                          0
% 2.74/0.99  prep_cycles:                            4
% 2.74/0.99  pred_elim_time:                         0.001
% 2.74/0.99  splitting_time:                         0.
% 2.74/0.99  sem_filter_time:                        0.
% 2.74/0.99  monotx_time:                            0.
% 2.74/0.99  subtype_inf_time:                       0.
% 2.74/0.99  
% 2.74/0.99  ------ Problem properties
% 2.74/0.99  
% 2.74/0.99  clauses:                                22
% 2.74/0.99  conjectures:                            4
% 2.74/0.99  epr:                                    1
% 2.74/0.99  horn:                                   10
% 2.74/0.99  ground:                                 4
% 2.74/0.99  unary:                                  4
% 2.74/0.99  binary:                                 5
% 2.74/0.99  lits:                                   59
% 2.74/0.99  lits_eq:                                23
% 2.74/0.99  fd_pure:                                0
% 2.74/0.99  fd_pseudo:                              0
% 2.74/0.99  fd_cond:                                3
% 2.74/0.99  fd_pseudo_cond:                         6
% 2.74/0.99  ac_symbols:                             0
% 2.74/0.99  
% 2.74/0.99  ------ Propositional Solver
% 2.74/0.99  
% 2.74/0.99  prop_solver_calls:                      26
% 2.74/0.99  prop_fast_solver_calls:                 651
% 2.74/0.99  smt_solver_calls:                       0
% 2.74/0.99  smt_fast_solver_calls:                  0
% 2.74/0.99  prop_num_of_clauses:                    722
% 2.74/0.99  prop_preprocess_simplified:             3410
% 2.74/0.99  prop_fo_subsumed:                       5
% 2.74/0.99  prop_solver_time:                       0.
% 2.74/0.99  smt_solver_time:                        0.
% 2.74/0.99  smt_fast_solver_time:                   0.
% 2.74/0.99  prop_fast_solver_time:                  0.
% 2.74/0.99  prop_unsat_core_time:                   0.
% 2.74/0.99  
% 2.74/0.99  ------ QBF
% 2.74/0.99  
% 2.74/0.99  qbf_q_res:                              0
% 2.74/0.99  qbf_num_tautologies:                    0
% 2.74/0.99  qbf_prep_cycles:                        0
% 2.74/0.99  
% 2.74/0.99  ------ BMC1
% 2.74/0.99  
% 2.74/0.99  bmc1_current_bound:                     -1
% 2.74/0.99  bmc1_last_solved_bound:                 -1
% 2.74/0.99  bmc1_unsat_core_size:                   -1
% 2.74/0.99  bmc1_unsat_core_parents_size:           -1
% 2.74/0.99  bmc1_merge_next_fun:                    0
% 2.74/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.74/0.99  
% 2.74/0.99  ------ Instantiation
% 2.74/0.99  
% 2.74/0.99  inst_num_of_clauses:                    217
% 2.74/0.99  inst_num_in_passive:                    0
% 2.74/0.99  inst_num_in_active:                     133
% 2.74/0.99  inst_num_in_unprocessed:                84
% 2.74/0.99  inst_num_of_loops:                      170
% 2.74/0.99  inst_num_of_learning_restarts:          0
% 2.74/0.99  inst_num_moves_active_passive:          35
% 2.74/0.99  inst_lit_activity:                      0
% 2.74/0.99  inst_lit_activity_moves:                0
% 2.74/0.99  inst_num_tautologies:                   0
% 2.74/0.99  inst_num_prop_implied:                  0
% 2.74/0.99  inst_num_existing_simplified:           0
% 2.74/0.99  inst_num_eq_res_simplified:             0
% 2.74/0.99  inst_num_child_elim:                    0
% 2.74/0.99  inst_num_of_dismatching_blockings:      140
% 2.74/0.99  inst_num_of_non_proper_insts:           157
% 2.74/0.99  inst_num_of_duplicates:                 0
% 2.74/0.99  inst_inst_num_from_inst_to_res:         0
% 2.74/0.99  inst_dismatching_checking_time:         0.
% 2.74/0.99  
% 2.74/0.99  ------ Resolution
% 2.74/0.99  
% 2.74/0.99  res_num_of_clauses:                     0
% 2.74/0.99  res_num_in_passive:                     0
% 2.74/0.99  res_num_in_active:                      0
% 2.74/0.99  res_num_of_loops:                       112
% 2.74/0.99  res_forward_subset_subsumed:            26
% 2.74/0.99  res_backward_subset_subsumed:           0
% 2.74/0.99  res_forward_subsumed:                   0
% 2.74/0.99  res_backward_subsumed:                  0
% 2.74/0.99  res_forward_subsumption_resolution:     0
% 2.74/0.99  res_backward_subsumption_resolution:    0
% 2.74/0.99  res_clause_to_clause_subsumption:       84
% 2.74/0.99  res_orphan_elimination:                 0
% 2.74/0.99  res_tautology_del:                      6
% 2.74/0.99  res_num_eq_res_simplified:              0
% 2.74/0.99  res_num_sel_changes:                    0
% 2.74/0.99  res_moves_from_active_to_pass:          0
% 2.74/0.99  
% 2.74/0.99  ------ Superposition
% 2.74/0.99  
% 2.74/0.99  sup_time_total:                         0.
% 2.74/0.99  sup_time_generating:                    0.
% 2.74/0.99  sup_time_sim_full:                      0.
% 2.74/0.99  sup_time_sim_immed:                     0.
% 2.74/0.99  
% 2.74/0.99  sup_num_of_clauses:                     31
% 2.74/0.99  sup_num_in_active:                      15
% 2.74/0.99  sup_num_in_passive:                     16
% 2.74/0.99  sup_num_of_loops:                       32
% 2.74/0.99  sup_fw_superposition:                   11
% 2.74/0.99  sup_bw_superposition:                   17
% 2.74/0.99  sup_immediate_simplified:               7
% 2.74/0.99  sup_given_eliminated:                   0
% 2.74/0.99  comparisons_done:                       0
% 2.74/0.99  comparisons_avoided:                    3
% 2.74/0.99  
% 2.74/0.99  ------ Simplifications
% 2.74/0.99  
% 2.74/0.99  
% 2.74/0.99  sim_fw_subset_subsumed:                 2
% 2.74/0.99  sim_bw_subset_subsumed:                 9
% 2.74/0.99  sim_fw_subsumed:                        1
% 2.74/0.99  sim_bw_subsumed:                        0
% 2.74/0.99  sim_fw_subsumption_res:                 1
% 2.74/0.99  sim_bw_subsumption_res:                 0
% 2.74/0.99  sim_tautology_del:                      4
% 2.74/0.99  sim_eq_tautology_del:                   4
% 2.74/0.99  sim_eq_res_simp:                        2
% 2.74/0.99  sim_fw_demodulated:                     0
% 2.74/0.99  sim_bw_demodulated:                     11
% 2.74/0.99  sim_light_normalised:                   3
% 2.74/0.99  sim_joinable_taut:                      0
% 2.74/0.99  sim_joinable_simp:                      0
% 2.74/0.99  sim_ac_normalised:                      0
% 2.74/0.99  sim_smt_subsumption:                    0
% 2.74/0.99  
%------------------------------------------------------------------------------
