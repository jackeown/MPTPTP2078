%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0426+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:16 EST 2020

% Result     : Theorem 2.41s
% Output     : CNFRefutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 791 expanded)
%              Number of clauses        :   52 ( 214 expanded)
%              Number of leaves         :   12 ( 180 expanded)
%              Depth                    :   22
%              Number of atoms          :  351 (4596 expanded)
%              Number of equality atoms :  149 (1056 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
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
    inference(ennf_transformation,[],[f1])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f9])).

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

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,k8_setfam_1(X0,X2))
      <~> ! [X3] :
            ( r2_hidden(X1,X3)
            | ~ r2_hidden(X3,X2) ) )
      & r2_hidden(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,k8_setfam_1(X0,X2))
      <~> ! [X3] :
            ( r2_hidden(X1,X3)
            | ~ r2_hidden(X3,X2) ) )
      & r2_hidden(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f14])).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f26,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( ~ r2_hidden(X1,X3)
          & r2_hidden(X3,X2) )
     => ( ~ r2_hidden(X1,sK6)
        & r2_hidden(sK6,X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
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

fof(f27,plain,
    ( ( ( ~ r2_hidden(sK4,sK6)
        & r2_hidden(sK6,sK5) )
      | ~ r2_hidden(sK4,k8_setfam_1(sK3,sK5)) )
    & ( ! [X4] :
          ( r2_hidden(sK4,X4)
          | ~ r2_hidden(X4,sK5) )
      | r2_hidden(sK4,k8_setfam_1(sK3,sK5)) )
    & r2_hidden(sK4,sK3)
    & m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK3))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f24,f26,f25])).

fof(f42,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK3))) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f2,axiom,(
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
    inference(ennf_transformation,[],[f2])).

fof(f16,plain,(
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

fof(f17,plain,(
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
    inference(rectify,[],[f16])).

fof(f20,plain,(
    ! [X5,X0] :
      ( ? [X6] :
          ( ~ r2_hidden(X5,X6)
          & r2_hidden(X6,X0) )
     => ( ~ r2_hidden(X5,sK2(X0,X5))
        & r2_hidden(sK2(X0,X5),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X2,X3)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(X2,sK1(X0,X1))
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
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

fof(f21,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f20,f19,f18])).

fof(f31,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | r2_hidden(sK2(X0,X5),X0)
      | k1_setfam_1(X0) != X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f53,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,k1_setfam_1(X0))
      | r2_hidden(sK2(X0,X5),X0)
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f31])).

fof(f44,plain,(
    ! [X4] :
      ( r2_hidden(sK4,X4)
      | ~ r2_hidden(X4,sK5)
      | r2_hidden(sK4,k8_setfam_1(sK3,sK5)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f32,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X5,sK2(X0,X5))
      | k1_setfam_1(X0) != X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f52,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,k1_setfam_1(X0))
      | ~ r2_hidden(X5,sK2(X0,X5))
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f32])).

fof(f45,plain,
    ( r2_hidden(sK6,sK5)
    | ~ r2_hidden(sK4,k8_setfam_1(sK3,sK5)) ),
    inference(cnf_transformation,[],[f27])).

fof(f30,plain,(
    ! [X0,X7,X5,X1] :
      ( r2_hidden(X5,X7)
      | ~ r2_hidden(X7,X0)
      | ~ r2_hidden(X5,X1)
      | k1_setfam_1(X0) != X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f54,plain,(
    ! [X0,X7,X5] :
      ( r2_hidden(X5,X7)
      | ~ r2_hidden(X7,X0)
      | ~ r2_hidden(X5,k1_setfam_1(X0))
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f30])).

fof(f46,plain,
    ( ~ r2_hidden(sK4,sK6)
    | ~ r2_hidden(sK4,k8_setfam_1(sK3,sK5)) ),
    inference(cnf_transformation,[],[f27])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f47,plain,(
    ! [X0] :
      ( k8_setfam_1(X0,k1_xboole_0) = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f29])).

fof(f43,plain,(
    r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f40,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k6_setfam_1(X1,X0) = k8_setfam_1(X1,X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK3))) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_229,plain,
    ( k6_setfam_1(X0,X1) = k8_setfam_1(X0,X1)
    | k1_zfmisc_1(k1_zfmisc_1(X0)) != k1_zfmisc_1(k1_zfmisc_1(sK3))
    | sK5 != X1
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_18])).

cnf(c_230,plain,
    ( k6_setfam_1(X0,sK5) = k8_setfam_1(X0,sK5)
    | k1_zfmisc_1(k1_zfmisc_1(X0)) != k1_zfmisc_1(k1_zfmisc_1(sK3))
    | k1_xboole_0 = sK5 ),
    inference(unflattening,[status(thm)],[c_229])).

cnf(c_705,plain,
    ( k6_setfam_1(sK3,sK5) = k8_setfam_1(sK3,sK5)
    | sK5 = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_230])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k6_setfam_1(X1,X0) = k1_setfam_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_220,plain,
    ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
    | k1_zfmisc_1(k1_zfmisc_1(X0)) != k1_zfmisc_1(k1_zfmisc_1(sK3))
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_18])).

cnf(c_221,plain,
    ( k6_setfam_1(X0,sK5) = k1_setfam_1(sK5)
    | k1_zfmisc_1(k1_zfmisc_1(X0)) != k1_zfmisc_1(k1_zfmisc_1(sK3)) ),
    inference(unflattening,[status(thm)],[c_220])).

cnf(c_649,plain,
    ( k6_setfam_1(sK3,sK5) = k1_setfam_1(sK5) ),
    inference(equality_resolution,[status(thm)],[c_221])).

cnf(c_1024,plain,
    ( k8_setfam_1(sK3,sK5) = k1_setfam_1(sK5)
    | sK5 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_705,c_649])).

cnf(c_8,plain,
    ( r2_hidden(X0,k1_setfam_1(X1))
    | r2_hidden(sK2(X1,X0),X1)
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_517,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(X1,k1_setfam_1(X0)) = iProver_top
    | r2_hidden(sK2(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_16,negated_conjecture,
    ( ~ r2_hidden(X0,sK5)
    | r2_hidden(sK4,X0)
    | r2_hidden(sK4,k8_setfam_1(sK3,sK5)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_513,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(sK4,X0) = iProver_top
    | r2_hidden(sK4,k8_setfam_1(sK3,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_907,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(X0,k1_setfam_1(sK5)) = iProver_top
    | r2_hidden(sK4,sK2(sK5,X0)) = iProver_top
    | r2_hidden(sK4,k8_setfam_1(sK3,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_517,c_513])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,sK2(X1,X0))
    | r2_hidden(X0,k1_setfam_1(X1))
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_518,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(X1,sK2(X0,X1)) != iProver_top
    | r2_hidden(X1,k1_setfam_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1145,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK4,k8_setfam_1(sK3,sK5)) = iProver_top
    | r2_hidden(sK4,k1_setfam_1(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_907,c_518])).

cnf(c_1182,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK4,k1_setfam_1(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1024,c_1145])).

cnf(c_15,negated_conjecture,
    ( r2_hidden(sK6,sK5)
    | ~ r2_hidden(sK4,k8_setfam_1(sK3,sK5)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_514,plain,
    ( r2_hidden(sK6,sK5) = iProver_top
    | r2_hidden(sK4,k8_setfam_1(sK3,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1028,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK6,sK5) = iProver_top
    | r2_hidden(sK4,k1_setfam_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1024,c_514])).

cnf(c_1210,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK6,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1182,c_1028])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X0)
    | ~ r2_hidden(X2,k1_setfam_1(X1))
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_516,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(X1,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top
    | r2_hidden(X2,k1_setfam_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1209,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(sK4,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1182,c_516])).

cnf(c_1798,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK4,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1210,c_1209])).

cnf(c_14,negated_conjecture,
    ( ~ r2_hidden(sK4,k8_setfam_1(sK3,sK5))
    | ~ r2_hidden(sK4,sK6) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_515,plain,
    ( r2_hidden(sK4,k8_setfam_1(sK3,sK5)) != iProver_top
    | r2_hidden(sK4,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1027,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK4,k1_setfam_1(sK5)) != iProver_top
    | r2_hidden(sK4,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1024,c_515])).

cnf(c_1211,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK4,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1182,c_1027])).

cnf(c_2660,plain,
    ( sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1798,c_1211])).

cnf(c_0,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
    | k8_setfam_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_209,plain,
    ( k8_setfam_1(X0,k1_xboole_0) = X0
    | k1_zfmisc_1(k1_zfmisc_1(X0)) != k1_zfmisc_1(k1_zfmisc_1(sK3))
    | sK5 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_18])).

cnf(c_701,plain,
    ( k8_setfam_1(sK3,k1_xboole_0) = sK3
    | sK5 != k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_209])).

cnf(c_2674,plain,
    ( k8_setfam_1(sK3,k1_xboole_0) = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2660,c_701])).

cnf(c_2703,plain,
    ( k8_setfam_1(sK3,k1_xboole_0) = sK3 ),
    inference(equality_resolution_simp,[status(thm)],[c_2674])).

cnf(c_2681,plain,
    ( r2_hidden(sK6,k1_xboole_0) = iProver_top
    | r2_hidden(sK4,k8_setfam_1(sK3,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2660,c_514])).

cnf(c_2706,plain,
    ( r2_hidden(sK6,k1_xboole_0) = iProver_top
    | r2_hidden(sK4,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2703,c_2681])).

cnf(c_17,negated_conjecture,
    ( r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_20,plain,
    ( r2_hidden(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2856,plain,
    ( r2_hidden(sK6,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2706,c_20])).

cnf(c_10,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_197,plain,
    ( ~ r2_hidden(X0,X1)
    | o_0_0_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_13])).

cnf(c_198,plain,
    ( ~ r2_hidden(X0,o_0_0_xboole_0) ),
    inference(unflattening,[status(thm)],[c_197])).

cnf(c_511,plain,
    ( r2_hidden(X0,o_0_0_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_198])).

cnf(c_12,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_192,plain,
    ( o_0_0_xboole_0 != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_12])).

cnf(c_193,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(unflattening,[status(thm)],[c_192])).

cnf(c_528,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_511,c_193])).

cnf(c_2861,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2856,c_528])).


%------------------------------------------------------------------------------
