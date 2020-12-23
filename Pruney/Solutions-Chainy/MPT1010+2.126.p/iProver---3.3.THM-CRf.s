%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:06:26 EST 2020

% Result     : Theorem 1.58s
% Output     : CNFRefutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 520 expanded)
%              Number of clauses        :   25 (  37 expanded)
%              Number of leaves         :   17 ( 161 expanded)
%              Depth                    :   19
%              Number of atoms          :  292 ( 981 expanded)
%              Number of equality atoms :  178 ( 618 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f21])).

fof(f29,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_funct_1(X3,X2) != X1
        & r2_hidden(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
   => ( k1_funct_1(sK4,sK3) != sK2
      & r2_hidden(sK3,sK1)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))))
      & v1_funct_2(sK4,sK1,k1_tarski(sK2))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( k1_funct_1(sK4,sK3) != sK2
    & r2_hidden(sK3,sK1)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))))
    & v1_funct_2(sK4,sK1,k1_tarski(sK2))
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f22,f29])).

fof(f55,plain,(
    v1_funct_2(sK4,sK1,k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f59,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f45,f46])).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f44,f59])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f43,f60])).

fof(f62,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f42,f61])).

fof(f63,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f41,f62])).

fof(f66,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f40,f63])).

fof(f81,plain,(
    v1_funct_2(sK4,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(definition_unfolding,[],[f55,f66])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f19])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f56,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2)))) ),
    inference(cnf_transformation,[],[f30])).

fof(f80,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) ),
    inference(definition_unfolding,[],[f56,f66])).

fof(f54,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f30])).

fof(f57,plain,(
    r2_hidden(sK3,sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f58,plain,(
    k1_funct_1(sK4,sK3) != sK2 ),
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f23])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK0(X0,X1,X2,X3) != X2
            & sK0(X0,X1,X2,X3) != X1
            & sK0(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
        & ( sK0(X0,X1,X2,X3) = X2
          | sK0(X0,X1,X2,X3) = X1
          | sK0(X0,X1,X2,X3) = X0
          | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK0(X0,X1,X2,X3) != X2
              & sK0(X0,X1,X2,X3) != X1
              & sK0(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
          & ( sK0(X0,X1,X2,X3) = X2
            | sK0(X0,X1,X2,X3) = X1
            | sK0(X0,X1,X2,X3) = X0
            | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).

fof(f32,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f74,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f32,f62])).

fof(f88,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f74])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
        | X0 = X1 )
      & ( X0 != X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f48,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f14,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f64,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f52,f63])).

fof(f65,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f31,f64])).

fof(f77,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ) ),
    inference(definition_unfolding,[],[f48,f65,f66,f66,f66])).

fof(f89,plain,(
    ! [X1] : k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(equality_resolution,[],[f77])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f75,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f47,f64,f66,f63,f66])).

fof(f12,axiom,(
    ! [X0,X1] : k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f12])).

fof(f78,plain,(
    ! [X0,X1] : k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f50,f65,f66,f63])).

cnf(c_17,negated_conjecture,
    ( v1_funct_2(sK4,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_151,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_16])).

cnf(c_152,plain,
    ( ~ v1_funct_2(sK4,X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(k1_funct_1(sK4,X2),X1)
    | ~ v1_funct_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_151])).

cnf(c_18,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_156,plain,
    ( r2_hidden(k1_funct_1(sK4,X2),X1)
    | ~ r2_hidden(X2,X0)
    | ~ v1_funct_2(sK4,X0,X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_152,c_18])).

cnf(c_157,plain,
    ( ~ v1_funct_2(sK4,X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(k1_funct_1(sK4,X2),X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X1 ),
    inference(renaming,[status(thm)],[c_156])).

cnf(c_184,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k1_funct_1(sK4,X0),X2)
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != X2
    | k1_zfmisc_1(k2_zfmisc_1(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK1 != X1
    | sK4 != sK4
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_157])).

cnf(c_185,plain,
    ( ~ r2_hidden(X0,sK1)
    | r2_hidden(k1_funct_1(sK4,X0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | k1_zfmisc_1(k2_zfmisc_1(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) != k1_zfmisc_1(k2_zfmisc_1(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))
    | k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(unflattening,[status(thm)],[c_184])).

cnf(c_217,plain,
    ( ~ r2_hidden(X0,sK1)
    | r2_hidden(k1_funct_1(sK4,X0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(equality_resolution_simp,[status(thm)],[c_185])).

cnf(c_446,plain,
    ( k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | r2_hidden(X0,sK1) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_217])).

cnf(c_15,negated_conjecture,
    ( r2_hidden(sK3,sK1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_14,negated_conjecture,
    ( k1_funct_1(sK4,sK3) != sK2 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_545,plain,
    ( r2_hidden(k1_funct_1(sK4,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | ~ r2_hidden(sK3,sK1)
    | k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_217])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_568,plain,
    ( ~ r2_hidden(k1_funct_1(sK4,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,X0,X1))
    | k1_funct_1(sK4,sK3) = X0
    | k1_funct_1(sK4,sK3) = X1
    | k1_funct_1(sK4,sK3) = sK2 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_570,plain,
    ( ~ r2_hidden(k1_funct_1(sK4,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | k1_funct_1(sK4,sK3) = sK2 ),
    inference(instantiation,[status(thm)],[c_568])).

cnf(c_574,plain,
    ( k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_446,c_15,c_14,c_545,c_570])).

cnf(c_10,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_8,plain,
    ( k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_11,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_512,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_11,c_8])).

cnf(c_515,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_10,c_8,c_512])).

cnf(c_657,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_574,c_515])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:02:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  % Running in FOF mode
% 1.58/0.97  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.58/0.97  
% 1.58/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.58/0.97  
% 1.58/0.97  ------  iProver source info
% 1.58/0.97  
% 1.58/0.97  git: date: 2020-06-30 10:37:57 +0100
% 1.58/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.58/0.97  git: non_committed_changes: false
% 1.58/0.97  git: last_make_outside_of_git: false
% 1.58/0.97  
% 1.58/0.97  ------ 
% 1.58/0.97  
% 1.58/0.97  ------ Input Options
% 1.58/0.97  
% 1.58/0.97  --out_options                           all
% 1.58/0.97  --tptp_safe_out                         true
% 1.58/0.97  --problem_path                          ""
% 1.58/0.97  --include_path                          ""
% 1.58/0.97  --clausifier                            res/vclausify_rel
% 1.58/0.97  --clausifier_options                    --mode clausify
% 1.58/0.97  --stdin                                 false
% 1.58/0.97  --stats_out                             all
% 1.58/0.97  
% 1.58/0.97  ------ General Options
% 1.58/0.97  
% 1.58/0.97  --fof                                   false
% 1.58/0.97  --time_out_real                         305.
% 1.58/0.97  --time_out_virtual                      -1.
% 1.58/0.97  --symbol_type_check                     false
% 1.58/0.97  --clausify_out                          false
% 1.58/0.97  --sig_cnt_out                           false
% 1.58/0.97  --trig_cnt_out                          false
% 1.58/0.97  --trig_cnt_out_tolerance                1.
% 1.58/0.97  --trig_cnt_out_sk_spl                   false
% 1.58/0.97  --abstr_cl_out                          false
% 1.58/0.97  
% 1.58/0.97  ------ Global Options
% 1.58/0.97  
% 1.58/0.97  --schedule                              default
% 1.58/0.97  --add_important_lit                     false
% 1.58/0.97  --prop_solver_per_cl                    1000
% 1.58/0.97  --min_unsat_core                        false
% 1.58/0.97  --soft_assumptions                      false
% 1.58/0.97  --soft_lemma_size                       3
% 1.58/0.97  --prop_impl_unit_size                   0
% 1.58/0.97  --prop_impl_unit                        []
% 1.58/0.97  --share_sel_clauses                     true
% 1.58/0.97  --reset_solvers                         false
% 1.58/0.97  --bc_imp_inh                            [conj_cone]
% 1.58/0.97  --conj_cone_tolerance                   3.
% 1.58/0.97  --extra_neg_conj                        none
% 1.58/0.97  --large_theory_mode                     true
% 1.58/0.97  --prolific_symb_bound                   200
% 1.58/0.97  --lt_threshold                          2000
% 1.58/0.97  --clause_weak_htbl                      true
% 1.58/0.97  --gc_record_bc_elim                     false
% 1.58/0.97  
% 1.58/0.97  ------ Preprocessing Options
% 1.58/0.97  
% 1.58/0.97  --preprocessing_flag                    true
% 1.58/0.97  --time_out_prep_mult                    0.1
% 1.58/0.97  --splitting_mode                        input
% 1.58/0.97  --splitting_grd                         true
% 1.58/0.97  --splitting_cvd                         false
% 1.58/0.97  --splitting_cvd_svl                     false
% 1.58/0.97  --splitting_nvd                         32
% 1.58/0.97  --sub_typing                            true
% 1.58/0.97  --prep_gs_sim                           true
% 1.58/0.97  --prep_unflatten                        true
% 1.58/0.97  --prep_res_sim                          true
% 1.58/0.97  --prep_upred                            true
% 1.58/0.97  --prep_sem_filter                       exhaustive
% 1.58/0.97  --prep_sem_filter_out                   false
% 1.58/0.97  --pred_elim                             true
% 1.58/0.97  --res_sim_input                         true
% 1.58/0.97  --eq_ax_congr_red                       true
% 1.58/0.97  --pure_diseq_elim                       true
% 1.58/0.97  --brand_transform                       false
% 1.58/0.97  --non_eq_to_eq                          false
% 1.58/0.97  --prep_def_merge                        true
% 1.58/0.97  --prep_def_merge_prop_impl              false
% 1.58/0.97  --prep_def_merge_mbd                    true
% 1.58/0.97  --prep_def_merge_tr_red                 false
% 1.58/0.97  --prep_def_merge_tr_cl                  false
% 1.58/0.97  --smt_preprocessing                     true
% 1.58/0.97  --smt_ac_axioms                         fast
% 1.58/0.97  --preprocessed_out                      false
% 1.58/0.97  --preprocessed_stats                    false
% 1.58/0.97  
% 1.58/0.97  ------ Abstraction refinement Options
% 1.58/0.97  
% 1.58/0.97  --abstr_ref                             []
% 1.58/0.97  --abstr_ref_prep                        false
% 1.58/0.97  --abstr_ref_until_sat                   false
% 1.58/0.97  --abstr_ref_sig_restrict                funpre
% 1.58/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 1.58/0.97  --abstr_ref_under                       []
% 1.58/0.97  
% 1.58/0.97  ------ SAT Options
% 1.58/0.97  
% 1.58/0.97  --sat_mode                              false
% 1.58/0.97  --sat_fm_restart_options                ""
% 1.58/0.97  --sat_gr_def                            false
% 1.58/0.97  --sat_epr_types                         true
% 1.58/0.97  --sat_non_cyclic_types                  false
% 1.58/0.97  --sat_finite_models                     false
% 1.58/0.97  --sat_fm_lemmas                         false
% 1.58/0.97  --sat_fm_prep                           false
% 1.58/0.97  --sat_fm_uc_incr                        true
% 1.58/0.97  --sat_out_model                         small
% 1.58/0.97  --sat_out_clauses                       false
% 1.58/0.97  
% 1.58/0.97  ------ QBF Options
% 1.58/0.97  
% 1.58/0.97  --qbf_mode                              false
% 1.58/0.97  --qbf_elim_univ                         false
% 1.58/0.97  --qbf_dom_inst                          none
% 1.58/0.97  --qbf_dom_pre_inst                      false
% 1.58/0.97  --qbf_sk_in                             false
% 1.58/0.97  --qbf_pred_elim                         true
% 1.58/0.97  --qbf_split                             512
% 1.58/0.97  
% 1.58/0.97  ------ BMC1 Options
% 1.58/0.97  
% 1.58/0.97  --bmc1_incremental                      false
% 1.58/0.97  --bmc1_axioms                           reachable_all
% 1.58/0.97  --bmc1_min_bound                        0
% 1.58/0.97  --bmc1_max_bound                        -1
% 1.58/0.97  --bmc1_max_bound_default                -1
% 1.58/0.97  --bmc1_symbol_reachability              true
% 1.58/0.97  --bmc1_property_lemmas                  false
% 1.58/0.97  --bmc1_k_induction                      false
% 1.58/0.97  --bmc1_non_equiv_states                 false
% 1.58/0.97  --bmc1_deadlock                         false
% 1.58/0.97  --bmc1_ucm                              false
% 1.58/0.97  --bmc1_add_unsat_core                   none
% 1.58/0.97  --bmc1_unsat_core_children              false
% 1.58/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 1.58/0.97  --bmc1_out_stat                         full
% 1.58/0.97  --bmc1_ground_init                      false
% 1.58/0.97  --bmc1_pre_inst_next_state              false
% 1.58/0.97  --bmc1_pre_inst_state                   false
% 1.58/0.97  --bmc1_pre_inst_reach_state             false
% 1.58/0.97  --bmc1_out_unsat_core                   false
% 1.58/0.97  --bmc1_aig_witness_out                  false
% 1.58/0.97  --bmc1_verbose                          false
% 1.58/0.97  --bmc1_dump_clauses_tptp                false
% 1.58/0.97  --bmc1_dump_unsat_core_tptp             false
% 1.58/0.97  --bmc1_dump_file                        -
% 1.58/0.97  --bmc1_ucm_expand_uc_limit              128
% 1.58/0.97  --bmc1_ucm_n_expand_iterations          6
% 1.58/0.97  --bmc1_ucm_extend_mode                  1
% 1.58/0.97  --bmc1_ucm_init_mode                    2
% 1.58/0.97  --bmc1_ucm_cone_mode                    none
% 1.58/0.97  --bmc1_ucm_reduced_relation_type        0
% 1.58/0.97  --bmc1_ucm_relax_model                  4
% 1.58/0.97  --bmc1_ucm_full_tr_after_sat            true
% 1.58/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 1.58/0.97  --bmc1_ucm_layered_model                none
% 1.58/0.97  --bmc1_ucm_max_lemma_size               10
% 1.58/0.97  
% 1.58/0.97  ------ AIG Options
% 1.58/0.97  
% 1.58/0.97  --aig_mode                              false
% 1.58/0.97  
% 1.58/0.97  ------ Instantiation Options
% 1.58/0.97  
% 1.58/0.97  --instantiation_flag                    true
% 1.58/0.97  --inst_sos_flag                         false
% 1.58/0.97  --inst_sos_phase                        true
% 1.58/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.58/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.58/0.97  --inst_lit_sel_side                     num_symb
% 1.58/0.97  --inst_solver_per_active                1400
% 1.58/0.97  --inst_solver_calls_frac                1.
% 1.58/0.97  --inst_passive_queue_type               priority_queues
% 1.58/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.58/0.97  --inst_passive_queues_freq              [25;2]
% 1.58/0.97  --inst_dismatching                      true
% 1.58/0.97  --inst_eager_unprocessed_to_passive     true
% 1.58/0.97  --inst_prop_sim_given                   true
% 1.58/0.97  --inst_prop_sim_new                     false
% 1.58/0.97  --inst_subs_new                         false
% 1.58/0.97  --inst_eq_res_simp                      false
% 1.58/0.97  --inst_subs_given                       false
% 1.58/0.97  --inst_orphan_elimination               true
% 1.58/0.97  --inst_learning_loop_flag               true
% 1.58/0.97  --inst_learning_start                   3000
% 1.58/0.97  --inst_learning_factor                  2
% 1.58/0.97  --inst_start_prop_sim_after_learn       3
% 1.58/0.97  --inst_sel_renew                        solver
% 1.58/0.97  --inst_lit_activity_flag                true
% 1.58/0.97  --inst_restr_to_given                   false
% 1.58/0.97  --inst_activity_threshold               500
% 1.58/0.97  --inst_out_proof                        true
% 1.58/0.97  
% 1.58/0.97  ------ Resolution Options
% 1.58/0.97  
% 1.58/0.97  --resolution_flag                       true
% 1.58/0.97  --res_lit_sel                           adaptive
% 1.58/0.97  --res_lit_sel_side                      none
% 1.58/0.97  --res_ordering                          kbo
% 1.58/0.97  --res_to_prop_solver                    active
% 1.58/0.97  --res_prop_simpl_new                    false
% 1.58/0.97  --res_prop_simpl_given                  true
% 1.58/0.97  --res_passive_queue_type                priority_queues
% 1.58/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.58/0.97  --res_passive_queues_freq               [15;5]
% 1.58/0.97  --res_forward_subs                      full
% 1.58/0.97  --res_backward_subs                     full
% 1.58/0.97  --res_forward_subs_resolution           true
% 1.58/0.97  --res_backward_subs_resolution          true
% 1.58/0.97  --res_orphan_elimination                true
% 1.58/0.97  --res_time_limit                        2.
% 1.58/0.97  --res_out_proof                         true
% 1.58/0.97  
% 1.58/0.97  ------ Superposition Options
% 1.58/0.97  
% 1.58/0.97  --superposition_flag                    true
% 1.58/0.97  --sup_passive_queue_type                priority_queues
% 1.58/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.58/0.97  --sup_passive_queues_freq               [8;1;4]
% 1.58/0.97  --demod_completeness_check              fast
% 1.58/0.97  --demod_use_ground                      true
% 1.58/0.97  --sup_to_prop_solver                    passive
% 1.58/0.97  --sup_prop_simpl_new                    true
% 1.58/0.97  --sup_prop_simpl_given                  true
% 1.58/0.97  --sup_fun_splitting                     false
% 1.58/0.97  --sup_smt_interval                      50000
% 1.58/0.97  
% 1.58/0.97  ------ Superposition Simplification Setup
% 1.58/0.97  
% 1.58/0.97  --sup_indices_passive                   []
% 1.58/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.58/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.58/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.58/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 1.58/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.58/0.97  --sup_full_bw                           [BwDemod]
% 1.58/0.97  --sup_immed_triv                        [TrivRules]
% 1.58/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.58/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.58/0.97  --sup_immed_bw_main                     []
% 1.58/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.58/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 1.58/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.58/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.58/0.97  
% 1.58/0.97  ------ Combination Options
% 1.58/0.97  
% 1.58/0.97  --comb_res_mult                         3
% 1.58/0.97  --comb_sup_mult                         2
% 1.58/0.97  --comb_inst_mult                        10
% 1.58/0.97  
% 1.58/0.97  ------ Debug Options
% 1.58/0.97  
% 1.58/0.97  --dbg_backtrace                         false
% 1.58/0.97  --dbg_dump_prop_clauses                 false
% 1.58/0.97  --dbg_dump_prop_clauses_file            -
% 1.58/0.97  --dbg_out_stat                          false
% 1.58/0.97  ------ Parsing...
% 1.58/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.58/0.97  
% 1.58/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 1.58/0.97  
% 1.58/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.58/0.97  
% 1.58/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.58/0.97  ------ Proving...
% 1.58/0.97  ------ Problem Properties 
% 1.58/0.97  
% 1.58/0.97  
% 1.58/0.97  clauses                                 16
% 1.58/0.97  conjectures                             2
% 1.58/0.97  EPR                                     1
% 1.58/0.97  Horn                                    12
% 1.58/0.97  unary                                   9
% 1.58/0.97  binary                                  1
% 1.58/0.97  lits                                    32
% 1.58/0.97  lits eq                                 21
% 1.58/0.97  fd_pure                                 0
% 1.58/0.97  fd_pseudo                               0
% 1.58/0.97  fd_cond                                 0
% 1.58/0.97  fd_pseudo_cond                          5
% 1.58/0.97  AC symbols                              0
% 1.58/0.97  
% 1.58/0.97  ------ Schedule dynamic 5 is on 
% 1.58/0.97  
% 1.58/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.58/0.97  
% 1.58/0.97  
% 1.58/0.97  ------ 
% 1.58/0.97  Current options:
% 1.58/0.97  ------ 
% 1.58/0.97  
% 1.58/0.97  ------ Input Options
% 1.58/0.97  
% 1.58/0.97  --out_options                           all
% 1.58/0.97  --tptp_safe_out                         true
% 1.58/0.97  --problem_path                          ""
% 1.58/0.97  --include_path                          ""
% 1.58/0.97  --clausifier                            res/vclausify_rel
% 1.58/0.97  --clausifier_options                    --mode clausify
% 1.58/0.97  --stdin                                 false
% 1.58/0.97  --stats_out                             all
% 1.58/0.97  
% 1.58/0.97  ------ General Options
% 1.58/0.97  
% 1.58/0.97  --fof                                   false
% 1.58/0.97  --time_out_real                         305.
% 1.58/0.97  --time_out_virtual                      -1.
% 1.58/0.97  --symbol_type_check                     false
% 1.58/0.97  --clausify_out                          false
% 1.58/0.97  --sig_cnt_out                           false
% 1.58/0.97  --trig_cnt_out                          false
% 1.58/0.97  --trig_cnt_out_tolerance                1.
% 1.58/0.97  --trig_cnt_out_sk_spl                   false
% 1.58/0.97  --abstr_cl_out                          false
% 1.58/0.97  
% 1.58/0.97  ------ Global Options
% 1.58/0.97  
% 1.58/0.97  --schedule                              default
% 1.58/0.97  --add_important_lit                     false
% 1.58/0.97  --prop_solver_per_cl                    1000
% 1.58/0.97  --min_unsat_core                        false
% 1.58/0.97  --soft_assumptions                      false
% 1.58/0.97  --soft_lemma_size                       3
% 1.58/0.97  --prop_impl_unit_size                   0
% 1.58/0.97  --prop_impl_unit                        []
% 1.58/0.97  --share_sel_clauses                     true
% 1.58/0.97  --reset_solvers                         false
% 1.58/0.97  --bc_imp_inh                            [conj_cone]
% 1.58/0.97  --conj_cone_tolerance                   3.
% 1.58/0.97  --extra_neg_conj                        none
% 1.58/0.97  --large_theory_mode                     true
% 1.58/0.97  --prolific_symb_bound                   200
% 1.58/0.97  --lt_threshold                          2000
% 1.58/0.97  --clause_weak_htbl                      true
% 1.58/0.97  --gc_record_bc_elim                     false
% 1.58/0.97  
% 1.58/0.97  ------ Preprocessing Options
% 1.58/0.97  
% 1.58/0.97  --preprocessing_flag                    true
% 1.58/0.97  --time_out_prep_mult                    0.1
% 1.58/0.97  --splitting_mode                        input
% 1.58/0.97  --splitting_grd                         true
% 1.58/0.97  --splitting_cvd                         false
% 1.58/0.97  --splitting_cvd_svl                     false
% 1.58/0.97  --splitting_nvd                         32
% 1.58/0.97  --sub_typing                            true
% 1.58/0.97  --prep_gs_sim                           true
% 1.58/0.97  --prep_unflatten                        true
% 1.58/0.97  --prep_res_sim                          true
% 1.58/0.97  --prep_upred                            true
% 1.58/0.97  --prep_sem_filter                       exhaustive
% 1.58/0.97  --prep_sem_filter_out                   false
% 1.58/0.97  --pred_elim                             true
% 1.58/0.97  --res_sim_input                         true
% 1.58/0.97  --eq_ax_congr_red                       true
% 1.58/0.97  --pure_diseq_elim                       true
% 1.58/0.97  --brand_transform                       false
% 1.58/0.97  --non_eq_to_eq                          false
% 1.58/0.97  --prep_def_merge                        true
% 1.58/0.97  --prep_def_merge_prop_impl              false
% 1.58/0.97  --prep_def_merge_mbd                    true
% 1.58/0.97  --prep_def_merge_tr_red                 false
% 1.58/0.97  --prep_def_merge_tr_cl                  false
% 1.58/0.97  --smt_preprocessing                     true
% 1.58/0.97  --smt_ac_axioms                         fast
% 1.58/0.97  --preprocessed_out                      false
% 1.58/0.97  --preprocessed_stats                    false
% 1.58/0.97  
% 1.58/0.97  ------ Abstraction refinement Options
% 1.58/0.97  
% 1.58/0.97  --abstr_ref                             []
% 1.58/0.97  --abstr_ref_prep                        false
% 1.58/0.97  --abstr_ref_until_sat                   false
% 1.58/0.97  --abstr_ref_sig_restrict                funpre
% 1.58/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 1.58/0.97  --abstr_ref_under                       []
% 1.58/0.97  
% 1.58/0.97  ------ SAT Options
% 1.58/0.97  
% 1.58/0.97  --sat_mode                              false
% 1.58/0.97  --sat_fm_restart_options                ""
% 1.58/0.97  --sat_gr_def                            false
% 1.58/0.97  --sat_epr_types                         true
% 1.58/0.97  --sat_non_cyclic_types                  false
% 1.58/0.97  --sat_finite_models                     false
% 1.58/0.97  --sat_fm_lemmas                         false
% 1.58/0.97  --sat_fm_prep                           false
% 1.58/0.97  --sat_fm_uc_incr                        true
% 1.58/0.97  --sat_out_model                         small
% 1.58/0.97  --sat_out_clauses                       false
% 1.58/0.97  
% 1.58/0.97  ------ QBF Options
% 1.58/0.97  
% 1.58/0.97  --qbf_mode                              false
% 1.58/0.97  --qbf_elim_univ                         false
% 1.58/0.97  --qbf_dom_inst                          none
% 1.58/0.97  --qbf_dom_pre_inst                      false
% 1.58/0.97  --qbf_sk_in                             false
% 1.58/0.97  --qbf_pred_elim                         true
% 1.58/0.97  --qbf_split                             512
% 1.58/0.97  
% 1.58/0.97  ------ BMC1 Options
% 1.58/0.97  
% 1.58/0.97  --bmc1_incremental                      false
% 1.58/0.97  --bmc1_axioms                           reachable_all
% 1.58/0.97  --bmc1_min_bound                        0
% 1.58/0.97  --bmc1_max_bound                        -1
% 1.58/0.97  --bmc1_max_bound_default                -1
% 1.58/0.97  --bmc1_symbol_reachability              true
% 1.58/0.97  --bmc1_property_lemmas                  false
% 1.58/0.97  --bmc1_k_induction                      false
% 1.58/0.97  --bmc1_non_equiv_states                 false
% 1.58/0.97  --bmc1_deadlock                         false
% 1.58/0.97  --bmc1_ucm                              false
% 1.58/0.97  --bmc1_add_unsat_core                   none
% 1.58/0.97  --bmc1_unsat_core_children              false
% 1.58/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 1.58/0.97  --bmc1_out_stat                         full
% 1.58/0.97  --bmc1_ground_init                      false
% 1.58/0.97  --bmc1_pre_inst_next_state              false
% 1.58/0.97  --bmc1_pre_inst_state                   false
% 1.58/0.97  --bmc1_pre_inst_reach_state             false
% 1.58/0.97  --bmc1_out_unsat_core                   false
% 1.58/0.97  --bmc1_aig_witness_out                  false
% 1.58/0.97  --bmc1_verbose                          false
% 1.58/0.97  --bmc1_dump_clauses_tptp                false
% 1.58/0.97  --bmc1_dump_unsat_core_tptp             false
% 1.58/0.97  --bmc1_dump_file                        -
% 1.58/0.97  --bmc1_ucm_expand_uc_limit              128
% 1.58/0.97  --bmc1_ucm_n_expand_iterations          6
% 1.58/0.97  --bmc1_ucm_extend_mode                  1
% 1.58/0.97  --bmc1_ucm_init_mode                    2
% 1.58/0.97  --bmc1_ucm_cone_mode                    none
% 1.58/0.97  --bmc1_ucm_reduced_relation_type        0
% 1.58/0.97  --bmc1_ucm_relax_model                  4
% 1.58/0.97  --bmc1_ucm_full_tr_after_sat            true
% 1.58/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 1.58/0.97  --bmc1_ucm_layered_model                none
% 1.58/0.97  --bmc1_ucm_max_lemma_size               10
% 1.58/0.97  
% 1.58/0.97  ------ AIG Options
% 1.58/0.97  
% 1.58/0.97  --aig_mode                              false
% 1.58/0.97  
% 1.58/0.97  ------ Instantiation Options
% 1.58/0.97  
% 1.58/0.97  --instantiation_flag                    true
% 1.58/0.97  --inst_sos_flag                         false
% 1.58/0.97  --inst_sos_phase                        true
% 1.58/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.58/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.58/0.97  --inst_lit_sel_side                     none
% 1.58/0.97  --inst_solver_per_active                1400
% 1.58/0.97  --inst_solver_calls_frac                1.
% 1.58/0.97  --inst_passive_queue_type               priority_queues
% 1.58/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.58/0.97  --inst_passive_queues_freq              [25;2]
% 1.58/0.97  --inst_dismatching                      true
% 1.58/0.97  --inst_eager_unprocessed_to_passive     true
% 1.58/0.97  --inst_prop_sim_given                   true
% 1.58/0.97  --inst_prop_sim_new                     false
% 1.58/0.97  --inst_subs_new                         false
% 1.58/0.97  --inst_eq_res_simp                      false
% 1.58/0.97  --inst_subs_given                       false
% 1.58/0.97  --inst_orphan_elimination               true
% 1.58/0.97  --inst_learning_loop_flag               true
% 1.58/0.97  --inst_learning_start                   3000
% 1.58/0.97  --inst_learning_factor                  2
% 1.58/0.97  --inst_start_prop_sim_after_learn       3
% 1.58/0.97  --inst_sel_renew                        solver
% 1.58/0.97  --inst_lit_activity_flag                true
% 1.58/0.97  --inst_restr_to_given                   false
% 1.58/0.97  --inst_activity_threshold               500
% 1.58/0.97  --inst_out_proof                        true
% 1.58/0.97  
% 1.58/0.97  ------ Resolution Options
% 1.58/0.97  
% 1.58/0.97  --resolution_flag                       false
% 1.58/0.97  --res_lit_sel                           adaptive
% 1.58/0.97  --res_lit_sel_side                      none
% 1.58/0.97  --res_ordering                          kbo
% 1.58/0.97  --res_to_prop_solver                    active
% 1.58/0.97  --res_prop_simpl_new                    false
% 1.58/0.97  --res_prop_simpl_given                  true
% 1.58/0.97  --res_passive_queue_type                priority_queues
% 1.58/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.58/0.97  --res_passive_queues_freq               [15;5]
% 1.58/0.97  --res_forward_subs                      full
% 1.58/0.97  --res_backward_subs                     full
% 1.58/0.97  --res_forward_subs_resolution           true
% 1.58/0.97  --res_backward_subs_resolution          true
% 1.58/0.97  --res_orphan_elimination                true
% 1.58/0.97  --res_time_limit                        2.
% 1.58/0.97  --res_out_proof                         true
% 1.58/0.97  
% 1.58/0.97  ------ Superposition Options
% 1.58/0.97  
% 1.58/0.97  --superposition_flag                    true
% 1.58/0.97  --sup_passive_queue_type                priority_queues
% 1.58/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.58/0.97  --sup_passive_queues_freq               [8;1;4]
% 1.58/0.97  --demod_completeness_check              fast
% 1.58/0.97  --demod_use_ground                      true
% 1.58/0.97  --sup_to_prop_solver                    passive
% 1.58/0.97  --sup_prop_simpl_new                    true
% 1.58/0.97  --sup_prop_simpl_given                  true
% 1.58/0.97  --sup_fun_splitting                     false
% 1.58/0.97  --sup_smt_interval                      50000
% 1.58/0.97  
% 1.58/0.97  ------ Superposition Simplification Setup
% 1.58/0.97  
% 1.58/0.97  --sup_indices_passive                   []
% 1.58/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.58/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.58/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.58/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 1.58/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.58/0.97  --sup_full_bw                           [BwDemod]
% 1.58/0.97  --sup_immed_triv                        [TrivRules]
% 1.58/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.58/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.58/0.97  --sup_immed_bw_main                     []
% 1.58/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.58/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 1.58/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.58/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.58/0.97  
% 1.58/0.97  ------ Combination Options
% 1.58/0.97  
% 1.58/0.97  --comb_res_mult                         3
% 1.58/0.97  --comb_sup_mult                         2
% 1.58/0.97  --comb_inst_mult                        10
% 1.58/0.97  
% 1.58/0.97  ------ Debug Options
% 1.58/0.97  
% 1.58/0.97  --dbg_backtrace                         false
% 1.58/0.97  --dbg_dump_prop_clauses                 false
% 1.58/0.97  --dbg_dump_prop_clauses_file            -
% 1.58/0.97  --dbg_out_stat                          false
% 1.58/0.97  
% 1.58/0.97  
% 1.58/0.97  
% 1.58/0.97  
% 1.58/0.97  ------ Proving...
% 1.58/0.97  
% 1.58/0.97  
% 1.58/0.97  % SZS status Theorem for theBenchmark.p
% 1.58/0.97  
% 1.58/0.97   Resolution empty clause
% 1.58/0.97  
% 1.58/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 1.58/0.97  
% 1.58/0.97  fof(f16,conjecture,(
% 1.58/0.97    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 1.58/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.58/0.97  
% 1.58/0.97  fof(f17,negated_conjecture,(
% 1.58/0.97    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 1.58/0.97    inference(negated_conjecture,[],[f16])).
% 1.58/0.97  
% 1.58/0.97  fof(f21,plain,(
% 1.58/0.97    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 1.58/0.97    inference(ennf_transformation,[],[f17])).
% 1.58/0.97  
% 1.58/0.97  fof(f22,plain,(
% 1.58/0.97    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 1.58/0.97    inference(flattening,[],[f21])).
% 1.58/0.97  
% 1.58/0.97  fof(f29,plain,(
% 1.58/0.97    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (k1_funct_1(sK4,sK3) != sK2 & r2_hidden(sK3,sK1) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2)))) & v1_funct_2(sK4,sK1,k1_tarski(sK2)) & v1_funct_1(sK4))),
% 1.58/0.97    introduced(choice_axiom,[])).
% 1.58/0.97  
% 1.58/0.97  fof(f30,plain,(
% 1.58/0.97    k1_funct_1(sK4,sK3) != sK2 & r2_hidden(sK3,sK1) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2)))) & v1_funct_2(sK4,sK1,k1_tarski(sK2)) & v1_funct_1(sK4)),
% 1.58/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f22,f29])).
% 1.58/0.97  
% 1.58/0.97  fof(f55,plain,(
% 1.58/0.97    v1_funct_2(sK4,sK1,k1_tarski(sK2))),
% 1.58/0.97    inference(cnf_transformation,[],[f30])).
% 1.58/0.97  
% 1.58/0.97  fof(f3,axiom,(
% 1.58/0.97    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.58/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.58/0.97  
% 1.58/0.97  fof(f40,plain,(
% 1.58/0.97    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.58/0.97    inference(cnf_transformation,[],[f3])).
% 1.58/0.97  
% 1.58/0.97  fof(f4,axiom,(
% 1.58/0.97    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.58/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.58/0.97  
% 1.58/0.97  fof(f41,plain,(
% 1.58/0.97    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.58/0.97    inference(cnf_transformation,[],[f4])).
% 1.58/0.97  
% 1.58/0.97  fof(f5,axiom,(
% 1.58/0.97    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.58/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.58/0.97  
% 1.58/0.97  fof(f42,plain,(
% 1.58/0.97    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.58/0.97    inference(cnf_transformation,[],[f5])).
% 1.58/0.97  
% 1.58/0.97  fof(f6,axiom,(
% 1.58/0.97    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 1.58/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.58/0.97  
% 1.58/0.97  fof(f43,plain,(
% 1.58/0.97    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 1.58/0.97    inference(cnf_transformation,[],[f6])).
% 1.58/0.97  
% 1.58/0.97  fof(f7,axiom,(
% 1.58/0.97    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 1.58/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.58/0.97  
% 1.58/0.97  fof(f44,plain,(
% 1.58/0.97    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 1.58/0.97    inference(cnf_transformation,[],[f7])).
% 1.58/0.97  
% 1.58/0.97  fof(f8,axiom,(
% 1.58/0.97    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 1.58/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.58/0.97  
% 1.58/0.97  fof(f45,plain,(
% 1.58/0.97    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 1.58/0.97    inference(cnf_transformation,[],[f8])).
% 1.58/0.97  
% 1.58/0.97  fof(f9,axiom,(
% 1.58/0.97    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 1.58/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.58/0.97  
% 1.58/0.97  fof(f46,plain,(
% 1.58/0.97    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 1.58/0.97    inference(cnf_transformation,[],[f9])).
% 1.58/0.97  
% 1.58/0.97  fof(f59,plain,(
% 1.58/0.97    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.58/0.97    inference(definition_unfolding,[],[f45,f46])).
% 1.58/0.97  
% 1.58/0.97  fof(f60,plain,(
% 1.58/0.97    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.58/0.97    inference(definition_unfolding,[],[f44,f59])).
% 1.58/0.97  
% 1.58/0.97  fof(f61,plain,(
% 1.58/0.97    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.58/0.97    inference(definition_unfolding,[],[f43,f60])).
% 1.58/0.97  
% 1.58/0.97  fof(f62,plain,(
% 1.58/0.97    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.58/0.97    inference(definition_unfolding,[],[f42,f61])).
% 1.58/0.97  
% 1.58/0.97  fof(f63,plain,(
% 1.58/0.97    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.58/0.97    inference(definition_unfolding,[],[f41,f62])).
% 1.58/0.97  
% 1.58/0.97  fof(f66,plain,(
% 1.58/0.97    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.58/0.97    inference(definition_unfolding,[],[f40,f63])).
% 1.58/0.97  
% 1.58/0.97  fof(f81,plain,(
% 1.58/0.97    v1_funct_2(sK4,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),
% 1.58/0.97    inference(definition_unfolding,[],[f55,f66])).
% 1.58/0.97  
% 1.58/0.97  fof(f15,axiom,(
% 1.58/0.97    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 1.58/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.58/0.97  
% 1.58/0.97  fof(f19,plain,(
% 1.58/0.97    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.58/0.97    inference(ennf_transformation,[],[f15])).
% 1.58/0.97  
% 1.58/0.97  fof(f20,plain,(
% 1.58/0.97    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.58/0.97    inference(flattening,[],[f19])).
% 1.58/0.97  
% 1.58/0.97  fof(f53,plain,(
% 1.58/0.97    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.58/0.97    inference(cnf_transformation,[],[f20])).
% 1.58/0.97  
% 1.58/0.97  fof(f56,plain,(
% 1.58/0.97    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))))),
% 1.58/0.97    inference(cnf_transformation,[],[f30])).
% 1.58/0.97  
% 1.58/0.97  fof(f80,plain,(
% 1.58/0.97    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))),
% 1.58/0.97    inference(definition_unfolding,[],[f56,f66])).
% 1.58/0.97  
% 1.58/0.97  fof(f54,plain,(
% 1.58/0.97    v1_funct_1(sK4)),
% 1.58/0.97    inference(cnf_transformation,[],[f30])).
% 1.58/0.97  
% 1.58/0.97  fof(f57,plain,(
% 1.58/0.97    r2_hidden(sK3,sK1)),
% 1.58/0.97    inference(cnf_transformation,[],[f30])).
% 1.58/0.97  
% 1.58/0.97  fof(f58,plain,(
% 1.58/0.97    k1_funct_1(sK4,sK3) != sK2),
% 1.58/0.97    inference(cnf_transformation,[],[f30])).
% 1.58/0.97  
% 1.58/0.97  fof(f2,axiom,(
% 1.58/0.97    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.58/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.58/0.97  
% 1.58/0.97  fof(f18,plain,(
% 1.58/0.97    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.58/0.97    inference(ennf_transformation,[],[f2])).
% 1.58/0.97  
% 1.58/0.97  fof(f23,plain,(
% 1.58/0.97    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.58/0.97    inference(nnf_transformation,[],[f18])).
% 1.58/0.97  
% 1.58/0.97  fof(f24,plain,(
% 1.58/0.97    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.58/0.97    inference(flattening,[],[f23])).
% 1.58/0.97  
% 1.58/0.97  fof(f25,plain,(
% 1.58/0.97    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.58/0.97    inference(rectify,[],[f24])).
% 1.58/0.97  
% 1.58/0.97  fof(f26,plain,(
% 1.58/0.97    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3))))),
% 1.58/0.97    introduced(choice_axiom,[])).
% 1.58/0.97  
% 1.58/0.97  fof(f27,plain,(
% 1.58/0.97    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.58/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).
% 1.58/0.97  
% 1.58/0.97  fof(f32,plain,(
% 1.58/0.97    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.58/0.97    inference(cnf_transformation,[],[f27])).
% 1.58/0.97  
% 1.58/0.97  fof(f74,plain,(
% 1.58/0.97    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 1.58/0.97    inference(definition_unfolding,[],[f32,f62])).
% 1.58/0.97  
% 1.58/0.97  fof(f88,plain,(
% 1.58/0.97    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))) )),
% 1.58/0.97    inference(equality_resolution,[],[f74])).
% 1.58/0.97  
% 1.58/0.97  fof(f11,axiom,(
% 1.58/0.97    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 1.58/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.58/0.97  
% 1.58/0.97  fof(f28,plain,(
% 1.58/0.97    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)))),
% 1.58/0.97    inference(nnf_transformation,[],[f11])).
% 1.58/0.97  
% 1.58/0.97  fof(f48,plain,(
% 1.58/0.97    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) )),
% 1.58/0.97    inference(cnf_transformation,[],[f28])).
% 1.58/0.97  
% 1.58/0.97  fof(f1,axiom,(
% 1.58/0.97    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.58/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.58/0.97  
% 1.58/0.97  fof(f31,plain,(
% 1.58/0.97    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.58/0.97    inference(cnf_transformation,[],[f1])).
% 1.58/0.97  
% 1.58/0.97  fof(f14,axiom,(
% 1.58/0.97    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.58/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.58/0.97  
% 1.58/0.97  fof(f52,plain,(
% 1.58/0.97    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.58/0.97    inference(cnf_transformation,[],[f14])).
% 1.58/0.97  
% 1.58/0.97  fof(f64,plain,(
% 1.58/0.97    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.58/0.97    inference(definition_unfolding,[],[f52,f63])).
% 1.58/0.97  
% 1.58/0.97  fof(f65,plain,(
% 1.58/0.97    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.58/0.97    inference(definition_unfolding,[],[f31,f64])).
% 1.58/0.97  
% 1.58/0.97  fof(f77,plain,(
% 1.58/0.97    ( ! [X0,X1] : (X0 != X1 | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.58/0.97    inference(definition_unfolding,[],[f48,f65,f66,f66,f66])).
% 1.58/0.97  
% 1.58/0.97  fof(f89,plain,(
% 1.58/0.97    ( ! [X1] : (k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) )),
% 1.58/0.97    inference(equality_resolution,[],[f77])).
% 1.58/0.97  
% 1.58/0.97  fof(f10,axiom,(
% 1.58/0.97    ! [X0,X1] : k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k1_tarski(X0)),
% 1.58/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.58/0.97  
% 1.58/0.97  fof(f47,plain,(
% 1.58/0.97    ( ! [X0,X1] : (k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k1_tarski(X0)) )),
% 1.58/0.97    inference(cnf_transformation,[],[f10])).
% 1.58/0.97  
% 1.58/0.97  fof(f75,plain,(
% 1.58/0.97    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.58/0.97    inference(definition_unfolding,[],[f47,f64,f66,f63,f66])).
% 1.58/0.97  
% 1.58/0.97  fof(f12,axiom,(
% 1.58/0.97    ! [X0,X1] : k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k1_xboole_0),
% 1.58/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.58/0.97  
% 1.58/0.97  fof(f50,plain,(
% 1.58/0.97    ( ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k1_xboole_0) )),
% 1.58/0.97    inference(cnf_transformation,[],[f12])).
% 1.58/0.97  
% 1.58/0.97  fof(f78,plain,(
% 1.58/0.97    ( ! [X0,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k1_xboole_0) )),
% 1.58/0.97    inference(definition_unfolding,[],[f50,f65,f66,f63])).
% 1.58/0.97  
% 1.58/0.97  cnf(c_17,negated_conjecture,
% 1.58/0.97      ( v1_funct_2(sK4,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
% 1.58/0.97      inference(cnf_transformation,[],[f81]) ).
% 1.58/0.97  
% 1.58/0.97  cnf(c_13,plain,
% 1.58/0.97      ( ~ v1_funct_2(X0,X1,X2)
% 1.58/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.58/0.97      | ~ r2_hidden(X3,X1)
% 1.58/0.97      | r2_hidden(k1_funct_1(X0,X3),X2)
% 1.58/0.97      | ~ v1_funct_1(X0)
% 1.58/0.97      | k1_xboole_0 = X2 ),
% 1.58/0.97      inference(cnf_transformation,[],[f53]) ).
% 1.58/0.97  
% 1.58/0.97  cnf(c_16,negated_conjecture,
% 1.58/0.97      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) ),
% 1.58/0.97      inference(cnf_transformation,[],[f80]) ).
% 1.58/0.97  
% 1.58/0.97  cnf(c_151,plain,
% 1.58/0.97      ( ~ v1_funct_2(X0,X1,X2)
% 1.58/0.97      | ~ r2_hidden(X3,X1)
% 1.58/0.97      | r2_hidden(k1_funct_1(X0,X3),X2)
% 1.58/0.97      | ~ v1_funct_1(X0)
% 1.58/0.97      | k1_zfmisc_1(k2_zfmisc_1(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 1.58/0.97      | sK4 != X0
% 1.58/0.97      | k1_xboole_0 = X2 ),
% 1.58/0.97      inference(resolution_lifted,[status(thm)],[c_13,c_16]) ).
% 1.58/0.97  
% 1.58/0.97  cnf(c_152,plain,
% 1.58/0.97      ( ~ v1_funct_2(sK4,X0,X1)
% 1.58/0.97      | ~ r2_hidden(X2,X0)
% 1.58/0.97      | r2_hidden(k1_funct_1(sK4,X2),X1)
% 1.58/0.97      | ~ v1_funct_1(sK4)
% 1.58/0.97      | k1_zfmisc_1(k2_zfmisc_1(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.58/0.97      | k1_xboole_0 = X1 ),
% 1.58/0.97      inference(unflattening,[status(thm)],[c_151]) ).
% 1.58/0.97  
% 1.58/0.97  cnf(c_18,negated_conjecture,
% 1.58/0.97      ( v1_funct_1(sK4) ),
% 1.58/0.97      inference(cnf_transformation,[],[f54]) ).
% 1.58/0.97  
% 1.58/0.97  cnf(c_156,plain,
% 1.58/0.97      ( r2_hidden(k1_funct_1(sK4,X2),X1)
% 1.58/0.97      | ~ r2_hidden(X2,X0)
% 1.58/0.97      | ~ v1_funct_2(sK4,X0,X1)
% 1.58/0.97      | k1_zfmisc_1(k2_zfmisc_1(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.58/0.97      | k1_xboole_0 = X1 ),
% 1.58/0.97      inference(global_propositional_subsumption,[status(thm)],[c_152,c_18]) ).
% 1.58/0.97  
% 1.58/0.97  cnf(c_157,plain,
% 1.58/0.97      ( ~ v1_funct_2(sK4,X0,X1)
% 1.58/0.97      | ~ r2_hidden(X2,X0)
% 1.58/0.97      | r2_hidden(k1_funct_1(sK4,X2),X1)
% 1.58/0.97      | k1_zfmisc_1(k2_zfmisc_1(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.58/0.97      | k1_xboole_0 = X1 ),
% 1.58/0.97      inference(renaming,[status(thm)],[c_156]) ).
% 1.58/0.97  
% 1.58/0.97  cnf(c_184,plain,
% 1.58/0.97      ( ~ r2_hidden(X0,X1)
% 1.58/0.97      | r2_hidden(k1_funct_1(sK4,X0),X2)
% 1.58/0.97      | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != X2
% 1.58/0.97      | k1_zfmisc_1(k2_zfmisc_1(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 1.58/0.97      | sK1 != X1
% 1.58/0.97      | sK4 != sK4
% 1.58/0.97      | k1_xboole_0 = X2 ),
% 1.58/0.97      inference(resolution_lifted,[status(thm)],[c_17,c_157]) ).
% 1.58/0.97  
% 1.58/0.97  cnf(c_185,plain,
% 1.58/0.97      ( ~ r2_hidden(X0,sK1)
% 1.58/0.97      | r2_hidden(k1_funct_1(sK4,X0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 1.58/0.97      | k1_zfmisc_1(k2_zfmisc_1(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) != k1_zfmisc_1(k2_zfmisc_1(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))
% 1.58/0.97      | k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 1.58/0.97      inference(unflattening,[status(thm)],[c_184]) ).
% 1.58/0.97  
% 1.58/0.97  cnf(c_217,plain,
% 1.58/0.97      ( ~ r2_hidden(X0,sK1)
% 1.58/0.97      | r2_hidden(k1_funct_1(sK4,X0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 1.58/0.97      | k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 1.58/0.97      inference(equality_resolution_simp,[status(thm)],[c_185]) ).
% 1.58/0.97  
% 1.58/0.97  cnf(c_446,plain,
% 1.58/0.97      ( k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
% 1.58/0.97      | r2_hidden(X0,sK1) != iProver_top
% 1.58/0.97      | r2_hidden(k1_funct_1(sK4,X0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
% 1.58/0.97      inference(predicate_to_equality,[status(thm)],[c_217]) ).
% 1.58/0.97  
% 1.58/0.97  cnf(c_15,negated_conjecture,
% 1.58/0.97      ( r2_hidden(sK3,sK1) ),
% 1.58/0.97      inference(cnf_transformation,[],[f57]) ).
% 1.58/0.97  
% 1.58/0.97  cnf(c_14,negated_conjecture,
% 1.58/0.97      ( k1_funct_1(sK4,sK3) != sK2 ),
% 1.58/0.97      inference(cnf_transformation,[],[f58]) ).
% 1.58/0.97  
% 1.58/0.97  cnf(c_545,plain,
% 1.58/0.97      ( r2_hidden(k1_funct_1(sK4,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 1.58/0.97      | ~ r2_hidden(sK3,sK1)
% 1.58/0.97      | k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 1.58/0.97      inference(instantiation,[status(thm)],[c_217]) ).
% 1.58/0.97  
% 1.58/0.97  cnf(c_7,plain,
% 1.58/0.97      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))
% 1.58/0.97      | X0 = X1
% 1.58/0.97      | X0 = X2
% 1.58/0.97      | X0 = X3 ),
% 1.58/0.97      inference(cnf_transformation,[],[f88]) ).
% 1.58/0.97  
% 1.58/0.97  cnf(c_568,plain,
% 1.58/0.97      ( ~ r2_hidden(k1_funct_1(sK4,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,X0,X1))
% 1.58/0.97      | k1_funct_1(sK4,sK3) = X0
% 1.58/0.97      | k1_funct_1(sK4,sK3) = X1
% 1.58/0.97      | k1_funct_1(sK4,sK3) = sK2 ),
% 1.58/0.97      inference(instantiation,[status(thm)],[c_7]) ).
% 1.58/0.97  
% 1.58/0.97  cnf(c_570,plain,
% 1.58/0.97      ( ~ r2_hidden(k1_funct_1(sK4,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 1.58/0.97      | k1_funct_1(sK4,sK3) = sK2 ),
% 1.58/0.97      inference(instantiation,[status(thm)],[c_568]) ).
% 1.58/0.97  
% 1.58/0.97  cnf(c_574,plain,
% 1.58/0.97      ( k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 1.58/0.97      inference(global_propositional_subsumption,
% 1.58/0.97                [status(thm)],
% 1.58/0.97                [c_446,c_15,c_14,c_545,c_570]) ).
% 1.58/0.97  
% 1.58/0.97  cnf(c_10,plain,
% 1.58/0.97      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 1.58/0.97      inference(cnf_transformation,[],[f89]) ).
% 1.58/0.97  
% 1.58/0.97  cnf(c_8,plain,
% 1.58/0.97      ( k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 1.58/0.97      inference(cnf_transformation,[],[f75]) ).
% 1.58/0.97  
% 1.58/0.97  cnf(c_11,plain,
% 1.58/0.97      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k1_xboole_0 ),
% 1.58/0.97      inference(cnf_transformation,[],[f78]) ).
% 1.58/0.97  
% 1.58/0.97  cnf(c_512,plain,
% 1.58/0.97      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k1_xboole_0 ),
% 1.58/0.97      inference(light_normalisation,[status(thm)],[c_11,c_8]) ).
% 1.58/0.97  
% 1.58/0.97  cnf(c_515,plain,
% 1.58/0.97      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_xboole_0 ),
% 1.58/0.97      inference(demodulation,[status(thm)],[c_10,c_8,c_512]) ).
% 1.58/0.97  
% 1.58/0.97  cnf(c_657,plain,
% 1.58/0.97      ( $false ),
% 1.58/0.97      inference(superposition,[status(thm)],[c_574,c_515]) ).
% 1.58/0.97  
% 1.58/0.97  
% 1.58/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 1.58/0.97  
% 1.58/0.97  ------                               Statistics
% 1.58/0.97  
% 1.58/0.97  ------ General
% 1.58/0.97  
% 1.58/0.97  abstr_ref_over_cycles:                  0
% 1.58/0.97  abstr_ref_under_cycles:                 0
% 1.58/0.97  gc_basic_clause_elim:                   0
% 1.58/0.97  forced_gc_time:                         0
% 1.58/0.97  parsing_time:                           0.013
% 1.58/0.97  unif_index_cands_time:                  0.
% 1.58/0.97  unif_index_add_time:                    0.
% 1.58/0.97  orderings_time:                         0.
% 1.58/0.97  out_proof_time:                         0.019
% 1.58/0.97  total_time:                             0.077
% 1.58/0.98  num_of_symbols:                         47
% 1.58/0.98  num_of_terms:                           682
% 1.58/0.98  
% 1.58/0.98  ------ Preprocessing
% 1.58/0.98  
% 1.58/0.98  num_of_splits:                          0
% 1.58/0.98  num_of_split_atoms:                     0
% 1.58/0.98  num_of_reused_defs:                     0
% 1.58/0.98  num_eq_ax_congr_red:                    12
% 1.58/0.98  num_of_sem_filtered_clauses:            1
% 1.58/0.98  num_of_subtypes:                        0
% 1.58/0.98  monotx_restored_types:                  0
% 1.58/0.98  sat_num_of_epr_types:                   0
% 1.58/0.98  sat_num_of_non_cyclic_types:            0
% 1.58/0.98  sat_guarded_non_collapsed_types:        0
% 1.58/0.98  num_pure_diseq_elim:                    0
% 1.58/0.98  simp_replaced_by:                       0
% 1.58/0.98  res_preprocessed:                       82
% 1.58/0.98  prep_upred:                             0
% 1.58/0.98  prep_unflattend:                        3
% 1.58/0.98  smt_new_axioms:                         0
% 1.58/0.98  pred_elim_cands:                        1
% 1.58/0.98  pred_elim:                              3
% 1.58/0.98  pred_elim_cl:                           3
% 1.58/0.98  pred_elim_cycles:                       5
% 1.58/0.98  merged_defs:                            0
% 1.58/0.98  merged_defs_ncl:                        0
% 1.58/0.98  bin_hyper_res:                          0
% 1.58/0.98  prep_cycles:                            4
% 1.58/0.98  pred_elim_time:                         0.002
% 1.58/0.98  splitting_time:                         0.
% 1.58/0.98  sem_filter_time:                        0.
% 1.58/0.98  monotx_time:                            0.
% 1.58/0.98  subtype_inf_time:                       0.
% 1.58/0.98  
% 1.58/0.98  ------ Problem properties
% 1.58/0.98  
% 1.58/0.98  clauses:                                16
% 1.58/0.98  conjectures:                            2
% 1.58/0.98  epr:                                    1
% 1.58/0.98  horn:                                   12
% 1.58/0.98  ground:                                 2
% 1.58/0.98  unary:                                  9
% 1.58/0.98  binary:                                 1
% 1.58/0.98  lits:                                   32
% 1.58/0.98  lits_eq:                                21
% 1.58/0.98  fd_pure:                                0
% 1.58/0.98  fd_pseudo:                              0
% 1.58/0.98  fd_cond:                                0
% 1.58/0.98  fd_pseudo_cond:                         5
% 1.58/0.98  ac_symbols:                             0
% 1.58/0.98  
% 1.58/0.98  ------ Propositional Solver
% 1.58/0.98  
% 1.58/0.98  prop_solver_calls:                      24
% 1.58/0.98  prop_fast_solver_calls:                 394
% 1.58/0.98  smt_solver_calls:                       0
% 1.58/0.98  smt_fast_solver_calls:                  0
% 1.58/0.98  prop_num_of_clauses:                    156
% 1.58/0.98  prop_preprocess_simplified:             1907
% 1.58/0.98  prop_fo_subsumed:                       3
% 1.58/0.98  prop_solver_time:                       0.
% 1.58/0.98  smt_solver_time:                        0.
% 1.58/0.98  smt_fast_solver_time:                   0.
% 1.58/0.98  prop_fast_solver_time:                  0.
% 1.58/0.98  prop_unsat_core_time:                   0.
% 1.58/0.98  
% 1.58/0.98  ------ QBF
% 1.58/0.98  
% 1.58/0.98  qbf_q_res:                              0
% 1.58/0.98  qbf_num_tautologies:                    0
% 1.58/0.98  qbf_prep_cycles:                        0
% 1.58/0.98  
% 1.58/0.98  ------ BMC1
% 1.58/0.98  
% 1.58/0.98  bmc1_current_bound:                     -1
% 1.58/0.98  bmc1_last_solved_bound:                 -1
% 1.58/0.98  bmc1_unsat_core_size:                   -1
% 1.58/0.98  bmc1_unsat_core_parents_size:           -1
% 1.58/0.98  bmc1_merge_next_fun:                    0
% 1.58/0.98  bmc1_unsat_core_clauses_time:           0.
% 1.58/0.98  
% 1.58/0.98  ------ Instantiation
% 1.58/0.98  
% 1.58/0.98  inst_num_of_clauses:                    54
% 1.58/0.98  inst_num_in_passive:                    26
% 1.58/0.98  inst_num_in_active:                     28
% 1.58/0.98  inst_num_in_unprocessed:                0
% 1.58/0.98  inst_num_of_loops:                      30
% 1.58/0.98  inst_num_of_learning_restarts:          0
% 1.58/0.98  inst_num_moves_active_passive:          1
% 1.58/0.98  inst_lit_activity:                      0
% 1.58/0.98  inst_lit_activity_moves:                0
% 1.58/0.98  inst_num_tautologies:                   0
% 1.58/0.98  inst_num_prop_implied:                  0
% 1.58/0.98  inst_num_existing_simplified:           0
% 1.58/0.98  inst_num_eq_res_simplified:             0
% 1.58/0.98  inst_num_child_elim:                    0
% 1.58/0.98  inst_num_of_dismatching_blockings:      0
% 1.58/0.98  inst_num_of_non_proper_insts:           16
% 1.58/0.98  inst_num_of_duplicates:                 0
% 1.58/0.98  inst_inst_num_from_inst_to_res:         0
% 1.58/0.98  inst_dismatching_checking_time:         0.
% 1.58/0.98  
% 1.58/0.98  ------ Resolution
% 1.58/0.98  
% 1.58/0.98  res_num_of_clauses:                     0
% 1.58/0.98  res_num_in_passive:                     0
% 1.58/0.98  res_num_in_active:                      0
% 1.58/0.98  res_num_of_loops:                       86
% 1.58/0.98  res_forward_subset_subsumed:            2
% 1.58/0.98  res_backward_subset_subsumed:           0
% 1.58/0.98  res_forward_subsumed:                   0
% 1.58/0.98  res_backward_subsumed:                  0
% 1.58/0.98  res_forward_subsumption_resolution:     0
% 1.58/0.98  res_backward_subsumption_resolution:    0
% 1.58/0.98  res_clause_to_clause_subsumption:       54
% 1.58/0.98  res_orphan_elimination:                 0
% 1.58/0.98  res_tautology_del:                      0
% 1.58/0.98  res_num_eq_res_simplified:              1
% 1.58/0.98  res_num_sel_changes:                    0
% 1.58/0.98  res_moves_from_active_to_pass:          0
% 1.58/0.98  
% 1.58/0.98  ------ Superposition
% 1.58/0.98  
% 1.58/0.98  sup_time_total:                         0.
% 1.58/0.98  sup_time_generating:                    0.
% 1.58/0.98  sup_time_sim_full:                      0.
% 1.58/0.98  sup_time_sim_immed:                     0.
% 1.58/0.98  
% 1.58/0.98  sup_num_of_clauses:                     17
% 1.58/0.98  sup_num_in_active:                      6
% 1.58/0.98  sup_num_in_passive:                     11
% 1.58/0.98  sup_num_of_loops:                       5
% 1.58/0.98  sup_fw_superposition:                   1
% 1.58/0.98  sup_bw_superposition:                   0
% 1.58/0.98  sup_immediate_simplified:               0
% 1.58/0.98  sup_given_eliminated:                   0
% 1.58/0.98  comparisons_done:                       0
% 1.58/0.98  comparisons_avoided:                    0
% 1.58/0.98  
% 1.58/0.98  ------ Simplifications
% 1.58/0.98  
% 1.58/0.98  
% 1.58/0.98  sim_fw_subset_subsumed:                 0
% 1.58/0.98  sim_bw_subset_subsumed:                 0
% 1.58/0.98  sim_fw_subsumed:                        0
% 1.58/0.98  sim_bw_subsumed:                        0
% 1.58/0.98  sim_fw_subsumption_res:                 0
% 1.58/0.98  sim_bw_subsumption_res:                 0
% 1.58/0.98  sim_tautology_del:                      0
% 1.58/0.98  sim_eq_tautology_del:                   0
% 1.58/0.98  sim_eq_res_simp:                        0
% 1.58/0.98  sim_fw_demodulated:                     1
% 1.58/0.98  sim_bw_demodulated:                     0
% 1.58/0.98  sim_light_normalised:                   1
% 1.58/0.98  sim_joinable_taut:                      0
% 1.58/0.98  sim_joinable_simp:                      0
% 1.58/0.98  sim_ac_normalised:                      0
% 1.58/0.98  sim_smt_subsumption:                    0
% 1.58/0.98  
%------------------------------------------------------------------------------
