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
% DateTime   : Thu Dec  3 11:40:59 EST 2020

% Result     : Theorem 7.73s
% Output     : CNFRefutation 7.73s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 624 expanded)
%              Number of clauses        :   80 ( 233 expanded)
%              Number of leaves         :   18 ( 166 expanded)
%              Depth                    :   17
%              Number of atoms          :  393 (1313 expanded)
%              Number of equality atoms :  164 ( 658 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ( ~ r2_hidden(X2,X1)
               => r2_hidden(X2,k3_subset_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( k1_xboole_0 != X0
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(X0))
           => ! [X2] :
                ( m1_subset_1(X2,X0)
               => ( ~ r2_hidden(X2,X1)
                 => r2_hidden(X2,k3_subset_1(X0,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X2,k3_subset_1(X0,X1))
              & ~ r2_hidden(X2,X1)
              & m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X2,k3_subset_1(X0,X1))
              & ~ r2_hidden(X2,X1)
              & m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      & k1_xboole_0 != X0 ) ),
    inference(flattening,[],[f17])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,k3_subset_1(X0,X1))
          & ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
     => ( ~ r2_hidden(sK5,k3_subset_1(X0,X1))
        & ~ r2_hidden(sK5,X1)
        & m1_subset_1(sK5,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X2,k3_subset_1(X0,X1))
              & ~ r2_hidden(X2,X1)
              & m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( ? [X2] :
            ( ~ r2_hidden(X2,k3_subset_1(X0,sK4))
            & ~ r2_hidden(X2,sK4)
            & m1_subset_1(X2,X0) )
        & m1_subset_1(sK4,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r2_hidden(X2,k3_subset_1(X0,X1))
                & ~ r2_hidden(X2,X1)
                & m1_subset_1(X2,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(X0)) )
        & k1_xboole_0 != X0 )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X2,k3_subset_1(sK3,X1))
              & ~ r2_hidden(X2,X1)
              & m1_subset_1(X2,sK3) )
          & m1_subset_1(X1,k1_zfmisc_1(sK3)) )
      & k1_xboole_0 != sK3 ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ~ r2_hidden(sK5,k3_subset_1(sK3,sK4))
    & ~ r2_hidden(sK5,sK4)
    & m1_subset_1(sK5,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(sK3))
    & k1_xboole_0 != sK3 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f18,f37,f36,f35])).

fof(f64,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f38])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f68,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f53,f57])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f62,f68])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f6,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f75,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k2_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f54,f57])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f72,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) != X2 ) ),
    inference(definition_unfolding,[],[f46,f68])).

fof(f77,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f72])).

fof(f67,plain,(
    ~ r2_hidden(sK5,k3_subset_1(sK3,sK4)) ),
    inference(cnf_transformation,[],[f38])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f19])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f21])).

fof(f39,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f47,f68])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) = X2
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f48,f68])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f80,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f51])).

fof(f52,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f65,plain,(
    m1_subset_1(sK5,sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f81,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f50])).

fof(f66,plain,(
    ~ r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f63,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_978,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X0),k2_xboole_0(X1,X0))) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_982,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) = k3_subset_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1931,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(sK3,sK4),k2_xboole_0(sK3,sK4))) = k3_subset_1(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_978,c_982])).

cnf(c_15,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_16,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_14,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k2_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1013,plain,
    ( k5_xboole_0(X0,k2_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_14,c_15])).

cnf(c_1284,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_16,c_1013])).

cnf(c_1514,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k2_xboole_0(X0,k1_xboole_0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_15,c_1284])).

cnf(c_1282,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k2_xboole_0(X0,k1_xboole_0),X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_1013,c_16])).

cnf(c_1711,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k2_xboole_0(k2_xboole_0(X0,k1_xboole_0),k1_xboole_0))) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1514,c_1282])).

cnf(c_1401,plain,
    ( k5_xboole_0(k1_xboole_0,k2_xboole_0(k2_xboole_0(X0,k1_xboole_0),k1_xboole_0)) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1013,c_1282])).

cnf(c_1423,plain,
    ( k5_xboole_0(k1_xboole_0,k2_xboole_0(k2_xboole_0(X0,k1_xboole_0),k1_xboole_0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1401,c_15])).

cnf(c_1713,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1711,c_15,c_1423])).

cnf(c_1749,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k1_xboole_0),k1_xboole_0) = X0 ),
    inference(superposition,[status(thm)],[c_1713,c_1423])).

cnf(c_1405,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k2_xboole_0(X0,k1_xboole_0),X1),X2)) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),X2) ),
    inference(superposition,[status(thm)],[c_1282,c_16])).

cnf(c_2800,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k2_xboole_0(X0,k1_xboole_0),X1),X2)) = k5_xboole_0(X1,X2) ),
    inference(demodulation,[status(thm)],[c_1405,c_1713])).

cnf(c_2817,plain,
    ( k5_xboole_0(k2_xboole_0(X0,k1_xboole_0),k5_xboole_0(k5_xboole_0(X0,X1),X2)) = k5_xboole_0(X1,X2) ),
    inference(superposition,[status(thm)],[c_1749,c_2800])).

cnf(c_2849,plain,
    ( k5_xboole_0(k2_xboole_0(X0,k1_xboole_0),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X1,X2) ),
    inference(light_normalisation,[status(thm)],[c_2817,c_16])).

cnf(c_3865,plain,
    ( k5_xboole_0(k2_xboole_0(sK3,k1_xboole_0),k3_subset_1(sK3,sK4)) = k5_xboole_0(k5_xboole_0(sK3,sK4),k2_xboole_0(sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_1931,c_2849])).

cnf(c_2107,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(sK3,k5_xboole_0(sK4,k2_xboole_0(sK3,sK4)))) = k3_subset_1(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_16,c_1931])).

cnf(c_3870,plain,
    ( k5_xboole_0(k2_xboole_0(sK3,k1_xboole_0),k3_subset_1(sK3,sK4)) = k5_xboole_0(sK3,k5_xboole_0(sK4,k2_xboole_0(sK3,sK4))) ),
    inference(superposition,[status(thm)],[c_2107,c_2849])).

cnf(c_4003,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(sK4,k2_xboole_0(sK3,sK4))) = k5_xboole_0(k5_xboole_0(sK3,sK4),k2_xboole_0(sK3,sK4)) ),
    inference(light_normalisation,[status(thm)],[c_3865,c_3870])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_990,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_10969,plain,
    ( r2_hidden(X0,k5_xboole_0(sK3,k5_xboole_0(sK3,k5_xboole_0(sK4,k2_xboole_0(sK3,sK4))))) = iProver_top
    | r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4003,c_990])).

cnf(c_11253,plain,
    ( r2_hidden(X0,k3_subset_1(sK3,sK4)) = iProver_top
    | r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10969,c_2107])).

cnf(c_22,negated_conjecture,
    ( ~ r2_hidden(sK5,k3_subset_1(sK3,sK4)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_981,plain,
    ( r2_hidden(sK5,k3_subset_1(sK3,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_13820,plain,
    ( r2_hidden(sK5,sK4) = iProver_top
    | r2_hidden(sK5,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_11253,c_981])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_5168,plain,
    ( ~ r2_hidden(sK2(X0,X1,X2),X2)
    | ~ v1_xboole_0(X2) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_12642,plain,
    ( ~ r2_hidden(sK2(X0,X1,sK3),sK3)
    | ~ v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_5168])).

cnf(c_12643,plain,
    ( r2_hidden(sK2(X0,X1,sK3),sK3) != iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12642])).

cnf(c_12645,plain,
    ( r2_hidden(sK2(k1_xboole_0,k1_xboole_0,sK3),sK3) != iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_12643])).

cnf(c_612,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_10930,plain,
    ( k5_xboole_0(X0,X1) != X2
    | k1_xboole_0 != X2
    | k1_xboole_0 = k5_xboole_0(X0,X1) ),
    inference(instantiation,[status(thm)],[c_612])).

cnf(c_10931,plain,
    ( k5_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_10930])).

cnf(c_614,plain,
    ( X0 != X1
    | X2 != X3
    | k5_xboole_0(X0,X2) = k5_xboole_0(X1,X3) ),
    theory(equality)).

cnf(c_3672,plain,
    ( X0 != X1
    | k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X2),k2_xboole_0(X0,X2))) = k5_xboole_0(X1,X3)
    | k5_xboole_0(k5_xboole_0(X0,X2),k2_xboole_0(X0,X2)) != X3 ),
    inference(instantiation,[status(thm)],[c_614])).

cnf(c_3674,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k2_xboole_0(k1_xboole_0,k1_xboole_0)) != k1_xboole_0
    | k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k2_xboole_0(k1_xboole_0,k1_xboole_0))) = k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3672])).

cnf(c_3083,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) != X2
    | k1_xboole_0 != X2
    | k1_xboole_0 = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_612])).

cnf(c_3671,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) != k5_xboole_0(X2,X3)
    | k1_xboole_0 != k5_xboole_0(X2,X3)
    | k1_xboole_0 = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_3083])).

cnf(c_3673,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k2_xboole_0(k1_xboole_0,k1_xboole_0))) != k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k2_xboole_0(k1_xboole_0,k1_xboole_0)))
    | k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3671])).

cnf(c_1447,plain,
    ( X0 != X1
    | X0 = sK3
    | sK3 != X1 ),
    inference(instantiation,[status(thm)],[c_612])).

cnf(c_2487,plain,
    ( X0 != k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)))
    | X0 = sK3
    | sK3 != k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))) ),
    inference(instantiation,[status(thm)],[c_1447])).

cnf(c_2490,plain,
    ( sK3 != k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k2_xboole_0(k1_xboole_0,k1_xboole_0)))
    | k1_xboole_0 != k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k2_xboole_0(k1_xboole_0,k1_xboole_0)))
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_2487])).

cnf(c_7,plain,
    ( r2_hidden(sK2(X0,X1,X2),X0)
    | r2_hidden(sK2(X0,X1,X2),X2)
    | k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) = X2 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1434,plain,
    ( r2_hidden(sK2(X0,X1,sK3),X0)
    | r2_hidden(sK2(X0,X1,sK3),sK3)
    | k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) = sK3 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1441,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) = sK3
    | r2_hidden(sK2(X0,X1,sK3),X0) = iProver_top
    | r2_hidden(sK2(X0,X1,sK3),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1434])).

cnf(c_1443,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k2_xboole_0(k1_xboole_0,k1_xboole_0))) = sK3
    | r2_hidden(sK2(k1_xboole_0,k1_xboole_0,sK3),sK3) = iProver_top
    | r2_hidden(sK2(k1_xboole_0,k1_xboole_0,sK3),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1441])).

cnf(c_6,plain,
    ( ~ r2_hidden(sK2(X0,X1,X2),X1)
    | r2_hidden(sK2(X0,X1,X2),X2)
    | k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) = X2 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1435,plain,
    ( ~ r2_hidden(sK2(X0,X1,sK3),X1)
    | r2_hidden(sK2(X0,X1,sK3),sK3)
    | k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) = sK3 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1437,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) = sK3
    | r2_hidden(sK2(X0,X1,sK3),X1) != iProver_top
    | r2_hidden(sK2(X0,X1,sK3),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1435])).

cnf(c_1439,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k2_xboole_0(k1_xboole_0,k1_xboole_0))) = sK3
    | r2_hidden(sK2(k1_xboole_0,k1_xboole_0,sK3),sK3) = iProver_top
    | r2_hidden(sK2(k1_xboole_0,k1_xboole_0,sK3),k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1437])).

cnf(c_1192,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_612])).

cnf(c_1272,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1192])).

cnf(c_1432,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) != sK3
    | sK3 = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1272])).

cnf(c_1436,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k2_xboole_0(k1_xboole_0,k1_xboole_0))) != sK3
    | sK3 = k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k2_xboole_0(k1_xboole_0,k1_xboole_0)))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1432])).

cnf(c_12,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1265,plain,
    ( r1_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1193,plain,
    ( ~ r1_tarski(X0,sK3)
    | ~ r1_tarski(sK3,X0)
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1264,plain,
    ( ~ r1_tarski(sK3,sK3)
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1193])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK5,sK3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_286,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | sK3 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_24])).

cnf(c_287,plain,
    ( r2_hidden(sK5,sK3)
    | v1_xboole_0(sK3) ),
    inference(unflattening,[status(thm)],[c_286])).

cnf(c_288,plain,
    ( r2_hidden(sK5,sK3) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_287])).

cnf(c_52,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_13,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_48,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_46,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k2_xboole_0(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_45,plain,
    ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_23,negated_conjecture,
    ( ~ r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_29,plain,
    ( r2_hidden(sK5,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_26,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f63])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13820,c_12645,c_10931,c_3674,c_3673,c_2490,c_1443,c_1439,c_1436,c_1265,c_1264,c_288,c_52,c_48,c_46,c_45,c_29,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:35:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 7.73/1.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.73/1.48  
% 7.73/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.73/1.48  
% 7.73/1.48  ------  iProver source info
% 7.73/1.48  
% 7.73/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.73/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.73/1.48  git: non_committed_changes: false
% 7.73/1.48  git: last_make_outside_of_git: false
% 7.73/1.48  
% 7.73/1.48  ------ 
% 7.73/1.48  
% 7.73/1.48  ------ Input Options
% 7.73/1.48  
% 7.73/1.48  --out_options                           all
% 7.73/1.48  --tptp_safe_out                         true
% 7.73/1.48  --problem_path                          ""
% 7.73/1.48  --include_path                          ""
% 7.73/1.48  --clausifier                            res/vclausify_rel
% 7.73/1.48  --clausifier_options                    --mode clausify
% 7.73/1.48  --stdin                                 false
% 7.73/1.48  --stats_out                             all
% 7.73/1.48  
% 7.73/1.48  ------ General Options
% 7.73/1.48  
% 7.73/1.48  --fof                                   false
% 7.73/1.48  --time_out_real                         305.
% 7.73/1.48  --time_out_virtual                      -1.
% 7.73/1.48  --symbol_type_check                     false
% 7.73/1.48  --clausify_out                          false
% 7.73/1.48  --sig_cnt_out                           false
% 7.73/1.48  --trig_cnt_out                          false
% 7.73/1.48  --trig_cnt_out_tolerance                1.
% 7.73/1.48  --trig_cnt_out_sk_spl                   false
% 7.73/1.48  --abstr_cl_out                          false
% 7.73/1.48  
% 7.73/1.48  ------ Global Options
% 7.73/1.48  
% 7.73/1.48  --schedule                              default
% 7.73/1.48  --add_important_lit                     false
% 7.73/1.48  --prop_solver_per_cl                    1000
% 7.73/1.48  --min_unsat_core                        false
% 7.73/1.48  --soft_assumptions                      false
% 7.73/1.48  --soft_lemma_size                       3
% 7.73/1.48  --prop_impl_unit_size                   0
% 7.73/1.48  --prop_impl_unit                        []
% 7.73/1.48  --share_sel_clauses                     true
% 7.73/1.48  --reset_solvers                         false
% 7.73/1.48  --bc_imp_inh                            [conj_cone]
% 7.73/1.48  --conj_cone_tolerance                   3.
% 7.73/1.48  --extra_neg_conj                        none
% 7.73/1.48  --large_theory_mode                     true
% 7.73/1.48  --prolific_symb_bound                   200
% 7.73/1.48  --lt_threshold                          2000
% 7.73/1.48  --clause_weak_htbl                      true
% 7.73/1.48  --gc_record_bc_elim                     false
% 7.73/1.48  
% 7.73/1.48  ------ Preprocessing Options
% 7.73/1.48  
% 7.73/1.48  --preprocessing_flag                    true
% 7.73/1.48  --time_out_prep_mult                    0.1
% 7.73/1.48  --splitting_mode                        input
% 7.73/1.48  --splitting_grd                         true
% 7.73/1.48  --splitting_cvd                         false
% 7.73/1.48  --splitting_cvd_svl                     false
% 7.73/1.48  --splitting_nvd                         32
% 7.73/1.48  --sub_typing                            true
% 7.73/1.48  --prep_gs_sim                           true
% 7.73/1.48  --prep_unflatten                        true
% 7.73/1.48  --prep_res_sim                          true
% 7.73/1.48  --prep_upred                            true
% 7.73/1.48  --prep_sem_filter                       exhaustive
% 7.73/1.48  --prep_sem_filter_out                   false
% 7.73/1.48  --pred_elim                             true
% 7.73/1.48  --res_sim_input                         true
% 7.73/1.48  --eq_ax_congr_red                       true
% 7.73/1.48  --pure_diseq_elim                       true
% 7.73/1.48  --brand_transform                       false
% 7.73/1.48  --non_eq_to_eq                          false
% 7.73/1.48  --prep_def_merge                        true
% 7.73/1.48  --prep_def_merge_prop_impl              false
% 7.73/1.48  --prep_def_merge_mbd                    true
% 7.73/1.48  --prep_def_merge_tr_red                 false
% 7.73/1.48  --prep_def_merge_tr_cl                  false
% 7.73/1.48  --smt_preprocessing                     true
% 7.73/1.48  --smt_ac_axioms                         fast
% 7.73/1.48  --preprocessed_out                      false
% 7.73/1.48  --preprocessed_stats                    false
% 7.73/1.48  
% 7.73/1.48  ------ Abstraction refinement Options
% 7.73/1.48  
% 7.73/1.48  --abstr_ref                             []
% 7.73/1.48  --abstr_ref_prep                        false
% 7.73/1.48  --abstr_ref_until_sat                   false
% 7.73/1.48  --abstr_ref_sig_restrict                funpre
% 7.73/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.73/1.48  --abstr_ref_under                       []
% 7.73/1.48  
% 7.73/1.48  ------ SAT Options
% 7.73/1.48  
% 7.73/1.48  --sat_mode                              false
% 7.73/1.48  --sat_fm_restart_options                ""
% 7.73/1.48  --sat_gr_def                            false
% 7.73/1.48  --sat_epr_types                         true
% 7.73/1.48  --sat_non_cyclic_types                  false
% 7.73/1.48  --sat_finite_models                     false
% 7.73/1.48  --sat_fm_lemmas                         false
% 7.73/1.48  --sat_fm_prep                           false
% 7.73/1.48  --sat_fm_uc_incr                        true
% 7.73/1.48  --sat_out_model                         small
% 7.73/1.48  --sat_out_clauses                       false
% 7.73/1.48  
% 7.73/1.48  ------ QBF Options
% 7.73/1.48  
% 7.73/1.48  --qbf_mode                              false
% 7.73/1.48  --qbf_elim_univ                         false
% 7.73/1.48  --qbf_dom_inst                          none
% 7.73/1.48  --qbf_dom_pre_inst                      false
% 7.73/1.48  --qbf_sk_in                             false
% 7.73/1.48  --qbf_pred_elim                         true
% 7.73/1.48  --qbf_split                             512
% 7.73/1.48  
% 7.73/1.48  ------ BMC1 Options
% 7.73/1.48  
% 7.73/1.48  --bmc1_incremental                      false
% 7.73/1.48  --bmc1_axioms                           reachable_all
% 7.73/1.48  --bmc1_min_bound                        0
% 7.73/1.48  --bmc1_max_bound                        -1
% 7.73/1.48  --bmc1_max_bound_default                -1
% 7.73/1.48  --bmc1_symbol_reachability              true
% 7.73/1.48  --bmc1_property_lemmas                  false
% 7.73/1.48  --bmc1_k_induction                      false
% 7.73/1.48  --bmc1_non_equiv_states                 false
% 7.73/1.48  --bmc1_deadlock                         false
% 7.73/1.48  --bmc1_ucm                              false
% 7.73/1.48  --bmc1_add_unsat_core                   none
% 7.73/1.48  --bmc1_unsat_core_children              false
% 7.73/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.73/1.48  --bmc1_out_stat                         full
% 7.73/1.48  --bmc1_ground_init                      false
% 7.73/1.48  --bmc1_pre_inst_next_state              false
% 7.73/1.48  --bmc1_pre_inst_state                   false
% 7.73/1.48  --bmc1_pre_inst_reach_state             false
% 7.73/1.48  --bmc1_out_unsat_core                   false
% 7.73/1.48  --bmc1_aig_witness_out                  false
% 7.73/1.48  --bmc1_verbose                          false
% 7.73/1.48  --bmc1_dump_clauses_tptp                false
% 7.73/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.73/1.48  --bmc1_dump_file                        -
% 7.73/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.73/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.73/1.48  --bmc1_ucm_extend_mode                  1
% 7.73/1.48  --bmc1_ucm_init_mode                    2
% 7.73/1.48  --bmc1_ucm_cone_mode                    none
% 7.73/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.73/1.48  --bmc1_ucm_relax_model                  4
% 7.73/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.73/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.73/1.48  --bmc1_ucm_layered_model                none
% 7.73/1.48  --bmc1_ucm_max_lemma_size               10
% 7.73/1.48  
% 7.73/1.48  ------ AIG Options
% 7.73/1.48  
% 7.73/1.48  --aig_mode                              false
% 7.73/1.48  
% 7.73/1.48  ------ Instantiation Options
% 7.73/1.48  
% 7.73/1.48  --instantiation_flag                    true
% 7.73/1.48  --inst_sos_flag                         false
% 7.73/1.48  --inst_sos_phase                        true
% 7.73/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.73/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.73/1.48  --inst_lit_sel_side                     num_symb
% 7.73/1.48  --inst_solver_per_active                1400
% 7.73/1.48  --inst_solver_calls_frac                1.
% 7.73/1.48  --inst_passive_queue_type               priority_queues
% 7.73/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.73/1.48  --inst_passive_queues_freq              [25;2]
% 7.73/1.48  --inst_dismatching                      true
% 7.73/1.48  --inst_eager_unprocessed_to_passive     true
% 7.73/1.48  --inst_prop_sim_given                   true
% 7.73/1.48  --inst_prop_sim_new                     false
% 7.73/1.48  --inst_subs_new                         false
% 7.73/1.48  --inst_eq_res_simp                      false
% 7.73/1.48  --inst_subs_given                       false
% 7.73/1.48  --inst_orphan_elimination               true
% 7.73/1.48  --inst_learning_loop_flag               true
% 7.73/1.48  --inst_learning_start                   3000
% 7.73/1.48  --inst_learning_factor                  2
% 7.73/1.48  --inst_start_prop_sim_after_learn       3
% 7.73/1.48  --inst_sel_renew                        solver
% 7.73/1.48  --inst_lit_activity_flag                true
% 7.73/1.48  --inst_restr_to_given                   false
% 7.73/1.48  --inst_activity_threshold               500
% 7.73/1.48  --inst_out_proof                        true
% 7.73/1.48  
% 7.73/1.48  ------ Resolution Options
% 7.73/1.48  
% 7.73/1.48  --resolution_flag                       true
% 7.73/1.48  --res_lit_sel                           adaptive
% 7.73/1.48  --res_lit_sel_side                      none
% 7.73/1.48  --res_ordering                          kbo
% 7.73/1.48  --res_to_prop_solver                    active
% 7.73/1.48  --res_prop_simpl_new                    false
% 7.73/1.48  --res_prop_simpl_given                  true
% 7.73/1.48  --res_passive_queue_type                priority_queues
% 7.73/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.73/1.48  --res_passive_queues_freq               [15;5]
% 7.73/1.48  --res_forward_subs                      full
% 7.73/1.48  --res_backward_subs                     full
% 7.73/1.48  --res_forward_subs_resolution           true
% 7.73/1.48  --res_backward_subs_resolution          true
% 7.73/1.48  --res_orphan_elimination                true
% 7.73/1.48  --res_time_limit                        2.
% 7.73/1.48  --res_out_proof                         true
% 7.73/1.48  
% 7.73/1.48  ------ Superposition Options
% 7.73/1.48  
% 7.73/1.48  --superposition_flag                    true
% 7.73/1.48  --sup_passive_queue_type                priority_queues
% 7.73/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.73/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.73/1.48  --demod_completeness_check              fast
% 7.73/1.48  --demod_use_ground                      true
% 7.73/1.48  --sup_to_prop_solver                    passive
% 7.73/1.48  --sup_prop_simpl_new                    true
% 7.73/1.48  --sup_prop_simpl_given                  true
% 7.73/1.48  --sup_fun_splitting                     false
% 7.73/1.48  --sup_smt_interval                      50000
% 7.73/1.48  
% 7.73/1.48  ------ Superposition Simplification Setup
% 7.73/1.48  
% 7.73/1.48  --sup_indices_passive                   []
% 7.73/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.73/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.73/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.73/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.73/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.73/1.48  --sup_full_bw                           [BwDemod]
% 7.73/1.48  --sup_immed_triv                        [TrivRules]
% 7.73/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.73/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.73/1.48  --sup_immed_bw_main                     []
% 7.73/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.73/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.73/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.73/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.73/1.48  
% 7.73/1.48  ------ Combination Options
% 7.73/1.48  
% 7.73/1.48  --comb_res_mult                         3
% 7.73/1.48  --comb_sup_mult                         2
% 7.73/1.48  --comb_inst_mult                        10
% 7.73/1.48  
% 7.73/1.48  ------ Debug Options
% 7.73/1.48  
% 7.73/1.48  --dbg_backtrace                         false
% 7.73/1.48  --dbg_dump_prop_clauses                 false
% 7.73/1.48  --dbg_dump_prop_clauses_file            -
% 7.73/1.48  --dbg_out_stat                          false
% 7.73/1.48  ------ Parsing...
% 7.73/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.73/1.48  
% 7.73/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.73/1.48  
% 7.73/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.73/1.48  
% 7.73/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.73/1.48  ------ Proving...
% 7.73/1.48  ------ Problem Properties 
% 7.73/1.48  
% 7.73/1.48  
% 7.73/1.48  clauses                                 26
% 7.73/1.48  conjectures                             5
% 7.73/1.48  EPR                                     11
% 7.73/1.48  Horn                                    19
% 7.73/1.48  unary                                   9
% 7.73/1.48  binary                                  8
% 7.73/1.48  lits                                    53
% 7.73/1.48  lits eq                                 9
% 7.73/1.48  fd_pure                                 0
% 7.73/1.48  fd_pseudo                               0
% 7.73/1.48  fd_cond                                 0
% 7.73/1.48  fd_pseudo_cond                          4
% 7.73/1.48  AC symbols                              0
% 7.73/1.48  
% 7.73/1.48  ------ Schedule dynamic 5 is on 
% 7.73/1.48  
% 7.73/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.73/1.48  
% 7.73/1.48  
% 7.73/1.48  ------ 
% 7.73/1.48  Current options:
% 7.73/1.48  ------ 
% 7.73/1.48  
% 7.73/1.48  ------ Input Options
% 7.73/1.48  
% 7.73/1.48  --out_options                           all
% 7.73/1.48  --tptp_safe_out                         true
% 7.73/1.48  --problem_path                          ""
% 7.73/1.48  --include_path                          ""
% 7.73/1.48  --clausifier                            res/vclausify_rel
% 7.73/1.48  --clausifier_options                    --mode clausify
% 7.73/1.48  --stdin                                 false
% 7.73/1.48  --stats_out                             all
% 7.73/1.48  
% 7.73/1.48  ------ General Options
% 7.73/1.48  
% 7.73/1.48  --fof                                   false
% 7.73/1.48  --time_out_real                         305.
% 7.73/1.48  --time_out_virtual                      -1.
% 7.73/1.48  --symbol_type_check                     false
% 7.73/1.48  --clausify_out                          false
% 7.73/1.48  --sig_cnt_out                           false
% 7.73/1.48  --trig_cnt_out                          false
% 7.73/1.48  --trig_cnt_out_tolerance                1.
% 7.73/1.48  --trig_cnt_out_sk_spl                   false
% 7.73/1.48  --abstr_cl_out                          false
% 7.73/1.48  
% 7.73/1.48  ------ Global Options
% 7.73/1.48  
% 7.73/1.48  --schedule                              default
% 7.73/1.48  --add_important_lit                     false
% 7.73/1.48  --prop_solver_per_cl                    1000
% 7.73/1.48  --min_unsat_core                        false
% 7.73/1.48  --soft_assumptions                      false
% 7.73/1.48  --soft_lemma_size                       3
% 7.73/1.48  --prop_impl_unit_size                   0
% 7.73/1.48  --prop_impl_unit                        []
% 7.73/1.48  --share_sel_clauses                     true
% 7.73/1.48  --reset_solvers                         false
% 7.73/1.48  --bc_imp_inh                            [conj_cone]
% 7.73/1.48  --conj_cone_tolerance                   3.
% 7.73/1.48  --extra_neg_conj                        none
% 7.73/1.48  --large_theory_mode                     true
% 7.73/1.48  --prolific_symb_bound                   200
% 7.73/1.48  --lt_threshold                          2000
% 7.73/1.48  --clause_weak_htbl                      true
% 7.73/1.48  --gc_record_bc_elim                     false
% 7.73/1.48  
% 7.73/1.48  ------ Preprocessing Options
% 7.73/1.48  
% 7.73/1.48  --preprocessing_flag                    true
% 7.73/1.48  --time_out_prep_mult                    0.1
% 7.73/1.48  --splitting_mode                        input
% 7.73/1.48  --splitting_grd                         true
% 7.73/1.48  --splitting_cvd                         false
% 7.73/1.48  --splitting_cvd_svl                     false
% 7.73/1.48  --splitting_nvd                         32
% 7.73/1.48  --sub_typing                            true
% 7.73/1.48  --prep_gs_sim                           true
% 7.73/1.48  --prep_unflatten                        true
% 7.73/1.48  --prep_res_sim                          true
% 7.73/1.48  --prep_upred                            true
% 7.73/1.48  --prep_sem_filter                       exhaustive
% 7.73/1.48  --prep_sem_filter_out                   false
% 7.73/1.48  --pred_elim                             true
% 7.73/1.48  --res_sim_input                         true
% 7.73/1.48  --eq_ax_congr_red                       true
% 7.73/1.48  --pure_diseq_elim                       true
% 7.73/1.48  --brand_transform                       false
% 7.73/1.48  --non_eq_to_eq                          false
% 7.73/1.48  --prep_def_merge                        true
% 7.73/1.48  --prep_def_merge_prop_impl              false
% 7.73/1.48  --prep_def_merge_mbd                    true
% 7.73/1.48  --prep_def_merge_tr_red                 false
% 7.73/1.48  --prep_def_merge_tr_cl                  false
% 7.73/1.48  --smt_preprocessing                     true
% 7.73/1.48  --smt_ac_axioms                         fast
% 7.73/1.48  --preprocessed_out                      false
% 7.73/1.48  --preprocessed_stats                    false
% 7.73/1.48  
% 7.73/1.48  ------ Abstraction refinement Options
% 7.73/1.48  
% 7.73/1.48  --abstr_ref                             []
% 7.73/1.48  --abstr_ref_prep                        false
% 7.73/1.48  --abstr_ref_until_sat                   false
% 7.73/1.48  --abstr_ref_sig_restrict                funpre
% 7.73/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.73/1.48  --abstr_ref_under                       []
% 7.73/1.48  
% 7.73/1.48  ------ SAT Options
% 7.73/1.48  
% 7.73/1.48  --sat_mode                              false
% 7.73/1.48  --sat_fm_restart_options                ""
% 7.73/1.48  --sat_gr_def                            false
% 7.73/1.48  --sat_epr_types                         true
% 7.73/1.48  --sat_non_cyclic_types                  false
% 7.73/1.48  --sat_finite_models                     false
% 7.73/1.48  --sat_fm_lemmas                         false
% 7.73/1.48  --sat_fm_prep                           false
% 7.73/1.48  --sat_fm_uc_incr                        true
% 7.73/1.48  --sat_out_model                         small
% 7.73/1.48  --sat_out_clauses                       false
% 7.73/1.48  
% 7.73/1.48  ------ QBF Options
% 7.73/1.48  
% 7.73/1.48  --qbf_mode                              false
% 7.73/1.48  --qbf_elim_univ                         false
% 7.73/1.48  --qbf_dom_inst                          none
% 7.73/1.48  --qbf_dom_pre_inst                      false
% 7.73/1.48  --qbf_sk_in                             false
% 7.73/1.48  --qbf_pred_elim                         true
% 7.73/1.48  --qbf_split                             512
% 7.73/1.48  
% 7.73/1.48  ------ BMC1 Options
% 7.73/1.48  
% 7.73/1.48  --bmc1_incremental                      false
% 7.73/1.48  --bmc1_axioms                           reachable_all
% 7.73/1.48  --bmc1_min_bound                        0
% 7.73/1.48  --bmc1_max_bound                        -1
% 7.73/1.48  --bmc1_max_bound_default                -1
% 7.73/1.48  --bmc1_symbol_reachability              true
% 7.73/1.48  --bmc1_property_lemmas                  false
% 7.73/1.48  --bmc1_k_induction                      false
% 7.73/1.48  --bmc1_non_equiv_states                 false
% 7.73/1.48  --bmc1_deadlock                         false
% 7.73/1.48  --bmc1_ucm                              false
% 7.73/1.48  --bmc1_add_unsat_core                   none
% 7.73/1.48  --bmc1_unsat_core_children              false
% 7.73/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.73/1.48  --bmc1_out_stat                         full
% 7.73/1.48  --bmc1_ground_init                      false
% 7.73/1.48  --bmc1_pre_inst_next_state              false
% 7.73/1.48  --bmc1_pre_inst_state                   false
% 7.73/1.48  --bmc1_pre_inst_reach_state             false
% 7.73/1.48  --bmc1_out_unsat_core                   false
% 7.73/1.48  --bmc1_aig_witness_out                  false
% 7.73/1.48  --bmc1_verbose                          false
% 7.73/1.48  --bmc1_dump_clauses_tptp                false
% 7.73/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.73/1.48  --bmc1_dump_file                        -
% 7.73/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.73/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.73/1.48  --bmc1_ucm_extend_mode                  1
% 7.73/1.48  --bmc1_ucm_init_mode                    2
% 7.73/1.48  --bmc1_ucm_cone_mode                    none
% 7.73/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.73/1.48  --bmc1_ucm_relax_model                  4
% 7.73/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.73/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.73/1.48  --bmc1_ucm_layered_model                none
% 7.73/1.48  --bmc1_ucm_max_lemma_size               10
% 7.73/1.48  
% 7.73/1.48  ------ AIG Options
% 7.73/1.48  
% 7.73/1.48  --aig_mode                              false
% 7.73/1.48  
% 7.73/1.48  ------ Instantiation Options
% 7.73/1.48  
% 7.73/1.48  --instantiation_flag                    true
% 7.73/1.48  --inst_sos_flag                         false
% 7.73/1.48  --inst_sos_phase                        true
% 7.73/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.73/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.73/1.48  --inst_lit_sel_side                     none
% 7.73/1.48  --inst_solver_per_active                1400
% 7.73/1.48  --inst_solver_calls_frac                1.
% 7.73/1.48  --inst_passive_queue_type               priority_queues
% 7.73/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.73/1.48  --inst_passive_queues_freq              [25;2]
% 7.73/1.48  --inst_dismatching                      true
% 7.73/1.48  --inst_eager_unprocessed_to_passive     true
% 7.73/1.48  --inst_prop_sim_given                   true
% 7.73/1.48  --inst_prop_sim_new                     false
% 7.73/1.48  --inst_subs_new                         false
% 7.73/1.48  --inst_eq_res_simp                      false
% 7.73/1.48  --inst_subs_given                       false
% 7.73/1.48  --inst_orphan_elimination               true
% 7.73/1.48  --inst_learning_loop_flag               true
% 7.73/1.48  --inst_learning_start                   3000
% 7.73/1.48  --inst_learning_factor                  2
% 7.73/1.48  --inst_start_prop_sim_after_learn       3
% 7.73/1.48  --inst_sel_renew                        solver
% 7.73/1.48  --inst_lit_activity_flag                true
% 7.73/1.48  --inst_restr_to_given                   false
% 7.73/1.48  --inst_activity_threshold               500
% 7.73/1.48  --inst_out_proof                        true
% 7.73/1.48  
% 7.73/1.48  ------ Resolution Options
% 7.73/1.48  
% 7.73/1.48  --resolution_flag                       false
% 7.73/1.48  --res_lit_sel                           adaptive
% 7.73/1.48  --res_lit_sel_side                      none
% 7.73/1.48  --res_ordering                          kbo
% 7.73/1.48  --res_to_prop_solver                    active
% 7.73/1.48  --res_prop_simpl_new                    false
% 7.73/1.48  --res_prop_simpl_given                  true
% 7.73/1.48  --res_passive_queue_type                priority_queues
% 7.73/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.73/1.48  --res_passive_queues_freq               [15;5]
% 7.73/1.48  --res_forward_subs                      full
% 7.73/1.48  --res_backward_subs                     full
% 7.73/1.48  --res_forward_subs_resolution           true
% 7.73/1.48  --res_backward_subs_resolution          true
% 7.73/1.48  --res_orphan_elimination                true
% 7.73/1.48  --res_time_limit                        2.
% 7.73/1.48  --res_out_proof                         true
% 7.73/1.48  
% 7.73/1.48  ------ Superposition Options
% 7.73/1.48  
% 7.73/1.48  --superposition_flag                    true
% 7.73/1.48  --sup_passive_queue_type                priority_queues
% 7.73/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.73/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.73/1.48  --demod_completeness_check              fast
% 7.73/1.48  --demod_use_ground                      true
% 7.73/1.48  --sup_to_prop_solver                    passive
% 7.73/1.48  --sup_prop_simpl_new                    true
% 7.73/1.48  --sup_prop_simpl_given                  true
% 7.73/1.48  --sup_fun_splitting                     false
% 7.73/1.48  --sup_smt_interval                      50000
% 7.73/1.48  
% 7.73/1.48  ------ Superposition Simplification Setup
% 7.73/1.48  
% 7.73/1.48  --sup_indices_passive                   []
% 7.73/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.73/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.73/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.73/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.73/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.73/1.48  --sup_full_bw                           [BwDemod]
% 7.73/1.48  --sup_immed_triv                        [TrivRules]
% 7.73/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.73/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.73/1.48  --sup_immed_bw_main                     []
% 7.73/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.73/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.73/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.73/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.73/1.48  
% 7.73/1.48  ------ Combination Options
% 7.73/1.48  
% 7.73/1.48  --comb_res_mult                         3
% 7.73/1.48  --comb_sup_mult                         2
% 7.73/1.48  --comb_inst_mult                        10
% 7.73/1.48  
% 7.73/1.48  ------ Debug Options
% 7.73/1.48  
% 7.73/1.48  --dbg_backtrace                         false
% 7.73/1.48  --dbg_dump_prop_clauses                 false
% 7.73/1.48  --dbg_dump_prop_clauses_file            -
% 7.73/1.48  --dbg_out_stat                          false
% 7.73/1.48  
% 7.73/1.48  
% 7.73/1.48  
% 7.73/1.48  
% 7.73/1.48  ------ Proving...
% 7.73/1.48  
% 7.73/1.48  
% 7.73/1.48  % SZS status Theorem for theBenchmark.p
% 7.73/1.48  
% 7.73/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.73/1.48  
% 7.73/1.48  fof(f12,conjecture,(
% 7.73/1.48    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,X0) => (~r2_hidden(X2,X1) => r2_hidden(X2,k3_subset_1(X0,X1))))))),
% 7.73/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.48  
% 7.73/1.48  fof(f13,negated_conjecture,(
% 7.73/1.48    ~! [X0] : (k1_xboole_0 != X0 => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,X0) => (~r2_hidden(X2,X1) => r2_hidden(X2,k3_subset_1(X0,X1))))))),
% 7.73/1.48    inference(negated_conjecture,[],[f12])).
% 7.73/1.48  
% 7.73/1.48  fof(f17,plain,(
% 7.73/1.48    ? [X0] : (? [X1] : (? [X2] : ((~r2_hidden(X2,k3_subset_1(X0,X1)) & ~r2_hidden(X2,X1)) & m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) & k1_xboole_0 != X0)),
% 7.73/1.48    inference(ennf_transformation,[],[f13])).
% 7.73/1.48  
% 7.73/1.48  fof(f18,plain,(
% 7.73/1.48    ? [X0] : (? [X1] : (? [X2] : (~r2_hidden(X2,k3_subset_1(X0,X1)) & ~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) & k1_xboole_0 != X0)),
% 7.73/1.48    inference(flattening,[],[f17])).
% 7.73/1.48  
% 7.73/1.48  fof(f37,plain,(
% 7.73/1.48    ( ! [X0,X1] : (? [X2] : (~r2_hidden(X2,k3_subset_1(X0,X1)) & ~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) => (~r2_hidden(sK5,k3_subset_1(X0,X1)) & ~r2_hidden(sK5,X1) & m1_subset_1(sK5,X0))) )),
% 7.73/1.48    introduced(choice_axiom,[])).
% 7.73/1.48  
% 7.73/1.48  fof(f36,plain,(
% 7.73/1.48    ( ! [X0] : (? [X1] : (? [X2] : (~r2_hidden(X2,k3_subset_1(X0,X1)) & ~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (~r2_hidden(X2,k3_subset_1(X0,sK4)) & ~r2_hidden(X2,sK4) & m1_subset_1(X2,X0)) & m1_subset_1(sK4,k1_zfmisc_1(X0)))) )),
% 7.73/1.48    introduced(choice_axiom,[])).
% 7.73/1.48  
% 7.73/1.48  fof(f35,plain,(
% 7.73/1.48    ? [X0] : (? [X1] : (? [X2] : (~r2_hidden(X2,k3_subset_1(X0,X1)) & ~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) & k1_xboole_0 != X0) => (? [X1] : (? [X2] : (~r2_hidden(X2,k3_subset_1(sK3,X1)) & ~r2_hidden(X2,X1) & m1_subset_1(X2,sK3)) & m1_subset_1(X1,k1_zfmisc_1(sK3))) & k1_xboole_0 != sK3)),
% 7.73/1.48    introduced(choice_axiom,[])).
% 7.73/1.48  
% 7.73/1.48  fof(f38,plain,(
% 7.73/1.48    ((~r2_hidden(sK5,k3_subset_1(sK3,sK4)) & ~r2_hidden(sK5,sK4) & m1_subset_1(sK5,sK3)) & m1_subset_1(sK4,k1_zfmisc_1(sK3))) & k1_xboole_0 != sK3),
% 7.73/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f18,f37,f36,f35])).
% 7.73/1.48  
% 7.73/1.48  fof(f64,plain,(
% 7.73/1.48    m1_subset_1(sK4,k1_zfmisc_1(sK3))),
% 7.73/1.48    inference(cnf_transformation,[],[f38])).
% 7.73/1.48  
% 7.73/1.48  fof(f11,axiom,(
% 7.73/1.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 7.73/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.48  
% 7.73/1.48  fof(f16,plain,(
% 7.73/1.48    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.73/1.48    inference(ennf_transformation,[],[f11])).
% 7.73/1.48  
% 7.73/1.48  fof(f62,plain,(
% 7.73/1.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.73/1.48    inference(cnf_transformation,[],[f16])).
% 7.73/1.48  
% 7.73/1.48  fof(f5,axiom,(
% 7.73/1.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.73/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.48  
% 7.73/1.48  fof(f53,plain,(
% 7.73/1.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.73/1.48    inference(cnf_transformation,[],[f5])).
% 7.73/1.48  
% 7.73/1.48  fof(f9,axiom,(
% 7.73/1.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 7.73/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.48  
% 7.73/1.48  fof(f57,plain,(
% 7.73/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 7.73/1.48    inference(cnf_transformation,[],[f9])).
% 7.73/1.48  
% 7.73/1.48  fof(f68,plain,(
% 7.73/1.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)))) )),
% 7.73/1.48    inference(definition_unfolding,[],[f53,f57])).
% 7.73/1.48  
% 7.73/1.48  fof(f76,plain,(
% 7.73/1.48    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.73/1.48    inference(definition_unfolding,[],[f62,f68])).
% 7.73/1.48  
% 7.73/1.48  fof(f7,axiom,(
% 7.73/1.48    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 7.73/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.48  
% 7.73/1.48  fof(f55,plain,(
% 7.73/1.48    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.73/1.48    inference(cnf_transformation,[],[f7])).
% 7.73/1.48  
% 7.73/1.48  fof(f8,axiom,(
% 7.73/1.48    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 7.73/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.48  
% 7.73/1.48  fof(f56,plain,(
% 7.73/1.48    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 7.73/1.48    inference(cnf_transformation,[],[f8])).
% 7.73/1.48  
% 7.73/1.48  fof(f6,axiom,(
% 7.73/1.48    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 7.73/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.48  
% 7.73/1.48  fof(f54,plain,(
% 7.73/1.48    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 7.73/1.48    inference(cnf_transformation,[],[f6])).
% 7.73/1.48  
% 7.73/1.48  fof(f75,plain,(
% 7.73/1.48    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k2_xboole_0(X0,k1_xboole_0)) = k1_xboole_0) )),
% 7.73/1.48    inference(definition_unfolding,[],[f54,f57])).
% 7.73/1.48  
% 7.73/1.48  fof(f3,axiom,(
% 7.73/1.48    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 7.73/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.48  
% 7.73/1.48  fof(f27,plain,(
% 7.73/1.48    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.73/1.48    inference(nnf_transformation,[],[f3])).
% 7.73/1.48  
% 7.73/1.48  fof(f28,plain,(
% 7.73/1.48    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.73/1.48    inference(flattening,[],[f27])).
% 7.73/1.48  
% 7.73/1.48  fof(f29,plain,(
% 7.73/1.48    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.73/1.48    inference(rectify,[],[f28])).
% 7.73/1.48  
% 7.73/1.48  fof(f30,plain,(
% 7.73/1.48    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 7.73/1.48    introduced(choice_axiom,[])).
% 7.73/1.48  
% 7.73/1.48  fof(f31,plain,(
% 7.73/1.48    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.73/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).
% 7.73/1.48  
% 7.73/1.48  fof(f46,plain,(
% 7.73/1.48    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 7.73/1.48    inference(cnf_transformation,[],[f31])).
% 7.73/1.48  
% 7.73/1.48  fof(f72,plain,(
% 7.73/1.48    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) != X2) )),
% 7.73/1.48    inference(definition_unfolding,[],[f46,f68])).
% 7.73/1.48  
% 7.73/1.48  fof(f77,plain,(
% 7.73/1.48    ( ! [X4,X0,X1] : (r2_hidden(X4,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)))) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 7.73/1.48    inference(equality_resolution,[],[f72])).
% 7.73/1.48  
% 7.73/1.48  fof(f67,plain,(
% 7.73/1.48    ~r2_hidden(sK5,k3_subset_1(sK3,sK4))),
% 7.73/1.48    inference(cnf_transformation,[],[f38])).
% 7.73/1.48  
% 7.73/1.48  fof(f1,axiom,(
% 7.73/1.48    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 7.73/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.48  
% 7.73/1.48  fof(f19,plain,(
% 7.73/1.48    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 7.73/1.48    inference(nnf_transformation,[],[f1])).
% 7.73/1.48  
% 7.73/1.48  fof(f20,plain,(
% 7.73/1.48    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 7.73/1.48    inference(rectify,[],[f19])).
% 7.73/1.48  
% 7.73/1.48  fof(f21,plain,(
% 7.73/1.48    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 7.73/1.48    introduced(choice_axiom,[])).
% 7.73/1.48  
% 7.73/1.48  fof(f22,plain,(
% 7.73/1.48    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 7.73/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f21])).
% 7.73/1.48  
% 7.73/1.48  fof(f39,plain,(
% 7.73/1.48    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 7.73/1.48    inference(cnf_transformation,[],[f22])).
% 7.73/1.48  
% 7.73/1.48  fof(f47,plain,(
% 7.73/1.48    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 7.73/1.48    inference(cnf_transformation,[],[f31])).
% 7.73/1.48  
% 7.73/1.48  fof(f71,plain,(
% 7.73/1.48    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) = X2 | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 7.73/1.48    inference(definition_unfolding,[],[f47,f68])).
% 7.73/1.48  
% 7.73/1.48  fof(f48,plain,(
% 7.73/1.48    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 7.73/1.48    inference(cnf_transformation,[],[f31])).
% 7.73/1.48  
% 7.73/1.48  fof(f70,plain,(
% 7.73/1.48    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) = X2 | ~r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 7.73/1.48    inference(definition_unfolding,[],[f48,f68])).
% 7.73/1.48  
% 7.73/1.48  fof(f4,axiom,(
% 7.73/1.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.73/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.48  
% 7.73/1.48  fof(f32,plain,(
% 7.73/1.48    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.73/1.48    inference(nnf_transformation,[],[f4])).
% 7.73/1.48  
% 7.73/1.48  fof(f33,plain,(
% 7.73/1.48    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.73/1.48    inference(flattening,[],[f32])).
% 7.73/1.48  
% 7.73/1.48  fof(f51,plain,(
% 7.73/1.48    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 7.73/1.48    inference(cnf_transformation,[],[f33])).
% 7.73/1.48  
% 7.73/1.48  fof(f80,plain,(
% 7.73/1.48    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.73/1.48    inference(equality_resolution,[],[f51])).
% 7.73/1.48  
% 7.73/1.48  fof(f52,plain,(
% 7.73/1.48    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.73/1.48    inference(cnf_transformation,[],[f33])).
% 7.73/1.48  
% 7.73/1.48  fof(f10,axiom,(
% 7.73/1.48    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 7.73/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.48  
% 7.73/1.48  fof(f15,plain,(
% 7.73/1.48    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 7.73/1.48    inference(ennf_transformation,[],[f10])).
% 7.73/1.48  
% 7.73/1.48  fof(f34,plain,(
% 7.73/1.48    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 7.73/1.48    inference(nnf_transformation,[],[f15])).
% 7.73/1.48  
% 7.73/1.48  fof(f58,plain,(
% 7.73/1.48    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 7.73/1.48    inference(cnf_transformation,[],[f34])).
% 7.73/1.48  
% 7.73/1.48  fof(f65,plain,(
% 7.73/1.48    m1_subset_1(sK5,sK3)),
% 7.73/1.48    inference(cnf_transformation,[],[f38])).
% 7.73/1.48  
% 7.73/1.48  fof(f50,plain,(
% 7.73/1.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.73/1.48    inference(cnf_transformation,[],[f33])).
% 7.73/1.48  
% 7.73/1.48  fof(f81,plain,(
% 7.73/1.48    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.73/1.48    inference(equality_resolution,[],[f50])).
% 7.73/1.48  
% 7.73/1.48  fof(f66,plain,(
% 7.73/1.48    ~r2_hidden(sK5,sK4)),
% 7.73/1.48    inference(cnf_transformation,[],[f38])).
% 7.73/1.48  
% 7.73/1.48  fof(f63,plain,(
% 7.73/1.48    k1_xboole_0 != sK3),
% 7.73/1.48    inference(cnf_transformation,[],[f38])).
% 7.73/1.48  
% 7.73/1.48  cnf(c_25,negated_conjecture,
% 7.73/1.48      ( m1_subset_1(sK4,k1_zfmisc_1(sK3)) ),
% 7.73/1.48      inference(cnf_transformation,[],[f64]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_978,plain,
% 7.73/1.48      ( m1_subset_1(sK4,k1_zfmisc_1(sK3)) = iProver_top ),
% 7.73/1.48      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_21,plain,
% 7.73/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.73/1.48      | k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X0),k2_xboole_0(X1,X0))) = k3_subset_1(X1,X0) ),
% 7.73/1.48      inference(cnf_transformation,[],[f76]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_982,plain,
% 7.73/1.48      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) = k3_subset_1(X0,X1)
% 7.73/1.48      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 7.73/1.48      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_1931,plain,
% 7.73/1.48      ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(sK3,sK4),k2_xboole_0(sK3,sK4))) = k3_subset_1(sK3,sK4) ),
% 7.73/1.48      inference(superposition,[status(thm)],[c_978,c_982]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_15,plain,
% 7.73/1.48      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.73/1.48      inference(cnf_transformation,[],[f55]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_16,plain,
% 7.73/1.48      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 7.73/1.48      inference(cnf_transformation,[],[f56]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_14,plain,
% 7.73/1.48      ( k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k2_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 7.73/1.48      inference(cnf_transformation,[],[f75]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_1013,plain,
% 7.73/1.48      ( k5_xboole_0(X0,k2_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 7.73/1.48      inference(light_normalisation,[status(thm)],[c_14,c_15]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_1284,plain,
% 7.73/1.48      ( k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0))) = k1_xboole_0 ),
% 7.73/1.48      inference(superposition,[status(thm)],[c_16,c_1013]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_1514,plain,
% 7.73/1.48      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k2_xboole_0(X0,k1_xboole_0))) = k1_xboole_0 ),
% 7.73/1.48      inference(superposition,[status(thm)],[c_15,c_1284]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_1282,plain,
% 7.73/1.48      ( k5_xboole_0(X0,k5_xboole_0(k2_xboole_0(X0,k1_xboole_0),X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 7.73/1.48      inference(superposition,[status(thm)],[c_1013,c_16]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_1711,plain,
% 7.73/1.48      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k2_xboole_0(k2_xboole_0(X0,k1_xboole_0),k1_xboole_0))) = k5_xboole_0(X0,k1_xboole_0) ),
% 7.73/1.48      inference(superposition,[status(thm)],[c_1514,c_1282]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_1401,plain,
% 7.73/1.48      ( k5_xboole_0(k1_xboole_0,k2_xboole_0(k2_xboole_0(X0,k1_xboole_0),k1_xboole_0)) = k5_xboole_0(X0,k1_xboole_0) ),
% 7.73/1.48      inference(superposition,[status(thm)],[c_1013,c_1282]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_1423,plain,
% 7.73/1.48      ( k5_xboole_0(k1_xboole_0,k2_xboole_0(k2_xboole_0(X0,k1_xboole_0),k1_xboole_0)) = X0 ),
% 7.73/1.48      inference(light_normalisation,[status(thm)],[c_1401,c_15]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_1713,plain,
% 7.73/1.48      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 7.73/1.48      inference(light_normalisation,[status(thm)],[c_1711,c_15,c_1423]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_1749,plain,
% 7.73/1.48      ( k2_xboole_0(k2_xboole_0(X0,k1_xboole_0),k1_xboole_0) = X0 ),
% 7.73/1.48      inference(superposition,[status(thm)],[c_1713,c_1423]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_1405,plain,
% 7.73/1.48      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k2_xboole_0(X0,k1_xboole_0),X1),X2)) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),X2) ),
% 7.73/1.48      inference(superposition,[status(thm)],[c_1282,c_16]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_2800,plain,
% 7.73/1.48      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k2_xboole_0(X0,k1_xboole_0),X1),X2)) = k5_xboole_0(X1,X2) ),
% 7.73/1.48      inference(demodulation,[status(thm)],[c_1405,c_1713]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_2817,plain,
% 7.73/1.48      ( k5_xboole_0(k2_xboole_0(X0,k1_xboole_0),k5_xboole_0(k5_xboole_0(X0,X1),X2)) = k5_xboole_0(X1,X2) ),
% 7.73/1.48      inference(superposition,[status(thm)],[c_1749,c_2800]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_2849,plain,
% 7.73/1.48      ( k5_xboole_0(k2_xboole_0(X0,k1_xboole_0),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X1,X2) ),
% 7.73/1.48      inference(light_normalisation,[status(thm)],[c_2817,c_16]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_3865,plain,
% 7.73/1.48      ( k5_xboole_0(k2_xboole_0(sK3,k1_xboole_0),k3_subset_1(sK3,sK4)) = k5_xboole_0(k5_xboole_0(sK3,sK4),k2_xboole_0(sK3,sK4)) ),
% 7.73/1.48      inference(superposition,[status(thm)],[c_1931,c_2849]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_2107,plain,
% 7.73/1.48      ( k5_xboole_0(sK3,k5_xboole_0(sK3,k5_xboole_0(sK4,k2_xboole_0(sK3,sK4)))) = k3_subset_1(sK3,sK4) ),
% 7.73/1.48      inference(superposition,[status(thm)],[c_16,c_1931]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_3870,plain,
% 7.73/1.48      ( k5_xboole_0(k2_xboole_0(sK3,k1_xboole_0),k3_subset_1(sK3,sK4)) = k5_xboole_0(sK3,k5_xboole_0(sK4,k2_xboole_0(sK3,sK4))) ),
% 7.73/1.48      inference(superposition,[status(thm)],[c_2107,c_2849]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_4003,plain,
% 7.73/1.48      ( k5_xboole_0(sK3,k5_xboole_0(sK4,k2_xboole_0(sK3,sK4))) = k5_xboole_0(k5_xboole_0(sK3,sK4),k2_xboole_0(sK3,sK4)) ),
% 7.73/1.48      inference(light_normalisation,[status(thm)],[c_3865,c_3870]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_8,plain,
% 7.73/1.48      ( ~ r2_hidden(X0,X1)
% 7.73/1.48      | r2_hidden(X0,X2)
% 7.73/1.48      | r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)))) ),
% 7.73/1.48      inference(cnf_transformation,[],[f77]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_990,plain,
% 7.73/1.48      ( r2_hidden(X0,X1) != iProver_top
% 7.73/1.48      | r2_hidden(X0,X2) = iProver_top
% 7.73/1.48      | r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)))) = iProver_top ),
% 7.73/1.48      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_10969,plain,
% 7.73/1.48      ( r2_hidden(X0,k5_xboole_0(sK3,k5_xboole_0(sK3,k5_xboole_0(sK4,k2_xboole_0(sK3,sK4))))) = iProver_top
% 7.73/1.48      | r2_hidden(X0,sK4) = iProver_top
% 7.73/1.48      | r2_hidden(X0,sK3) != iProver_top ),
% 7.73/1.48      inference(superposition,[status(thm)],[c_4003,c_990]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_11253,plain,
% 7.73/1.48      ( r2_hidden(X0,k3_subset_1(sK3,sK4)) = iProver_top
% 7.73/1.48      | r2_hidden(X0,sK4) = iProver_top
% 7.73/1.48      | r2_hidden(X0,sK3) != iProver_top ),
% 7.73/1.48      inference(light_normalisation,[status(thm)],[c_10969,c_2107]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_22,negated_conjecture,
% 7.73/1.48      ( ~ r2_hidden(sK5,k3_subset_1(sK3,sK4)) ),
% 7.73/1.48      inference(cnf_transformation,[],[f67]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_981,plain,
% 7.73/1.48      ( r2_hidden(sK5,k3_subset_1(sK3,sK4)) != iProver_top ),
% 7.73/1.48      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_13820,plain,
% 7.73/1.48      ( r2_hidden(sK5,sK4) = iProver_top
% 7.73/1.48      | r2_hidden(sK5,sK3) != iProver_top ),
% 7.73/1.48      inference(superposition,[status(thm)],[c_11253,c_981]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_1,plain,
% 7.73/1.48      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 7.73/1.48      inference(cnf_transformation,[],[f39]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_5168,plain,
% 7.73/1.48      ( ~ r2_hidden(sK2(X0,X1,X2),X2) | ~ v1_xboole_0(X2) ),
% 7.73/1.48      inference(instantiation,[status(thm)],[c_1]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_12642,plain,
% 7.73/1.48      ( ~ r2_hidden(sK2(X0,X1,sK3),sK3) | ~ v1_xboole_0(sK3) ),
% 7.73/1.48      inference(instantiation,[status(thm)],[c_5168]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_12643,plain,
% 7.73/1.48      ( r2_hidden(sK2(X0,X1,sK3),sK3) != iProver_top
% 7.73/1.48      | v1_xboole_0(sK3) != iProver_top ),
% 7.73/1.48      inference(predicate_to_equality,[status(thm)],[c_12642]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_12645,plain,
% 7.73/1.48      ( r2_hidden(sK2(k1_xboole_0,k1_xboole_0,sK3),sK3) != iProver_top
% 7.73/1.48      | v1_xboole_0(sK3) != iProver_top ),
% 7.73/1.48      inference(instantiation,[status(thm)],[c_12643]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_612,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_10930,plain,
% 7.73/1.48      ( k5_xboole_0(X0,X1) != X2
% 7.73/1.48      | k1_xboole_0 != X2
% 7.73/1.48      | k1_xboole_0 = k5_xboole_0(X0,X1) ),
% 7.73/1.48      inference(instantiation,[status(thm)],[c_612]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_10931,plain,
% 7.73/1.48      ( k5_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 7.73/1.48      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)
% 7.73/1.48      | k1_xboole_0 != k1_xboole_0 ),
% 7.73/1.48      inference(instantiation,[status(thm)],[c_10930]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_614,plain,
% 7.73/1.48      ( X0 != X1 | X2 != X3 | k5_xboole_0(X0,X2) = k5_xboole_0(X1,X3) ),
% 7.73/1.48      theory(equality) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_3672,plain,
% 7.73/1.48      ( X0 != X1
% 7.73/1.48      | k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X2),k2_xboole_0(X0,X2))) = k5_xboole_0(X1,X3)
% 7.73/1.48      | k5_xboole_0(k5_xboole_0(X0,X2),k2_xboole_0(X0,X2)) != X3 ),
% 7.73/1.48      inference(instantiation,[status(thm)],[c_614]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_3674,plain,
% 7.73/1.48      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k2_xboole_0(k1_xboole_0,k1_xboole_0)) != k1_xboole_0
% 7.73/1.48      | k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k2_xboole_0(k1_xboole_0,k1_xboole_0))) = k5_xboole_0(k1_xboole_0,k1_xboole_0)
% 7.73/1.48      | k1_xboole_0 != k1_xboole_0 ),
% 7.73/1.48      inference(instantiation,[status(thm)],[c_3672]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_3083,plain,
% 7.73/1.48      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) != X2
% 7.73/1.48      | k1_xboole_0 != X2
% 7.73/1.48      | k1_xboole_0 = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) ),
% 7.73/1.48      inference(instantiation,[status(thm)],[c_612]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_3671,plain,
% 7.73/1.48      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) != k5_xboole_0(X2,X3)
% 7.73/1.48      | k1_xboole_0 != k5_xboole_0(X2,X3)
% 7.73/1.48      | k1_xboole_0 = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) ),
% 7.73/1.48      inference(instantiation,[status(thm)],[c_3083]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_3673,plain,
% 7.73/1.48      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k2_xboole_0(k1_xboole_0,k1_xboole_0))) != k5_xboole_0(k1_xboole_0,k1_xboole_0)
% 7.73/1.48      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k2_xboole_0(k1_xboole_0,k1_xboole_0)))
% 7.73/1.48      | k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 7.73/1.48      inference(instantiation,[status(thm)],[c_3671]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_1447,plain,
% 7.73/1.48      ( X0 != X1 | X0 = sK3 | sK3 != X1 ),
% 7.73/1.48      inference(instantiation,[status(thm)],[c_612]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_2487,plain,
% 7.73/1.48      ( X0 != k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)))
% 7.73/1.48      | X0 = sK3
% 7.73/1.48      | sK3 != k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))) ),
% 7.73/1.48      inference(instantiation,[status(thm)],[c_1447]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_2490,plain,
% 7.73/1.48      ( sK3 != k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k2_xboole_0(k1_xboole_0,k1_xboole_0)))
% 7.73/1.48      | k1_xboole_0 != k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k2_xboole_0(k1_xboole_0,k1_xboole_0)))
% 7.73/1.48      | k1_xboole_0 = sK3 ),
% 7.73/1.48      inference(instantiation,[status(thm)],[c_2487]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_7,plain,
% 7.73/1.48      ( r2_hidden(sK2(X0,X1,X2),X0)
% 7.73/1.48      | r2_hidden(sK2(X0,X1,X2),X2)
% 7.73/1.48      | k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) = X2 ),
% 7.73/1.48      inference(cnf_transformation,[],[f71]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_1434,plain,
% 7.73/1.48      ( r2_hidden(sK2(X0,X1,sK3),X0)
% 7.73/1.48      | r2_hidden(sK2(X0,X1,sK3),sK3)
% 7.73/1.48      | k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) = sK3 ),
% 7.73/1.48      inference(instantiation,[status(thm)],[c_7]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_1441,plain,
% 7.73/1.48      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) = sK3
% 7.73/1.48      | r2_hidden(sK2(X0,X1,sK3),X0) = iProver_top
% 7.73/1.48      | r2_hidden(sK2(X0,X1,sK3),sK3) = iProver_top ),
% 7.73/1.48      inference(predicate_to_equality,[status(thm)],[c_1434]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_1443,plain,
% 7.73/1.48      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k2_xboole_0(k1_xboole_0,k1_xboole_0))) = sK3
% 7.73/1.48      | r2_hidden(sK2(k1_xboole_0,k1_xboole_0,sK3),sK3) = iProver_top
% 7.73/1.48      | r2_hidden(sK2(k1_xboole_0,k1_xboole_0,sK3),k1_xboole_0) = iProver_top ),
% 7.73/1.48      inference(instantiation,[status(thm)],[c_1441]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_6,plain,
% 7.73/1.48      ( ~ r2_hidden(sK2(X0,X1,X2),X1)
% 7.73/1.48      | r2_hidden(sK2(X0,X1,X2),X2)
% 7.73/1.48      | k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) = X2 ),
% 7.73/1.48      inference(cnf_transformation,[],[f70]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_1435,plain,
% 7.73/1.48      ( ~ r2_hidden(sK2(X0,X1,sK3),X1)
% 7.73/1.48      | r2_hidden(sK2(X0,X1,sK3),sK3)
% 7.73/1.48      | k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) = sK3 ),
% 7.73/1.48      inference(instantiation,[status(thm)],[c_6]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_1437,plain,
% 7.73/1.48      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) = sK3
% 7.73/1.48      | r2_hidden(sK2(X0,X1,sK3),X1) != iProver_top
% 7.73/1.48      | r2_hidden(sK2(X0,X1,sK3),sK3) = iProver_top ),
% 7.73/1.48      inference(predicate_to_equality,[status(thm)],[c_1435]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_1439,plain,
% 7.73/1.48      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k2_xboole_0(k1_xboole_0,k1_xboole_0))) = sK3
% 7.73/1.48      | r2_hidden(sK2(k1_xboole_0,k1_xboole_0,sK3),sK3) = iProver_top
% 7.73/1.48      | r2_hidden(sK2(k1_xboole_0,k1_xboole_0,sK3),k1_xboole_0) != iProver_top ),
% 7.73/1.48      inference(instantiation,[status(thm)],[c_1437]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_1192,plain,
% 7.73/1.48      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 7.73/1.48      inference(instantiation,[status(thm)],[c_612]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_1272,plain,
% 7.73/1.48      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 7.73/1.48      inference(instantiation,[status(thm)],[c_1192]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_1432,plain,
% 7.73/1.48      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) != sK3
% 7.73/1.48      | sK3 = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)))
% 7.73/1.48      | sK3 != sK3 ),
% 7.73/1.48      inference(instantiation,[status(thm)],[c_1272]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_1436,plain,
% 7.73/1.48      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k2_xboole_0(k1_xboole_0,k1_xboole_0))) != sK3
% 7.73/1.48      | sK3 = k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k2_xboole_0(k1_xboole_0,k1_xboole_0)))
% 7.73/1.48      | sK3 != sK3 ),
% 7.73/1.48      inference(instantiation,[status(thm)],[c_1432]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_12,plain,
% 7.73/1.48      ( r1_tarski(X0,X0) ),
% 7.73/1.48      inference(cnf_transformation,[],[f80]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_1265,plain,
% 7.73/1.48      ( r1_tarski(sK3,sK3) ),
% 7.73/1.48      inference(instantiation,[status(thm)],[c_12]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_11,plain,
% 7.73/1.48      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 7.73/1.48      inference(cnf_transformation,[],[f52]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_1193,plain,
% 7.73/1.48      ( ~ r1_tarski(X0,sK3) | ~ r1_tarski(sK3,X0) | sK3 = X0 ),
% 7.73/1.48      inference(instantiation,[status(thm)],[c_11]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_1264,plain,
% 7.73/1.48      ( ~ r1_tarski(sK3,sK3) | sK3 = sK3 ),
% 7.73/1.48      inference(instantiation,[status(thm)],[c_1193]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_20,plain,
% 7.73/1.48      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 7.73/1.48      inference(cnf_transformation,[],[f58]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_24,negated_conjecture,
% 7.73/1.48      ( m1_subset_1(sK5,sK3) ),
% 7.73/1.48      inference(cnf_transformation,[],[f65]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_286,plain,
% 7.73/1.48      ( r2_hidden(X0,X1) | v1_xboole_0(X1) | sK3 != X1 | sK5 != X0 ),
% 7.73/1.48      inference(resolution_lifted,[status(thm)],[c_20,c_24]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_287,plain,
% 7.73/1.48      ( r2_hidden(sK5,sK3) | v1_xboole_0(sK3) ),
% 7.73/1.48      inference(unflattening,[status(thm)],[c_286]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_288,plain,
% 7.73/1.48      ( r2_hidden(sK5,sK3) = iProver_top
% 7.73/1.48      | v1_xboole_0(sK3) = iProver_top ),
% 7.73/1.48      inference(predicate_to_equality,[status(thm)],[c_287]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_52,plain,
% 7.73/1.48      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 7.73/1.48      | k1_xboole_0 = k1_xboole_0 ),
% 7.73/1.48      inference(instantiation,[status(thm)],[c_11]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_13,plain,
% 7.73/1.48      ( r1_tarski(X0,X0) ),
% 7.73/1.48      inference(cnf_transformation,[],[f81]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_48,plain,
% 7.73/1.48      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 7.73/1.48      inference(instantiation,[status(thm)],[c_13]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_46,plain,
% 7.73/1.48      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k2_xboole_0(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
% 7.73/1.48      inference(instantiation,[status(thm)],[c_14]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_45,plain,
% 7.73/1.48      ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 7.73/1.48      inference(instantiation,[status(thm)],[c_15]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_23,negated_conjecture,
% 7.73/1.48      ( ~ r2_hidden(sK5,sK4) ),
% 7.73/1.48      inference(cnf_transformation,[],[f66]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_29,plain,
% 7.73/1.48      ( r2_hidden(sK5,sK4) != iProver_top ),
% 7.73/1.48      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_26,negated_conjecture,
% 7.73/1.48      ( k1_xboole_0 != sK3 ),
% 7.73/1.48      inference(cnf_transformation,[],[f63]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(contradiction,plain,
% 7.73/1.48      ( $false ),
% 7.73/1.48      inference(minisat,
% 7.73/1.48                [status(thm)],
% 7.73/1.48                [c_13820,c_12645,c_10931,c_3674,c_3673,c_2490,c_1443,
% 7.73/1.48                 c_1439,c_1436,c_1265,c_1264,c_288,c_52,c_48,c_46,c_45,
% 7.73/1.48                 c_29,c_26]) ).
% 7.73/1.48  
% 7.73/1.48  
% 7.73/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.73/1.48  
% 7.73/1.48  ------                               Statistics
% 7.73/1.48  
% 7.73/1.48  ------ General
% 7.73/1.48  
% 7.73/1.48  abstr_ref_over_cycles:                  0
% 7.73/1.48  abstr_ref_under_cycles:                 0
% 7.73/1.48  gc_basic_clause_elim:                   0
% 7.73/1.48  forced_gc_time:                         0
% 7.73/1.48  parsing_time:                           0.008
% 7.73/1.48  unif_index_cands_time:                  0.
% 7.73/1.48  unif_index_add_time:                    0.
% 7.73/1.48  orderings_time:                         0.
% 7.73/1.48  out_proof_time:                         0.011
% 7.73/1.48  total_time:                             0.601
% 7.73/1.48  num_of_symbols:                         46
% 7.73/1.48  num_of_terms:                           18723
% 7.73/1.48  
% 7.73/1.48  ------ Preprocessing
% 7.73/1.48  
% 7.73/1.48  num_of_splits:                          0
% 7.73/1.48  num_of_split_atoms:                     0
% 7.73/1.48  num_of_reused_defs:                     0
% 7.73/1.48  num_eq_ax_congr_red:                    30
% 7.73/1.48  num_of_sem_filtered_clauses:            1
% 7.73/1.48  num_of_subtypes:                        0
% 7.73/1.48  monotx_restored_types:                  0
% 7.73/1.48  sat_num_of_epr_types:                   0
% 7.73/1.48  sat_num_of_non_cyclic_types:            0
% 7.73/1.48  sat_guarded_non_collapsed_types:        0
% 7.73/1.48  num_pure_diseq_elim:                    0
% 7.73/1.48  simp_replaced_by:                       0
% 7.73/1.48  res_preprocessed:                       121
% 7.73/1.48  prep_upred:                             0
% 7.73/1.48  prep_unflattend:                        28
% 7.73/1.48  smt_new_axioms:                         0
% 7.73/1.48  pred_elim_cands:                        4
% 7.73/1.48  pred_elim:                              0
% 7.73/1.48  pred_elim_cl:                           0
% 7.73/1.48  pred_elim_cycles:                       2
% 7.73/1.48  merged_defs:                            0
% 7.73/1.48  merged_defs_ncl:                        0
% 7.73/1.48  bin_hyper_res:                          0
% 7.73/1.48  prep_cycles:                            4
% 7.73/1.48  pred_elim_time:                         0.004
% 7.73/1.48  splitting_time:                         0.
% 7.73/1.48  sem_filter_time:                        0.
% 7.73/1.48  monotx_time:                            0.
% 7.73/1.48  subtype_inf_time:                       0.
% 7.73/1.48  
% 7.73/1.48  ------ Problem properties
% 7.73/1.48  
% 7.73/1.48  clauses:                                26
% 7.73/1.48  conjectures:                            5
% 7.73/1.48  epr:                                    11
% 7.73/1.48  horn:                                   19
% 7.73/1.48  ground:                                 5
% 7.73/1.48  unary:                                  9
% 7.73/1.48  binary:                                 8
% 7.73/1.48  lits:                                   53
% 7.73/1.48  lits_eq:                                9
% 7.73/1.48  fd_pure:                                0
% 7.73/1.48  fd_pseudo:                              0
% 7.73/1.48  fd_cond:                                0
% 7.73/1.48  fd_pseudo_cond:                         4
% 7.73/1.48  ac_symbols:                             0
% 7.73/1.48  
% 7.73/1.48  ------ Propositional Solver
% 7.73/1.48  
% 7.73/1.48  prop_solver_calls:                      30
% 7.73/1.48  prop_fast_solver_calls:                 704
% 7.73/1.48  smt_solver_calls:                       0
% 7.73/1.48  smt_fast_solver_calls:                  0
% 7.73/1.48  prop_num_of_clauses:                    4106
% 7.73/1.48  prop_preprocess_simplified:             7570
% 7.73/1.48  prop_fo_subsumed:                       1
% 7.73/1.48  prop_solver_time:                       0.
% 7.73/1.48  smt_solver_time:                        0.
% 7.73/1.48  smt_fast_solver_time:                   0.
% 7.73/1.48  prop_fast_solver_time:                  0.
% 7.73/1.48  prop_unsat_core_time:                   0.
% 7.73/1.48  
% 7.73/1.48  ------ QBF
% 7.73/1.48  
% 7.73/1.48  qbf_q_res:                              0
% 7.73/1.48  qbf_num_tautologies:                    0
% 7.73/1.48  qbf_prep_cycles:                        0
% 7.73/1.48  
% 7.73/1.48  ------ BMC1
% 7.73/1.48  
% 7.73/1.48  bmc1_current_bound:                     -1
% 7.73/1.48  bmc1_last_solved_bound:                 -1
% 7.73/1.48  bmc1_unsat_core_size:                   -1
% 7.73/1.48  bmc1_unsat_core_parents_size:           -1
% 7.73/1.48  bmc1_merge_next_fun:                    0
% 7.73/1.48  bmc1_unsat_core_clauses_time:           0.
% 7.73/1.48  
% 7.73/1.48  ------ Instantiation
% 7.73/1.48  
% 7.73/1.48  inst_num_of_clauses:                    730
% 7.73/1.48  inst_num_in_passive:                    259
% 7.73/1.48  inst_num_in_active:                     340
% 7.73/1.48  inst_num_in_unprocessed:                131
% 7.73/1.48  inst_num_of_loops:                      490
% 7.73/1.48  inst_num_of_learning_restarts:          0
% 7.73/1.48  inst_num_moves_active_passive:          145
% 7.73/1.48  inst_lit_activity:                      0
% 7.73/1.48  inst_lit_activity_moves:                0
% 7.73/1.48  inst_num_tautologies:                   0
% 7.73/1.48  inst_num_prop_implied:                  0
% 7.73/1.48  inst_num_existing_simplified:           0
% 7.73/1.48  inst_num_eq_res_simplified:             0
% 7.73/1.48  inst_num_child_elim:                    0
% 7.73/1.48  inst_num_of_dismatching_blockings:      195
% 7.73/1.48  inst_num_of_non_proper_insts:           647
% 7.73/1.48  inst_num_of_duplicates:                 0
% 7.73/1.48  inst_inst_num_from_inst_to_res:         0
% 7.73/1.48  inst_dismatching_checking_time:         0.
% 7.73/1.48  
% 7.73/1.48  ------ Resolution
% 7.73/1.48  
% 7.73/1.48  res_num_of_clauses:                     0
% 7.73/1.48  res_num_in_passive:                     0
% 7.73/1.48  res_num_in_active:                      0
% 7.73/1.48  res_num_of_loops:                       125
% 7.73/1.48  res_forward_subset_subsumed:            69
% 7.73/1.48  res_backward_subset_subsumed:           0
% 7.73/1.48  res_forward_subsumed:                   0
% 7.73/1.48  res_backward_subsumed:                  0
% 7.73/1.48  res_forward_subsumption_resolution:     0
% 7.73/1.48  res_backward_subsumption_resolution:    0
% 7.73/1.48  res_clause_to_clause_subsumption:       4334
% 7.73/1.48  res_orphan_elimination:                 0
% 7.73/1.48  res_tautology_del:                      80
% 7.73/1.48  res_num_eq_res_simplified:              0
% 7.73/1.48  res_num_sel_changes:                    0
% 7.73/1.48  res_moves_from_active_to_pass:          0
% 7.73/1.48  
% 7.73/1.48  ------ Superposition
% 7.73/1.48  
% 7.73/1.48  sup_time_total:                         0.
% 7.73/1.48  sup_time_generating:                    0.
% 7.73/1.48  sup_time_sim_full:                      0.
% 7.73/1.48  sup_time_sim_immed:                     0.
% 7.73/1.48  
% 7.73/1.48  sup_num_of_clauses:                     954
% 7.73/1.48  sup_num_in_active:                      71
% 7.73/1.48  sup_num_in_passive:                     883
% 7.73/1.48  sup_num_of_loops:                       97
% 7.73/1.48  sup_fw_superposition:                   1307
% 7.73/1.48  sup_bw_superposition:                   953
% 7.73/1.48  sup_immediate_simplified:               1438
% 7.73/1.48  sup_given_eliminated:                   15
% 7.73/1.48  comparisons_done:                       0
% 7.73/1.48  comparisons_avoided:                    0
% 7.73/1.48  
% 7.73/1.48  ------ Simplifications
% 7.73/1.48  
% 7.73/1.48  
% 7.73/1.48  sim_fw_subset_subsumed:                 6
% 7.73/1.48  sim_bw_subset_subsumed:                 0
% 7.73/1.48  sim_fw_subsumed:                        159
% 7.73/1.48  sim_bw_subsumed:                        56
% 7.73/1.48  sim_fw_subsumption_res:                 0
% 7.73/1.48  sim_bw_subsumption_res:                 0
% 7.73/1.48  sim_tautology_del:                      24
% 7.73/1.48  sim_eq_tautology_del:                   345
% 7.73/1.48  sim_eq_res_simp:                        1
% 7.73/1.48  sim_fw_demodulated:                     912
% 7.73/1.48  sim_bw_demodulated:                     112
% 7.73/1.48  sim_light_normalised:                   595
% 7.73/1.48  sim_joinable_taut:                      0
% 7.73/1.48  sim_joinable_simp:                      0
% 7.73/1.48  sim_ac_normalised:                      0
% 7.73/1.48  sim_smt_subsumption:                    0
% 7.73/1.48  
%------------------------------------------------------------------------------
