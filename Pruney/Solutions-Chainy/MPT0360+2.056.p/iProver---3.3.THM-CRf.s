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
% DateTime   : Thu Dec  3 11:40:23 EST 2020

% Result     : Theorem 51.80s
% Output     : CNFRefutation 51.80s
% Verified   : 
% Statistics : Number of formulae       :  176 (3618 expanded)
%              Number of clauses        :  118 ( 969 expanded)
%              Number of leaves         :   14 ( 864 expanded)
%              Depth                    :   26
%              Number of atoms          :  429 (13259 expanded)
%              Number of equality atoms :  245 (4148 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
          & r1_tarski(X1,X2) )
       => k1_xboole_0 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X0))
       => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
            & r1_tarski(X1,X2) )
         => k1_xboole_0 = X1 ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f16])).

fof(f24,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != X1
        & r1_tarski(X1,k3_subset_1(X0,X2))
        & r1_tarski(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X0)) )
   => ( k1_xboole_0 != sK2
      & r1_tarski(sK2,k3_subset_1(sK1,sK3))
      & r1_tarski(sK2,sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( k1_xboole_0 != sK2
    & r1_tarski(sK2,k3_subset_1(sK1,sK3))
    & r1_tarski(sK2,sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f17,f24])).

fof(f44,plain,(
    r1_tarski(sK2,k3_subset_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f25])).

fof(f42,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f41,f32])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
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

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f20,plain,(
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
    inference(rectify,[],[f19])).

fof(f21,plain,(
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

fof(f22,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f21])).

fof(f28,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f28,f32])).

fof(f60,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f50])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f31,f32])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f29,f32])).

fof(f26,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f52,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f26,f32])).

fof(f62,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f52])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f37,f32,f32])).

fof(f27,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f51,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f27,f32])).

fof(f61,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f51])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f30,f32])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ) ),
    inference(definition_unfolding,[],[f34,f32])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f40,f32])).

fof(f43,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f38,f32])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f55,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f36,f32])).

fof(f45,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_16,negated_conjecture,
    ( r1_tarski(sK2,k3_subset_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_574,plain,
    ( r1_tarski(sK2,k3_subset_1(sK1,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_572,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_575,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3218,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)) = k3_subset_1(sK1,sK3) ),
    inference(superposition,[status(thm)],[c_572,c_575])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_584,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_6843,plain,
    ( r2_hidden(X0,k3_subset_1(sK1,sK3)) = iProver_top
    | r2_hidden(X0,sK3) = iProver_top
    | r2_hidden(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3218,c_584])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X0)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(sK0(X0,X1,X2),X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_587,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_8928,plain,
    ( k5_xboole_0(k3_subset_1(sK1,sK3),k3_xboole_0(k3_subset_1(sK1,sK3),X0)) = X1
    | r2_hidden(sK0(k3_subset_1(sK1,sK3),X0,X1),X1) != iProver_top
    | r2_hidden(sK0(k3_subset_1(sK1,sK3),X0,X1),X0) = iProver_top
    | r2_hidden(sK0(k3_subset_1(sK1,sK3),X0,X1),sK3) = iProver_top
    | r2_hidden(sK0(k3_subset_1(sK1,sK3),X0,X1),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_6843,c_587])).

cnf(c_16154,plain,
    ( k5_xboole_0(k3_subset_1(sK1,sK3),k3_xboole_0(k3_subset_1(sK1,sK3),X0)) = k3_subset_1(sK1,sK3)
    | r2_hidden(sK0(k3_subset_1(sK1,sK3),X0,k3_subset_1(sK1,sK3)),X0) = iProver_top
    | r2_hidden(sK0(k3_subset_1(sK1,sK3),X0,k3_subset_1(sK1,sK3)),sK3) = iProver_top
    | r2_hidden(sK0(k3_subset_1(sK1,sK3),X0,k3_subset_1(sK1,sK3)),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_6843,c_8928])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_585,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_582,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3796,plain,
    ( r2_hidden(X0,k3_subset_1(sK1,sK3)) != iProver_top
    | r2_hidden(X0,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3218,c_582])).

cnf(c_7361,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(sK1,sK3)
    | r2_hidden(sK0(X0,X1,k3_subset_1(sK1,sK3)),X0) = iProver_top
    | r2_hidden(sK0(X0,X1,k3_subset_1(sK1,sK3)),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_585,c_3796])).

cnf(c_12732,plain,
    ( k5_xboole_0(k3_subset_1(sK1,sK3),k3_xboole_0(k3_subset_1(sK1,sK3),X0)) = k3_subset_1(sK1,sK3)
    | r2_hidden(sK0(k3_subset_1(sK1,sK3),X0,k3_subset_1(sK1,sK3)),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_7361,c_3796])).

cnf(c_16382,plain,
    ( r2_hidden(sK0(k3_subset_1(sK1,sK3),X0,k3_subset_1(sK1,sK3)),sK3) = iProver_top
    | r2_hidden(sK0(k3_subset_1(sK1,sK3),X0,k3_subset_1(sK1,sK3)),X0) = iProver_top
    | k5_xboole_0(k3_subset_1(sK1,sK3),k3_xboole_0(k3_subset_1(sK1,sK3),X0)) = k3_subset_1(sK1,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16154,c_12732])).

cnf(c_16383,plain,
    ( k5_xboole_0(k3_subset_1(sK1,sK3),k3_xboole_0(k3_subset_1(sK1,sK3),X0)) = k3_subset_1(sK1,sK3)
    | r2_hidden(sK0(k3_subset_1(sK1,sK3),X0,k3_subset_1(sK1,sK3)),X0) = iProver_top
    | r2_hidden(sK0(k3_subset_1(sK1,sK3),X0,k3_subset_1(sK1,sK3)),sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_16382])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2063,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_582])).

cnf(c_16401,plain,
    ( k5_xboole_0(k3_subset_1(sK1,sK3),k3_xboole_0(k3_subset_1(sK1,sK3),k3_xboole_0(X0,X1))) = k3_subset_1(sK1,sK3)
    | r2_hidden(sK0(k3_subset_1(sK1,sK3),k3_xboole_0(X0,X1),k3_subset_1(sK1,sK3)),X0) = iProver_top
    | r2_hidden(sK0(k3_subset_1(sK1,sK3),k3_xboole_0(X0,X1),k3_subset_1(sK1,sK3)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_16383,c_2063])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_583,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3800,plain,
    ( r2_hidden(X0,k3_subset_1(sK1,sK3)) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3218,c_583])).

cnf(c_7360,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(sK1,sK3)
    | r2_hidden(sK0(X0,X1,k3_subset_1(sK1,sK3)),X0) = iProver_top
    | r2_hidden(sK0(X0,X1,k3_subset_1(sK1,sK3)),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_585,c_3800])).

cnf(c_16393,plain,
    ( k5_xboole_0(k3_subset_1(sK1,sK3),k3_xboole_0(k3_subset_1(sK1,sK3),X0)) = k3_subset_1(sK1,sK3)
    | r2_hidden(sK0(k3_subset_1(sK1,sK3),X0,k3_subset_1(sK1,sK3)),X0) = iProver_top
    | r2_hidden(sK0(k3_subset_1(sK1,sK3),X0,k3_subset_1(sK1,sK3)),k3_subset_1(sK1,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_16383,c_7360])).

cnf(c_2,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_586,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_76321,plain,
    ( k5_xboole_0(k3_subset_1(sK1,sK3),k3_xboole_0(k3_subset_1(sK1,sK3),X0)) = k3_subset_1(sK1,sK3)
    | r2_hidden(sK0(k3_subset_1(sK1,sK3),X0,k3_subset_1(sK1,sK3)),k3_subset_1(sK1,sK3)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_16393,c_586])).

cnf(c_76328,plain,
    ( k5_xboole_0(k3_subset_1(sK1,sK3),k3_xboole_0(k3_subset_1(sK1,sK3),X0)) = k3_subset_1(sK1,sK3)
    | r2_hidden(sK0(k3_subset_1(sK1,sK3),X0,k3_subset_1(sK1,sK3)),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_76321,c_3800])).

cnf(c_83568,plain,
    ( k5_xboole_0(k3_subset_1(sK1,sK3),k3_xboole_0(k3_subset_1(sK1,sK3),k3_xboole_0(X0,X1))) = k3_subset_1(sK1,sK3)
    | r2_hidden(sK0(k3_subset_1(sK1,sK3),k3_xboole_0(X0,X1),k3_subset_1(sK1,sK3)),X0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_16401,c_76328])).

cnf(c_83612,plain,
    ( k5_xboole_0(k3_subset_1(sK1,sK3),k3_xboole_0(k3_subset_1(sK1,sK3),k3_xboole_0(sK3,X0))) = k3_subset_1(sK1,sK3) ),
    inference(superposition,[status(thm)],[c_83568,c_76328])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
    | r1_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_581,plain,
    ( r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top
    | r1_xboole_0(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_84521,plain,
    ( r1_tarski(X0,k3_subset_1(sK1,sK3)) != iProver_top
    | r1_xboole_0(X0,k3_xboole_0(sK3,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_83612,c_581])).

cnf(c_88268,plain,
    ( r1_xboole_0(sK2,k3_xboole_0(sK3,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_574,c_84521])).

cnf(c_857,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1))) = k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_0,c_0])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
    | ~ r1_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_576,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = iProver_top
    | r1_xboole_0(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_970,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k3_xboole_0(X1,X2)) = iProver_top
    | r1_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_576])).

cnf(c_2991,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k3_xboole_0(X1,k3_xboole_0(X1,X2))) = iProver_top
    | r1_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_857,c_970])).

cnf(c_88477,plain,
    ( r1_tarski(sK2,k3_xboole_0(sK3,k3_xboole_0(sK3,X0))) = iProver_top
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_88268,c_2991])).

cnf(c_17,negated_conjecture,
    ( r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_20,plain,
    ( r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_89424,plain,
    ( r1_tarski(sK2,k3_xboole_0(sK3,k3_xboole_0(sK3,X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_88477,c_20])).

cnf(c_9,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_579,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1792,plain,
    ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_579,c_581])).

cnf(c_12,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_577,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2406,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1792,c_577])).

cnf(c_2417,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2406,c_0])).

cnf(c_3222,plain,
    ( r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top
    | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_583])).

cnf(c_5339,plain,
    ( r2_hidden(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) != iProver_top
    | r2_hidden(X0,k3_xboole_0(k1_xboole_0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2417,c_3222])).

cnf(c_10,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_856,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_10,c_0])).

cnf(c_867,plain,
    ( k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_856,c_10])).

cnf(c_995,plain,
    ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_867,c_856])).

cnf(c_996,plain,
    ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_995,c_867])).

cnf(c_5342,plain,
    ( r2_hidden(X0,k3_xboole_0(k1_xboole_0,X1)) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5339,c_996])).

cnf(c_5343,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5342,c_2417])).

cnf(c_9187,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
    | r2_hidden(sK0(X0,X1,k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_585,c_5343])).

cnf(c_13970,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k1_xboole_0
    | r2_hidden(sK0(k3_xboole_0(X0,X1),X2,k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_9187,c_2063])).

cnf(c_117179,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X0)) = k1_xboole_0
    | r2_hidden(sK0(k3_xboole_0(X0,X1),X0,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_13970,c_586])).

cnf(c_129245,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X0)) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_117179,c_5343])).

cnf(c_129324,plain,
    ( r1_tarski(X0,k3_xboole_0(X1,X2)) != iProver_top
    | r1_tarski(X0,k1_xboole_0) = iProver_top
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_129245,c_576])).

cnf(c_167141,plain,
    ( r1_tarski(sK2,k1_xboole_0) = iProver_top
    | r1_xboole_0(sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_89424,c_129324])).

cnf(c_9186,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = X1
    | r2_hidden(sK0(k1_xboole_0,X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_585,c_5343])).

cnf(c_9194,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(k1_xboole_0,X1,X0),X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9186,c_996,c_2417])).

cnf(c_3797,plain,
    ( r1_tarski(X0,k3_subset_1(sK1,sK3)) != iProver_top
    | r1_xboole_0(X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3218,c_581])).

cnf(c_4284,plain,
    ( r1_xboole_0(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_574,c_3797])).

cnf(c_4291,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK3)) = sK2 ),
    inference(superposition,[status(thm)],[c_4284,c_577])).

cnf(c_4523,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK2)) = k3_xboole_0(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_4291,c_0])).

cnf(c_4545,plain,
    ( k3_xboole_0(sK2,sK3) = k3_xboole_0(sK2,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_4523,c_856])).

cnf(c_9209,plain,
    ( r2_hidden(X0,k5_xboole_0(sK2,k3_xboole_0(sK2,k1_xboole_0))) != iProver_top
    | r2_hidden(X0,k3_xboole_0(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4545,c_3222])).

cnf(c_9248,plain,
    ( r2_hidden(X0,k5_xboole_0(sK2,k3_xboole_0(sK2,k1_xboole_0))) != iProver_top
    | r2_hidden(X0,k3_xboole_0(sK2,k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9209,c_4545])).

cnf(c_9251,plain,
    ( r2_hidden(X0,k3_xboole_0(sK2,k1_xboole_0)) != iProver_top
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9248,c_10])).

cnf(c_9567,plain,
    ( r2_hidden(X0,k3_xboole_0(sK2,k1_xboole_0)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_9251,c_2063])).

cnf(c_11208,plain,
    ( k3_xboole_0(sK2,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9194,c_9567])).

cnf(c_3225,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_856,c_583])).

cnf(c_11603,plain,
    ( r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3225,c_2063])).

cnf(c_11606,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X2,k1_xboole_0)
    | r2_hidden(sK0(X0,X1,k3_xboole_0(X2,k1_xboole_0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_585,c_11603])).

cnf(c_24657,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k3_xboole_0(X1,k1_xboole_0)
    | r2_hidden(sK0(X0,X0,k3_xboole_0(X1,k1_xboole_0)),k3_xboole_0(X1,k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_11606,c_586])).

cnf(c_24760,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k3_xboole_0(X1,k1_xboole_0)
    | r2_hidden(sK0(X1,X1,k3_xboole_0(X0,k1_xboole_0)),k3_xboole_0(X0,k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_24657,c_856])).

cnf(c_53395,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k3_xboole_0(X1,k1_xboole_0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_24760,c_11603])).

cnf(c_16402,plain,
    ( k5_xboole_0(k3_subset_1(sK1,sK3),k3_xboole_0(k3_subset_1(sK1,sK3),k3_xboole_0(X0,k1_xboole_0))) = k3_subset_1(sK1,sK3)
    | r2_hidden(sK0(k3_subset_1(sK1,sK3),k3_xboole_0(X0,k1_xboole_0),k3_subset_1(sK1,sK3)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_16383,c_11603])).

cnf(c_41963,plain,
    ( k5_xboole_0(k3_subset_1(sK1,sK3),k3_xboole_0(k3_subset_1(sK1,sK3),k3_xboole_0(X0,k1_xboole_0))) = k3_subset_1(sK1,sK3)
    | r2_hidden(sK0(k3_subset_1(sK1,sK3),k3_xboole_0(X0,k1_xboole_0),k3_subset_1(sK1,sK3)),k3_subset_1(sK1,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_16402,c_7360])).

cnf(c_44025,plain,
    ( k5_xboole_0(k3_subset_1(sK1,sK3),k3_xboole_0(k3_subset_1(sK1,sK3),k3_xboole_0(X0,k1_xboole_0))) = k3_subset_1(sK1,sK3)
    | r2_hidden(sK0(k3_subset_1(sK1,sK3),k3_xboole_0(X0,k1_xboole_0),k3_subset_1(sK1,sK3)),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_41963,c_3800])).

cnf(c_44076,plain,
    ( k5_xboole_0(k3_subset_1(sK1,sK3),k3_xboole_0(k3_subset_1(sK1,sK3),k3_xboole_0(X0,k1_xboole_0))) = k3_subset_1(sK1,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_44025,c_16402])).

cnf(c_44105,plain,
    ( r1_tarski(X0,k3_subset_1(sK1,sK3)) != iProver_top
    | r1_xboole_0(X0,k3_xboole_0(X1,k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_44076,c_581])).

cnf(c_46191,plain,
    ( r1_xboole_0(sK2,k3_xboole_0(X0,k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_574,c_44105])).

cnf(c_866,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) = k3_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_856,c_0])).

cnf(c_1078,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k3_xboole_0(X1,X1)) = iProver_top
    | r1_xboole_0(X0,k3_xboole_0(X1,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_866,c_576])).

cnf(c_46216,plain,
    ( r1_tarski(sK2,X0) != iProver_top
    | r1_tarski(sK2,k3_xboole_0(X0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_46191,c_1078])).

cnf(c_53602,plain,
    ( r1_tarski(sK2,k3_xboole_0(X0,k1_xboole_0)) = iProver_top
    | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_53395,c_46216])).

cnf(c_1793,plain,
    ( r1_tarski(X0,k3_xboole_0(X1,X2)) != iProver_top
    | r1_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_581])).

cnf(c_5286,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = X0
    | r1_tarski(X0,k3_xboole_0(X1,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1793,c_577])).

cnf(c_21079,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK2,k3_xboole_0(sK2,sK3)))) = X0
    | r1_tarski(X0,k3_xboole_0(sK2,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4545,c_5286])).

cnf(c_21082,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK2,k3_xboole_0(sK2,k1_xboole_0)))) = X0
    | r1_tarski(X0,k3_xboole_0(sK2,k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_21079,c_4545])).

cnf(c_21083,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,sK2)) = X0
    | r1_tarski(X0,k3_xboole_0(sK2,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_21082,c_10])).

cnf(c_55233,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK2)) = sK2
    | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_53602,c_21083])).

cnf(c_46215,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK2,k3_xboole_0(X0,k1_xboole_0))) = sK2 ),
    inference(superposition,[status(thm)],[c_46191,c_577])).

cnf(c_46734,plain,
    ( k3_xboole_0(sK2,sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_46215,c_866])).

cnf(c_47358,plain,
    ( k5_xboole_0(sK2,sK2) = k3_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_46734,c_856])).

cnf(c_55274,plain,
    ( k3_xboole_0(sK2,k1_xboole_0) = sK2
    | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_55233,c_46734,c_47358])).

cnf(c_134742,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11208,c_55274])).

cnf(c_190,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_720,plain,
    ( sK2 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_190])).

cnf(c_721,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_720])).

cnf(c_189,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_206,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_189])).

cnf(c_15,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f45])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_167141,c_134742,c_4284,c_721,c_206,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n024.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:16:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 51.80/7.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 51.80/7.01  
% 51.80/7.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 51.80/7.01  
% 51.80/7.01  ------  iProver source info
% 51.80/7.01  
% 51.80/7.01  git: date: 2020-06-30 10:37:57 +0100
% 51.80/7.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 51.80/7.01  git: non_committed_changes: false
% 51.80/7.01  git: last_make_outside_of_git: false
% 51.80/7.01  
% 51.80/7.01  ------ 
% 51.80/7.01  ------ Parsing...
% 51.80/7.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 51.80/7.01  
% 51.80/7.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 51.80/7.01  
% 51.80/7.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 51.80/7.01  
% 51.80/7.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 51.80/7.01  ------ Proving...
% 51.80/7.01  ------ Problem Properties 
% 51.80/7.01  
% 51.80/7.01  
% 51.80/7.01  clauses                                 19
% 51.80/7.01  conjectures                             4
% 51.80/7.01  EPR                                     3
% 51.80/7.01  Horn                                    15
% 51.80/7.01  unary                                   7
% 51.80/7.01  binary                                  7
% 51.80/7.01  lits                                    37
% 51.80/7.01  lits eq                                 9
% 51.80/7.01  fd_pure                                 0
% 51.80/7.01  fd_pseudo                               0
% 51.80/7.01  fd_cond                                 0
% 51.80/7.01  fd_pseudo_cond                          3
% 51.80/7.01  AC symbols                              0
% 51.80/7.01  
% 51.80/7.01  ------ Input Options Time Limit: Unbounded
% 51.80/7.01  
% 51.80/7.01  
% 51.80/7.01  ------ 
% 51.80/7.01  Current options:
% 51.80/7.01  ------ 
% 51.80/7.01  
% 51.80/7.01  
% 51.80/7.01  
% 51.80/7.01  
% 51.80/7.01  ------ Proving...
% 51.80/7.01  
% 51.80/7.01  
% 51.80/7.01  % SZS status Theorem for theBenchmark.p
% 51.80/7.01  
% 51.80/7.01  % SZS output start CNFRefutation for theBenchmark.p
% 51.80/7.01  
% 51.80/7.01  fof(f10,conjecture,(
% 51.80/7.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 51.80/7.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.80/7.01  
% 51.80/7.01  fof(f11,negated_conjecture,(
% 51.80/7.01    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 51.80/7.01    inference(negated_conjecture,[],[f10])).
% 51.80/7.01  
% 51.80/7.01  fof(f16,plain,(
% 51.80/7.01    ? [X0,X1,X2] : ((k1_xboole_0 != X1 & (r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 51.80/7.01    inference(ennf_transformation,[],[f11])).
% 51.80/7.01  
% 51.80/7.01  fof(f17,plain,(
% 51.80/7.01    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 51.80/7.01    inference(flattening,[],[f16])).
% 51.80/7.01  
% 51.80/7.01  fof(f24,plain,(
% 51.80/7.01    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0))) => (k1_xboole_0 != sK2 & r1_tarski(sK2,k3_subset_1(sK1,sK3)) & r1_tarski(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK1)))),
% 51.80/7.01    introduced(choice_axiom,[])).
% 51.80/7.01  
% 51.80/7.01  fof(f25,plain,(
% 51.80/7.01    k1_xboole_0 != sK2 & r1_tarski(sK2,k3_subset_1(sK1,sK3)) & r1_tarski(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK1))),
% 51.80/7.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f17,f24])).
% 51.80/7.01  
% 51.80/7.01  fof(f44,plain,(
% 51.80/7.01    r1_tarski(sK2,k3_subset_1(sK1,sK3))),
% 51.80/7.01    inference(cnf_transformation,[],[f25])).
% 51.80/7.01  
% 51.80/7.01  fof(f42,plain,(
% 51.80/7.01    m1_subset_1(sK3,k1_zfmisc_1(sK1))),
% 51.80/7.01    inference(cnf_transformation,[],[f25])).
% 51.80/7.01  
% 51.80/7.01  fof(f9,axiom,(
% 51.80/7.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 51.80/7.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.80/7.01  
% 51.80/7.01  fof(f15,plain,(
% 51.80/7.01    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 51.80/7.01    inference(ennf_transformation,[],[f9])).
% 51.80/7.01  
% 51.80/7.01  fof(f41,plain,(
% 51.80/7.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 51.80/7.01    inference(cnf_transformation,[],[f15])).
% 51.80/7.01  
% 51.80/7.01  fof(f2,axiom,(
% 51.80/7.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 51.80/7.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.80/7.01  
% 51.80/7.01  fof(f32,plain,(
% 51.80/7.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 51.80/7.01    inference(cnf_transformation,[],[f2])).
% 51.80/7.01  
% 51.80/7.01  fof(f59,plain,(
% 51.80/7.01    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 51.80/7.01    inference(definition_unfolding,[],[f41,f32])).
% 51.80/7.01  
% 51.80/7.01  fof(f1,axiom,(
% 51.80/7.01    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 51.80/7.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.80/7.01  
% 51.80/7.01  fof(f18,plain,(
% 51.80/7.01    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 51.80/7.01    inference(nnf_transformation,[],[f1])).
% 51.80/7.01  
% 51.80/7.01  fof(f19,plain,(
% 51.80/7.01    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 51.80/7.01    inference(flattening,[],[f18])).
% 51.80/7.01  
% 51.80/7.01  fof(f20,plain,(
% 51.80/7.01    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 51.80/7.01    inference(rectify,[],[f19])).
% 51.80/7.01  
% 51.80/7.01  fof(f21,plain,(
% 51.80/7.01    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 51.80/7.01    introduced(choice_axiom,[])).
% 51.80/7.01  
% 51.80/7.01  fof(f22,plain,(
% 51.80/7.01    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 51.80/7.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f21])).
% 51.80/7.01  
% 51.80/7.01  fof(f28,plain,(
% 51.80/7.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 51.80/7.01    inference(cnf_transformation,[],[f22])).
% 51.80/7.01  
% 51.80/7.01  fof(f50,plain,(
% 51.80/7.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 51.80/7.01    inference(definition_unfolding,[],[f28,f32])).
% 51.80/7.01  
% 51.80/7.01  fof(f60,plain,(
% 51.80/7.01    ( ! [X4,X0,X1] : (r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 51.80/7.01    inference(equality_resolution,[],[f50])).
% 51.80/7.01  
% 51.80/7.01  fof(f31,plain,(
% 51.80/7.01    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 51.80/7.01    inference(cnf_transformation,[],[f22])).
% 51.80/7.01  
% 51.80/7.01  fof(f47,plain,(
% 51.80/7.01    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 51.80/7.01    inference(definition_unfolding,[],[f31,f32])).
% 51.80/7.01  
% 51.80/7.01  fof(f29,plain,(
% 51.80/7.01    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 51.80/7.01    inference(cnf_transformation,[],[f22])).
% 51.80/7.01  
% 51.80/7.01  fof(f49,plain,(
% 51.80/7.01    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 51.80/7.01    inference(definition_unfolding,[],[f29,f32])).
% 51.80/7.01  
% 51.80/7.01  fof(f26,plain,(
% 51.80/7.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 51.80/7.01    inference(cnf_transformation,[],[f22])).
% 51.80/7.01  
% 51.80/7.01  fof(f52,plain,(
% 51.80/7.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 51.80/7.01    inference(definition_unfolding,[],[f26,f32])).
% 51.80/7.01  
% 51.80/7.01  fof(f62,plain,(
% 51.80/7.01    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 51.80/7.01    inference(equality_resolution,[],[f52])).
% 51.80/7.01  
% 51.80/7.01  fof(f6,axiom,(
% 51.80/7.01    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 51.80/7.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.80/7.01  
% 51.80/7.01  fof(f37,plain,(
% 51.80/7.01    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 51.80/7.01    inference(cnf_transformation,[],[f6])).
% 51.80/7.01  
% 51.80/7.01  fof(f46,plain,(
% 51.80/7.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) )),
% 51.80/7.01    inference(definition_unfolding,[],[f37,f32,f32])).
% 51.80/7.01  
% 51.80/7.01  fof(f27,plain,(
% 51.80/7.01    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 51.80/7.01    inference(cnf_transformation,[],[f22])).
% 51.80/7.01  
% 51.80/7.01  fof(f51,plain,(
% 51.80/7.01    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 51.80/7.01    inference(definition_unfolding,[],[f27,f32])).
% 51.80/7.01  
% 51.80/7.01  fof(f61,plain,(
% 51.80/7.01    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 51.80/7.01    inference(equality_resolution,[],[f51])).
% 51.80/7.01  
% 51.80/7.01  fof(f30,plain,(
% 51.80/7.01    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 51.80/7.01    inference(cnf_transformation,[],[f22])).
% 51.80/7.01  
% 51.80/7.01  fof(f48,plain,(
% 51.80/7.01    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 51.80/7.01    inference(definition_unfolding,[],[f30,f32])).
% 51.80/7.01  
% 51.80/7.01  fof(f3,axiom,(
% 51.80/7.01    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 51.80/7.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.80/7.01  
% 51.80/7.01  fof(f12,plain,(
% 51.80/7.01    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 51.80/7.01    inference(ennf_transformation,[],[f3])).
% 51.80/7.01  
% 51.80/7.01  fof(f34,plain,(
% 51.80/7.01    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 51.80/7.01    inference(cnf_transformation,[],[f12])).
% 51.80/7.01  
% 51.80/7.01  fof(f53,plain,(
% 51.80/7.01    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) )),
% 51.80/7.01    inference(definition_unfolding,[],[f34,f32])).
% 51.80/7.01  
% 51.80/7.01  fof(f8,axiom,(
% 51.80/7.01    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 51.80/7.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.80/7.01  
% 51.80/7.01  fof(f13,plain,(
% 51.80/7.01    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)))),
% 51.80/7.01    inference(ennf_transformation,[],[f8])).
% 51.80/7.01  
% 51.80/7.01  fof(f14,plain,(
% 51.80/7.01    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))),
% 51.80/7.01    inference(flattening,[],[f13])).
% 51.80/7.01  
% 51.80/7.01  fof(f40,plain,(
% 51.80/7.01    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 51.80/7.01    inference(cnf_transformation,[],[f14])).
% 51.80/7.01  
% 51.80/7.01  fof(f58,plain,(
% 51.80/7.01    ( ! [X2,X0,X1] : (r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 51.80/7.01    inference(definition_unfolding,[],[f40,f32])).
% 51.80/7.01  
% 51.80/7.01  fof(f43,plain,(
% 51.80/7.01    r1_tarski(sK2,sK3)),
% 51.80/7.01    inference(cnf_transformation,[],[f25])).
% 51.80/7.01  
% 51.80/7.01  fof(f4,axiom,(
% 51.80/7.01    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 51.80/7.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.80/7.01  
% 51.80/7.01  fof(f35,plain,(
% 51.80/7.01    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 51.80/7.01    inference(cnf_transformation,[],[f4])).
% 51.80/7.01  
% 51.80/7.01  fof(f7,axiom,(
% 51.80/7.01    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 51.80/7.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.80/7.01  
% 51.80/7.01  fof(f23,plain,(
% 51.80/7.01    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 51.80/7.01    inference(nnf_transformation,[],[f7])).
% 51.80/7.01  
% 51.80/7.01  fof(f38,plain,(
% 51.80/7.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 51.80/7.01    inference(cnf_transformation,[],[f23])).
% 51.80/7.01  
% 51.80/7.01  fof(f57,plain,(
% 51.80/7.01    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 | ~r1_xboole_0(X0,X1)) )),
% 51.80/7.01    inference(definition_unfolding,[],[f38,f32])).
% 51.80/7.01  
% 51.80/7.01  fof(f5,axiom,(
% 51.80/7.01    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 51.80/7.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.80/7.01  
% 51.80/7.01  fof(f36,plain,(
% 51.80/7.01    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 51.80/7.01    inference(cnf_transformation,[],[f5])).
% 51.80/7.01  
% 51.80/7.01  fof(f55,plain,(
% 51.80/7.01    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 51.80/7.01    inference(definition_unfolding,[],[f36,f32])).
% 51.80/7.01  
% 51.80/7.01  fof(f45,plain,(
% 51.80/7.01    k1_xboole_0 != sK2),
% 51.80/7.01    inference(cnf_transformation,[],[f25])).
% 51.80/7.01  
% 51.80/7.01  cnf(c_16,negated_conjecture,
% 51.80/7.01      ( r1_tarski(sK2,k3_subset_1(sK1,sK3)) ),
% 51.80/7.01      inference(cnf_transformation,[],[f44]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_574,plain,
% 51.80/7.01      ( r1_tarski(sK2,k3_subset_1(sK1,sK3)) = iProver_top ),
% 51.80/7.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_18,negated_conjecture,
% 51.80/7.01      ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
% 51.80/7.01      inference(cnf_transformation,[],[f42]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_572,plain,
% 51.80/7.01      ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
% 51.80/7.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_14,plain,
% 51.80/7.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 51.80/7.01      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 51.80/7.01      inference(cnf_transformation,[],[f59]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_575,plain,
% 51.80/7.01      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
% 51.80/7.01      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 51.80/7.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_3218,plain,
% 51.80/7.01      ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)) = k3_subset_1(sK1,sK3) ),
% 51.80/7.01      inference(superposition,[status(thm)],[c_572,c_575]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_4,plain,
% 51.80/7.01      ( ~ r2_hidden(X0,X1)
% 51.80/7.01      | r2_hidden(X0,X2)
% 51.80/7.01      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 51.80/7.01      inference(cnf_transformation,[],[f60]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_584,plain,
% 51.80/7.01      ( r2_hidden(X0,X1) != iProver_top
% 51.80/7.01      | r2_hidden(X0,X2) = iProver_top
% 51.80/7.01      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = iProver_top ),
% 51.80/7.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_6843,plain,
% 51.80/7.01      ( r2_hidden(X0,k3_subset_1(sK1,sK3)) = iProver_top
% 51.80/7.01      | r2_hidden(X0,sK3) = iProver_top
% 51.80/7.01      | r2_hidden(X0,sK1) != iProver_top ),
% 51.80/7.01      inference(superposition,[status(thm)],[c_3218,c_584]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_1,plain,
% 51.80/7.01      ( ~ r2_hidden(sK0(X0,X1,X2),X0)
% 51.80/7.01      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 51.80/7.01      | r2_hidden(sK0(X0,X1,X2),X1)
% 51.80/7.01      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
% 51.80/7.01      inference(cnf_transformation,[],[f47]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_587,plain,
% 51.80/7.01      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
% 51.80/7.01      | r2_hidden(sK0(X0,X1,X2),X0) != iProver_top
% 51.80/7.01      | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top
% 51.80/7.01      | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top ),
% 51.80/7.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_8928,plain,
% 51.80/7.01      ( k5_xboole_0(k3_subset_1(sK1,sK3),k3_xboole_0(k3_subset_1(sK1,sK3),X0)) = X1
% 51.80/7.01      | r2_hidden(sK0(k3_subset_1(sK1,sK3),X0,X1),X1) != iProver_top
% 51.80/7.01      | r2_hidden(sK0(k3_subset_1(sK1,sK3),X0,X1),X0) = iProver_top
% 51.80/7.01      | r2_hidden(sK0(k3_subset_1(sK1,sK3),X0,X1),sK3) = iProver_top
% 51.80/7.01      | r2_hidden(sK0(k3_subset_1(sK1,sK3),X0,X1),sK1) != iProver_top ),
% 51.80/7.01      inference(superposition,[status(thm)],[c_6843,c_587]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_16154,plain,
% 51.80/7.01      ( k5_xboole_0(k3_subset_1(sK1,sK3),k3_xboole_0(k3_subset_1(sK1,sK3),X0)) = k3_subset_1(sK1,sK3)
% 51.80/7.01      | r2_hidden(sK0(k3_subset_1(sK1,sK3),X0,k3_subset_1(sK1,sK3)),X0) = iProver_top
% 51.80/7.01      | r2_hidden(sK0(k3_subset_1(sK1,sK3),X0,k3_subset_1(sK1,sK3)),sK3) = iProver_top
% 51.80/7.01      | r2_hidden(sK0(k3_subset_1(sK1,sK3),X0,k3_subset_1(sK1,sK3)),sK1) != iProver_top ),
% 51.80/7.01      inference(superposition,[status(thm)],[c_6843,c_8928]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_3,plain,
% 51.80/7.01      ( r2_hidden(sK0(X0,X1,X2),X0)
% 51.80/7.01      | r2_hidden(sK0(X0,X1,X2),X2)
% 51.80/7.01      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
% 51.80/7.01      inference(cnf_transformation,[],[f49]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_585,plain,
% 51.80/7.01      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
% 51.80/7.01      | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
% 51.80/7.01      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
% 51.80/7.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_6,plain,
% 51.80/7.01      ( r2_hidden(X0,X1)
% 51.80/7.01      | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 51.80/7.01      inference(cnf_transformation,[],[f62]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_582,plain,
% 51.80/7.01      ( r2_hidden(X0,X1) = iProver_top
% 51.80/7.01      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
% 51.80/7.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_3796,plain,
% 51.80/7.01      ( r2_hidden(X0,k3_subset_1(sK1,sK3)) != iProver_top
% 51.80/7.01      | r2_hidden(X0,sK1) = iProver_top ),
% 51.80/7.01      inference(superposition,[status(thm)],[c_3218,c_582]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_7361,plain,
% 51.80/7.01      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(sK1,sK3)
% 51.80/7.01      | r2_hidden(sK0(X0,X1,k3_subset_1(sK1,sK3)),X0) = iProver_top
% 51.80/7.01      | r2_hidden(sK0(X0,X1,k3_subset_1(sK1,sK3)),sK1) = iProver_top ),
% 51.80/7.01      inference(superposition,[status(thm)],[c_585,c_3796]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_12732,plain,
% 51.80/7.01      ( k5_xboole_0(k3_subset_1(sK1,sK3),k3_xboole_0(k3_subset_1(sK1,sK3),X0)) = k3_subset_1(sK1,sK3)
% 51.80/7.01      | r2_hidden(sK0(k3_subset_1(sK1,sK3),X0,k3_subset_1(sK1,sK3)),sK1) = iProver_top ),
% 51.80/7.01      inference(superposition,[status(thm)],[c_7361,c_3796]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_16382,plain,
% 51.80/7.01      ( r2_hidden(sK0(k3_subset_1(sK1,sK3),X0,k3_subset_1(sK1,sK3)),sK3) = iProver_top
% 51.80/7.01      | r2_hidden(sK0(k3_subset_1(sK1,sK3),X0,k3_subset_1(sK1,sK3)),X0) = iProver_top
% 51.80/7.01      | k5_xboole_0(k3_subset_1(sK1,sK3),k3_xboole_0(k3_subset_1(sK1,sK3),X0)) = k3_subset_1(sK1,sK3) ),
% 51.80/7.01      inference(global_propositional_subsumption,
% 51.80/7.01                [status(thm)],
% 51.80/7.01                [c_16154,c_12732]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_16383,plain,
% 51.80/7.01      ( k5_xboole_0(k3_subset_1(sK1,sK3),k3_xboole_0(k3_subset_1(sK1,sK3),X0)) = k3_subset_1(sK1,sK3)
% 51.80/7.01      | r2_hidden(sK0(k3_subset_1(sK1,sK3),X0,k3_subset_1(sK1,sK3)),X0) = iProver_top
% 51.80/7.01      | r2_hidden(sK0(k3_subset_1(sK1,sK3),X0,k3_subset_1(sK1,sK3)),sK3) = iProver_top ),
% 51.80/7.01      inference(renaming,[status(thm)],[c_16382]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_0,plain,
% 51.80/7.01      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
% 51.80/7.01      inference(cnf_transformation,[],[f46]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_2063,plain,
% 51.80/7.01      ( r2_hidden(X0,X1) = iProver_top
% 51.80/7.01      | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
% 51.80/7.01      inference(superposition,[status(thm)],[c_0,c_582]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_16401,plain,
% 51.80/7.01      ( k5_xboole_0(k3_subset_1(sK1,sK3),k3_xboole_0(k3_subset_1(sK1,sK3),k3_xboole_0(X0,X1))) = k3_subset_1(sK1,sK3)
% 51.80/7.01      | r2_hidden(sK0(k3_subset_1(sK1,sK3),k3_xboole_0(X0,X1),k3_subset_1(sK1,sK3)),X0) = iProver_top
% 51.80/7.01      | r2_hidden(sK0(k3_subset_1(sK1,sK3),k3_xboole_0(X0,X1),k3_subset_1(sK1,sK3)),sK3) = iProver_top ),
% 51.80/7.01      inference(superposition,[status(thm)],[c_16383,c_2063]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_5,plain,
% 51.80/7.01      ( ~ r2_hidden(X0,X1)
% 51.80/7.01      | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
% 51.80/7.01      inference(cnf_transformation,[],[f61]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_583,plain,
% 51.80/7.01      ( r2_hidden(X0,X1) != iProver_top
% 51.80/7.01      | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
% 51.80/7.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_3800,plain,
% 51.80/7.01      ( r2_hidden(X0,k3_subset_1(sK1,sK3)) != iProver_top
% 51.80/7.01      | r2_hidden(X0,sK3) != iProver_top ),
% 51.80/7.01      inference(superposition,[status(thm)],[c_3218,c_583]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_7360,plain,
% 51.80/7.01      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(sK1,sK3)
% 51.80/7.01      | r2_hidden(sK0(X0,X1,k3_subset_1(sK1,sK3)),X0) = iProver_top
% 51.80/7.01      | r2_hidden(sK0(X0,X1,k3_subset_1(sK1,sK3)),sK3) != iProver_top ),
% 51.80/7.01      inference(superposition,[status(thm)],[c_585,c_3800]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_16393,plain,
% 51.80/7.01      ( k5_xboole_0(k3_subset_1(sK1,sK3),k3_xboole_0(k3_subset_1(sK1,sK3),X0)) = k3_subset_1(sK1,sK3)
% 51.80/7.01      | r2_hidden(sK0(k3_subset_1(sK1,sK3),X0,k3_subset_1(sK1,sK3)),X0) = iProver_top
% 51.80/7.01      | r2_hidden(sK0(k3_subset_1(sK1,sK3),X0,k3_subset_1(sK1,sK3)),k3_subset_1(sK1,sK3)) = iProver_top ),
% 51.80/7.01      inference(superposition,[status(thm)],[c_16383,c_7360]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_2,plain,
% 51.80/7.01      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 51.80/7.01      | r2_hidden(sK0(X0,X1,X2),X2)
% 51.80/7.01      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
% 51.80/7.01      inference(cnf_transformation,[],[f48]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_586,plain,
% 51.80/7.01      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
% 51.80/7.01      | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top
% 51.80/7.01      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
% 51.80/7.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_76321,plain,
% 51.80/7.01      ( k5_xboole_0(k3_subset_1(sK1,sK3),k3_xboole_0(k3_subset_1(sK1,sK3),X0)) = k3_subset_1(sK1,sK3)
% 51.80/7.01      | r2_hidden(sK0(k3_subset_1(sK1,sK3),X0,k3_subset_1(sK1,sK3)),k3_subset_1(sK1,sK3)) = iProver_top ),
% 51.80/7.01      inference(forward_subsumption_resolution,
% 51.80/7.01                [status(thm)],
% 51.80/7.01                [c_16393,c_586]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_76328,plain,
% 51.80/7.01      ( k5_xboole_0(k3_subset_1(sK1,sK3),k3_xboole_0(k3_subset_1(sK1,sK3),X0)) = k3_subset_1(sK1,sK3)
% 51.80/7.01      | r2_hidden(sK0(k3_subset_1(sK1,sK3),X0,k3_subset_1(sK1,sK3)),sK3) != iProver_top ),
% 51.80/7.01      inference(superposition,[status(thm)],[c_76321,c_3800]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_83568,plain,
% 51.80/7.01      ( k5_xboole_0(k3_subset_1(sK1,sK3),k3_xboole_0(k3_subset_1(sK1,sK3),k3_xboole_0(X0,X1))) = k3_subset_1(sK1,sK3)
% 51.80/7.01      | r2_hidden(sK0(k3_subset_1(sK1,sK3),k3_xboole_0(X0,X1),k3_subset_1(sK1,sK3)),X0) = iProver_top ),
% 51.80/7.01      inference(forward_subsumption_resolution,
% 51.80/7.01                [status(thm)],
% 51.80/7.01                [c_16401,c_76328]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_83612,plain,
% 51.80/7.01      ( k5_xboole_0(k3_subset_1(sK1,sK3),k3_xboole_0(k3_subset_1(sK1,sK3),k3_xboole_0(sK3,X0))) = k3_subset_1(sK1,sK3) ),
% 51.80/7.01      inference(superposition,[status(thm)],[c_83568,c_76328]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_7,plain,
% 51.80/7.01      ( ~ r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
% 51.80/7.01      | r1_xboole_0(X0,X2) ),
% 51.80/7.01      inference(cnf_transformation,[],[f53]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_581,plain,
% 51.80/7.01      ( r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top
% 51.80/7.01      | r1_xboole_0(X0,X2) = iProver_top ),
% 51.80/7.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_84521,plain,
% 51.80/7.01      ( r1_tarski(X0,k3_subset_1(sK1,sK3)) != iProver_top
% 51.80/7.01      | r1_xboole_0(X0,k3_xboole_0(sK3,X1)) = iProver_top ),
% 51.80/7.01      inference(superposition,[status(thm)],[c_83612,c_581]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_88268,plain,
% 51.80/7.01      ( r1_xboole_0(sK2,k3_xboole_0(sK3,X0)) = iProver_top ),
% 51.80/7.01      inference(superposition,[status(thm)],[c_574,c_84521]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_857,plain,
% 51.80/7.01      ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1))) = k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 51.80/7.01      inference(superposition,[status(thm)],[c_0,c_0]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_13,plain,
% 51.80/7.01      ( ~ r1_tarski(X0,X1)
% 51.80/7.01      | r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
% 51.80/7.01      | ~ r1_xboole_0(X0,X2) ),
% 51.80/7.01      inference(cnf_transformation,[],[f58]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_576,plain,
% 51.80/7.01      ( r1_tarski(X0,X1) != iProver_top
% 51.80/7.01      | r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = iProver_top
% 51.80/7.01      | r1_xboole_0(X0,X2) != iProver_top ),
% 51.80/7.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_970,plain,
% 51.80/7.01      ( r1_tarski(X0,X1) != iProver_top
% 51.80/7.01      | r1_tarski(X0,k3_xboole_0(X1,X2)) = iProver_top
% 51.80/7.01      | r1_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
% 51.80/7.01      inference(superposition,[status(thm)],[c_0,c_576]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_2991,plain,
% 51.80/7.01      ( r1_tarski(X0,X1) != iProver_top
% 51.80/7.01      | r1_tarski(X0,k3_xboole_0(X1,k3_xboole_0(X1,X2))) = iProver_top
% 51.80/7.01      | r1_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) != iProver_top ),
% 51.80/7.01      inference(superposition,[status(thm)],[c_857,c_970]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_88477,plain,
% 51.80/7.01      ( r1_tarski(sK2,k3_xboole_0(sK3,k3_xboole_0(sK3,X0))) = iProver_top
% 51.80/7.01      | r1_tarski(sK2,sK3) != iProver_top ),
% 51.80/7.01      inference(superposition,[status(thm)],[c_88268,c_2991]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_17,negated_conjecture,
% 51.80/7.01      ( r1_tarski(sK2,sK3) ),
% 51.80/7.01      inference(cnf_transformation,[],[f43]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_20,plain,
% 51.80/7.01      ( r1_tarski(sK2,sK3) = iProver_top ),
% 51.80/7.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_89424,plain,
% 51.80/7.01      ( r1_tarski(sK2,k3_xboole_0(sK3,k3_xboole_0(sK3,X0))) = iProver_top ),
% 51.80/7.01      inference(global_propositional_subsumption,
% 51.80/7.01                [status(thm)],
% 51.80/7.01                [c_88477,c_20]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_9,plain,
% 51.80/7.01      ( r1_tarski(k1_xboole_0,X0) ),
% 51.80/7.01      inference(cnf_transformation,[],[f35]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_579,plain,
% 51.80/7.01      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 51.80/7.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_1792,plain,
% 51.80/7.01      ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
% 51.80/7.01      inference(superposition,[status(thm)],[c_579,c_581]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_12,plain,
% 51.80/7.01      ( ~ r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
% 51.80/7.01      inference(cnf_transformation,[],[f57]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_577,plain,
% 51.80/7.01      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
% 51.80/7.01      | r1_xboole_0(X0,X1) != iProver_top ),
% 51.80/7.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_2406,plain,
% 51.80/7.01      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
% 51.80/7.01      inference(superposition,[status(thm)],[c_1792,c_577]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_2417,plain,
% 51.80/7.01      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 51.80/7.01      inference(superposition,[status(thm)],[c_2406,c_0]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_3222,plain,
% 51.80/7.01      ( r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top
% 51.80/7.01      | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
% 51.80/7.01      inference(superposition,[status(thm)],[c_0,c_583]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_5339,plain,
% 51.80/7.01      ( r2_hidden(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) != iProver_top
% 51.80/7.01      | r2_hidden(X0,k3_xboole_0(k1_xboole_0,X1)) != iProver_top ),
% 51.80/7.01      inference(superposition,[status(thm)],[c_2417,c_3222]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_10,plain,
% 51.80/7.01      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
% 51.80/7.01      inference(cnf_transformation,[],[f55]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_856,plain,
% 51.80/7.01      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k3_xboole_0(X0,k1_xboole_0) ),
% 51.80/7.01      inference(superposition,[status(thm)],[c_10,c_0]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_867,plain,
% 51.80/7.01      ( k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 51.80/7.01      inference(superposition,[status(thm)],[c_856,c_10]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_995,plain,
% 51.80/7.01      ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 51.80/7.01      inference(superposition,[status(thm)],[c_867,c_856]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_996,plain,
% 51.80/7.01      ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 51.80/7.01      inference(light_normalisation,[status(thm)],[c_995,c_867]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_5342,plain,
% 51.80/7.01      ( r2_hidden(X0,k3_xboole_0(k1_xboole_0,X1)) != iProver_top
% 51.80/7.01      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 51.80/7.01      inference(light_normalisation,[status(thm)],[c_5339,c_996]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_5343,plain,
% 51.80/7.01      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 51.80/7.01      inference(demodulation,[status(thm)],[c_5342,c_2417]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_9187,plain,
% 51.80/7.01      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
% 51.80/7.01      | r2_hidden(sK0(X0,X1,k1_xboole_0),X0) = iProver_top ),
% 51.80/7.01      inference(superposition,[status(thm)],[c_585,c_5343]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_13970,plain,
% 51.80/7.01      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k1_xboole_0
% 51.80/7.01      | r2_hidden(sK0(k3_xboole_0(X0,X1),X2,k1_xboole_0),X0) = iProver_top ),
% 51.80/7.01      inference(superposition,[status(thm)],[c_9187,c_2063]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_117179,plain,
% 51.80/7.01      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X0)) = k1_xboole_0
% 51.80/7.01      | r2_hidden(sK0(k3_xboole_0(X0,X1),X0,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 51.80/7.01      inference(superposition,[status(thm)],[c_13970,c_586]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_129245,plain,
% 51.80/7.01      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X0)) = k1_xboole_0 ),
% 51.80/7.01      inference(forward_subsumption_resolution,
% 51.80/7.01                [status(thm)],
% 51.80/7.01                [c_117179,c_5343]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_129324,plain,
% 51.80/7.01      ( r1_tarski(X0,k3_xboole_0(X1,X2)) != iProver_top
% 51.80/7.01      | r1_tarski(X0,k1_xboole_0) = iProver_top
% 51.80/7.01      | r1_xboole_0(X0,X1) != iProver_top ),
% 51.80/7.01      inference(superposition,[status(thm)],[c_129245,c_576]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_167141,plain,
% 51.80/7.01      ( r1_tarski(sK2,k1_xboole_0) = iProver_top
% 51.80/7.01      | r1_xboole_0(sK2,sK3) != iProver_top ),
% 51.80/7.01      inference(superposition,[status(thm)],[c_89424,c_129324]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_9186,plain,
% 51.80/7.01      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = X1
% 51.80/7.01      | r2_hidden(sK0(k1_xboole_0,X0,X1),X1) = iProver_top ),
% 51.80/7.01      inference(superposition,[status(thm)],[c_585,c_5343]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_9194,plain,
% 51.80/7.01      ( k1_xboole_0 = X0
% 51.80/7.01      | r2_hidden(sK0(k1_xboole_0,X1,X0),X0) = iProver_top ),
% 51.80/7.01      inference(light_normalisation,[status(thm)],[c_9186,c_996,c_2417]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_3797,plain,
% 51.80/7.01      ( r1_tarski(X0,k3_subset_1(sK1,sK3)) != iProver_top
% 51.80/7.01      | r1_xboole_0(X0,sK3) = iProver_top ),
% 51.80/7.01      inference(superposition,[status(thm)],[c_3218,c_581]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_4284,plain,
% 51.80/7.01      ( r1_xboole_0(sK2,sK3) = iProver_top ),
% 51.80/7.01      inference(superposition,[status(thm)],[c_574,c_3797]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_4291,plain,
% 51.80/7.01      ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK3)) = sK2 ),
% 51.80/7.01      inference(superposition,[status(thm)],[c_4284,c_577]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_4523,plain,
% 51.80/7.01      ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK2)) = k3_xboole_0(sK2,sK3) ),
% 51.80/7.01      inference(superposition,[status(thm)],[c_4291,c_0]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_4545,plain,
% 51.80/7.01      ( k3_xboole_0(sK2,sK3) = k3_xboole_0(sK2,k1_xboole_0) ),
% 51.80/7.01      inference(demodulation,[status(thm)],[c_4523,c_856]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_9209,plain,
% 51.80/7.01      ( r2_hidden(X0,k5_xboole_0(sK2,k3_xboole_0(sK2,k1_xboole_0))) != iProver_top
% 51.80/7.01      | r2_hidden(X0,k3_xboole_0(sK2,sK3)) != iProver_top ),
% 51.80/7.01      inference(superposition,[status(thm)],[c_4545,c_3222]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_9248,plain,
% 51.80/7.01      ( r2_hidden(X0,k5_xboole_0(sK2,k3_xboole_0(sK2,k1_xboole_0))) != iProver_top
% 51.80/7.01      | r2_hidden(X0,k3_xboole_0(sK2,k1_xboole_0)) != iProver_top ),
% 51.80/7.01      inference(light_normalisation,[status(thm)],[c_9209,c_4545]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_9251,plain,
% 51.80/7.01      ( r2_hidden(X0,k3_xboole_0(sK2,k1_xboole_0)) != iProver_top
% 51.80/7.01      | r2_hidden(X0,sK2) != iProver_top ),
% 51.80/7.01      inference(demodulation,[status(thm)],[c_9248,c_10]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_9567,plain,
% 51.80/7.01      ( r2_hidden(X0,k3_xboole_0(sK2,k1_xboole_0)) != iProver_top ),
% 51.80/7.01      inference(forward_subsumption_resolution,
% 51.80/7.01                [status(thm)],
% 51.80/7.01                [c_9251,c_2063]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_11208,plain,
% 51.80/7.01      ( k3_xboole_0(sK2,k1_xboole_0) = k1_xboole_0 ),
% 51.80/7.01      inference(superposition,[status(thm)],[c_9194,c_9567]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_3225,plain,
% 51.80/7.01      ( r2_hidden(X0,X1) != iProver_top
% 51.80/7.01      | r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) != iProver_top ),
% 51.80/7.01      inference(superposition,[status(thm)],[c_856,c_583]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_11603,plain,
% 51.80/7.01      ( r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) != iProver_top ),
% 51.80/7.01      inference(forward_subsumption_resolution,
% 51.80/7.01                [status(thm)],
% 51.80/7.01                [c_3225,c_2063]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_11606,plain,
% 51.80/7.01      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X2,k1_xboole_0)
% 51.80/7.01      | r2_hidden(sK0(X0,X1,k3_xboole_0(X2,k1_xboole_0)),X0) = iProver_top ),
% 51.80/7.01      inference(superposition,[status(thm)],[c_585,c_11603]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_24657,plain,
% 51.80/7.01      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k3_xboole_0(X1,k1_xboole_0)
% 51.80/7.01      | r2_hidden(sK0(X0,X0,k3_xboole_0(X1,k1_xboole_0)),k3_xboole_0(X1,k1_xboole_0)) = iProver_top ),
% 51.80/7.01      inference(superposition,[status(thm)],[c_11606,c_586]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_24760,plain,
% 51.80/7.01      ( k3_xboole_0(X0,k1_xboole_0) = k3_xboole_0(X1,k1_xboole_0)
% 51.80/7.01      | r2_hidden(sK0(X1,X1,k3_xboole_0(X0,k1_xboole_0)),k3_xboole_0(X0,k1_xboole_0)) = iProver_top ),
% 51.80/7.01      inference(demodulation,[status(thm)],[c_24657,c_856]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_53395,plain,
% 51.80/7.01      ( k3_xboole_0(X0,k1_xboole_0) = k3_xboole_0(X1,k1_xboole_0) ),
% 51.80/7.01      inference(forward_subsumption_resolution,
% 51.80/7.01                [status(thm)],
% 51.80/7.01                [c_24760,c_11603]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_16402,plain,
% 51.80/7.01      ( k5_xboole_0(k3_subset_1(sK1,sK3),k3_xboole_0(k3_subset_1(sK1,sK3),k3_xboole_0(X0,k1_xboole_0))) = k3_subset_1(sK1,sK3)
% 51.80/7.01      | r2_hidden(sK0(k3_subset_1(sK1,sK3),k3_xboole_0(X0,k1_xboole_0),k3_subset_1(sK1,sK3)),sK3) = iProver_top ),
% 51.80/7.01      inference(superposition,[status(thm)],[c_16383,c_11603]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_41963,plain,
% 51.80/7.01      ( k5_xboole_0(k3_subset_1(sK1,sK3),k3_xboole_0(k3_subset_1(sK1,sK3),k3_xboole_0(X0,k1_xboole_0))) = k3_subset_1(sK1,sK3)
% 51.80/7.01      | r2_hidden(sK0(k3_subset_1(sK1,sK3),k3_xboole_0(X0,k1_xboole_0),k3_subset_1(sK1,sK3)),k3_subset_1(sK1,sK3)) = iProver_top ),
% 51.80/7.01      inference(superposition,[status(thm)],[c_16402,c_7360]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_44025,plain,
% 51.80/7.01      ( k5_xboole_0(k3_subset_1(sK1,sK3),k3_xboole_0(k3_subset_1(sK1,sK3),k3_xboole_0(X0,k1_xboole_0))) = k3_subset_1(sK1,sK3)
% 51.80/7.01      | r2_hidden(sK0(k3_subset_1(sK1,sK3),k3_xboole_0(X0,k1_xboole_0),k3_subset_1(sK1,sK3)),sK3) != iProver_top ),
% 51.80/7.01      inference(superposition,[status(thm)],[c_41963,c_3800]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_44076,plain,
% 51.80/7.01      ( k5_xboole_0(k3_subset_1(sK1,sK3),k3_xboole_0(k3_subset_1(sK1,sK3),k3_xboole_0(X0,k1_xboole_0))) = k3_subset_1(sK1,sK3) ),
% 51.80/7.01      inference(global_propositional_subsumption,
% 51.80/7.01                [status(thm)],
% 51.80/7.01                [c_44025,c_16402]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_44105,plain,
% 51.80/7.01      ( r1_tarski(X0,k3_subset_1(sK1,sK3)) != iProver_top
% 51.80/7.01      | r1_xboole_0(X0,k3_xboole_0(X1,k1_xboole_0)) = iProver_top ),
% 51.80/7.01      inference(superposition,[status(thm)],[c_44076,c_581]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_46191,plain,
% 51.80/7.01      ( r1_xboole_0(sK2,k3_xboole_0(X0,k1_xboole_0)) = iProver_top ),
% 51.80/7.01      inference(superposition,[status(thm)],[c_574,c_44105]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_866,plain,
% 51.80/7.01      ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) = k3_xboole_0(X0,X0) ),
% 51.80/7.01      inference(superposition,[status(thm)],[c_856,c_0]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_1078,plain,
% 51.80/7.01      ( r1_tarski(X0,X1) != iProver_top
% 51.80/7.01      | r1_tarski(X0,k3_xboole_0(X1,X1)) = iProver_top
% 51.80/7.01      | r1_xboole_0(X0,k3_xboole_0(X1,k1_xboole_0)) != iProver_top ),
% 51.80/7.01      inference(superposition,[status(thm)],[c_866,c_576]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_46216,plain,
% 51.80/7.01      ( r1_tarski(sK2,X0) != iProver_top
% 51.80/7.01      | r1_tarski(sK2,k3_xboole_0(X0,X0)) = iProver_top ),
% 51.80/7.01      inference(superposition,[status(thm)],[c_46191,c_1078]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_53602,plain,
% 51.80/7.01      ( r1_tarski(sK2,k3_xboole_0(X0,k1_xboole_0)) = iProver_top
% 51.80/7.01      | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
% 51.80/7.01      inference(superposition,[status(thm)],[c_53395,c_46216]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_1793,plain,
% 51.80/7.01      ( r1_tarski(X0,k3_xboole_0(X1,X2)) != iProver_top
% 51.80/7.01      | r1_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = iProver_top ),
% 51.80/7.01      inference(superposition,[status(thm)],[c_0,c_581]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_5286,plain,
% 51.80/7.01      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = X0
% 51.80/7.01      | r1_tarski(X0,k3_xboole_0(X1,X2)) != iProver_top ),
% 51.80/7.01      inference(superposition,[status(thm)],[c_1793,c_577]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_21079,plain,
% 51.80/7.01      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK2,k3_xboole_0(sK2,sK3)))) = X0
% 51.80/7.01      | r1_tarski(X0,k3_xboole_0(sK2,k1_xboole_0)) != iProver_top ),
% 51.80/7.01      inference(superposition,[status(thm)],[c_4545,c_5286]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_21082,plain,
% 51.80/7.01      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK2,k3_xboole_0(sK2,k1_xboole_0)))) = X0
% 51.80/7.01      | r1_tarski(X0,k3_xboole_0(sK2,k1_xboole_0)) != iProver_top ),
% 51.80/7.01      inference(light_normalisation,[status(thm)],[c_21079,c_4545]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_21083,plain,
% 51.80/7.01      ( k5_xboole_0(X0,k3_xboole_0(X0,sK2)) = X0
% 51.80/7.01      | r1_tarski(X0,k3_xboole_0(sK2,k1_xboole_0)) != iProver_top ),
% 51.80/7.01      inference(demodulation,[status(thm)],[c_21082,c_10]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_55233,plain,
% 51.80/7.01      ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK2)) = sK2
% 51.80/7.01      | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
% 51.80/7.01      inference(superposition,[status(thm)],[c_53602,c_21083]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_46215,plain,
% 51.80/7.01      ( k5_xboole_0(sK2,k3_xboole_0(sK2,k3_xboole_0(X0,k1_xboole_0))) = sK2 ),
% 51.80/7.01      inference(superposition,[status(thm)],[c_46191,c_577]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_46734,plain,
% 51.80/7.01      ( k3_xboole_0(sK2,sK2) = sK2 ),
% 51.80/7.01      inference(superposition,[status(thm)],[c_46215,c_866]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_47358,plain,
% 51.80/7.01      ( k5_xboole_0(sK2,sK2) = k3_xboole_0(sK2,k1_xboole_0) ),
% 51.80/7.01      inference(superposition,[status(thm)],[c_46734,c_856]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_55274,plain,
% 51.80/7.01      ( k3_xboole_0(sK2,k1_xboole_0) = sK2
% 51.80/7.01      | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
% 51.80/7.01      inference(light_normalisation,
% 51.80/7.01                [status(thm)],
% 51.80/7.01                [c_55233,c_46734,c_47358]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_134742,plain,
% 51.80/7.01      ( sK2 = k1_xboole_0 | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
% 51.80/7.01      inference(demodulation,[status(thm)],[c_11208,c_55274]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_190,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_720,plain,
% 51.80/7.01      ( sK2 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK2 ),
% 51.80/7.01      inference(instantiation,[status(thm)],[c_190]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_721,plain,
% 51.80/7.01      ( sK2 != k1_xboole_0
% 51.80/7.01      | k1_xboole_0 = sK2
% 51.80/7.01      | k1_xboole_0 != k1_xboole_0 ),
% 51.80/7.01      inference(instantiation,[status(thm)],[c_720]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_189,plain,( X0 = X0 ),theory(equality) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_206,plain,
% 51.80/7.01      ( k1_xboole_0 = k1_xboole_0 ),
% 51.80/7.01      inference(instantiation,[status(thm)],[c_189]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(c_15,negated_conjecture,
% 51.80/7.01      ( k1_xboole_0 != sK2 ),
% 51.80/7.01      inference(cnf_transformation,[],[f45]) ).
% 51.80/7.01  
% 51.80/7.01  cnf(contradiction,plain,
% 51.80/7.01      ( $false ),
% 51.80/7.01      inference(minisat,
% 51.80/7.01                [status(thm)],
% 51.80/7.01                [c_167141,c_134742,c_4284,c_721,c_206,c_15]) ).
% 51.80/7.01  
% 51.80/7.01  
% 51.80/7.01  % SZS output end CNFRefutation for theBenchmark.p
% 51.80/7.01  
% 51.80/7.01  ------                               Statistics
% 51.80/7.01  
% 51.80/7.01  ------ Selected
% 51.80/7.01  
% 51.80/7.01  total_time:                             6.379
% 51.80/7.01  
%------------------------------------------------------------------------------
