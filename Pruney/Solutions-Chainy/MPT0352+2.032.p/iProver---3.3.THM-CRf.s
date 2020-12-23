%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:39:36 EST 2020

% Result     : Theorem 11.40s
% Output     : CNFRefutation 11.40s
% Verified   : 
% Statistics : Number of formulae       :  175 (1121 expanded)
%              Number of clauses        :  120 ( 415 expanded)
%              Number of leaves         :   20 ( 255 expanded)
%              Depth                    :   21
%              Number of atoms          :  448 (3746 expanded)
%              Number of equality atoms :  180 ( 834 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_tarski(X1,X2)
            <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_tarski(X1,X2)
          <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f28,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f29,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f28])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
     => ( ( ~ r1_tarski(k3_subset_1(X0,sK3),k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,sK3) )
        & ( r1_tarski(k3_subset_1(X0,sK3),k3_subset_1(X0,X1))
          | r1_tarski(X1,sK3) )
        & m1_subset_1(sK3,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | r1_tarski(X1,X2) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(sK1,X2),k3_subset_1(sK1,sK2))
            | ~ r1_tarski(sK2,X2) )
          & ( r1_tarski(k3_subset_1(sK1,X2),k3_subset_1(sK1,sK2))
            | r1_tarski(sK2,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(sK1)) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ( ~ r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
      | ~ r1_tarski(sK2,sK3) )
    & ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
      | r1_tarski(sK2,sK3) )
    & m1_subset_1(sK3,k1_zfmisc_1(sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f29,f31,f30])).

fof(f54,plain,
    ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
    | r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f53,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f32])).

fof(f52,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f32])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f38,f40])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f57,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f33,f40,f40])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK0(X0,X1),X0)
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( r1_tarski(sK0(X0,X1),X0)
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK0(X0,X1),X0)
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( r1_tarski(sK0(X0,X1),X0)
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f60,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f42])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f59,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f43])).

fof(f12,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f56,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f35,f40])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f55,plain,
    ( ~ r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
    | ~ r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_19,negated_conjecture,
    ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
    | r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1230,plain,
    ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) = iProver_top
    | r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_462,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_20])).

cnf(c_463,plain,
    ( k3_subset_1(X0,sK3) = k4_xboole_0(X0,sK3)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
    inference(unflattening,[status(thm)],[c_462])).

cnf(c_1314,plain,
    ( k3_subset_1(sK1,sK3) = k4_xboole_0(sK1,sK3) ),
    inference(equality_resolution,[status(thm)],[c_463])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_471,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_21])).

cnf(c_472,plain,
    ( k3_subset_1(X0,sK2) = k4_xboole_0(X0,sK2)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
    inference(unflattening,[status(thm)],[c_471])).

cnf(c_1315,plain,
    ( k3_subset_1(sK1,sK2) = k4_xboole_0(sK1,sK2) ),
    inference(equality_resolution,[status(thm)],[c_472])).

cnf(c_1377,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK3),k4_xboole_0(sK1,sK2)) = iProver_top
    | r1_tarski(sK2,sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1230,c_1314,c_1315])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1238,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2287,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK3),k4_xboole_0(k4_xboole_0(sK1,sK3),k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK1,sK3)
    | r1_tarski(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1377,c_1238])).

cnf(c_2523,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK3),k4_xboole_0(k4_xboole_0(sK1,sK3),k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK1,sK3)
    | k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = sK2 ),
    inference(superposition,[status(thm)],[c_2287,c_1238])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_6,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1237,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1741,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_1237])).

cnf(c_14,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_405,plain,
    ( ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | X2 != X0
    | k3_subset_1(X3,X2) = k4_xboole_0(X3,X2)
    | k1_zfmisc_1(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_16])).

cnf(c_406,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | v1_xboole_0(k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(unflattening,[status(thm)],[c_405])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_10,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_163,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_10])).

cnf(c_164,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_163])).

cnf(c_349,plain,
    ( m1_subset_1(X0,X1)
    | ~ r1_tarski(X2,X3)
    | v1_xboole_0(X1)
    | X0 != X2
    | k1_zfmisc_1(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_164,c_14])).

cnf(c_350,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1)
    | v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(unflattening,[status(thm)],[c_349])).

cnf(c_17,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_360,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_350,c_17])).

cnf(c_410,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_406,c_16,c_11,c_360])).

cnf(c_674,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_10])).

cnf(c_675,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_674])).

cnf(c_713,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_410,c_675])).

cnf(c_1227,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_713])).

cnf(c_1836,plain,
    ( k3_subset_1(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_1741,c_1227])).

cnf(c_5633,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK3),k4_xboole_0(k4_xboole_0(sK1,sK3),k4_xboole_0(sK1,sK2)))) = k3_subset_1(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK3))
    | k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = sK2 ),
    inference(superposition,[status(thm)],[c_2523,c_1836])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_12949,plain,
    ( k5_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),k3_subset_1(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK3)))) = k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK3),k4_xboole_0(k4_xboole_0(sK1,sK3),k4_xboole_0(sK1,sK2))))
    | k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = sK2 ),
    inference(superposition,[status(thm)],[c_5633,c_0])).

cnf(c_161,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_11])).

cnf(c_162,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_161])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_426,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | k1_zfmisc_1(sK1) != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_20])).

cnf(c_427,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(unflattening,[status(thm)],[c_426])).

cnf(c_27,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_429,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_427,c_27])).

cnf(c_571,plain,
    ( r1_tarski(X0,X1)
    | k1_zfmisc_1(X1) != k1_zfmisc_1(sK1)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_162,c_429])).

cnf(c_572,plain,
    ( r1_tarski(sK3,X0)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
    inference(unflattening,[status(thm)],[c_571])).

cnf(c_574,plain,
    ( r1_tarski(sK3,sK1)
    | k1_zfmisc_1(sK1) != k1_zfmisc_1(sK1) ),
    inference(instantiation,[status(thm)],[c_572])).

cnf(c_444,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | k1_zfmisc_1(sK1) != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_21])).

cnf(c_445,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(unflattening,[status(thm)],[c_444])).

cnf(c_447,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_445,c_27])).

cnf(c_585,plain,
    ( r1_tarski(X0,X1)
    | k1_zfmisc_1(X1) != k1_zfmisc_1(sK1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_162,c_447])).

cnf(c_586,plain,
    ( r1_tarski(sK2,X0)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
    inference(unflattening,[status(thm)],[c_585])).

cnf(c_587,plain,
    ( k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
    | r1_tarski(sK2,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_586])).

cnf(c_589,plain,
    ( k1_zfmisc_1(sK1) != k1_zfmisc_1(sK1)
    | r1_tarski(sK2,sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_587])).

cnf(c_864,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_870,plain,
    ( k1_zfmisc_1(sK1) = k1_zfmisc_1(sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_864])).

cnf(c_859,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_874,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_859])).

cnf(c_18,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
    | ~ r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1231,plain,
    ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) != iProver_top
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1374,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK3),k4_xboole_0(sK1,sK2)) != iProver_top
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1231,c_1314,c_1315])).

cnf(c_1413,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_859])).

cnf(c_1675,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_859])).

cnf(c_863,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1297,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK2,k4_xboole_0(sK3,X2))
    | k4_xboole_0(sK3,X2) != X1
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_863])).

cnf(c_1358,plain,
    ( ~ r1_tarski(sK2,X0)
    | r1_tarski(sK2,k4_xboole_0(sK3,X1))
    | k4_xboole_0(sK3,X1) != X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1297])).

cnf(c_1748,plain,
    ( ~ r1_tarski(sK2,k4_xboole_0(X0,k4_xboole_0(X0,sK3)))
    | r1_tarski(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,X0)))
    | k4_xboole_0(sK3,k4_xboole_0(sK3,X0)) != k4_xboole_0(X0,k4_xboole_0(X0,sK3))
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1358])).

cnf(c_1749,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,X0)) != k4_xboole_0(X0,k4_xboole_0(X0,sK3))
    | sK2 != sK2
    | r1_tarski(sK2,k4_xboole_0(X0,k4_xboole_0(X0,sK3))) != iProver_top
    | r1_tarski(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1748])).

cnf(c_1751,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) != k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))
    | sK2 != sK2
    | r1_tarski(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK1))) = iProver_top
    | r1_tarski(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1749])).

cnf(c_2218,plain,
    ( ~ r1_tarski(sK3,X0)
    | k4_xboole_0(sK3,k4_xboole_0(sK3,X0)) = sK3 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2220,plain,
    ( ~ r1_tarski(sK3,sK1)
    | k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) = sK3 ),
    inference(instantiation,[status(thm)],[c_2218])).

cnf(c_860,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1365,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_860])).

cnf(c_1427,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1365])).

cnf(c_2546,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,X0)) != sK3
    | sK3 = k4_xboole_0(sK3,k4_xboole_0(sK3,X0))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1427])).

cnf(c_2547,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) != sK3
    | sK3 = k4_xboole_0(sK3,k4_xboole_0(sK3,sK1))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2546])).

cnf(c_3020,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = sK2
    | r1_tarski(k4_xboole_0(sK1,sK3),k4_xboole_0(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2523,c_1741])).

cnf(c_1269,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK2,sK3)
    | sK2 != X0
    | sK3 != X1 ),
    inference(instantiation,[status(thm)],[c_863])).

cnf(c_1308,plain,
    ( ~ r1_tarski(sK2,X0)
    | r1_tarski(sK2,sK3)
    | sK2 != sK2
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_1269])).

cnf(c_4487,plain,
    ( ~ r1_tarski(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,X0)))
    | r1_tarski(sK2,sK3)
    | sK2 != sK2
    | sK3 != k4_xboole_0(sK3,k4_xboole_0(sK3,X0)) ),
    inference(instantiation,[status(thm)],[c_1308])).

cnf(c_4488,plain,
    ( sK2 != sK2
    | sK3 != k4_xboole_0(sK3,k4_xboole_0(sK3,X0))
    | r1_tarski(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,X0))) != iProver_top
    | r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4487])).

cnf(c_4490,plain,
    ( sK2 != sK2
    | sK3 != k4_xboole_0(sK3,k4_xboole_0(sK3,sK1))
    | r1_tarski(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK1))) != iProver_top
    | r1_tarski(sK2,sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4488])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k4_xboole_0(X1,X2))
    | ~ r1_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1489,plain,
    ( ~ r1_tarski(sK2,X0)
    | r1_tarski(sK2,k4_xboole_0(X0,X1))
    | ~ r1_xboole_0(sK2,X1) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_4528,plain,
    ( ~ r1_tarski(sK2,X0)
    | r1_tarski(sK2,k4_xboole_0(X0,k4_xboole_0(X0,sK3)))
    | ~ r1_xboole_0(sK2,k4_xboole_0(X0,sK3)) ),
    inference(instantiation,[status(thm)],[c_1489])).

cnf(c_4529,plain,
    ( r1_tarski(sK2,X0) != iProver_top
    | r1_tarski(sK2,k4_xboole_0(X0,k4_xboole_0(X0,sK3))) = iProver_top
    | r1_xboole_0(sK2,k4_xboole_0(X0,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4528])).

cnf(c_4531,plain,
    ( r1_tarski(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))) = iProver_top
    | r1_tarski(sK2,sK1) != iProver_top
    | r1_xboole_0(sK2,k4_xboole_0(sK1,sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4529])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
    | r1_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1240,plain,
    ( r1_tarski(X0,k4_xboole_0(X1,X2)) != iProver_top
    | r1_xboole_0(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_6343,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = sK2
    | r1_xboole_0(k4_xboole_0(sK1,sK3),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3020,c_1240])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1398,plain,
    ( ~ r1_xboole_0(X0,sK2)
    | r1_xboole_0(sK2,X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_9736,plain,
    ( ~ r1_xboole_0(k4_xboole_0(X0,sK3),sK2)
    | r1_xboole_0(sK2,k4_xboole_0(X0,sK3)) ),
    inference(instantiation,[status(thm)],[c_1398])).

cnf(c_9742,plain,
    ( r1_xboole_0(k4_xboole_0(X0,sK3),sK2) != iProver_top
    | r1_xboole_0(sK2,k4_xboole_0(X0,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9736])).

cnf(c_9744,plain,
    ( r1_xboole_0(k4_xboole_0(sK1,sK3),sK2) != iProver_top
    | r1_xboole_0(sK2,k4_xboole_0(sK1,sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_9742])).

cnf(c_22731,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,sK3)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_22732,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_22731])).

cnf(c_22752,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12949,c_574,c_589,c_870,c_874,c_1374,c_1413,c_1675,c_1751,c_2220,c_2547,c_3020,c_4490,c_4531,c_6343,c_9744,c_22732])).

cnf(c_22881,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_22752,c_1])).

cnf(c_1229,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_429])).

cnf(c_1232,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2105,plain,
    ( r1_tarski(sK3,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1229,c_1232])).

cnf(c_2286,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) = sK3 ),
    inference(superposition,[status(thm)],[c_2105,c_1238])).

cnf(c_2667,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_2286,c_1])).

cnf(c_2398,plain,
    ( r1_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1237,c_1240])).

cnf(c_31962,plain,
    ( r1_xboole_0(k4_xboole_0(sK3,X0),k4_xboole_0(sK1,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2667,c_2398])).

cnf(c_32568,plain,
    ( r1_xboole_0(sK2,k4_xboole_0(sK1,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_22881,c_31962])).

cnf(c_22836,plain,
    ( r1_tarski(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_22752,c_1741])).

cnf(c_1479,plain,
    ( r1_xboole_0(X0,sK2)
    | ~ r1_xboole_0(sK2,X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_4412,plain,
    ( r1_xboole_0(k4_xboole_0(sK1,X0),sK2)
    | ~ r1_xboole_0(sK2,k4_xboole_0(sK1,X0)) ),
    inference(instantiation,[status(thm)],[c_1479])).

cnf(c_18100,plain,
    ( r1_xboole_0(k4_xboole_0(sK1,sK3),sK2)
    | ~ r1_xboole_0(sK2,k4_xboole_0(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_4412])).

cnf(c_18103,plain,
    ( r1_xboole_0(k4_xboole_0(sK1,sK3),sK2) = iProver_top
    | r1_xboole_0(sK2,k4_xboole_0(sK1,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18100])).

cnf(c_1236,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k4_xboole_0(X1,X2)) = iProver_top
    | r1_xboole_0(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4464,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK3),sK1) != iProver_top
    | r1_tarski(sK2,sK3) != iProver_top
    | r1_xboole_0(k4_xboole_0(sK1,sK3),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1236,c_1374])).

cnf(c_3542,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK3),sK1) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_3543,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK3),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3542])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_32568,c_22836,c_18103,c_4464,c_3543])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n013.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:26:09 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 11.40/2.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.40/2.02  
% 11.40/2.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.40/2.02  
% 11.40/2.02  ------  iProver source info
% 11.40/2.02  
% 11.40/2.02  git: date: 2020-06-30 10:37:57 +0100
% 11.40/2.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.40/2.02  git: non_committed_changes: false
% 11.40/2.02  git: last_make_outside_of_git: false
% 11.40/2.02  
% 11.40/2.02  ------ 
% 11.40/2.02  
% 11.40/2.02  ------ Input Options
% 11.40/2.02  
% 11.40/2.02  --out_options                           all
% 11.40/2.02  --tptp_safe_out                         true
% 11.40/2.02  --problem_path                          ""
% 11.40/2.02  --include_path                          ""
% 11.40/2.02  --clausifier                            res/vclausify_rel
% 11.40/2.02  --clausifier_options                    ""
% 11.40/2.02  --stdin                                 false
% 11.40/2.02  --stats_out                             all
% 11.40/2.02  
% 11.40/2.02  ------ General Options
% 11.40/2.02  
% 11.40/2.02  --fof                                   false
% 11.40/2.02  --time_out_real                         305.
% 11.40/2.02  --time_out_virtual                      -1.
% 11.40/2.02  --symbol_type_check                     false
% 11.40/2.02  --clausify_out                          false
% 11.40/2.02  --sig_cnt_out                           false
% 11.40/2.02  --trig_cnt_out                          false
% 11.40/2.02  --trig_cnt_out_tolerance                1.
% 11.40/2.02  --trig_cnt_out_sk_spl                   false
% 11.40/2.02  --abstr_cl_out                          false
% 11.40/2.02  
% 11.40/2.02  ------ Global Options
% 11.40/2.02  
% 11.40/2.02  --schedule                              default
% 11.40/2.02  --add_important_lit                     false
% 11.40/2.02  --prop_solver_per_cl                    1000
% 11.40/2.02  --min_unsat_core                        false
% 11.40/2.02  --soft_assumptions                      false
% 11.40/2.02  --soft_lemma_size                       3
% 11.40/2.02  --prop_impl_unit_size                   0
% 11.40/2.02  --prop_impl_unit                        []
% 11.40/2.02  --share_sel_clauses                     true
% 11.40/2.02  --reset_solvers                         false
% 11.40/2.02  --bc_imp_inh                            [conj_cone]
% 11.40/2.02  --conj_cone_tolerance                   3.
% 11.40/2.02  --extra_neg_conj                        none
% 11.40/2.02  --large_theory_mode                     true
% 11.40/2.02  --prolific_symb_bound                   200
% 11.40/2.02  --lt_threshold                          2000
% 11.40/2.02  --clause_weak_htbl                      true
% 11.40/2.02  --gc_record_bc_elim                     false
% 11.40/2.02  
% 11.40/2.02  ------ Preprocessing Options
% 11.40/2.02  
% 11.40/2.02  --preprocessing_flag                    true
% 11.40/2.02  --time_out_prep_mult                    0.1
% 11.40/2.02  --splitting_mode                        input
% 11.40/2.02  --splitting_grd                         true
% 11.40/2.02  --splitting_cvd                         false
% 11.40/2.02  --splitting_cvd_svl                     false
% 11.40/2.02  --splitting_nvd                         32
% 11.40/2.02  --sub_typing                            true
% 11.40/2.02  --prep_gs_sim                           true
% 11.40/2.02  --prep_unflatten                        true
% 11.40/2.02  --prep_res_sim                          true
% 11.40/2.02  --prep_upred                            true
% 11.40/2.02  --prep_sem_filter                       exhaustive
% 11.40/2.02  --prep_sem_filter_out                   false
% 11.40/2.02  --pred_elim                             true
% 11.40/2.02  --res_sim_input                         true
% 11.40/2.02  --eq_ax_congr_red                       true
% 11.40/2.02  --pure_diseq_elim                       true
% 11.40/2.02  --brand_transform                       false
% 11.40/2.02  --non_eq_to_eq                          false
% 11.40/2.02  --prep_def_merge                        true
% 11.40/2.02  --prep_def_merge_prop_impl              false
% 11.40/2.02  --prep_def_merge_mbd                    true
% 11.40/2.02  --prep_def_merge_tr_red                 false
% 11.40/2.02  --prep_def_merge_tr_cl                  false
% 11.40/2.02  --smt_preprocessing                     true
% 11.40/2.02  --smt_ac_axioms                         fast
% 11.40/2.02  --preprocessed_out                      false
% 11.40/2.02  --preprocessed_stats                    false
% 11.40/2.02  
% 11.40/2.02  ------ Abstraction refinement Options
% 11.40/2.02  
% 11.40/2.02  --abstr_ref                             []
% 11.40/2.02  --abstr_ref_prep                        false
% 11.40/2.02  --abstr_ref_until_sat                   false
% 11.40/2.02  --abstr_ref_sig_restrict                funpre
% 11.40/2.02  --abstr_ref_af_restrict_to_split_sk     false
% 11.40/2.02  --abstr_ref_under                       []
% 11.40/2.02  
% 11.40/2.02  ------ SAT Options
% 11.40/2.02  
% 11.40/2.02  --sat_mode                              false
% 11.40/2.02  --sat_fm_restart_options                ""
% 11.40/2.02  --sat_gr_def                            false
% 11.40/2.02  --sat_epr_types                         true
% 11.40/2.02  --sat_non_cyclic_types                  false
% 11.40/2.02  --sat_finite_models                     false
% 11.40/2.02  --sat_fm_lemmas                         false
% 11.40/2.02  --sat_fm_prep                           false
% 11.40/2.02  --sat_fm_uc_incr                        true
% 11.40/2.02  --sat_out_model                         small
% 11.40/2.02  --sat_out_clauses                       false
% 11.40/2.02  
% 11.40/2.02  ------ QBF Options
% 11.40/2.02  
% 11.40/2.02  --qbf_mode                              false
% 11.40/2.02  --qbf_elim_univ                         false
% 11.40/2.02  --qbf_dom_inst                          none
% 11.40/2.02  --qbf_dom_pre_inst                      false
% 11.40/2.02  --qbf_sk_in                             false
% 11.40/2.02  --qbf_pred_elim                         true
% 11.40/2.02  --qbf_split                             512
% 11.40/2.02  
% 11.40/2.02  ------ BMC1 Options
% 11.40/2.02  
% 11.40/2.02  --bmc1_incremental                      false
% 11.40/2.02  --bmc1_axioms                           reachable_all
% 11.40/2.02  --bmc1_min_bound                        0
% 11.40/2.02  --bmc1_max_bound                        -1
% 11.40/2.02  --bmc1_max_bound_default                -1
% 11.40/2.02  --bmc1_symbol_reachability              true
% 11.40/2.02  --bmc1_property_lemmas                  false
% 11.40/2.02  --bmc1_k_induction                      false
% 11.40/2.02  --bmc1_non_equiv_states                 false
% 11.40/2.02  --bmc1_deadlock                         false
% 11.40/2.02  --bmc1_ucm                              false
% 11.40/2.02  --bmc1_add_unsat_core                   none
% 11.40/2.02  --bmc1_unsat_core_children              false
% 11.40/2.02  --bmc1_unsat_core_extrapolate_axioms    false
% 11.40/2.02  --bmc1_out_stat                         full
% 11.40/2.02  --bmc1_ground_init                      false
% 11.40/2.02  --bmc1_pre_inst_next_state              false
% 11.40/2.02  --bmc1_pre_inst_state                   false
% 11.40/2.02  --bmc1_pre_inst_reach_state             false
% 11.40/2.02  --bmc1_out_unsat_core                   false
% 11.40/2.02  --bmc1_aig_witness_out                  false
% 11.40/2.02  --bmc1_verbose                          false
% 11.40/2.02  --bmc1_dump_clauses_tptp                false
% 11.40/2.02  --bmc1_dump_unsat_core_tptp             false
% 11.40/2.02  --bmc1_dump_file                        -
% 11.40/2.02  --bmc1_ucm_expand_uc_limit              128
% 11.40/2.02  --bmc1_ucm_n_expand_iterations          6
% 11.40/2.02  --bmc1_ucm_extend_mode                  1
% 11.40/2.02  --bmc1_ucm_init_mode                    2
% 11.40/2.02  --bmc1_ucm_cone_mode                    none
% 11.40/2.02  --bmc1_ucm_reduced_relation_type        0
% 11.40/2.02  --bmc1_ucm_relax_model                  4
% 11.40/2.02  --bmc1_ucm_full_tr_after_sat            true
% 11.40/2.02  --bmc1_ucm_expand_neg_assumptions       false
% 11.40/2.02  --bmc1_ucm_layered_model                none
% 11.40/2.02  --bmc1_ucm_max_lemma_size               10
% 11.40/2.02  
% 11.40/2.02  ------ AIG Options
% 11.40/2.02  
% 11.40/2.02  --aig_mode                              false
% 11.40/2.02  
% 11.40/2.02  ------ Instantiation Options
% 11.40/2.02  
% 11.40/2.02  --instantiation_flag                    true
% 11.40/2.02  --inst_sos_flag                         true
% 11.40/2.02  --inst_sos_phase                        true
% 11.40/2.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.40/2.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.40/2.02  --inst_lit_sel_side                     num_symb
% 11.40/2.02  --inst_solver_per_active                1400
% 11.40/2.02  --inst_solver_calls_frac                1.
% 11.40/2.02  --inst_passive_queue_type               priority_queues
% 11.40/2.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.40/2.02  --inst_passive_queues_freq              [25;2]
% 11.40/2.02  --inst_dismatching                      true
% 11.40/2.02  --inst_eager_unprocessed_to_passive     true
% 11.40/2.02  --inst_prop_sim_given                   true
% 11.40/2.02  --inst_prop_sim_new                     false
% 11.40/2.02  --inst_subs_new                         false
% 11.40/2.02  --inst_eq_res_simp                      false
% 11.40/2.02  --inst_subs_given                       false
% 11.40/2.02  --inst_orphan_elimination               true
% 11.40/2.02  --inst_learning_loop_flag               true
% 11.40/2.02  --inst_learning_start                   3000
% 11.40/2.02  --inst_learning_factor                  2
% 11.40/2.02  --inst_start_prop_sim_after_learn       3
% 11.40/2.02  --inst_sel_renew                        solver
% 11.40/2.02  --inst_lit_activity_flag                true
% 11.40/2.02  --inst_restr_to_given                   false
% 11.40/2.02  --inst_activity_threshold               500
% 11.40/2.02  --inst_out_proof                        true
% 11.40/2.02  
% 11.40/2.02  ------ Resolution Options
% 11.40/2.02  
% 11.40/2.02  --resolution_flag                       true
% 11.40/2.02  --res_lit_sel                           adaptive
% 11.40/2.02  --res_lit_sel_side                      none
% 11.40/2.02  --res_ordering                          kbo
% 11.40/2.02  --res_to_prop_solver                    active
% 11.40/2.02  --res_prop_simpl_new                    false
% 11.40/2.02  --res_prop_simpl_given                  true
% 11.40/2.02  --res_passive_queue_type                priority_queues
% 11.40/2.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.40/2.02  --res_passive_queues_freq               [15;5]
% 11.40/2.02  --res_forward_subs                      full
% 11.40/2.02  --res_backward_subs                     full
% 11.40/2.02  --res_forward_subs_resolution           true
% 11.40/2.02  --res_backward_subs_resolution          true
% 11.40/2.02  --res_orphan_elimination                true
% 11.40/2.02  --res_time_limit                        2.
% 11.40/2.02  --res_out_proof                         true
% 11.40/2.02  
% 11.40/2.02  ------ Superposition Options
% 11.40/2.02  
% 11.40/2.02  --superposition_flag                    true
% 11.40/2.02  --sup_passive_queue_type                priority_queues
% 11.40/2.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.40/2.02  --sup_passive_queues_freq               [8;1;4]
% 11.40/2.02  --demod_completeness_check              fast
% 11.40/2.02  --demod_use_ground                      true
% 11.40/2.02  --sup_to_prop_solver                    passive
% 11.40/2.02  --sup_prop_simpl_new                    true
% 11.40/2.02  --sup_prop_simpl_given                  true
% 11.40/2.02  --sup_fun_splitting                     true
% 11.40/2.02  --sup_smt_interval                      50000
% 11.40/2.02  
% 11.40/2.02  ------ Superposition Simplification Setup
% 11.40/2.02  
% 11.40/2.02  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.40/2.02  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.40/2.02  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.40/2.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.40/2.02  --sup_full_triv                         [TrivRules;PropSubs]
% 11.40/2.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.40/2.02  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.40/2.02  --sup_immed_triv                        [TrivRules]
% 11.40/2.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.40/2.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.40/2.02  --sup_immed_bw_main                     []
% 11.40/2.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.40/2.02  --sup_input_triv                        [Unflattening;TrivRules]
% 11.40/2.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.40/2.02  --sup_input_bw                          []
% 11.40/2.02  
% 11.40/2.02  ------ Combination Options
% 11.40/2.02  
% 11.40/2.02  --comb_res_mult                         3
% 11.40/2.02  --comb_sup_mult                         2
% 11.40/2.02  --comb_inst_mult                        10
% 11.40/2.02  
% 11.40/2.02  ------ Debug Options
% 11.40/2.02  
% 11.40/2.02  --dbg_backtrace                         false
% 11.40/2.02  --dbg_dump_prop_clauses                 false
% 11.40/2.02  --dbg_dump_prop_clauses_file            -
% 11.40/2.02  --dbg_out_stat                          false
% 11.40/2.02  ------ Parsing...
% 11.40/2.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.40/2.02  
% 11.40/2.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 11.40/2.02  
% 11.40/2.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.40/2.02  
% 11.40/2.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.40/2.02  ------ Proving...
% 11.40/2.02  ------ Problem Properties 
% 11.40/2.02  
% 11.40/2.02  
% 11.40/2.02  clauses                                 19
% 11.40/2.02  conjectures                             2
% 11.40/2.02  EPR                                     1
% 11.40/2.02  Horn                                    17
% 11.40/2.02  unary                                   5
% 11.40/2.02  binary                                  11
% 11.40/2.02  lits                                    36
% 11.40/2.02  lits eq                                 10
% 11.40/2.02  fd_pure                                 0
% 11.40/2.02  fd_pseudo                               0
% 11.40/2.02  fd_cond                                 0
% 11.40/2.02  fd_pseudo_cond                          2
% 11.40/2.02  AC symbols                              0
% 11.40/2.02  
% 11.40/2.02  ------ Schedule dynamic 5 is on 
% 11.40/2.02  
% 11.40/2.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.40/2.02  
% 11.40/2.02  
% 11.40/2.02  ------ 
% 11.40/2.02  Current options:
% 11.40/2.02  ------ 
% 11.40/2.02  
% 11.40/2.02  ------ Input Options
% 11.40/2.02  
% 11.40/2.02  --out_options                           all
% 11.40/2.02  --tptp_safe_out                         true
% 11.40/2.02  --problem_path                          ""
% 11.40/2.02  --include_path                          ""
% 11.40/2.02  --clausifier                            res/vclausify_rel
% 11.40/2.02  --clausifier_options                    ""
% 11.40/2.02  --stdin                                 false
% 11.40/2.02  --stats_out                             all
% 11.40/2.02  
% 11.40/2.02  ------ General Options
% 11.40/2.02  
% 11.40/2.02  --fof                                   false
% 11.40/2.02  --time_out_real                         305.
% 11.40/2.02  --time_out_virtual                      -1.
% 11.40/2.02  --symbol_type_check                     false
% 11.40/2.02  --clausify_out                          false
% 11.40/2.02  --sig_cnt_out                           false
% 11.40/2.02  --trig_cnt_out                          false
% 11.40/2.02  --trig_cnt_out_tolerance                1.
% 11.40/2.02  --trig_cnt_out_sk_spl                   false
% 11.40/2.02  --abstr_cl_out                          false
% 11.40/2.02  
% 11.40/2.02  ------ Global Options
% 11.40/2.02  
% 11.40/2.02  --schedule                              default
% 11.40/2.02  --add_important_lit                     false
% 11.40/2.02  --prop_solver_per_cl                    1000
% 11.40/2.02  --min_unsat_core                        false
% 11.40/2.02  --soft_assumptions                      false
% 11.40/2.02  --soft_lemma_size                       3
% 11.40/2.02  --prop_impl_unit_size                   0
% 11.40/2.02  --prop_impl_unit                        []
% 11.40/2.02  --share_sel_clauses                     true
% 11.40/2.02  --reset_solvers                         false
% 11.40/2.02  --bc_imp_inh                            [conj_cone]
% 11.40/2.02  --conj_cone_tolerance                   3.
% 11.40/2.02  --extra_neg_conj                        none
% 11.40/2.02  --large_theory_mode                     true
% 11.40/2.02  --prolific_symb_bound                   200
% 11.40/2.02  --lt_threshold                          2000
% 11.40/2.02  --clause_weak_htbl                      true
% 11.40/2.02  --gc_record_bc_elim                     false
% 11.40/2.02  
% 11.40/2.02  ------ Preprocessing Options
% 11.40/2.02  
% 11.40/2.02  --preprocessing_flag                    true
% 11.40/2.02  --time_out_prep_mult                    0.1
% 11.40/2.02  --splitting_mode                        input
% 11.40/2.02  --splitting_grd                         true
% 11.40/2.02  --splitting_cvd                         false
% 11.40/2.02  --splitting_cvd_svl                     false
% 11.40/2.02  --splitting_nvd                         32
% 11.40/2.02  --sub_typing                            true
% 11.40/2.02  --prep_gs_sim                           true
% 11.40/2.02  --prep_unflatten                        true
% 11.40/2.02  --prep_res_sim                          true
% 11.40/2.02  --prep_upred                            true
% 11.40/2.02  --prep_sem_filter                       exhaustive
% 11.40/2.02  --prep_sem_filter_out                   false
% 11.40/2.02  --pred_elim                             true
% 11.40/2.02  --res_sim_input                         true
% 11.40/2.02  --eq_ax_congr_red                       true
% 11.40/2.02  --pure_diseq_elim                       true
% 11.40/2.02  --brand_transform                       false
% 11.40/2.02  --non_eq_to_eq                          false
% 11.40/2.02  --prep_def_merge                        true
% 11.40/2.02  --prep_def_merge_prop_impl              false
% 11.40/2.02  --prep_def_merge_mbd                    true
% 11.40/2.02  --prep_def_merge_tr_red                 false
% 11.40/2.02  --prep_def_merge_tr_cl                  false
% 11.40/2.02  --smt_preprocessing                     true
% 11.40/2.02  --smt_ac_axioms                         fast
% 11.40/2.02  --preprocessed_out                      false
% 11.40/2.02  --preprocessed_stats                    false
% 11.40/2.02  
% 11.40/2.02  ------ Abstraction refinement Options
% 11.40/2.02  
% 11.40/2.02  --abstr_ref                             []
% 11.40/2.02  --abstr_ref_prep                        false
% 11.40/2.02  --abstr_ref_until_sat                   false
% 11.40/2.02  --abstr_ref_sig_restrict                funpre
% 11.40/2.02  --abstr_ref_af_restrict_to_split_sk     false
% 11.40/2.02  --abstr_ref_under                       []
% 11.40/2.02  
% 11.40/2.02  ------ SAT Options
% 11.40/2.02  
% 11.40/2.02  --sat_mode                              false
% 11.40/2.02  --sat_fm_restart_options                ""
% 11.40/2.02  --sat_gr_def                            false
% 11.40/2.02  --sat_epr_types                         true
% 11.40/2.02  --sat_non_cyclic_types                  false
% 11.40/2.02  --sat_finite_models                     false
% 11.40/2.02  --sat_fm_lemmas                         false
% 11.40/2.02  --sat_fm_prep                           false
% 11.40/2.02  --sat_fm_uc_incr                        true
% 11.40/2.02  --sat_out_model                         small
% 11.40/2.02  --sat_out_clauses                       false
% 11.40/2.02  
% 11.40/2.02  ------ QBF Options
% 11.40/2.02  
% 11.40/2.02  --qbf_mode                              false
% 11.40/2.02  --qbf_elim_univ                         false
% 11.40/2.02  --qbf_dom_inst                          none
% 11.40/2.02  --qbf_dom_pre_inst                      false
% 11.40/2.02  --qbf_sk_in                             false
% 11.40/2.02  --qbf_pred_elim                         true
% 11.40/2.02  --qbf_split                             512
% 11.40/2.02  
% 11.40/2.02  ------ BMC1 Options
% 11.40/2.02  
% 11.40/2.02  --bmc1_incremental                      false
% 11.40/2.02  --bmc1_axioms                           reachable_all
% 11.40/2.02  --bmc1_min_bound                        0
% 11.40/2.02  --bmc1_max_bound                        -1
% 11.40/2.02  --bmc1_max_bound_default                -1
% 11.40/2.02  --bmc1_symbol_reachability              true
% 11.40/2.02  --bmc1_property_lemmas                  false
% 11.40/2.02  --bmc1_k_induction                      false
% 11.40/2.02  --bmc1_non_equiv_states                 false
% 11.40/2.02  --bmc1_deadlock                         false
% 11.40/2.02  --bmc1_ucm                              false
% 11.40/2.02  --bmc1_add_unsat_core                   none
% 11.40/2.02  --bmc1_unsat_core_children              false
% 11.40/2.02  --bmc1_unsat_core_extrapolate_axioms    false
% 11.40/2.02  --bmc1_out_stat                         full
% 11.40/2.02  --bmc1_ground_init                      false
% 11.40/2.02  --bmc1_pre_inst_next_state              false
% 11.40/2.02  --bmc1_pre_inst_state                   false
% 11.40/2.02  --bmc1_pre_inst_reach_state             false
% 11.40/2.02  --bmc1_out_unsat_core                   false
% 11.40/2.02  --bmc1_aig_witness_out                  false
% 11.40/2.02  --bmc1_verbose                          false
% 11.40/2.02  --bmc1_dump_clauses_tptp                false
% 11.40/2.02  --bmc1_dump_unsat_core_tptp             false
% 11.40/2.02  --bmc1_dump_file                        -
% 11.40/2.02  --bmc1_ucm_expand_uc_limit              128
% 11.40/2.02  --bmc1_ucm_n_expand_iterations          6
% 11.40/2.02  --bmc1_ucm_extend_mode                  1
% 11.40/2.02  --bmc1_ucm_init_mode                    2
% 11.40/2.02  --bmc1_ucm_cone_mode                    none
% 11.40/2.02  --bmc1_ucm_reduced_relation_type        0
% 11.40/2.02  --bmc1_ucm_relax_model                  4
% 11.40/2.02  --bmc1_ucm_full_tr_after_sat            true
% 11.40/2.02  --bmc1_ucm_expand_neg_assumptions       false
% 11.40/2.02  --bmc1_ucm_layered_model                none
% 11.40/2.02  --bmc1_ucm_max_lemma_size               10
% 11.40/2.02  
% 11.40/2.02  ------ AIG Options
% 11.40/2.02  
% 11.40/2.02  --aig_mode                              false
% 11.40/2.02  
% 11.40/2.02  ------ Instantiation Options
% 11.40/2.02  
% 11.40/2.02  --instantiation_flag                    true
% 11.40/2.02  --inst_sos_flag                         true
% 11.40/2.02  --inst_sos_phase                        true
% 11.40/2.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.40/2.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.40/2.02  --inst_lit_sel_side                     none
% 11.40/2.02  --inst_solver_per_active                1400
% 11.40/2.02  --inst_solver_calls_frac                1.
% 11.40/2.02  --inst_passive_queue_type               priority_queues
% 11.40/2.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.40/2.02  --inst_passive_queues_freq              [25;2]
% 11.40/2.02  --inst_dismatching                      true
% 11.40/2.02  --inst_eager_unprocessed_to_passive     true
% 11.40/2.02  --inst_prop_sim_given                   true
% 11.40/2.02  --inst_prop_sim_new                     false
% 11.40/2.02  --inst_subs_new                         false
% 11.40/2.02  --inst_eq_res_simp                      false
% 11.40/2.02  --inst_subs_given                       false
% 11.40/2.02  --inst_orphan_elimination               true
% 11.40/2.02  --inst_learning_loop_flag               true
% 11.40/2.02  --inst_learning_start                   3000
% 11.40/2.02  --inst_learning_factor                  2
% 11.40/2.02  --inst_start_prop_sim_after_learn       3
% 11.40/2.02  --inst_sel_renew                        solver
% 11.40/2.02  --inst_lit_activity_flag                true
% 11.40/2.02  --inst_restr_to_given                   false
% 11.40/2.02  --inst_activity_threshold               500
% 11.40/2.02  --inst_out_proof                        true
% 11.40/2.02  
% 11.40/2.02  ------ Resolution Options
% 11.40/2.02  
% 11.40/2.02  --resolution_flag                       false
% 11.40/2.02  --res_lit_sel                           adaptive
% 11.40/2.02  --res_lit_sel_side                      none
% 11.40/2.02  --res_ordering                          kbo
% 11.40/2.02  --res_to_prop_solver                    active
% 11.40/2.02  --res_prop_simpl_new                    false
% 11.40/2.02  --res_prop_simpl_given                  true
% 11.40/2.02  --res_passive_queue_type                priority_queues
% 11.40/2.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.40/2.02  --res_passive_queues_freq               [15;5]
% 11.40/2.02  --res_forward_subs                      full
% 11.40/2.02  --res_backward_subs                     full
% 11.40/2.02  --res_forward_subs_resolution           true
% 11.40/2.02  --res_backward_subs_resolution          true
% 11.40/2.02  --res_orphan_elimination                true
% 11.40/2.02  --res_time_limit                        2.
% 11.40/2.02  --res_out_proof                         true
% 11.40/2.02  
% 11.40/2.02  ------ Superposition Options
% 11.40/2.02  
% 11.40/2.02  --superposition_flag                    true
% 11.40/2.02  --sup_passive_queue_type                priority_queues
% 11.40/2.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.40/2.02  --sup_passive_queues_freq               [8;1;4]
% 11.40/2.02  --demod_completeness_check              fast
% 11.40/2.02  --demod_use_ground                      true
% 11.40/2.02  --sup_to_prop_solver                    passive
% 11.40/2.02  --sup_prop_simpl_new                    true
% 11.40/2.02  --sup_prop_simpl_given                  true
% 11.40/2.02  --sup_fun_splitting                     true
% 11.40/2.02  --sup_smt_interval                      50000
% 11.40/2.02  
% 11.40/2.02  ------ Superposition Simplification Setup
% 11.40/2.02  
% 11.40/2.02  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.40/2.02  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.40/2.02  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.40/2.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.40/2.02  --sup_full_triv                         [TrivRules;PropSubs]
% 11.40/2.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.40/2.02  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.40/2.02  --sup_immed_triv                        [TrivRules]
% 11.40/2.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.40/2.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.40/2.02  --sup_immed_bw_main                     []
% 11.40/2.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.40/2.02  --sup_input_triv                        [Unflattening;TrivRules]
% 11.40/2.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.40/2.02  --sup_input_bw                          []
% 11.40/2.02  
% 11.40/2.02  ------ Combination Options
% 11.40/2.02  
% 11.40/2.02  --comb_res_mult                         3
% 11.40/2.02  --comb_sup_mult                         2
% 11.40/2.02  --comb_inst_mult                        10
% 11.40/2.02  
% 11.40/2.02  ------ Debug Options
% 11.40/2.02  
% 11.40/2.02  --dbg_backtrace                         false
% 11.40/2.02  --dbg_dump_prop_clauses                 false
% 11.40/2.02  --dbg_dump_prop_clauses_file            -
% 11.40/2.02  --dbg_out_stat                          false
% 11.40/2.02  
% 11.40/2.02  
% 11.40/2.02  
% 11.40/2.02  
% 11.40/2.02  ------ Proving...
% 11.40/2.02  
% 11.40/2.02  
% 11.40/2.02  % SZS status Theorem for theBenchmark.p
% 11.40/2.02  
% 11.40/2.02  % SZS output start CNFRefutation for theBenchmark.p
% 11.40/2.02  
% 11.40/2.02  fof(f13,conjecture,(
% 11.40/2.02    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 11.40/2.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.40/2.02  
% 11.40/2.02  fof(f14,negated_conjecture,(
% 11.40/2.02    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 11.40/2.02    inference(negated_conjecture,[],[f13])).
% 11.40/2.02  
% 11.40/2.02  fof(f22,plain,(
% 11.40/2.02    ? [X0,X1] : (? [X2] : ((r1_tarski(X1,X2) <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.40/2.02    inference(ennf_transformation,[],[f14])).
% 11.40/2.02  
% 11.40/2.02  fof(f28,plain,(
% 11.40/2.02    ? [X0,X1] : (? [X2] : (((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.40/2.02    inference(nnf_transformation,[],[f22])).
% 11.40/2.02  
% 11.40/2.02  fof(f29,plain,(
% 11.40/2.02    ? [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.40/2.02    inference(flattening,[],[f28])).
% 11.40/2.02  
% 11.40/2.02  fof(f31,plain,(
% 11.40/2.02    ( ! [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) => ((~r1_tarski(k3_subset_1(X0,sK3),k3_subset_1(X0,X1)) | ~r1_tarski(X1,sK3)) & (r1_tarski(k3_subset_1(X0,sK3),k3_subset_1(X0,X1)) | r1_tarski(X1,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(X0)))) )),
% 11.40/2.02    introduced(choice_axiom,[])).
% 11.40/2.02  
% 11.40/2.02  fof(f30,plain,(
% 11.40/2.02    ? [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : ((~r1_tarski(k3_subset_1(sK1,X2),k3_subset_1(sK1,sK2)) | ~r1_tarski(sK2,X2)) & (r1_tarski(k3_subset_1(sK1,X2),k3_subset_1(sK1,sK2)) | r1_tarski(sK2,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(sK1)))),
% 11.40/2.02    introduced(choice_axiom,[])).
% 11.40/2.02  
% 11.40/2.02  fof(f32,plain,(
% 11.40/2.02    ((~r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) | ~r1_tarski(sK2,sK3)) & (r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) | r1_tarski(sK2,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 11.40/2.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f29,f31,f30])).
% 11.40/2.02  
% 11.40/2.02  fof(f54,plain,(
% 11.40/2.02    r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) | r1_tarski(sK2,sK3)),
% 11.40/2.02    inference(cnf_transformation,[],[f32])).
% 11.40/2.02  
% 11.40/2.02  fof(f11,axiom,(
% 11.40/2.02    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 11.40/2.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.40/2.02  
% 11.40/2.02  fof(f21,plain,(
% 11.40/2.02    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.40/2.02    inference(ennf_transformation,[],[f11])).
% 11.40/2.02  
% 11.40/2.02  fof(f50,plain,(
% 11.40/2.02    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.40/2.02    inference(cnf_transformation,[],[f21])).
% 11.40/2.02  
% 11.40/2.02  fof(f53,plain,(
% 11.40/2.02    m1_subset_1(sK3,k1_zfmisc_1(sK1))),
% 11.40/2.02    inference(cnf_transformation,[],[f32])).
% 11.40/2.02  
% 11.40/2.02  fof(f52,plain,(
% 11.40/2.02    m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 11.40/2.02    inference(cnf_transformation,[],[f32])).
% 11.40/2.02  
% 11.40/2.02  fof(f5,axiom,(
% 11.40/2.02    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 11.40/2.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.40/2.02  
% 11.40/2.02  fof(f17,plain,(
% 11.40/2.02    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 11.40/2.02    inference(ennf_transformation,[],[f5])).
% 11.40/2.02  
% 11.40/2.02  fof(f38,plain,(
% 11.40/2.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 11.40/2.02    inference(cnf_transformation,[],[f17])).
% 11.40/2.02  
% 11.40/2.02  fof(f7,axiom,(
% 11.40/2.02    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 11.40/2.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.40/2.02  
% 11.40/2.02  fof(f40,plain,(
% 11.40/2.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 11.40/2.02    inference(cnf_transformation,[],[f7])).
% 11.40/2.02  
% 11.40/2.02  fof(f58,plain,(
% 11.40/2.02    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 11.40/2.02    inference(definition_unfolding,[],[f38,f40])).
% 11.40/2.02  
% 11.40/2.02  fof(f1,axiom,(
% 11.40/2.02    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 11.40/2.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.40/2.02  
% 11.40/2.02  fof(f33,plain,(
% 11.40/2.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 11.40/2.02    inference(cnf_transformation,[],[f1])).
% 11.40/2.02  
% 11.40/2.02  fof(f57,plain,(
% 11.40/2.02    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 11.40/2.02    inference(definition_unfolding,[],[f33,f40,f40])).
% 11.40/2.02  
% 11.40/2.02  fof(f6,axiom,(
% 11.40/2.02    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 11.40/2.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.40/2.02  
% 11.40/2.02  fof(f39,plain,(
% 11.40/2.02    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 11.40/2.02    inference(cnf_transformation,[],[f6])).
% 11.40/2.02  
% 11.40/2.02  fof(f10,axiom,(
% 11.40/2.02    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 11.40/2.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.40/2.02  
% 11.40/2.02  fof(f20,plain,(
% 11.40/2.02    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 11.40/2.02    inference(ennf_transformation,[],[f10])).
% 11.40/2.02  
% 11.40/2.02  fof(f27,plain,(
% 11.40/2.02    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 11.40/2.02    inference(nnf_transformation,[],[f20])).
% 11.40/2.02  
% 11.40/2.02  fof(f47,plain,(
% 11.40/2.02    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 11.40/2.02    inference(cnf_transformation,[],[f27])).
% 11.40/2.02  
% 11.40/2.02  fof(f9,axiom,(
% 11.40/2.02    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 11.40/2.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.40/2.02  
% 11.40/2.02  fof(f23,plain,(
% 11.40/2.02    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 11.40/2.02    inference(nnf_transformation,[],[f9])).
% 11.40/2.02  
% 11.40/2.02  fof(f24,plain,(
% 11.40/2.02    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 11.40/2.02    inference(rectify,[],[f23])).
% 11.40/2.02  
% 11.40/2.02  fof(f25,plain,(
% 11.40/2.02    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 11.40/2.02    introduced(choice_axiom,[])).
% 11.40/2.02  
% 11.40/2.02  fof(f26,plain,(
% 11.40/2.02    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 11.40/2.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).
% 11.40/2.02  
% 11.40/2.02  fof(f42,plain,(
% 11.40/2.02    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 11.40/2.02    inference(cnf_transformation,[],[f26])).
% 11.40/2.02  
% 11.40/2.02  fof(f60,plain,(
% 11.40/2.02    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 11.40/2.02    inference(equality_resolution,[],[f42])).
% 11.40/2.02  
% 11.40/2.02  fof(f43,plain,(
% 11.40/2.02    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 11.40/2.02    inference(cnf_transformation,[],[f26])).
% 11.40/2.02  
% 11.40/2.02  fof(f59,plain,(
% 11.40/2.02    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 11.40/2.02    inference(equality_resolution,[],[f43])).
% 11.40/2.02  
% 11.40/2.02  fof(f12,axiom,(
% 11.40/2.02    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 11.40/2.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.40/2.02  
% 11.40/2.02  fof(f51,plain,(
% 11.40/2.02    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 11.40/2.02    inference(cnf_transformation,[],[f12])).
% 11.40/2.02  
% 11.40/2.02  fof(f3,axiom,(
% 11.40/2.02    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 11.40/2.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.40/2.02  
% 11.40/2.02  fof(f35,plain,(
% 11.40/2.02    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 11.40/2.02    inference(cnf_transformation,[],[f3])).
% 11.40/2.02  
% 11.40/2.02  fof(f56,plain,(
% 11.40/2.02    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 11.40/2.02    inference(definition_unfolding,[],[f35,f40])).
% 11.40/2.02  
% 11.40/2.02  fof(f46,plain,(
% 11.40/2.02    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 11.40/2.02    inference(cnf_transformation,[],[f27])).
% 11.40/2.02  
% 11.40/2.02  fof(f55,plain,(
% 11.40/2.02    ~r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) | ~r1_tarski(sK2,sK3)),
% 11.40/2.02    inference(cnf_transformation,[],[f32])).
% 11.40/2.02  
% 11.40/2.02  fof(f8,axiom,(
% 11.40/2.02    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 11.40/2.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.40/2.02  
% 11.40/2.02  fof(f18,plain,(
% 11.40/2.02    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)))),
% 11.40/2.02    inference(ennf_transformation,[],[f8])).
% 11.40/2.02  
% 11.40/2.02  fof(f19,plain,(
% 11.40/2.02    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))),
% 11.40/2.02    inference(flattening,[],[f18])).
% 11.40/2.02  
% 11.40/2.02  fof(f41,plain,(
% 11.40/2.02    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 11.40/2.02    inference(cnf_transformation,[],[f19])).
% 11.40/2.02  
% 11.40/2.02  fof(f4,axiom,(
% 11.40/2.02    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 11.40/2.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.40/2.02  
% 11.40/2.02  fof(f16,plain,(
% 11.40/2.02    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 11.40/2.02    inference(ennf_transformation,[],[f4])).
% 11.40/2.02  
% 11.40/2.02  fof(f37,plain,(
% 11.40/2.02    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 11.40/2.02    inference(cnf_transformation,[],[f16])).
% 11.40/2.02  
% 11.40/2.02  fof(f2,axiom,(
% 11.40/2.02    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 11.40/2.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.40/2.02  
% 11.40/2.02  fof(f15,plain,(
% 11.40/2.02    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 11.40/2.02    inference(ennf_transformation,[],[f2])).
% 11.40/2.02  
% 11.40/2.02  fof(f34,plain,(
% 11.40/2.02    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 11.40/2.02    inference(cnf_transformation,[],[f15])).
% 11.40/2.02  
% 11.40/2.02  cnf(c_19,negated_conjecture,
% 11.40/2.02      ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
% 11.40/2.02      | r1_tarski(sK2,sK3) ),
% 11.40/2.02      inference(cnf_transformation,[],[f54]) ).
% 11.40/2.02  
% 11.40/2.02  cnf(c_1230,plain,
% 11.40/2.02      ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) = iProver_top
% 11.40/2.02      | r1_tarski(sK2,sK3) = iProver_top ),
% 11.40/2.02      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 11.40/2.02  
% 11.40/2.02  cnf(c_16,plain,
% 11.40/2.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.40/2.02      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 11.40/2.02      inference(cnf_transformation,[],[f50]) ).
% 11.40/2.02  
% 11.40/2.02  cnf(c_20,negated_conjecture,
% 11.40/2.02      ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
% 11.40/2.02      inference(cnf_transformation,[],[f53]) ).
% 11.40/2.02  
% 11.40/2.02  cnf(c_462,plain,
% 11.40/2.02      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 11.40/2.02      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
% 11.40/2.02      | sK3 != X1 ),
% 11.40/2.02      inference(resolution_lifted,[status(thm)],[c_16,c_20]) ).
% 11.40/2.02  
% 11.40/2.02  cnf(c_463,plain,
% 11.40/2.02      ( k3_subset_1(X0,sK3) = k4_xboole_0(X0,sK3)
% 11.40/2.02      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
% 11.40/2.02      inference(unflattening,[status(thm)],[c_462]) ).
% 11.40/2.02  
% 11.40/2.02  cnf(c_1314,plain,
% 11.40/2.02      ( k3_subset_1(sK1,sK3) = k4_xboole_0(sK1,sK3) ),
% 11.40/2.02      inference(equality_resolution,[status(thm)],[c_463]) ).
% 11.40/2.02  
% 11.40/2.02  cnf(c_21,negated_conjecture,
% 11.40/2.02      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
% 11.40/2.02      inference(cnf_transformation,[],[f52]) ).
% 11.40/2.02  
% 11.40/2.02  cnf(c_471,plain,
% 11.40/2.02      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 11.40/2.02      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
% 11.40/2.02      | sK2 != X1 ),
% 11.40/2.02      inference(resolution_lifted,[status(thm)],[c_16,c_21]) ).
% 11.40/2.02  
% 11.40/2.02  cnf(c_472,plain,
% 11.40/2.02      ( k3_subset_1(X0,sK2) = k4_xboole_0(X0,sK2)
% 11.40/2.02      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
% 11.40/2.02      inference(unflattening,[status(thm)],[c_471]) ).
% 11.40/2.02  
% 11.40/2.02  cnf(c_1315,plain,
% 11.40/2.02      ( k3_subset_1(sK1,sK2) = k4_xboole_0(sK1,sK2) ),
% 11.40/2.02      inference(equality_resolution,[status(thm)],[c_472]) ).
% 11.40/2.02  
% 11.40/2.02  cnf(c_1377,plain,
% 11.40/2.02      ( r1_tarski(k4_xboole_0(sK1,sK3),k4_xboole_0(sK1,sK2)) = iProver_top
% 11.40/2.02      | r1_tarski(sK2,sK3) = iProver_top ),
% 11.40/2.02      inference(light_normalisation,[status(thm)],[c_1230,c_1314,c_1315]) ).
% 11.40/2.02  
% 11.40/2.02  cnf(c_5,plain,
% 11.40/2.02      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 11.40/2.02      inference(cnf_transformation,[],[f58]) ).
% 11.40/2.02  
% 11.40/2.02  cnf(c_1238,plain,
% 11.40/2.02      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 11.40/2.02      | r1_tarski(X0,X1) != iProver_top ),
% 11.40/2.02      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.40/2.02  
% 11.40/2.02  cnf(c_2287,plain,
% 11.40/2.02      ( k4_xboole_0(k4_xboole_0(sK1,sK3),k4_xboole_0(k4_xboole_0(sK1,sK3),k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK1,sK3)
% 11.40/2.02      | r1_tarski(sK2,sK3) = iProver_top ),
% 11.40/2.02      inference(superposition,[status(thm)],[c_1377,c_1238]) ).
% 11.40/2.02  
% 11.40/2.02  cnf(c_2523,plain,
% 11.40/2.02      ( k4_xboole_0(k4_xboole_0(sK1,sK3),k4_xboole_0(k4_xboole_0(sK1,sK3),k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK1,sK3)
% 11.40/2.02      | k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = sK2 ),
% 11.40/2.02      inference(superposition,[status(thm)],[c_2287,c_1238]) ).
% 11.40/2.02  
% 11.40/2.02  cnf(c_1,plain,
% 11.40/2.02      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 11.40/2.02      inference(cnf_transformation,[],[f57]) ).
% 11.40/2.02  
% 11.40/2.02  cnf(c_6,plain,
% 11.40/2.02      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 11.40/2.02      inference(cnf_transformation,[],[f39]) ).
% 11.40/2.02  
% 11.40/2.02  cnf(c_1237,plain,
% 11.40/2.02      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 11.40/2.02      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.40/2.02  
% 11.40/2.02  cnf(c_1741,plain,
% 11.40/2.02      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = iProver_top ),
% 11.40/2.02      inference(superposition,[status(thm)],[c_1,c_1237]) ).
% 11.40/2.02  
% 11.40/2.02  cnf(c_14,plain,
% 11.40/2.02      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 11.40/2.02      inference(cnf_transformation,[],[f47]) ).
% 11.40/2.02  
% 11.40/2.02  cnf(c_405,plain,
% 11.40/2.02      ( ~ r2_hidden(X0,X1)
% 11.40/2.02      | v1_xboole_0(X1)
% 11.40/2.02      | X2 != X0
% 11.40/2.02      | k3_subset_1(X3,X2) = k4_xboole_0(X3,X2)
% 11.40/2.02      | k1_zfmisc_1(X3) != X1 ),
% 11.40/2.02      inference(resolution_lifted,[status(thm)],[c_14,c_16]) ).
% 11.40/2.02  
% 11.40/2.02  cnf(c_406,plain,
% 11.40/2.02      ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
% 11.40/2.02      | v1_xboole_0(k1_zfmisc_1(X1))
% 11.40/2.02      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 11.40/2.02      inference(unflattening,[status(thm)],[c_405]) ).
% 11.40/2.02  
% 11.40/2.02  cnf(c_11,plain,
% 11.40/2.02      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 11.40/2.02      inference(cnf_transformation,[],[f60]) ).
% 11.40/2.02  
% 11.40/2.02  cnf(c_10,plain,
% 11.40/2.02      ( r2_hidden(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.40/2.02      inference(cnf_transformation,[],[f59]) ).
% 11.40/2.02  
% 11.40/2.02  cnf(c_163,plain,
% 11.40/2.02      ( ~ r1_tarski(X0,X1) | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 11.40/2.02      inference(prop_impl,[status(thm)],[c_10]) ).
% 11.40/2.02  
% 11.40/2.02  cnf(c_164,plain,
% 11.40/2.02      ( r2_hidden(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.40/2.02      inference(renaming,[status(thm)],[c_163]) ).
% 11.40/2.02  
% 11.40/2.02  cnf(c_349,plain,
% 11.40/2.02      ( m1_subset_1(X0,X1)
% 11.40/2.02      | ~ r1_tarski(X2,X3)
% 11.40/2.02      | v1_xboole_0(X1)
% 11.40/2.02      | X0 != X2
% 11.40/2.02      | k1_zfmisc_1(X3) != X1 ),
% 11.40/2.02      inference(resolution_lifted,[status(thm)],[c_164,c_14]) ).
% 11.40/2.02  
% 11.40/2.02  cnf(c_350,plain,
% 11.40/2.02      ( m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.40/2.02      | ~ r1_tarski(X0,X1)
% 11.40/2.02      | v1_xboole_0(k1_zfmisc_1(X1)) ),
% 11.40/2.02      inference(unflattening,[status(thm)],[c_349]) ).
% 11.40/2.02  
% 11.40/2.02  cnf(c_17,plain,
% 11.40/2.02      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 11.40/2.02      inference(cnf_transformation,[],[f51]) ).
% 11.40/2.02  
% 11.40/2.02  cnf(c_360,plain,
% 11.40/2.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.40/2.02      inference(forward_subsumption_resolution,
% 11.40/2.02                [status(thm)],
% 11.40/2.02                [c_350,c_17]) ).
% 11.40/2.02  
% 11.40/2.02  cnf(c_410,plain,
% 11.40/2.02      ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
% 11.40/2.02      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 11.40/2.02      inference(global_propositional_subsumption,
% 11.40/2.02                [status(thm)],
% 11.40/2.02                [c_406,c_16,c_11,c_360]) ).
% 11.40/2.02  
% 11.40/2.02  cnf(c_674,plain,
% 11.40/2.02      ( ~ r1_tarski(X0,X1) | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 11.40/2.02      inference(prop_impl,[status(thm)],[c_10]) ).
% 11.40/2.02  
% 11.40/2.03  cnf(c_675,plain,
% 11.40/2.03      ( r2_hidden(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.40/2.03      inference(renaming,[status(thm)],[c_674]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_713,plain,
% 11.40/2.03      ( ~ r1_tarski(X0,X1) | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 11.40/2.03      inference(bin_hyper_res,[status(thm)],[c_410,c_675]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_1227,plain,
% 11.40/2.03      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 11.40/2.03      | r1_tarski(X1,X0) != iProver_top ),
% 11.40/2.03      inference(predicate_to_equality,[status(thm)],[c_713]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_1836,plain,
% 11.40/2.03      ( k3_subset_1(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 11.40/2.03      inference(superposition,[status(thm)],[c_1741,c_1227]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_5633,plain,
% 11.40/2.03      ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK3),k4_xboole_0(k4_xboole_0(sK1,sK3),k4_xboole_0(sK1,sK2)))) = k3_subset_1(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK3))
% 11.40/2.03      | k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = sK2 ),
% 11.40/2.03      inference(superposition,[status(thm)],[c_2523,c_1836]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_0,plain,
% 11.40/2.03      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 11.40/2.03      inference(cnf_transformation,[],[f56]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_12949,plain,
% 11.40/2.03      ( k5_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),k3_subset_1(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK3)))) = k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK3),k4_xboole_0(k4_xboole_0(sK1,sK3),k4_xboole_0(sK1,sK2))))
% 11.40/2.03      | k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = sK2 ),
% 11.40/2.03      inference(superposition,[status(thm)],[c_5633,c_0]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_161,plain,
% 11.40/2.03      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 11.40/2.03      inference(prop_impl,[status(thm)],[c_11]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_162,plain,
% 11.40/2.03      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 11.40/2.03      inference(renaming,[status(thm)],[c_161]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_15,plain,
% 11.40/2.03      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 11.40/2.03      inference(cnf_transformation,[],[f46]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_426,plain,
% 11.40/2.03      ( r2_hidden(X0,X1)
% 11.40/2.03      | v1_xboole_0(X1)
% 11.40/2.03      | k1_zfmisc_1(sK1) != X1
% 11.40/2.03      | sK3 != X0 ),
% 11.40/2.03      inference(resolution_lifted,[status(thm)],[c_15,c_20]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_427,plain,
% 11.40/2.03      ( r2_hidden(sK3,k1_zfmisc_1(sK1)) | v1_xboole_0(k1_zfmisc_1(sK1)) ),
% 11.40/2.03      inference(unflattening,[status(thm)],[c_426]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_27,plain,
% 11.40/2.03      ( ~ v1_xboole_0(k1_zfmisc_1(sK1)) ),
% 11.40/2.03      inference(instantiation,[status(thm)],[c_17]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_429,plain,
% 11.40/2.03      ( r2_hidden(sK3,k1_zfmisc_1(sK1)) ),
% 11.40/2.03      inference(global_propositional_subsumption,
% 11.40/2.03                [status(thm)],
% 11.40/2.03                [c_427,c_27]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_571,plain,
% 11.40/2.03      ( r1_tarski(X0,X1)
% 11.40/2.03      | k1_zfmisc_1(X1) != k1_zfmisc_1(sK1)
% 11.40/2.03      | sK3 != X0 ),
% 11.40/2.03      inference(resolution_lifted,[status(thm)],[c_162,c_429]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_572,plain,
% 11.40/2.03      ( r1_tarski(sK3,X0) | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
% 11.40/2.03      inference(unflattening,[status(thm)],[c_571]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_574,plain,
% 11.40/2.03      ( r1_tarski(sK3,sK1) | k1_zfmisc_1(sK1) != k1_zfmisc_1(sK1) ),
% 11.40/2.03      inference(instantiation,[status(thm)],[c_572]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_444,plain,
% 11.40/2.03      ( r2_hidden(X0,X1)
% 11.40/2.03      | v1_xboole_0(X1)
% 11.40/2.03      | k1_zfmisc_1(sK1) != X1
% 11.40/2.03      | sK2 != X0 ),
% 11.40/2.03      inference(resolution_lifted,[status(thm)],[c_15,c_21]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_445,plain,
% 11.40/2.03      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) | v1_xboole_0(k1_zfmisc_1(sK1)) ),
% 11.40/2.03      inference(unflattening,[status(thm)],[c_444]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_447,plain,
% 11.40/2.03      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) ),
% 11.40/2.03      inference(global_propositional_subsumption,
% 11.40/2.03                [status(thm)],
% 11.40/2.03                [c_445,c_27]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_585,plain,
% 11.40/2.03      ( r1_tarski(X0,X1)
% 11.40/2.03      | k1_zfmisc_1(X1) != k1_zfmisc_1(sK1)
% 11.40/2.03      | sK2 != X0 ),
% 11.40/2.03      inference(resolution_lifted,[status(thm)],[c_162,c_447]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_586,plain,
% 11.40/2.03      ( r1_tarski(sK2,X0) | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
% 11.40/2.03      inference(unflattening,[status(thm)],[c_585]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_587,plain,
% 11.40/2.03      ( k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
% 11.40/2.03      | r1_tarski(sK2,X0) = iProver_top ),
% 11.40/2.03      inference(predicate_to_equality,[status(thm)],[c_586]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_589,plain,
% 11.40/2.03      ( k1_zfmisc_1(sK1) != k1_zfmisc_1(sK1)
% 11.40/2.03      | r1_tarski(sK2,sK1) = iProver_top ),
% 11.40/2.03      inference(instantiation,[status(thm)],[c_587]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_864,plain,
% 11.40/2.03      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 11.40/2.03      theory(equality) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_870,plain,
% 11.40/2.03      ( k1_zfmisc_1(sK1) = k1_zfmisc_1(sK1) | sK1 != sK1 ),
% 11.40/2.03      inference(instantiation,[status(thm)],[c_864]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_859,plain,( X0 = X0 ),theory(equality) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_874,plain,
% 11.40/2.03      ( sK1 = sK1 ),
% 11.40/2.03      inference(instantiation,[status(thm)],[c_859]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_18,negated_conjecture,
% 11.40/2.03      ( ~ r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
% 11.40/2.03      | ~ r1_tarski(sK2,sK3) ),
% 11.40/2.03      inference(cnf_transformation,[],[f55]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_1231,plain,
% 11.40/2.03      ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) != iProver_top
% 11.40/2.03      | r1_tarski(sK2,sK3) != iProver_top ),
% 11.40/2.03      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_1374,plain,
% 11.40/2.03      ( r1_tarski(k4_xboole_0(sK1,sK3),k4_xboole_0(sK1,sK2)) != iProver_top
% 11.40/2.03      | r1_tarski(sK2,sK3) != iProver_top ),
% 11.40/2.03      inference(light_normalisation,[status(thm)],[c_1231,c_1314,c_1315]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_1413,plain,
% 11.40/2.03      ( sK2 = sK2 ),
% 11.40/2.03      inference(instantiation,[status(thm)],[c_859]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_1675,plain,
% 11.40/2.03      ( sK3 = sK3 ),
% 11.40/2.03      inference(instantiation,[status(thm)],[c_859]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_863,plain,
% 11.40/2.03      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.40/2.03      theory(equality) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_1297,plain,
% 11.40/2.03      ( ~ r1_tarski(X0,X1)
% 11.40/2.03      | r1_tarski(sK2,k4_xboole_0(sK3,X2))
% 11.40/2.03      | k4_xboole_0(sK3,X2) != X1
% 11.40/2.03      | sK2 != X0 ),
% 11.40/2.03      inference(instantiation,[status(thm)],[c_863]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_1358,plain,
% 11.40/2.03      ( ~ r1_tarski(sK2,X0)
% 11.40/2.03      | r1_tarski(sK2,k4_xboole_0(sK3,X1))
% 11.40/2.03      | k4_xboole_0(sK3,X1) != X0
% 11.40/2.03      | sK2 != sK2 ),
% 11.40/2.03      inference(instantiation,[status(thm)],[c_1297]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_1748,plain,
% 11.40/2.03      ( ~ r1_tarski(sK2,k4_xboole_0(X0,k4_xboole_0(X0,sK3)))
% 11.40/2.03      | r1_tarski(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,X0)))
% 11.40/2.03      | k4_xboole_0(sK3,k4_xboole_0(sK3,X0)) != k4_xboole_0(X0,k4_xboole_0(X0,sK3))
% 11.40/2.03      | sK2 != sK2 ),
% 11.40/2.03      inference(instantiation,[status(thm)],[c_1358]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_1749,plain,
% 11.40/2.03      ( k4_xboole_0(sK3,k4_xboole_0(sK3,X0)) != k4_xboole_0(X0,k4_xboole_0(X0,sK3))
% 11.40/2.03      | sK2 != sK2
% 11.40/2.03      | r1_tarski(sK2,k4_xboole_0(X0,k4_xboole_0(X0,sK3))) != iProver_top
% 11.40/2.03      | r1_tarski(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,X0))) = iProver_top ),
% 11.40/2.03      inference(predicate_to_equality,[status(thm)],[c_1748]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_1751,plain,
% 11.40/2.03      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) != k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))
% 11.40/2.03      | sK2 != sK2
% 11.40/2.03      | r1_tarski(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK1))) = iProver_top
% 11.40/2.03      | r1_tarski(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))) != iProver_top ),
% 11.40/2.03      inference(instantiation,[status(thm)],[c_1749]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_2218,plain,
% 11.40/2.03      ( ~ r1_tarski(sK3,X0)
% 11.40/2.03      | k4_xboole_0(sK3,k4_xboole_0(sK3,X0)) = sK3 ),
% 11.40/2.03      inference(instantiation,[status(thm)],[c_5]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_2220,plain,
% 11.40/2.03      ( ~ r1_tarski(sK3,sK1)
% 11.40/2.03      | k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) = sK3 ),
% 11.40/2.03      inference(instantiation,[status(thm)],[c_2218]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_860,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_1365,plain,
% 11.40/2.03      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 11.40/2.03      inference(instantiation,[status(thm)],[c_860]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_1427,plain,
% 11.40/2.03      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 11.40/2.03      inference(instantiation,[status(thm)],[c_1365]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_2546,plain,
% 11.40/2.03      ( k4_xboole_0(sK3,k4_xboole_0(sK3,X0)) != sK3
% 11.40/2.03      | sK3 = k4_xboole_0(sK3,k4_xboole_0(sK3,X0))
% 11.40/2.03      | sK3 != sK3 ),
% 11.40/2.03      inference(instantiation,[status(thm)],[c_1427]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_2547,plain,
% 11.40/2.03      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) != sK3
% 11.40/2.03      | sK3 = k4_xboole_0(sK3,k4_xboole_0(sK3,sK1))
% 11.40/2.03      | sK3 != sK3 ),
% 11.40/2.03      inference(instantiation,[status(thm)],[c_2546]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_3020,plain,
% 11.40/2.03      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = sK2
% 11.40/2.03      | r1_tarski(k4_xboole_0(sK1,sK3),k4_xboole_0(sK1,sK2)) = iProver_top ),
% 11.40/2.03      inference(superposition,[status(thm)],[c_2523,c_1741]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_1269,plain,
% 11.40/2.03      ( ~ r1_tarski(X0,X1) | r1_tarski(sK2,sK3) | sK2 != X0 | sK3 != X1 ),
% 11.40/2.03      inference(instantiation,[status(thm)],[c_863]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_1308,plain,
% 11.40/2.03      ( ~ r1_tarski(sK2,X0)
% 11.40/2.03      | r1_tarski(sK2,sK3)
% 11.40/2.03      | sK2 != sK2
% 11.40/2.03      | sK3 != X0 ),
% 11.40/2.03      inference(instantiation,[status(thm)],[c_1269]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_4487,plain,
% 11.40/2.03      ( ~ r1_tarski(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,X0)))
% 11.40/2.03      | r1_tarski(sK2,sK3)
% 11.40/2.03      | sK2 != sK2
% 11.40/2.03      | sK3 != k4_xboole_0(sK3,k4_xboole_0(sK3,X0)) ),
% 11.40/2.03      inference(instantiation,[status(thm)],[c_1308]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_4488,plain,
% 11.40/2.03      ( sK2 != sK2
% 11.40/2.03      | sK3 != k4_xboole_0(sK3,k4_xboole_0(sK3,X0))
% 11.40/2.03      | r1_tarski(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,X0))) != iProver_top
% 11.40/2.03      | r1_tarski(sK2,sK3) = iProver_top ),
% 11.40/2.03      inference(predicate_to_equality,[status(thm)],[c_4487]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_4490,plain,
% 11.40/2.03      ( sK2 != sK2
% 11.40/2.03      | sK3 != k4_xboole_0(sK3,k4_xboole_0(sK3,sK1))
% 11.40/2.03      | r1_tarski(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK1))) != iProver_top
% 11.40/2.03      | r1_tarski(sK2,sK3) = iProver_top ),
% 11.40/2.03      inference(instantiation,[status(thm)],[c_4488]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_7,plain,
% 11.40/2.03      ( ~ r1_tarski(X0,X1)
% 11.40/2.03      | r1_tarski(X0,k4_xboole_0(X1,X2))
% 11.40/2.03      | ~ r1_xboole_0(X0,X2) ),
% 11.40/2.03      inference(cnf_transformation,[],[f41]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_1489,plain,
% 11.40/2.03      ( ~ r1_tarski(sK2,X0)
% 11.40/2.03      | r1_tarski(sK2,k4_xboole_0(X0,X1))
% 11.40/2.03      | ~ r1_xboole_0(sK2,X1) ),
% 11.40/2.03      inference(instantiation,[status(thm)],[c_7]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_4528,plain,
% 11.40/2.03      ( ~ r1_tarski(sK2,X0)
% 11.40/2.03      | r1_tarski(sK2,k4_xboole_0(X0,k4_xboole_0(X0,sK3)))
% 11.40/2.03      | ~ r1_xboole_0(sK2,k4_xboole_0(X0,sK3)) ),
% 11.40/2.03      inference(instantiation,[status(thm)],[c_1489]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_4529,plain,
% 11.40/2.03      ( r1_tarski(sK2,X0) != iProver_top
% 11.40/2.03      | r1_tarski(sK2,k4_xboole_0(X0,k4_xboole_0(X0,sK3))) = iProver_top
% 11.40/2.03      | r1_xboole_0(sK2,k4_xboole_0(X0,sK3)) != iProver_top ),
% 11.40/2.03      inference(predicate_to_equality,[status(thm)],[c_4528]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_4531,plain,
% 11.40/2.03      ( r1_tarski(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))) = iProver_top
% 11.40/2.03      | r1_tarski(sK2,sK1) != iProver_top
% 11.40/2.03      | r1_xboole_0(sK2,k4_xboole_0(sK1,sK3)) != iProver_top ),
% 11.40/2.03      inference(instantiation,[status(thm)],[c_4529]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_3,plain,
% 11.40/2.03      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2) ),
% 11.40/2.03      inference(cnf_transformation,[],[f37]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_1240,plain,
% 11.40/2.03      ( r1_tarski(X0,k4_xboole_0(X1,X2)) != iProver_top
% 11.40/2.03      | r1_xboole_0(X0,X2) = iProver_top ),
% 11.40/2.03      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_6343,plain,
% 11.40/2.03      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = sK2
% 11.40/2.03      | r1_xboole_0(k4_xboole_0(sK1,sK3),sK2) = iProver_top ),
% 11.40/2.03      inference(superposition,[status(thm)],[c_3020,c_1240]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_2,plain,
% 11.40/2.03      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 11.40/2.03      inference(cnf_transformation,[],[f34]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_1398,plain,
% 11.40/2.03      ( ~ r1_xboole_0(X0,sK2) | r1_xboole_0(sK2,X0) ),
% 11.40/2.03      inference(instantiation,[status(thm)],[c_2]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_9736,plain,
% 11.40/2.03      ( ~ r1_xboole_0(k4_xboole_0(X0,sK3),sK2)
% 11.40/2.03      | r1_xboole_0(sK2,k4_xboole_0(X0,sK3)) ),
% 11.40/2.03      inference(instantiation,[status(thm)],[c_1398]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_9742,plain,
% 11.40/2.03      ( r1_xboole_0(k4_xboole_0(X0,sK3),sK2) != iProver_top
% 11.40/2.03      | r1_xboole_0(sK2,k4_xboole_0(X0,sK3)) = iProver_top ),
% 11.40/2.03      inference(predicate_to_equality,[status(thm)],[c_9736]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_9744,plain,
% 11.40/2.03      ( r1_xboole_0(k4_xboole_0(sK1,sK3),sK2) != iProver_top
% 11.40/2.03      | r1_xboole_0(sK2,k4_xboole_0(sK1,sK3)) = iProver_top ),
% 11.40/2.03      inference(instantiation,[status(thm)],[c_9742]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_22731,plain,
% 11.40/2.03      ( k4_xboole_0(sK3,k4_xboole_0(sK3,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,sK3)) ),
% 11.40/2.03      inference(instantiation,[status(thm)],[c_1]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_22732,plain,
% 11.40/2.03      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) ),
% 11.40/2.03      inference(instantiation,[status(thm)],[c_22731]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_22752,plain,
% 11.40/2.03      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = sK2 ),
% 11.40/2.03      inference(global_propositional_subsumption,
% 11.40/2.03                [status(thm)],
% 11.40/2.03                [c_12949,c_574,c_589,c_870,c_874,c_1374,c_1413,c_1675,
% 11.40/2.03                 c_1751,c_2220,c_2547,c_3020,c_4490,c_4531,c_6343,c_9744,
% 11.40/2.03                 c_22732]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_22881,plain,
% 11.40/2.03      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)) = sK2 ),
% 11.40/2.03      inference(superposition,[status(thm)],[c_22752,c_1]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_1229,plain,
% 11.40/2.03      ( r2_hidden(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
% 11.40/2.03      inference(predicate_to_equality,[status(thm)],[c_429]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_1232,plain,
% 11.40/2.03      ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
% 11.40/2.03      | r1_tarski(X0,X1) = iProver_top ),
% 11.40/2.03      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_2105,plain,
% 11.40/2.03      ( r1_tarski(sK3,sK1) = iProver_top ),
% 11.40/2.03      inference(superposition,[status(thm)],[c_1229,c_1232]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_2286,plain,
% 11.40/2.03      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) = sK3 ),
% 11.40/2.03      inference(superposition,[status(thm)],[c_2105,c_1238]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_2667,plain,
% 11.40/2.03      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = sK3 ),
% 11.40/2.03      inference(superposition,[status(thm)],[c_2286,c_1]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_2398,plain,
% 11.40/2.03      ( r1_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X1) = iProver_top ),
% 11.40/2.03      inference(superposition,[status(thm)],[c_1237,c_1240]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_31962,plain,
% 11.40/2.03      ( r1_xboole_0(k4_xboole_0(sK3,X0),k4_xboole_0(sK1,sK3)) = iProver_top ),
% 11.40/2.03      inference(superposition,[status(thm)],[c_2667,c_2398]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_32568,plain,
% 11.40/2.03      ( r1_xboole_0(sK2,k4_xboole_0(sK1,sK3)) = iProver_top ),
% 11.40/2.03      inference(superposition,[status(thm)],[c_22881,c_31962]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_22836,plain,
% 11.40/2.03      ( r1_tarski(sK2,sK3) = iProver_top ),
% 11.40/2.03      inference(superposition,[status(thm)],[c_22752,c_1741]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_1479,plain,
% 11.40/2.03      ( r1_xboole_0(X0,sK2) | ~ r1_xboole_0(sK2,X0) ),
% 11.40/2.03      inference(instantiation,[status(thm)],[c_2]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_4412,plain,
% 11.40/2.03      ( r1_xboole_0(k4_xboole_0(sK1,X0),sK2)
% 11.40/2.03      | ~ r1_xboole_0(sK2,k4_xboole_0(sK1,X0)) ),
% 11.40/2.03      inference(instantiation,[status(thm)],[c_1479]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_18100,plain,
% 11.40/2.03      ( r1_xboole_0(k4_xboole_0(sK1,sK3),sK2)
% 11.40/2.03      | ~ r1_xboole_0(sK2,k4_xboole_0(sK1,sK3)) ),
% 11.40/2.03      inference(instantiation,[status(thm)],[c_4412]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_18103,plain,
% 11.40/2.03      ( r1_xboole_0(k4_xboole_0(sK1,sK3),sK2) = iProver_top
% 11.40/2.03      | r1_xboole_0(sK2,k4_xboole_0(sK1,sK3)) != iProver_top ),
% 11.40/2.03      inference(predicate_to_equality,[status(thm)],[c_18100]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_1236,plain,
% 11.40/2.03      ( r1_tarski(X0,X1) != iProver_top
% 11.40/2.03      | r1_tarski(X0,k4_xboole_0(X1,X2)) = iProver_top
% 11.40/2.03      | r1_xboole_0(X0,X2) != iProver_top ),
% 11.40/2.03      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_4464,plain,
% 11.40/2.03      ( r1_tarski(k4_xboole_0(sK1,sK3),sK1) != iProver_top
% 11.40/2.03      | r1_tarski(sK2,sK3) != iProver_top
% 11.40/2.03      | r1_xboole_0(k4_xboole_0(sK1,sK3),sK2) != iProver_top ),
% 11.40/2.03      inference(superposition,[status(thm)],[c_1236,c_1374]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_3542,plain,
% 11.40/2.03      ( r1_tarski(k4_xboole_0(sK1,sK3),sK1) ),
% 11.40/2.03      inference(instantiation,[status(thm)],[c_6]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(c_3543,plain,
% 11.40/2.03      ( r1_tarski(k4_xboole_0(sK1,sK3),sK1) = iProver_top ),
% 11.40/2.03      inference(predicate_to_equality,[status(thm)],[c_3542]) ).
% 11.40/2.03  
% 11.40/2.03  cnf(contradiction,plain,
% 11.40/2.03      ( $false ),
% 11.40/2.03      inference(minisat,
% 11.40/2.03                [status(thm)],
% 11.40/2.03                [c_32568,c_22836,c_18103,c_4464,c_3543]) ).
% 11.40/2.03  
% 11.40/2.03  
% 11.40/2.03  % SZS output end CNFRefutation for theBenchmark.p
% 11.40/2.03  
% 11.40/2.03  ------                               Statistics
% 11.40/2.03  
% 11.40/2.03  ------ General
% 11.40/2.03  
% 11.40/2.03  abstr_ref_over_cycles:                  0
% 11.40/2.03  abstr_ref_under_cycles:                 0
% 11.40/2.03  gc_basic_clause_elim:                   0
% 11.40/2.03  forced_gc_time:                         0
% 11.40/2.03  parsing_time:                           0.005
% 11.40/2.03  unif_index_cands_time:                  0.
% 11.40/2.03  unif_index_add_time:                    0.
% 11.40/2.03  orderings_time:                         0.
% 11.40/2.03  out_proof_time:                         0.012
% 11.40/2.03  total_time:                             1.034
% 11.40/2.03  num_of_symbols:                         44
% 11.40/2.03  num_of_terms:                           32200
% 11.40/2.03  
% 11.40/2.03  ------ Preprocessing
% 11.40/2.03  
% 11.40/2.03  num_of_splits:                          0
% 11.40/2.03  num_of_split_atoms:                     0
% 11.40/2.03  num_of_reused_defs:                     0
% 11.40/2.03  num_eq_ax_congr_red:                    18
% 11.40/2.03  num_of_sem_filtered_clauses:            1
% 11.40/2.03  num_of_subtypes:                        0
% 11.40/2.03  monotx_restored_types:                  0
% 11.40/2.03  sat_num_of_epr_types:                   0
% 11.40/2.03  sat_num_of_non_cyclic_types:            0
% 11.40/2.03  sat_guarded_non_collapsed_types:        0
% 11.40/2.03  num_pure_diseq_elim:                    0
% 11.40/2.03  simp_replaced_by:                       0
% 11.40/2.03  res_preprocessed:                       96
% 11.40/2.03  prep_upred:                             0
% 11.40/2.03  prep_unflattend:                        46
% 11.40/2.03  smt_new_axioms:                         0
% 11.40/2.03  pred_elim_cands:                        3
% 11.40/2.03  pred_elim:                              2
% 11.40/2.03  pred_elim_cl:                           3
% 11.40/2.03  pred_elim_cycles:                       5
% 11.40/2.03  merged_defs:                            16
% 11.40/2.03  merged_defs_ncl:                        0
% 11.40/2.03  bin_hyper_res:                          17
% 11.40/2.03  prep_cycles:                            4
% 11.40/2.03  pred_elim_time:                         0.004
% 11.40/2.03  splitting_time:                         0.
% 11.40/2.03  sem_filter_time:                        0.
% 11.40/2.03  monotx_time:                            0.
% 11.40/2.03  subtype_inf_time:                       0.
% 11.40/2.03  
% 11.40/2.03  ------ Problem properties
% 11.40/2.03  
% 11.40/2.03  clauses:                                19
% 11.40/2.03  conjectures:                            2
% 11.40/2.03  epr:                                    1
% 11.40/2.03  horn:                                   17
% 11.40/2.03  ground:                                 4
% 11.40/2.03  unary:                                  5
% 11.40/2.03  binary:                                 11
% 11.40/2.03  lits:                                   36
% 11.40/2.03  lits_eq:                                10
% 11.40/2.03  fd_pure:                                0
% 11.40/2.03  fd_pseudo:                              0
% 11.40/2.03  fd_cond:                                0
% 11.40/2.03  fd_pseudo_cond:                         2
% 11.40/2.03  ac_symbols:                             0
% 11.40/2.03  
% 11.40/2.03  ------ Propositional Solver
% 11.40/2.03  
% 11.40/2.03  prop_solver_calls:                      33
% 11.40/2.03  prop_fast_solver_calls:                 975
% 11.40/2.03  smt_solver_calls:                       0
% 11.40/2.03  smt_fast_solver_calls:                  0
% 11.40/2.03  prop_num_of_clauses:                    13748
% 11.40/2.03  prop_preprocess_simplified:             19196
% 11.40/2.03  prop_fo_subsumed:                       13
% 11.40/2.03  prop_solver_time:                       0.
% 11.40/2.03  smt_solver_time:                        0.
% 11.40/2.03  smt_fast_solver_time:                   0.
% 11.40/2.03  prop_fast_solver_time:                  0.
% 11.40/2.03  prop_unsat_core_time:                   0.001
% 11.40/2.03  
% 11.40/2.03  ------ QBF
% 11.40/2.03  
% 11.40/2.03  qbf_q_res:                              0
% 11.40/2.03  qbf_num_tautologies:                    0
% 11.40/2.03  qbf_prep_cycles:                        0
% 11.40/2.03  
% 11.40/2.03  ------ BMC1
% 11.40/2.03  
% 11.40/2.03  bmc1_current_bound:                     -1
% 11.40/2.03  bmc1_last_solved_bound:                 -1
% 11.40/2.03  bmc1_unsat_core_size:                   -1
% 11.40/2.03  bmc1_unsat_core_parents_size:           -1
% 11.40/2.03  bmc1_merge_next_fun:                    0
% 11.40/2.03  bmc1_unsat_core_clauses_time:           0.
% 11.40/2.03  
% 11.40/2.03  ------ Instantiation
% 11.40/2.03  
% 11.40/2.03  inst_num_of_clauses:                    2481
% 11.40/2.03  inst_num_in_passive:                    1413
% 11.40/2.03  inst_num_in_active:                     905
% 11.40/2.03  inst_num_in_unprocessed:                163
% 11.40/2.03  inst_num_of_loops:                      1260
% 11.40/2.03  inst_num_of_learning_restarts:          0
% 11.40/2.03  inst_num_moves_active_passive:          351
% 11.40/2.03  inst_lit_activity:                      0
% 11.40/2.03  inst_lit_activity_moves:                0
% 11.40/2.03  inst_num_tautologies:                   0
% 11.40/2.03  inst_num_prop_implied:                  0
% 11.40/2.03  inst_num_existing_simplified:           0
% 11.40/2.03  inst_num_eq_res_simplified:             0
% 11.40/2.03  inst_num_child_elim:                    0
% 11.40/2.03  inst_num_of_dismatching_blockings:      1989
% 11.40/2.03  inst_num_of_non_proper_insts:           3008
% 11.40/2.03  inst_num_of_duplicates:                 0
% 11.40/2.03  inst_inst_num_from_inst_to_res:         0
% 11.40/2.03  inst_dismatching_checking_time:         0.
% 11.40/2.03  
% 11.40/2.03  ------ Resolution
% 11.40/2.03  
% 11.40/2.03  res_num_of_clauses:                     0
% 11.40/2.03  res_num_in_passive:                     0
% 11.40/2.03  res_num_in_active:                      0
% 11.40/2.03  res_num_of_loops:                       100
% 11.40/2.03  res_forward_subset_subsumed:            181
% 11.40/2.03  res_backward_subset_subsumed:           0
% 11.40/2.03  res_forward_subsumed:                   3
% 11.40/2.03  res_backward_subsumed:                  0
% 11.40/2.03  res_forward_subsumption_resolution:     2
% 11.40/2.03  res_backward_subsumption_resolution:    0
% 11.40/2.03  res_clause_to_clause_subsumption:       30113
% 11.40/2.03  res_orphan_elimination:                 0
% 11.40/2.03  res_tautology_del:                      425
% 11.40/2.03  res_num_eq_res_simplified:              0
% 11.40/2.03  res_num_sel_changes:                    0
% 11.40/2.03  res_moves_from_active_to_pass:          0
% 11.40/2.03  
% 11.40/2.03  ------ Superposition
% 11.40/2.03  
% 11.40/2.03  sup_time_total:                         0.
% 11.40/2.03  sup_time_generating:                    0.
% 11.40/2.03  sup_time_sim_full:                      0.
% 11.40/2.03  sup_time_sim_immed:                     0.
% 11.40/2.03  
% 11.40/2.03  sup_num_of_clauses:                     1179
% 11.40/2.03  sup_num_in_active:                      159
% 11.40/2.03  sup_num_in_passive:                     1020
% 11.40/2.03  sup_num_of_loops:                       251
% 11.40/2.03  sup_fw_superposition:                   3339
% 11.40/2.03  sup_bw_superposition:                   3512
% 11.40/2.03  sup_immediate_simplified:               2591
% 11.40/2.03  sup_given_eliminated:                   5
% 11.40/2.03  comparisons_done:                       0
% 11.40/2.03  comparisons_avoided:                    91
% 11.40/2.03  
% 11.40/2.03  ------ Simplifications
% 11.40/2.03  
% 11.40/2.03  
% 11.40/2.03  sim_fw_subset_subsumed:                 23
% 11.40/2.03  sim_bw_subset_subsumed:                 998
% 11.40/2.03  sim_fw_subsumed:                        419
% 11.40/2.03  sim_bw_subsumed:                        41
% 11.40/2.03  sim_fw_subsumption_res:                 0
% 11.40/2.03  sim_bw_subsumption_res:                 0
% 11.40/2.03  sim_tautology_del:                      184
% 11.40/2.03  sim_eq_tautology_del:                   198
% 11.40/2.03  sim_eq_res_simp:                        0
% 11.40/2.03  sim_fw_demodulated:                     1742
% 11.40/2.03  sim_bw_demodulated:                     105
% 11.40/2.03  sim_light_normalised:                   1169
% 11.40/2.03  sim_joinable_taut:                      0
% 11.40/2.03  sim_joinable_simp:                      0
% 11.40/2.03  sim_ac_normalised:                      0
% 11.40/2.03  sim_smt_subsumption:                    0
% 11.40/2.03  
%------------------------------------------------------------------------------
