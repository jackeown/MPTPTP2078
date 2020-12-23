%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:40:26 EST 2020

% Result     : Theorem 23.65s
% Output     : CNFRefutation 23.65s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 297 expanded)
%              Number of clauses        :  100 ( 134 expanded)
%              Number of leaves         :   22 (  64 expanded)
%              Depth                    :   14
%              Number of atoms          :  388 ( 843 expanded)
%              Number of equality atoms :  154 ( 228 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
     => ( ~ r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,sK3)),k3_subset_1(X0,X1))
        & m1_subset_1(sK3,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,X2)),k3_subset_1(sK1,sK2))
          & m1_subset_1(X2,k1_zfmisc_1(sK1)) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ~ r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2))
    & m1_subset_1(sK3,k1_zfmisc_1(sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f25,f34,f33])).

fof(f57,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f35])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f12,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
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

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f30,plain,(
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

fof(f31,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f63,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f46])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f58,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f35])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f61,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f37])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f62,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f23])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f39,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f59,plain,(
    ~ r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_912,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_918,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1608,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_912,c_918])).

cnf(c_24,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_19,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_30,plain,
    ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_32,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_1113,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | r2_hidden(sK2,k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1114,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) != iProver_top
    | r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1113])).

cnf(c_3458,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1608,c_24,c_32,c_1114])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_922,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3463,plain,
    ( r1_tarski(sK2,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3458,c_922])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_930,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3638,plain,
    ( k2_xboole_0(sK2,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_3463,c_930])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_3652,plain,
    ( k2_xboole_0(sK1,sK2) = sK1 ),
    inference(superposition,[status(thm)],[c_3638,c_0])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_913,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1607,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK1)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_913,c_918])).

cnf(c_25,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1110,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
    | r2_hidden(sK3,k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1111,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
    | r2_hidden(sK3,k1_zfmisc_1(sK1)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1110])).

cnf(c_2815,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1607,c_25,c_32,c_1111])).

cnf(c_2820,plain,
    ( r1_tarski(sK3,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2815,c_922])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_931,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k2_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1734,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k2_xboole_0(X1,X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_931])).

cnf(c_1752,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2)
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1734,c_930])).

cnf(c_4935,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK1,X0)) = k2_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_2820,c_1752])).

cnf(c_83791,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(X0,sK1)) = k2_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_4935])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_932,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
    | r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_928,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1994,plain,
    ( r1_tarski(k4_xboole_0(k2_xboole_0(X0,X1),X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_932,c_928])).

cnf(c_6527,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X0),X1) = X1 ),
    inference(superposition,[status(thm)],[c_1994,c_930])).

cnf(c_9,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_926,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1736,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2)
    | r1_tarski(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_931,c_930])).

cnf(c_4224,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X0,X2))) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_926,c_1736])).

cnf(c_43987,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,k2_xboole_0(X0,X2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4224,c_926])).

cnf(c_46771,plain,
    ( r1_tarski(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_43987])).

cnf(c_47056,plain,
    ( r1_tarski(k4_xboole_0(k2_xboole_0(X0,X1),X0),k2_xboole_0(X1,X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6527,c_46771])).

cnf(c_8,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2))
    | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_927,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) = iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_69307,plain,
    ( r1_tarski(k2_xboole_0(X0,X1),k2_xboole_0(X0,k2_xboole_0(X1,X2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_47056,c_927])).

cnf(c_113156,plain,
    ( r1_tarski(k2_xboole_0(sK3,X0),k2_xboole_0(sK1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_83791,c_69307])).

cnf(c_113789,plain,
    ( r1_tarski(k2_xboole_0(sK3,sK2),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3652,c_113156])).

cnf(c_12,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_47528,plain,
    ( r2_hidden(k2_xboole_0(sK3,sK2),k1_zfmisc_1(X0))
    | ~ r1_tarski(k2_xboole_0(sK3,sK2),X0) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_47529,plain,
    ( r2_hidden(k2_xboole_0(sK3,sK2),k1_zfmisc_1(X0)) = iProver_top
    | r1_tarski(k2_xboole_0(sK3,sK2),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47528])).

cnf(c_47531,plain,
    ( r2_hidden(k2_xboole_0(sK3,sK2),k1_zfmisc_1(sK1)) = iProver_top
    | r1_tarski(k2_xboole_0(sK3,sK2),sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_47529])).

cnf(c_417,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2262,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,k4_subset_1(sK1,sK2,sK3))
    | X2 != X0
    | k4_subset_1(sK1,sK2,sK3) != X1 ),
    inference(instantiation,[status(thm)],[c_417])).

cnf(c_5904,plain,
    ( r1_tarski(X0,k4_subset_1(sK1,sK2,sK3))
    | ~ r1_tarski(X1,k2_xboole_0(sK2,sK3))
    | X0 != X1
    | k4_subset_1(sK1,sK2,sK3) != k2_xboole_0(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_2262])).

cnf(c_7631,plain,
    ( r1_tarski(X0,k4_subset_1(sK1,sK2,sK3))
    | ~ r1_tarski(sK2,k2_xboole_0(sK2,sK3))
    | X0 != sK2
    | k4_subset_1(sK1,sK2,sK3) != k2_xboole_0(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_5904])).

cnf(c_24830,plain,
    ( r1_tarski(sK2,k4_subset_1(sK1,sK2,sK3))
    | ~ r1_tarski(sK2,k2_xboole_0(sK2,sK3))
    | k4_subset_1(sK1,sK2,sK3) != k2_xboole_0(sK2,sK3)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_7631])).

cnf(c_419,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1194,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k1_zfmisc_1(X3))
    | X0 != X2
    | X1 != k1_zfmisc_1(X3) ),
    inference(instantiation,[status(thm)],[c_419])).

cnf(c_1719,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r2_hidden(X2,k1_zfmisc_1(X3))
    | X2 != X0
    | k1_zfmisc_1(X3) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_1194])).

cnf(c_3402,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r2_hidden(k4_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1))
    | k4_subset_1(sK1,sK2,sK3) != X0
    | k1_zfmisc_1(sK1) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_1719])).

cnf(c_10641,plain,
    ( r2_hidden(k4_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1))
    | ~ r2_hidden(k2_xboole_0(sK3,sK2),k1_zfmisc_1(X0))
    | k4_subset_1(sK1,sK2,sK3) != k2_xboole_0(sK3,sK2)
    | k1_zfmisc_1(sK1) != k1_zfmisc_1(X0) ),
    inference(instantiation,[status(thm)],[c_3402])).

cnf(c_10642,plain,
    ( k4_subset_1(sK1,sK2,sK3) != k2_xboole_0(sK3,sK2)
    | k1_zfmisc_1(sK1) != k1_zfmisc_1(X0)
    | r2_hidden(k4_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1)) = iProver_top
    | r2_hidden(k2_xboole_0(sK3,sK2),k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10641])).

cnf(c_10644,plain,
    ( k4_subset_1(sK1,sK2,sK3) != k2_xboole_0(sK3,sK2)
    | k1_zfmisc_1(sK1) != k1_zfmisc_1(sK1)
    | r2_hidden(k4_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1)) = iProver_top
    | r2_hidden(k2_xboole_0(sK3,sK2),k1_zfmisc_1(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_10642])).

cnf(c_2426,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,sK3)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_7632,plain,
    ( r1_tarski(sK2,k2_xboole_0(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_2426])).

cnf(c_3593,plain,
    ( k2_xboole_0(sK3,sK2) = k2_xboole_0(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_416,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1575,plain,
    ( X0 != X1
    | k4_subset_1(sK1,sK2,sK3) != X1
    | k4_subset_1(sK1,sK2,sK3) = X0 ),
    inference(instantiation,[status(thm)],[c_416])).

cnf(c_2731,plain,
    ( X0 != k2_xboole_0(sK2,sK3)
    | k4_subset_1(sK1,sK2,sK3) = X0
    | k4_subset_1(sK1,sK2,sK3) != k2_xboole_0(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1575])).

cnf(c_3592,plain,
    ( k4_subset_1(sK1,sK2,sK3) = k2_xboole_0(sK3,sK2)
    | k4_subset_1(sK1,sK2,sK3) != k2_xboole_0(sK2,sK3)
    | k2_xboole_0(sK3,sK2) != k2_xboole_0(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_2731])).

cnf(c_16,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1105,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2216,plain,
    ( m1_subset_1(k4_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1))
    | ~ r2_hidden(k4_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_1105])).

cnf(c_2217,plain,
    ( m1_subset_1(k4_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1)) = iProver_top
    | r2_hidden(k4_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1)) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2216])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1811,plain,
    ( r1_tarski(k4_xboole_0(sK1,k4_subset_1(sK1,sK2,sK3)),k4_xboole_0(sK1,sK2))
    | ~ r1_tarski(sK2,k4_subset_1(sK1,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1143,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2))
    | k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)) != X0
    | k3_subset_1(sK1,sK2) != X1 ),
    inference(instantiation,[status(thm)],[c_417])).

cnf(c_1546,plain,
    ( r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2))
    | ~ r1_tarski(k4_xboole_0(sK1,k4_subset_1(sK1,sK2,sK3)),X0)
    | k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)) != k4_xboole_0(sK1,k4_subset_1(sK1,sK2,sK3))
    | k3_subset_1(sK1,sK2) != X0 ),
    inference(instantiation,[status(thm)],[c_1143])).

cnf(c_1801,plain,
    ( r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2))
    | ~ r1_tarski(k4_xboole_0(sK1,k4_subset_1(sK1,sK2,sK3)),k4_xboole_0(sK1,sK2))
    | k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)) != k4_xboole_0(sK1,k4_subset_1(sK1,sK2,sK3))
    | k3_subset_1(sK1,sK2) != k4_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1546])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1158,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
    | k4_subset_1(sK1,X0,sK3) = k2_xboole_0(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_1581,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | k4_subset_1(sK1,sK2,sK3) = k2_xboole_0(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1158])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1545,plain,
    ( ~ m1_subset_1(k4_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1))
    | k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)) = k4_xboole_0(sK1,k4_subset_1(sK1,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1547,plain,
    ( k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)) = k4_xboole_0(sK1,k4_subset_1(sK1,sK2,sK3))
    | m1_subset_1(k4_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1545])).

cnf(c_415,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1331,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_415])).

cnf(c_1119,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | k3_subset_1(sK1,sK2) = k4_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_418,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_425,plain,
    ( k1_zfmisc_1(sK1) = k1_zfmisc_1(sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_418])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_77,plain,
    ( ~ r1_tarski(sK1,sK1)
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_73,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_21,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f59])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_113789,c_47531,c_24830,c_10644,c_7632,c_3593,c_3592,c_2217,c_1811,c_1801,c_1581,c_1547,c_1331,c_1119,c_425,c_77,c_73,c_32,c_21,c_22,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:17:20 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 23.65/3.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.65/3.49  
% 23.65/3.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.65/3.49  
% 23.65/3.49  ------  iProver source info
% 23.65/3.49  
% 23.65/3.49  git: date: 2020-06-30 10:37:57 +0100
% 23.65/3.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.65/3.49  git: non_committed_changes: false
% 23.65/3.49  git: last_make_outside_of_git: false
% 23.65/3.49  
% 23.65/3.49  ------ 
% 23.65/3.49  
% 23.65/3.49  ------ Input Options
% 23.65/3.49  
% 23.65/3.49  --out_options                           all
% 23.65/3.49  --tptp_safe_out                         true
% 23.65/3.49  --problem_path                          ""
% 23.65/3.49  --include_path                          ""
% 23.65/3.49  --clausifier                            res/vclausify_rel
% 23.65/3.49  --clausifier_options                    --mode clausify
% 23.65/3.49  --stdin                                 false
% 23.65/3.49  --stats_out                             sel
% 23.65/3.49  
% 23.65/3.49  ------ General Options
% 23.65/3.49  
% 23.65/3.49  --fof                                   false
% 23.65/3.49  --time_out_real                         604.99
% 23.65/3.49  --time_out_virtual                      -1.
% 23.65/3.49  --symbol_type_check                     false
% 23.65/3.49  --clausify_out                          false
% 23.65/3.49  --sig_cnt_out                           false
% 23.65/3.49  --trig_cnt_out                          false
% 23.65/3.49  --trig_cnt_out_tolerance                1.
% 23.65/3.49  --trig_cnt_out_sk_spl                   false
% 23.65/3.49  --abstr_cl_out                          false
% 23.65/3.49  
% 23.65/3.49  ------ Global Options
% 23.65/3.49  
% 23.65/3.49  --schedule                              none
% 23.65/3.49  --add_important_lit                     false
% 23.65/3.49  --prop_solver_per_cl                    1000
% 23.65/3.49  --min_unsat_core                        false
% 23.65/3.49  --soft_assumptions                      false
% 23.65/3.49  --soft_lemma_size                       3
% 23.65/3.49  --prop_impl_unit_size                   0
% 23.65/3.49  --prop_impl_unit                        []
% 23.65/3.49  --share_sel_clauses                     true
% 23.65/3.49  --reset_solvers                         false
% 23.65/3.49  --bc_imp_inh                            [conj_cone]
% 23.65/3.49  --conj_cone_tolerance                   3.
% 23.65/3.49  --extra_neg_conj                        none
% 23.65/3.49  --large_theory_mode                     true
% 23.65/3.49  --prolific_symb_bound                   200
% 23.65/3.49  --lt_threshold                          2000
% 23.65/3.49  --clause_weak_htbl                      true
% 23.65/3.49  --gc_record_bc_elim                     false
% 23.65/3.49  
% 23.65/3.49  ------ Preprocessing Options
% 23.65/3.49  
% 23.65/3.49  --preprocessing_flag                    true
% 23.65/3.49  --time_out_prep_mult                    0.1
% 23.65/3.49  --splitting_mode                        input
% 23.65/3.49  --splitting_grd                         true
% 23.65/3.49  --splitting_cvd                         false
% 23.65/3.49  --splitting_cvd_svl                     false
% 23.65/3.49  --splitting_nvd                         32
% 23.65/3.49  --sub_typing                            true
% 23.65/3.49  --prep_gs_sim                           false
% 23.65/3.49  --prep_unflatten                        true
% 23.65/3.49  --prep_res_sim                          true
% 23.65/3.49  --prep_upred                            true
% 23.65/3.49  --prep_sem_filter                       exhaustive
% 23.65/3.49  --prep_sem_filter_out                   false
% 23.65/3.49  --pred_elim                             false
% 23.65/3.49  --res_sim_input                         true
% 23.65/3.49  --eq_ax_congr_red                       true
% 23.65/3.49  --pure_diseq_elim                       true
% 23.65/3.49  --brand_transform                       false
% 23.65/3.49  --non_eq_to_eq                          false
% 23.65/3.49  --prep_def_merge                        true
% 23.65/3.49  --prep_def_merge_prop_impl              false
% 23.65/3.49  --prep_def_merge_mbd                    true
% 23.65/3.49  --prep_def_merge_tr_red                 false
% 23.65/3.49  --prep_def_merge_tr_cl                  false
% 23.65/3.49  --smt_preprocessing                     true
% 23.65/3.49  --smt_ac_axioms                         fast
% 23.65/3.49  --preprocessed_out                      false
% 23.65/3.49  --preprocessed_stats                    false
% 23.65/3.49  
% 23.65/3.49  ------ Abstraction refinement Options
% 23.65/3.49  
% 23.65/3.49  --abstr_ref                             []
% 23.65/3.49  --abstr_ref_prep                        false
% 23.65/3.49  --abstr_ref_until_sat                   false
% 23.65/3.49  --abstr_ref_sig_restrict                funpre
% 23.65/3.49  --abstr_ref_af_restrict_to_split_sk     false
% 23.65/3.49  --abstr_ref_under                       []
% 23.65/3.49  
% 23.65/3.49  ------ SAT Options
% 23.65/3.49  
% 23.65/3.49  --sat_mode                              false
% 23.65/3.49  --sat_fm_restart_options                ""
% 23.65/3.49  --sat_gr_def                            false
% 23.65/3.49  --sat_epr_types                         true
% 23.65/3.49  --sat_non_cyclic_types                  false
% 23.65/3.49  --sat_finite_models                     false
% 23.65/3.49  --sat_fm_lemmas                         false
% 23.65/3.49  --sat_fm_prep                           false
% 23.65/3.49  --sat_fm_uc_incr                        true
% 23.65/3.49  --sat_out_model                         small
% 23.65/3.49  --sat_out_clauses                       false
% 23.65/3.49  
% 23.65/3.49  ------ QBF Options
% 23.65/3.49  
% 23.65/3.49  --qbf_mode                              false
% 23.65/3.49  --qbf_elim_univ                         false
% 23.65/3.49  --qbf_dom_inst                          none
% 23.65/3.49  --qbf_dom_pre_inst                      false
% 23.65/3.49  --qbf_sk_in                             false
% 23.65/3.49  --qbf_pred_elim                         true
% 23.65/3.49  --qbf_split                             512
% 23.65/3.49  
% 23.65/3.49  ------ BMC1 Options
% 23.65/3.49  
% 23.65/3.49  --bmc1_incremental                      false
% 23.65/3.49  --bmc1_axioms                           reachable_all
% 23.65/3.49  --bmc1_min_bound                        0
% 23.65/3.49  --bmc1_max_bound                        -1
% 23.65/3.49  --bmc1_max_bound_default                -1
% 23.65/3.49  --bmc1_symbol_reachability              true
% 23.65/3.49  --bmc1_property_lemmas                  false
% 23.65/3.49  --bmc1_k_induction                      false
% 23.65/3.49  --bmc1_non_equiv_states                 false
% 23.65/3.49  --bmc1_deadlock                         false
% 23.65/3.49  --bmc1_ucm                              false
% 23.65/3.49  --bmc1_add_unsat_core                   none
% 23.65/3.49  --bmc1_unsat_core_children              false
% 23.65/3.49  --bmc1_unsat_core_extrapolate_axioms    false
% 23.65/3.49  --bmc1_out_stat                         full
% 23.65/3.49  --bmc1_ground_init                      false
% 23.65/3.49  --bmc1_pre_inst_next_state              false
% 23.65/3.49  --bmc1_pre_inst_state                   false
% 23.65/3.49  --bmc1_pre_inst_reach_state             false
% 23.65/3.49  --bmc1_out_unsat_core                   false
% 23.65/3.49  --bmc1_aig_witness_out                  false
% 23.65/3.49  --bmc1_verbose                          false
% 23.65/3.49  --bmc1_dump_clauses_tptp                false
% 23.65/3.49  --bmc1_dump_unsat_core_tptp             false
% 23.65/3.49  --bmc1_dump_file                        -
% 23.65/3.49  --bmc1_ucm_expand_uc_limit              128
% 23.65/3.49  --bmc1_ucm_n_expand_iterations          6
% 23.65/3.49  --bmc1_ucm_extend_mode                  1
% 23.65/3.49  --bmc1_ucm_init_mode                    2
% 23.65/3.49  --bmc1_ucm_cone_mode                    none
% 23.65/3.49  --bmc1_ucm_reduced_relation_type        0
% 23.65/3.49  --bmc1_ucm_relax_model                  4
% 23.65/3.49  --bmc1_ucm_full_tr_after_sat            true
% 23.65/3.49  --bmc1_ucm_expand_neg_assumptions       false
% 23.65/3.49  --bmc1_ucm_layered_model                none
% 23.65/3.49  --bmc1_ucm_max_lemma_size               10
% 23.65/3.49  
% 23.65/3.49  ------ AIG Options
% 23.65/3.49  
% 23.65/3.49  --aig_mode                              false
% 23.65/3.49  
% 23.65/3.49  ------ Instantiation Options
% 23.65/3.49  
% 23.65/3.49  --instantiation_flag                    true
% 23.65/3.49  --inst_sos_flag                         false
% 23.65/3.49  --inst_sos_phase                        true
% 23.65/3.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.65/3.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.65/3.49  --inst_lit_sel_side                     num_symb
% 23.65/3.49  --inst_solver_per_active                1400
% 23.65/3.49  --inst_solver_calls_frac                1.
% 23.65/3.49  --inst_passive_queue_type               priority_queues
% 23.65/3.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.65/3.49  --inst_passive_queues_freq              [25;2]
% 23.65/3.49  --inst_dismatching                      true
% 23.65/3.49  --inst_eager_unprocessed_to_passive     true
% 23.65/3.49  --inst_prop_sim_given                   true
% 23.65/3.49  --inst_prop_sim_new                     false
% 23.65/3.49  --inst_subs_new                         false
% 23.65/3.49  --inst_eq_res_simp                      false
% 23.65/3.49  --inst_subs_given                       false
% 23.65/3.49  --inst_orphan_elimination               true
% 23.65/3.49  --inst_learning_loop_flag               true
% 23.65/3.49  --inst_learning_start                   3000
% 23.65/3.49  --inst_learning_factor                  2
% 23.65/3.49  --inst_start_prop_sim_after_learn       3
% 23.65/3.49  --inst_sel_renew                        solver
% 23.65/3.49  --inst_lit_activity_flag                true
% 23.65/3.49  --inst_restr_to_given                   false
% 23.65/3.49  --inst_activity_threshold               500
% 23.65/3.49  --inst_out_proof                        true
% 23.65/3.49  
% 23.65/3.49  ------ Resolution Options
% 23.65/3.49  
% 23.65/3.49  --resolution_flag                       true
% 23.65/3.49  --res_lit_sel                           adaptive
% 23.65/3.49  --res_lit_sel_side                      none
% 23.65/3.49  --res_ordering                          kbo
% 23.65/3.49  --res_to_prop_solver                    active
% 23.65/3.49  --res_prop_simpl_new                    false
% 23.65/3.49  --res_prop_simpl_given                  true
% 23.65/3.49  --res_passive_queue_type                priority_queues
% 23.65/3.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.65/3.49  --res_passive_queues_freq               [15;5]
% 23.65/3.49  --res_forward_subs                      full
% 23.65/3.49  --res_backward_subs                     full
% 23.65/3.49  --res_forward_subs_resolution           true
% 23.65/3.49  --res_backward_subs_resolution          true
% 23.65/3.49  --res_orphan_elimination                true
% 23.65/3.49  --res_time_limit                        2.
% 23.65/3.49  --res_out_proof                         true
% 23.65/3.49  
% 23.65/3.49  ------ Superposition Options
% 23.65/3.49  
% 23.65/3.49  --superposition_flag                    true
% 23.65/3.49  --sup_passive_queue_type                priority_queues
% 23.65/3.49  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.65/3.49  --sup_passive_queues_freq               [1;4]
% 23.65/3.49  --demod_completeness_check              fast
% 23.65/3.49  --demod_use_ground                      true
% 23.65/3.49  --sup_to_prop_solver                    passive
% 23.65/3.49  --sup_prop_simpl_new                    true
% 23.65/3.49  --sup_prop_simpl_given                  true
% 23.65/3.49  --sup_fun_splitting                     false
% 23.65/3.49  --sup_smt_interval                      50000
% 23.65/3.49  
% 23.65/3.49  ------ Superposition Simplification Setup
% 23.65/3.49  
% 23.65/3.49  --sup_indices_passive                   []
% 23.65/3.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.65/3.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.65/3.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.65/3.49  --sup_full_triv                         [TrivRules;PropSubs]
% 23.65/3.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.65/3.49  --sup_full_bw                           [BwDemod]
% 23.65/3.49  --sup_immed_triv                        [TrivRules]
% 23.65/3.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.65/3.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.65/3.49  --sup_immed_bw_main                     []
% 23.65/3.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.65/3.49  --sup_input_triv                        [Unflattening;TrivRules]
% 23.65/3.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.65/3.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.65/3.49  
% 23.65/3.49  ------ Combination Options
% 23.65/3.49  
% 23.65/3.49  --comb_res_mult                         3
% 23.65/3.49  --comb_sup_mult                         2
% 23.65/3.49  --comb_inst_mult                        10
% 23.65/3.49  
% 23.65/3.49  ------ Debug Options
% 23.65/3.49  
% 23.65/3.49  --dbg_backtrace                         false
% 23.65/3.49  --dbg_dump_prop_clauses                 false
% 23.65/3.49  --dbg_dump_prop_clauses_file            -
% 23.65/3.49  --dbg_out_stat                          false
% 23.65/3.49  ------ Parsing...
% 23.65/3.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.65/3.49  
% 23.65/3.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 23.65/3.49  
% 23.65/3.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.65/3.49  
% 23.65/3.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.65/3.49  ------ Proving...
% 23.65/3.49  ------ Problem Properties 
% 23.65/3.49  
% 23.65/3.49  
% 23.65/3.49  clauses                                 23
% 23.65/3.49  conjectures                             3
% 23.65/3.49  EPR                                     6
% 23.65/3.49  Horn                                    20
% 23.65/3.49  unary                                   7
% 23.65/3.49  binary                                  8
% 23.65/3.49  lits                                    47
% 23.65/3.49  lits eq                                 7
% 23.65/3.49  fd_pure                                 0
% 23.65/3.49  fd_pseudo                               0
% 23.65/3.49  fd_cond                                 0
% 23.65/3.49  fd_pseudo_cond                          3
% 23.65/3.49  AC symbols                              0
% 23.65/3.49  
% 23.65/3.49  ------ Input Options Time Limit: Unbounded
% 23.65/3.49  
% 23.65/3.49  
% 23.65/3.49  ------ 
% 23.65/3.49  Current options:
% 23.65/3.49  ------ 
% 23.65/3.49  
% 23.65/3.49  ------ Input Options
% 23.65/3.49  
% 23.65/3.49  --out_options                           all
% 23.65/3.49  --tptp_safe_out                         true
% 23.65/3.49  --problem_path                          ""
% 23.65/3.49  --include_path                          ""
% 23.65/3.49  --clausifier                            res/vclausify_rel
% 23.65/3.49  --clausifier_options                    --mode clausify
% 23.65/3.49  --stdin                                 false
% 23.65/3.49  --stats_out                             sel
% 23.65/3.49  
% 23.65/3.49  ------ General Options
% 23.65/3.49  
% 23.65/3.49  --fof                                   false
% 23.65/3.49  --time_out_real                         604.99
% 23.65/3.49  --time_out_virtual                      -1.
% 23.65/3.49  --symbol_type_check                     false
% 23.65/3.49  --clausify_out                          false
% 23.65/3.49  --sig_cnt_out                           false
% 23.65/3.49  --trig_cnt_out                          false
% 23.65/3.49  --trig_cnt_out_tolerance                1.
% 23.65/3.49  --trig_cnt_out_sk_spl                   false
% 23.65/3.49  --abstr_cl_out                          false
% 23.65/3.49  
% 23.65/3.49  ------ Global Options
% 23.65/3.49  
% 23.65/3.49  --schedule                              none
% 23.65/3.49  --add_important_lit                     false
% 23.65/3.49  --prop_solver_per_cl                    1000
% 23.65/3.49  --min_unsat_core                        false
% 23.65/3.49  --soft_assumptions                      false
% 23.65/3.49  --soft_lemma_size                       3
% 23.65/3.49  --prop_impl_unit_size                   0
% 23.65/3.49  --prop_impl_unit                        []
% 23.65/3.49  --share_sel_clauses                     true
% 23.65/3.49  --reset_solvers                         false
% 23.65/3.49  --bc_imp_inh                            [conj_cone]
% 23.65/3.49  --conj_cone_tolerance                   3.
% 23.65/3.49  --extra_neg_conj                        none
% 23.65/3.49  --large_theory_mode                     true
% 23.65/3.49  --prolific_symb_bound                   200
% 23.65/3.49  --lt_threshold                          2000
% 23.65/3.49  --clause_weak_htbl                      true
% 23.65/3.49  --gc_record_bc_elim                     false
% 23.65/3.49  
% 23.65/3.49  ------ Preprocessing Options
% 23.65/3.49  
% 23.65/3.49  --preprocessing_flag                    true
% 23.65/3.49  --time_out_prep_mult                    0.1
% 23.65/3.49  --splitting_mode                        input
% 23.65/3.49  --splitting_grd                         true
% 23.65/3.49  --splitting_cvd                         false
% 23.65/3.49  --splitting_cvd_svl                     false
% 23.65/3.49  --splitting_nvd                         32
% 23.65/3.49  --sub_typing                            true
% 23.65/3.49  --prep_gs_sim                           false
% 23.65/3.49  --prep_unflatten                        true
% 23.65/3.49  --prep_res_sim                          true
% 23.65/3.49  --prep_upred                            true
% 23.65/3.49  --prep_sem_filter                       exhaustive
% 23.65/3.49  --prep_sem_filter_out                   false
% 23.65/3.49  --pred_elim                             false
% 23.65/3.49  --res_sim_input                         true
% 23.65/3.49  --eq_ax_congr_red                       true
% 23.65/3.49  --pure_diseq_elim                       true
% 23.65/3.49  --brand_transform                       false
% 23.65/3.49  --non_eq_to_eq                          false
% 23.65/3.49  --prep_def_merge                        true
% 23.65/3.49  --prep_def_merge_prop_impl              false
% 23.65/3.49  --prep_def_merge_mbd                    true
% 23.65/3.49  --prep_def_merge_tr_red                 false
% 23.65/3.49  --prep_def_merge_tr_cl                  false
% 23.65/3.49  --smt_preprocessing                     true
% 23.65/3.49  --smt_ac_axioms                         fast
% 23.65/3.49  --preprocessed_out                      false
% 23.65/3.49  --preprocessed_stats                    false
% 23.65/3.49  
% 23.65/3.49  ------ Abstraction refinement Options
% 23.65/3.49  
% 23.65/3.49  --abstr_ref                             []
% 23.65/3.49  --abstr_ref_prep                        false
% 23.65/3.49  --abstr_ref_until_sat                   false
% 23.65/3.49  --abstr_ref_sig_restrict                funpre
% 23.65/3.49  --abstr_ref_af_restrict_to_split_sk     false
% 23.65/3.49  --abstr_ref_under                       []
% 23.65/3.49  
% 23.65/3.49  ------ SAT Options
% 23.65/3.49  
% 23.65/3.49  --sat_mode                              false
% 23.65/3.49  --sat_fm_restart_options                ""
% 23.65/3.49  --sat_gr_def                            false
% 23.65/3.49  --sat_epr_types                         true
% 23.65/3.49  --sat_non_cyclic_types                  false
% 23.65/3.49  --sat_finite_models                     false
% 23.65/3.49  --sat_fm_lemmas                         false
% 23.65/3.49  --sat_fm_prep                           false
% 23.65/3.49  --sat_fm_uc_incr                        true
% 23.65/3.49  --sat_out_model                         small
% 23.65/3.49  --sat_out_clauses                       false
% 23.65/3.49  
% 23.65/3.49  ------ QBF Options
% 23.65/3.49  
% 23.65/3.49  --qbf_mode                              false
% 23.65/3.49  --qbf_elim_univ                         false
% 23.65/3.49  --qbf_dom_inst                          none
% 23.65/3.49  --qbf_dom_pre_inst                      false
% 23.65/3.49  --qbf_sk_in                             false
% 23.65/3.49  --qbf_pred_elim                         true
% 23.65/3.49  --qbf_split                             512
% 23.65/3.49  
% 23.65/3.49  ------ BMC1 Options
% 23.65/3.49  
% 23.65/3.49  --bmc1_incremental                      false
% 23.65/3.49  --bmc1_axioms                           reachable_all
% 23.65/3.49  --bmc1_min_bound                        0
% 23.65/3.49  --bmc1_max_bound                        -1
% 23.65/3.49  --bmc1_max_bound_default                -1
% 23.65/3.49  --bmc1_symbol_reachability              true
% 23.65/3.49  --bmc1_property_lemmas                  false
% 23.65/3.49  --bmc1_k_induction                      false
% 23.65/3.49  --bmc1_non_equiv_states                 false
% 23.65/3.49  --bmc1_deadlock                         false
% 23.65/3.49  --bmc1_ucm                              false
% 23.65/3.49  --bmc1_add_unsat_core                   none
% 23.65/3.49  --bmc1_unsat_core_children              false
% 23.65/3.49  --bmc1_unsat_core_extrapolate_axioms    false
% 23.65/3.49  --bmc1_out_stat                         full
% 23.65/3.49  --bmc1_ground_init                      false
% 23.65/3.49  --bmc1_pre_inst_next_state              false
% 23.65/3.49  --bmc1_pre_inst_state                   false
% 23.65/3.49  --bmc1_pre_inst_reach_state             false
% 23.65/3.49  --bmc1_out_unsat_core                   false
% 23.65/3.49  --bmc1_aig_witness_out                  false
% 23.65/3.49  --bmc1_verbose                          false
% 23.65/3.49  --bmc1_dump_clauses_tptp                false
% 23.65/3.49  --bmc1_dump_unsat_core_tptp             false
% 23.65/3.49  --bmc1_dump_file                        -
% 23.65/3.49  --bmc1_ucm_expand_uc_limit              128
% 23.65/3.49  --bmc1_ucm_n_expand_iterations          6
% 23.65/3.49  --bmc1_ucm_extend_mode                  1
% 23.65/3.49  --bmc1_ucm_init_mode                    2
% 23.65/3.49  --bmc1_ucm_cone_mode                    none
% 23.65/3.49  --bmc1_ucm_reduced_relation_type        0
% 23.65/3.49  --bmc1_ucm_relax_model                  4
% 23.65/3.49  --bmc1_ucm_full_tr_after_sat            true
% 23.65/3.49  --bmc1_ucm_expand_neg_assumptions       false
% 23.65/3.49  --bmc1_ucm_layered_model                none
% 23.65/3.49  --bmc1_ucm_max_lemma_size               10
% 23.65/3.49  
% 23.65/3.49  ------ AIG Options
% 23.65/3.49  
% 23.65/3.49  --aig_mode                              false
% 23.65/3.49  
% 23.65/3.49  ------ Instantiation Options
% 23.65/3.49  
% 23.65/3.49  --instantiation_flag                    true
% 23.65/3.49  --inst_sos_flag                         false
% 23.65/3.49  --inst_sos_phase                        true
% 23.65/3.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.65/3.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.65/3.49  --inst_lit_sel_side                     num_symb
% 23.65/3.49  --inst_solver_per_active                1400
% 23.65/3.49  --inst_solver_calls_frac                1.
% 23.65/3.49  --inst_passive_queue_type               priority_queues
% 23.65/3.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.65/3.49  --inst_passive_queues_freq              [25;2]
% 23.65/3.49  --inst_dismatching                      true
% 23.65/3.49  --inst_eager_unprocessed_to_passive     true
% 23.65/3.49  --inst_prop_sim_given                   true
% 23.65/3.49  --inst_prop_sim_new                     false
% 23.65/3.49  --inst_subs_new                         false
% 23.65/3.49  --inst_eq_res_simp                      false
% 23.65/3.49  --inst_subs_given                       false
% 23.65/3.49  --inst_orphan_elimination               true
% 23.65/3.49  --inst_learning_loop_flag               true
% 23.65/3.49  --inst_learning_start                   3000
% 23.65/3.49  --inst_learning_factor                  2
% 23.65/3.49  --inst_start_prop_sim_after_learn       3
% 23.65/3.49  --inst_sel_renew                        solver
% 23.65/3.49  --inst_lit_activity_flag                true
% 23.65/3.49  --inst_restr_to_given                   false
% 23.65/3.49  --inst_activity_threshold               500
% 23.65/3.49  --inst_out_proof                        true
% 23.65/3.49  
% 23.65/3.49  ------ Resolution Options
% 23.65/3.49  
% 23.65/3.49  --resolution_flag                       true
% 23.65/3.49  --res_lit_sel                           adaptive
% 23.65/3.49  --res_lit_sel_side                      none
% 23.65/3.49  --res_ordering                          kbo
% 23.65/3.49  --res_to_prop_solver                    active
% 23.65/3.49  --res_prop_simpl_new                    false
% 23.65/3.49  --res_prop_simpl_given                  true
% 23.65/3.49  --res_passive_queue_type                priority_queues
% 23.65/3.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.65/3.49  --res_passive_queues_freq               [15;5]
% 23.65/3.49  --res_forward_subs                      full
% 23.65/3.49  --res_backward_subs                     full
% 23.65/3.49  --res_forward_subs_resolution           true
% 23.65/3.49  --res_backward_subs_resolution          true
% 23.65/3.49  --res_orphan_elimination                true
% 23.65/3.49  --res_time_limit                        2.
% 23.65/3.49  --res_out_proof                         true
% 23.65/3.49  
% 23.65/3.49  ------ Superposition Options
% 23.65/3.49  
% 23.65/3.49  --superposition_flag                    true
% 23.65/3.49  --sup_passive_queue_type                priority_queues
% 23.65/3.49  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.65/3.49  --sup_passive_queues_freq               [1;4]
% 23.65/3.49  --demod_completeness_check              fast
% 23.65/3.49  --demod_use_ground                      true
% 23.65/3.49  --sup_to_prop_solver                    passive
% 23.65/3.49  --sup_prop_simpl_new                    true
% 23.65/3.49  --sup_prop_simpl_given                  true
% 23.65/3.49  --sup_fun_splitting                     false
% 23.65/3.49  --sup_smt_interval                      50000
% 23.65/3.49  
% 23.65/3.49  ------ Superposition Simplification Setup
% 23.65/3.49  
% 23.65/3.49  --sup_indices_passive                   []
% 23.65/3.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.65/3.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.65/3.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.65/3.49  --sup_full_triv                         [TrivRules;PropSubs]
% 23.65/3.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.65/3.49  --sup_full_bw                           [BwDemod]
% 23.65/3.49  --sup_immed_triv                        [TrivRules]
% 23.65/3.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.65/3.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.65/3.49  --sup_immed_bw_main                     []
% 23.65/3.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.65/3.49  --sup_input_triv                        [Unflattening;TrivRules]
% 23.65/3.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.65/3.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.65/3.49  
% 23.65/3.49  ------ Combination Options
% 23.65/3.49  
% 23.65/3.49  --comb_res_mult                         3
% 23.65/3.49  --comb_sup_mult                         2
% 23.65/3.49  --comb_inst_mult                        10
% 23.65/3.49  
% 23.65/3.49  ------ Debug Options
% 23.65/3.49  
% 23.65/3.49  --dbg_backtrace                         false
% 23.65/3.49  --dbg_dump_prop_clauses                 false
% 23.65/3.49  --dbg_dump_prop_clauses_file            -
% 23.65/3.49  --dbg_out_stat                          false
% 23.65/3.49  
% 23.65/3.49  
% 23.65/3.49  
% 23.65/3.49  
% 23.65/3.49  ------ Proving...
% 23.65/3.49  
% 23.65/3.49  
% 23.65/3.49  % SZS status Theorem for theBenchmark.p
% 23.65/3.49  
% 23.65/3.49  % SZS output start CNFRefutation for theBenchmark.p
% 23.65/3.49  
% 23.65/3.49  fof(f14,conjecture,(
% 23.65/3.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 23.65/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.65/3.49  
% 23.65/3.49  fof(f15,negated_conjecture,(
% 23.65/3.49    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 23.65/3.49    inference(negated_conjecture,[],[f14])).
% 23.65/3.49  
% 23.65/3.49  fof(f25,plain,(
% 23.65/3.49    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 23.65/3.49    inference(ennf_transformation,[],[f15])).
% 23.65/3.49  
% 23.65/3.49  fof(f34,plain,(
% 23.65/3.49    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(X0))) => (~r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,sK3)),k3_subset_1(X0,X1)) & m1_subset_1(sK3,k1_zfmisc_1(X0)))) )),
% 23.65/3.49    introduced(choice_axiom,[])).
% 23.65/3.49  
% 23.65/3.49  fof(f33,plain,(
% 23.65/3.49    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (~r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,X2)),k3_subset_1(sK1,sK2)) & m1_subset_1(X2,k1_zfmisc_1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(sK1)))),
% 23.65/3.49    introduced(choice_axiom,[])).
% 23.65/3.49  
% 23.65/3.49  fof(f35,plain,(
% 23.65/3.49    (~r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 23.65/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f25,f34,f33])).
% 23.65/3.49  
% 23.65/3.49  fof(f57,plain,(
% 23.65/3.49    m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 23.65/3.49    inference(cnf_transformation,[],[f35])).
% 23.65/3.49  
% 23.65/3.49  fof(f10,axiom,(
% 23.65/3.49    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 23.65/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.65/3.49  
% 23.65/3.49  fof(f21,plain,(
% 23.65/3.49    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 23.65/3.49    inference(ennf_transformation,[],[f10])).
% 23.65/3.49  
% 23.65/3.49  fof(f32,plain,(
% 23.65/3.49    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 23.65/3.49    inference(nnf_transformation,[],[f21])).
% 23.65/3.49  
% 23.65/3.49  fof(f50,plain,(
% 23.65/3.49    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 23.65/3.49    inference(cnf_transformation,[],[f32])).
% 23.65/3.49  
% 23.65/3.49  fof(f12,axiom,(
% 23.65/3.49    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 23.65/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.65/3.49  
% 23.65/3.49  fof(f55,plain,(
% 23.65/3.49    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 23.65/3.49    inference(cnf_transformation,[],[f12])).
% 23.65/3.49  
% 23.65/3.49  fof(f9,axiom,(
% 23.65/3.49    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 23.65/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.65/3.49  
% 23.65/3.49  fof(f28,plain,(
% 23.65/3.49    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 23.65/3.49    inference(nnf_transformation,[],[f9])).
% 23.65/3.49  
% 23.65/3.49  fof(f29,plain,(
% 23.65/3.49    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 23.65/3.49    inference(rectify,[],[f28])).
% 23.65/3.49  
% 23.65/3.49  fof(f30,plain,(
% 23.65/3.49    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 23.65/3.49    introduced(choice_axiom,[])).
% 23.65/3.49  
% 23.65/3.49  fof(f31,plain,(
% 23.65/3.49    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 23.65/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).
% 23.65/3.49  
% 23.65/3.49  fof(f46,plain,(
% 23.65/3.49    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 23.65/3.49    inference(cnf_transformation,[],[f31])).
% 23.65/3.49  
% 23.65/3.49  fof(f63,plain,(
% 23.65/3.49    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 23.65/3.49    inference(equality_resolution,[],[f46])).
% 23.65/3.49  
% 23.65/3.49  fof(f4,axiom,(
% 23.65/3.49    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 23.65/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.65/3.49  
% 23.65/3.49  fof(f17,plain,(
% 23.65/3.49    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 23.65/3.49    inference(ennf_transformation,[],[f4])).
% 23.65/3.49  
% 23.65/3.49  fof(f41,plain,(
% 23.65/3.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 23.65/3.49    inference(cnf_transformation,[],[f17])).
% 23.65/3.49  
% 23.65/3.49  fof(f1,axiom,(
% 23.65/3.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 23.65/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.65/3.49  
% 23.65/3.49  fof(f36,plain,(
% 23.65/3.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 23.65/3.49    inference(cnf_transformation,[],[f1])).
% 23.65/3.49  
% 23.65/3.49  fof(f58,plain,(
% 23.65/3.49    m1_subset_1(sK3,k1_zfmisc_1(sK1))),
% 23.65/3.49    inference(cnf_transformation,[],[f35])).
% 23.65/3.49  
% 23.65/3.49  fof(f3,axiom,(
% 23.65/3.49    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 23.65/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.65/3.49  
% 23.65/3.49  fof(f16,plain,(
% 23.65/3.49    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 23.65/3.49    inference(ennf_transformation,[],[f3])).
% 23.65/3.49  
% 23.65/3.49  fof(f40,plain,(
% 23.65/3.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 23.65/3.49    inference(cnf_transformation,[],[f16])).
% 23.65/3.49  
% 23.65/3.49  fof(f2,axiom,(
% 23.65/3.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 23.65/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.65/3.49  
% 23.65/3.49  fof(f26,plain,(
% 23.65/3.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 23.65/3.49    inference(nnf_transformation,[],[f2])).
% 23.65/3.49  
% 23.65/3.49  fof(f27,plain,(
% 23.65/3.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 23.65/3.49    inference(flattening,[],[f26])).
% 23.65/3.49  
% 23.65/3.49  fof(f37,plain,(
% 23.65/3.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 23.65/3.49    inference(cnf_transformation,[],[f27])).
% 23.65/3.49  
% 23.65/3.49  fof(f61,plain,(
% 23.65/3.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 23.65/3.49    inference(equality_resolution,[],[f37])).
% 23.65/3.49  
% 23.65/3.49  fof(f6,axiom,(
% 23.65/3.49    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 23.65/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.65/3.49  
% 23.65/3.49  fof(f19,plain,(
% 23.65/3.49    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 23.65/3.49    inference(ennf_transformation,[],[f6])).
% 23.65/3.49  
% 23.65/3.49  fof(f43,plain,(
% 23.65/3.49    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 23.65/3.49    inference(cnf_transformation,[],[f19])).
% 23.65/3.49  
% 23.65/3.49  fof(f8,axiom,(
% 23.65/3.49    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 23.65/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.65/3.49  
% 23.65/3.49  fof(f45,plain,(
% 23.65/3.49    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 23.65/3.49    inference(cnf_transformation,[],[f8])).
% 23.65/3.49  
% 23.65/3.49  fof(f7,axiom,(
% 23.65/3.49    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 23.65/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.65/3.49  
% 23.65/3.49  fof(f20,plain,(
% 23.65/3.49    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 23.65/3.49    inference(ennf_transformation,[],[f7])).
% 23.65/3.49  
% 23.65/3.49  fof(f44,plain,(
% 23.65/3.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 23.65/3.49    inference(cnf_transformation,[],[f20])).
% 23.65/3.49  
% 23.65/3.49  fof(f47,plain,(
% 23.65/3.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 23.65/3.49    inference(cnf_transformation,[],[f31])).
% 23.65/3.49  
% 23.65/3.49  fof(f62,plain,(
% 23.65/3.49    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 23.65/3.49    inference(equality_resolution,[],[f47])).
% 23.65/3.49  
% 23.65/3.49  fof(f51,plain,(
% 23.65/3.49    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 23.65/3.49    inference(cnf_transformation,[],[f32])).
% 23.65/3.49  
% 23.65/3.49  fof(f5,axiom,(
% 23.65/3.49    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)))),
% 23.65/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.65/3.49  
% 23.65/3.49  fof(f18,plain,(
% 23.65/3.49    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1))),
% 23.65/3.49    inference(ennf_transformation,[],[f5])).
% 23.65/3.49  
% 23.65/3.49  fof(f42,plain,(
% 23.65/3.49    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1)) )),
% 23.65/3.49    inference(cnf_transformation,[],[f18])).
% 23.65/3.49  
% 23.65/3.49  fof(f13,axiom,(
% 23.65/3.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 23.65/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.65/3.49  
% 23.65/3.49  fof(f23,plain,(
% 23.65/3.49    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 23.65/3.49    inference(ennf_transformation,[],[f13])).
% 23.65/3.49  
% 23.65/3.49  fof(f24,plain,(
% 23.65/3.49    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 23.65/3.49    inference(flattening,[],[f23])).
% 23.65/3.49  
% 23.65/3.49  fof(f56,plain,(
% 23.65/3.49    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 23.65/3.49    inference(cnf_transformation,[],[f24])).
% 23.65/3.49  
% 23.65/3.49  fof(f11,axiom,(
% 23.65/3.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 23.65/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.65/3.49  
% 23.65/3.49  fof(f22,plain,(
% 23.65/3.49    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 23.65/3.49    inference(ennf_transformation,[],[f11])).
% 23.65/3.49  
% 23.65/3.49  fof(f54,plain,(
% 23.65/3.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 23.65/3.49    inference(cnf_transformation,[],[f22])).
% 23.65/3.49  
% 23.65/3.49  fof(f39,plain,(
% 23.65/3.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 23.65/3.49    inference(cnf_transformation,[],[f27])).
% 23.65/3.49  
% 23.65/3.49  fof(f59,plain,(
% 23.65/3.49    ~r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2))),
% 23.65/3.49    inference(cnf_transformation,[],[f35])).
% 23.65/3.49  
% 23.65/3.49  cnf(c_23,negated_conjecture,
% 23.65/3.49      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
% 23.65/3.49      inference(cnf_transformation,[],[f57]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_912,plain,
% 23.65/3.49      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
% 23.65/3.49      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_17,plain,
% 23.65/3.49      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 23.65/3.49      inference(cnf_transformation,[],[f50]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_918,plain,
% 23.65/3.49      ( m1_subset_1(X0,X1) != iProver_top
% 23.65/3.49      | r2_hidden(X0,X1) = iProver_top
% 23.65/3.49      | v1_xboole_0(X1) = iProver_top ),
% 23.65/3.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_1608,plain,
% 23.65/3.49      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top
% 23.65/3.49      | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_912,c_918]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_24,plain,
% 23.65/3.49      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
% 23.65/3.49      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_19,plain,
% 23.65/3.49      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 23.65/3.49      inference(cnf_transformation,[],[f55]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_30,plain,
% 23.65/3.49      ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
% 23.65/3.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_32,plain,
% 23.65/3.49      ( v1_xboole_0(k1_zfmisc_1(sK1)) != iProver_top ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_30]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_1113,plain,
% 23.65/3.49      ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
% 23.65/3.49      | r2_hidden(sK2,k1_zfmisc_1(sK1))
% 23.65/3.49      | v1_xboole_0(k1_zfmisc_1(sK1)) ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_17]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_1114,plain,
% 23.65/3.49      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) != iProver_top
% 23.65/3.49      | r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top
% 23.65/3.49      | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
% 23.65/3.49      inference(predicate_to_equality,[status(thm)],[c_1113]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_3458,plain,
% 23.65/3.49      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
% 23.65/3.49      inference(global_propositional_subsumption,
% 23.65/3.49                [status(thm)],
% 23.65/3.49                [c_1608,c_24,c_32,c_1114]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_13,plain,
% 23.65/3.49      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 23.65/3.49      inference(cnf_transformation,[],[f63]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_922,plain,
% 23.65/3.49      ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
% 23.65/3.49      | r1_tarski(X0,X1) = iProver_top ),
% 23.65/3.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_3463,plain,
% 23.65/3.49      ( r1_tarski(sK2,sK1) = iProver_top ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_3458,c_922]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_5,plain,
% 23.65/3.49      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 23.65/3.49      inference(cnf_transformation,[],[f41]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_930,plain,
% 23.65/3.49      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 23.65/3.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_3638,plain,
% 23.65/3.49      ( k2_xboole_0(sK2,sK1) = sK1 ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_3463,c_930]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_0,plain,
% 23.65/3.49      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 23.65/3.49      inference(cnf_transformation,[],[f36]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_3652,plain,
% 23.65/3.49      ( k2_xboole_0(sK1,sK2) = sK1 ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_3638,c_0]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_22,negated_conjecture,
% 23.65/3.49      ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
% 23.65/3.49      inference(cnf_transformation,[],[f58]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_913,plain,
% 23.65/3.49      ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
% 23.65/3.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_1607,plain,
% 23.65/3.49      ( r2_hidden(sK3,k1_zfmisc_1(sK1)) = iProver_top
% 23.65/3.49      | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_913,c_918]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_25,plain,
% 23.65/3.49      ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
% 23.65/3.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_1110,plain,
% 23.65/3.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
% 23.65/3.49      | r2_hidden(sK3,k1_zfmisc_1(sK1))
% 23.65/3.49      | v1_xboole_0(k1_zfmisc_1(sK1)) ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_17]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_1111,plain,
% 23.65/3.49      ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
% 23.65/3.49      | r2_hidden(sK3,k1_zfmisc_1(sK1)) = iProver_top
% 23.65/3.49      | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
% 23.65/3.49      inference(predicate_to_equality,[status(thm)],[c_1110]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_2815,plain,
% 23.65/3.49      ( r2_hidden(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
% 23.65/3.49      inference(global_propositional_subsumption,
% 23.65/3.49                [status(thm)],
% 23.65/3.49                [c_1607,c_25,c_32,c_1111]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_2820,plain,
% 23.65/3.49      ( r1_tarski(sK3,sK1) = iProver_top ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_2815,c_922]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_4,plain,
% 23.65/3.49      ( ~ r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
% 23.65/3.49      inference(cnf_transformation,[],[f40]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_931,plain,
% 23.65/3.49      ( r1_tarski(X0,X1) != iProver_top
% 23.65/3.49      | r1_tarski(X0,k2_xboole_0(X2,X1)) = iProver_top ),
% 23.65/3.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_1734,plain,
% 23.65/3.49      ( r1_tarski(X0,X1) != iProver_top
% 23.65/3.49      | r1_tarski(X0,k2_xboole_0(X1,X2)) = iProver_top ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_0,c_931]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_1752,plain,
% 23.65/3.49      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2)
% 23.65/3.49      | r1_tarski(X0,X1) != iProver_top ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_1734,c_930]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_4935,plain,
% 23.65/3.49      ( k2_xboole_0(sK3,k2_xboole_0(sK1,X0)) = k2_xboole_0(sK1,X0) ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_2820,c_1752]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_83791,plain,
% 23.65/3.49      ( k2_xboole_0(sK3,k2_xboole_0(X0,sK1)) = k2_xboole_0(sK1,X0) ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_0,c_4935]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_3,plain,
% 23.65/3.49      ( r1_tarski(X0,X0) ),
% 23.65/3.49      inference(cnf_transformation,[],[f61]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_932,plain,
% 23.65/3.49      ( r1_tarski(X0,X0) = iProver_top ),
% 23.65/3.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_7,plain,
% 23.65/3.49      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
% 23.65/3.49      | r1_tarski(k4_xboole_0(X0,X1),X2) ),
% 23.65/3.49      inference(cnf_transformation,[],[f43]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_928,plain,
% 23.65/3.49      ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
% 23.65/3.49      | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
% 23.65/3.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_1994,plain,
% 23.65/3.49      ( r1_tarski(k4_xboole_0(k2_xboole_0(X0,X1),X0),X1) = iProver_top ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_932,c_928]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_6527,plain,
% 23.65/3.49      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X0),X1) = X1 ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_1994,c_930]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_9,plain,
% 23.65/3.49      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 23.65/3.49      inference(cnf_transformation,[],[f45]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_926,plain,
% 23.65/3.49      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 23.65/3.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_1736,plain,
% 23.65/3.49      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2)
% 23.65/3.49      | r1_tarski(X0,X2) != iProver_top ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_931,c_930]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_4224,plain,
% 23.65/3.49      ( k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X0,X2))) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_926,c_1736]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_43987,plain,
% 23.65/3.49      ( r1_tarski(X0,k2_xboole_0(X1,k2_xboole_0(X0,X2))) = iProver_top ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_4224,c_926]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_46771,plain,
% 23.65/3.49      ( r1_tarski(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) = iProver_top ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_0,c_43987]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_47056,plain,
% 23.65/3.49      ( r1_tarski(k4_xboole_0(k2_xboole_0(X0,X1),X0),k2_xboole_0(X1,X2)) = iProver_top ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_6527,c_46771]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_8,plain,
% 23.65/3.49      ( r1_tarski(X0,k2_xboole_0(X1,X2))
% 23.65/3.49      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ),
% 23.65/3.49      inference(cnf_transformation,[],[f44]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_927,plain,
% 23.65/3.49      ( r1_tarski(X0,k2_xboole_0(X1,X2)) = iProver_top
% 23.65/3.49      | r1_tarski(k4_xboole_0(X0,X1),X2) != iProver_top ),
% 23.65/3.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_69307,plain,
% 23.65/3.49      ( r1_tarski(k2_xboole_0(X0,X1),k2_xboole_0(X0,k2_xboole_0(X1,X2))) = iProver_top ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_47056,c_927]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_113156,plain,
% 23.65/3.49      ( r1_tarski(k2_xboole_0(sK3,X0),k2_xboole_0(sK1,X0)) = iProver_top ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_83791,c_69307]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_113789,plain,
% 23.65/3.49      ( r1_tarski(k2_xboole_0(sK3,sK2),sK1) = iProver_top ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_3652,c_113156]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_12,plain,
% 23.65/3.49      ( r2_hidden(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 23.65/3.49      inference(cnf_transformation,[],[f62]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_47528,plain,
% 23.65/3.49      ( r2_hidden(k2_xboole_0(sK3,sK2),k1_zfmisc_1(X0))
% 23.65/3.49      | ~ r1_tarski(k2_xboole_0(sK3,sK2),X0) ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_12]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_47529,plain,
% 23.65/3.49      ( r2_hidden(k2_xboole_0(sK3,sK2),k1_zfmisc_1(X0)) = iProver_top
% 23.65/3.49      | r1_tarski(k2_xboole_0(sK3,sK2),X0) != iProver_top ),
% 23.65/3.49      inference(predicate_to_equality,[status(thm)],[c_47528]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_47531,plain,
% 23.65/3.49      ( r2_hidden(k2_xboole_0(sK3,sK2),k1_zfmisc_1(sK1)) = iProver_top
% 23.65/3.49      | r1_tarski(k2_xboole_0(sK3,sK2),sK1) != iProver_top ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_47529]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_417,plain,
% 23.65/3.49      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 23.65/3.49      theory(equality) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_2262,plain,
% 23.65/3.49      ( ~ r1_tarski(X0,X1)
% 23.65/3.49      | r1_tarski(X2,k4_subset_1(sK1,sK2,sK3))
% 23.65/3.49      | X2 != X0
% 23.65/3.49      | k4_subset_1(sK1,sK2,sK3) != X1 ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_417]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_5904,plain,
% 23.65/3.49      ( r1_tarski(X0,k4_subset_1(sK1,sK2,sK3))
% 23.65/3.49      | ~ r1_tarski(X1,k2_xboole_0(sK2,sK3))
% 23.65/3.49      | X0 != X1
% 23.65/3.49      | k4_subset_1(sK1,sK2,sK3) != k2_xboole_0(sK2,sK3) ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_2262]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_7631,plain,
% 23.65/3.49      ( r1_tarski(X0,k4_subset_1(sK1,sK2,sK3))
% 23.65/3.49      | ~ r1_tarski(sK2,k2_xboole_0(sK2,sK3))
% 23.65/3.49      | X0 != sK2
% 23.65/3.49      | k4_subset_1(sK1,sK2,sK3) != k2_xboole_0(sK2,sK3) ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_5904]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_24830,plain,
% 23.65/3.49      ( r1_tarski(sK2,k4_subset_1(sK1,sK2,sK3))
% 23.65/3.49      | ~ r1_tarski(sK2,k2_xboole_0(sK2,sK3))
% 23.65/3.49      | k4_subset_1(sK1,sK2,sK3) != k2_xboole_0(sK2,sK3)
% 23.65/3.49      | sK2 != sK2 ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_7631]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_419,plain,
% 23.65/3.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 23.65/3.49      theory(equality) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_1194,plain,
% 23.65/3.49      ( r2_hidden(X0,X1)
% 23.65/3.49      | ~ r2_hidden(X2,k1_zfmisc_1(X3))
% 23.65/3.49      | X0 != X2
% 23.65/3.49      | X1 != k1_zfmisc_1(X3) ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_419]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_1719,plain,
% 23.65/3.49      ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
% 23.65/3.49      | r2_hidden(X2,k1_zfmisc_1(X3))
% 23.65/3.49      | X2 != X0
% 23.65/3.49      | k1_zfmisc_1(X3) != k1_zfmisc_1(X1) ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_1194]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_3402,plain,
% 23.65/3.49      ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
% 23.65/3.49      | r2_hidden(k4_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1))
% 23.65/3.49      | k4_subset_1(sK1,sK2,sK3) != X0
% 23.65/3.49      | k1_zfmisc_1(sK1) != k1_zfmisc_1(X1) ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_1719]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_10641,plain,
% 23.65/3.49      ( r2_hidden(k4_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1))
% 23.65/3.49      | ~ r2_hidden(k2_xboole_0(sK3,sK2),k1_zfmisc_1(X0))
% 23.65/3.49      | k4_subset_1(sK1,sK2,sK3) != k2_xboole_0(sK3,sK2)
% 23.65/3.49      | k1_zfmisc_1(sK1) != k1_zfmisc_1(X0) ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_3402]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_10642,plain,
% 23.65/3.49      ( k4_subset_1(sK1,sK2,sK3) != k2_xboole_0(sK3,sK2)
% 23.65/3.49      | k1_zfmisc_1(sK1) != k1_zfmisc_1(X0)
% 23.65/3.49      | r2_hidden(k4_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1)) = iProver_top
% 23.65/3.49      | r2_hidden(k2_xboole_0(sK3,sK2),k1_zfmisc_1(X0)) != iProver_top ),
% 23.65/3.49      inference(predicate_to_equality,[status(thm)],[c_10641]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_10644,plain,
% 23.65/3.49      ( k4_subset_1(sK1,sK2,sK3) != k2_xboole_0(sK3,sK2)
% 23.65/3.49      | k1_zfmisc_1(sK1) != k1_zfmisc_1(sK1)
% 23.65/3.49      | r2_hidden(k4_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1)) = iProver_top
% 23.65/3.49      | r2_hidden(k2_xboole_0(sK3,sK2),k1_zfmisc_1(sK1)) != iProver_top ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_10642]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_2426,plain,
% 23.65/3.49      ( r1_tarski(X0,k2_xboole_0(X0,sK3)) ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_9]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_7632,plain,
% 23.65/3.49      ( r1_tarski(sK2,k2_xboole_0(sK2,sK3)) ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_2426]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_3593,plain,
% 23.65/3.49      ( k2_xboole_0(sK3,sK2) = k2_xboole_0(sK2,sK3) ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_0]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_416,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_1575,plain,
% 23.65/3.49      ( X0 != X1
% 23.65/3.49      | k4_subset_1(sK1,sK2,sK3) != X1
% 23.65/3.49      | k4_subset_1(sK1,sK2,sK3) = X0 ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_416]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_2731,plain,
% 23.65/3.49      ( X0 != k2_xboole_0(sK2,sK3)
% 23.65/3.49      | k4_subset_1(sK1,sK2,sK3) = X0
% 23.65/3.49      | k4_subset_1(sK1,sK2,sK3) != k2_xboole_0(sK2,sK3) ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_1575]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_3592,plain,
% 23.65/3.49      ( k4_subset_1(sK1,sK2,sK3) = k2_xboole_0(sK3,sK2)
% 23.65/3.49      | k4_subset_1(sK1,sK2,sK3) != k2_xboole_0(sK2,sK3)
% 23.65/3.49      | k2_xboole_0(sK3,sK2) != k2_xboole_0(sK2,sK3) ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_2731]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_16,plain,
% 23.65/3.49      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 23.65/3.49      inference(cnf_transformation,[],[f51]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_1105,plain,
% 23.65/3.49      ( m1_subset_1(X0,k1_zfmisc_1(X1))
% 23.65/3.49      | ~ r2_hidden(X0,k1_zfmisc_1(X1))
% 23.65/3.49      | v1_xboole_0(k1_zfmisc_1(X1)) ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_16]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_2216,plain,
% 23.65/3.49      ( m1_subset_1(k4_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1))
% 23.65/3.49      | ~ r2_hidden(k4_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1))
% 23.65/3.49      | v1_xboole_0(k1_zfmisc_1(sK1)) ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_1105]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_2217,plain,
% 23.65/3.49      ( m1_subset_1(k4_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1)) = iProver_top
% 23.65/3.49      | r2_hidden(k4_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1)) != iProver_top
% 23.65/3.49      | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
% 23.65/3.49      inference(predicate_to_equality,[status(thm)],[c_2216]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_6,plain,
% 23.65/3.49      ( ~ r1_tarski(X0,X1)
% 23.65/3.49      | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ),
% 23.65/3.49      inference(cnf_transformation,[],[f42]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_1811,plain,
% 23.65/3.49      ( r1_tarski(k4_xboole_0(sK1,k4_subset_1(sK1,sK2,sK3)),k4_xboole_0(sK1,sK2))
% 23.65/3.49      | ~ r1_tarski(sK2,k4_subset_1(sK1,sK2,sK3)) ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_6]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_1143,plain,
% 23.65/3.49      ( ~ r1_tarski(X0,X1)
% 23.65/3.49      | r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2))
% 23.65/3.49      | k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)) != X0
% 23.65/3.49      | k3_subset_1(sK1,sK2) != X1 ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_417]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_1546,plain,
% 23.65/3.49      ( r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2))
% 23.65/3.49      | ~ r1_tarski(k4_xboole_0(sK1,k4_subset_1(sK1,sK2,sK3)),X0)
% 23.65/3.49      | k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)) != k4_xboole_0(sK1,k4_subset_1(sK1,sK2,sK3))
% 23.65/3.49      | k3_subset_1(sK1,sK2) != X0 ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_1143]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_1801,plain,
% 23.65/3.49      ( r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2))
% 23.65/3.49      | ~ r1_tarski(k4_xboole_0(sK1,k4_subset_1(sK1,sK2,sK3)),k4_xboole_0(sK1,sK2))
% 23.65/3.49      | k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)) != k4_xboole_0(sK1,k4_subset_1(sK1,sK2,sK3))
% 23.65/3.49      | k3_subset_1(sK1,sK2) != k4_xboole_0(sK1,sK2) ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_1546]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_20,plain,
% 23.65/3.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 23.65/3.49      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 23.65/3.49      | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
% 23.65/3.49      inference(cnf_transformation,[],[f56]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_1158,plain,
% 23.65/3.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
% 23.65/3.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
% 23.65/3.49      | k4_subset_1(sK1,X0,sK3) = k2_xboole_0(X0,sK3) ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_20]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_1581,plain,
% 23.65/3.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
% 23.65/3.49      | ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
% 23.65/3.49      | k4_subset_1(sK1,sK2,sK3) = k2_xboole_0(sK2,sK3) ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_1158]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_18,plain,
% 23.65/3.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 23.65/3.49      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 23.65/3.49      inference(cnf_transformation,[],[f54]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_1545,plain,
% 23.65/3.49      ( ~ m1_subset_1(k4_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1))
% 23.65/3.49      | k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)) = k4_xboole_0(sK1,k4_subset_1(sK1,sK2,sK3)) ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_18]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_1547,plain,
% 23.65/3.49      ( k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)) = k4_xboole_0(sK1,k4_subset_1(sK1,sK2,sK3))
% 23.65/3.49      | m1_subset_1(k4_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1)) != iProver_top ),
% 23.65/3.49      inference(predicate_to_equality,[status(thm)],[c_1545]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_415,plain,( X0 = X0 ),theory(equality) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_1331,plain,
% 23.65/3.49      ( sK2 = sK2 ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_415]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_1119,plain,
% 23.65/3.49      ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
% 23.65/3.49      | k3_subset_1(sK1,sK2) = k4_xboole_0(sK1,sK2) ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_18]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_418,plain,
% 23.65/3.49      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 23.65/3.49      theory(equality) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_425,plain,
% 23.65/3.49      ( k1_zfmisc_1(sK1) = k1_zfmisc_1(sK1) | sK1 != sK1 ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_418]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_1,plain,
% 23.65/3.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 23.65/3.49      inference(cnf_transformation,[],[f39]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_77,plain,
% 23.65/3.49      ( ~ r1_tarski(sK1,sK1) | sK1 = sK1 ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_1]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_73,plain,
% 23.65/3.49      ( r1_tarski(sK1,sK1) ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_3]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_21,negated_conjecture,
% 23.65/3.49      ( ~ r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2)) ),
% 23.65/3.49      inference(cnf_transformation,[],[f59]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(contradiction,plain,
% 23.65/3.49      ( $false ),
% 23.65/3.49      inference(minisat,
% 23.65/3.49                [status(thm)],
% 23.65/3.49                [c_113789,c_47531,c_24830,c_10644,c_7632,c_3593,c_3592,
% 23.65/3.49                 c_2217,c_1811,c_1801,c_1581,c_1547,c_1331,c_1119,c_425,
% 23.65/3.49                 c_77,c_73,c_32,c_21,c_22,c_23]) ).
% 23.65/3.49  
% 23.65/3.49  
% 23.65/3.49  % SZS output end CNFRefutation for theBenchmark.p
% 23.65/3.49  
% 23.65/3.49  ------                               Statistics
% 23.65/3.49  
% 23.65/3.49  ------ Selected
% 23.65/3.49  
% 23.65/3.49  total_time:                             2.638
% 23.65/3.49  
%------------------------------------------------------------------------------
