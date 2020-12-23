%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:49:06 EST 2020

% Result     : Theorem 3.29s
% Output     : CNFRefutation 3.29s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 171 expanded)
%              Number of clauses        :   48 (  58 expanded)
%              Number of leaves         :   14 (  36 expanded)
%              Depth                    :   14
%              Number of atoms          :  251 ( 633 expanded)
%              Number of equality atoms :   55 (  56 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f12,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
          <=> r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
            <=> r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r1_tarski(X0,X1)
          <~> r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0)))
            | ~ r1_tarski(X0,X1) )
          & ( r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0)))
            | r1_tarski(X0,X1) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0)))
            | ~ r1_tarski(X0,X1) )
          & ( r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0)))
            | r1_tarski(X0,X1) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0)))
            | ~ r1_tarski(X0,X1) )
          & ( r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0)))
            | r1_tarski(X0,X1) )
          & v1_relat_1(X1) )
     => ( ( ~ r1_tarski(X0,k7_relat_1(sK1,k1_relat_1(X0)))
          | ~ r1_tarski(X0,sK1) )
        & ( r1_tarski(X0,k7_relat_1(sK1,k1_relat_1(X0)))
          | r1_tarski(X0,sK1) )
        & v1_relat_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0)))
              | ~ r1_tarski(X0,X1) )
            & ( r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0)))
              | r1_tarski(X0,X1) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ( ~ r1_tarski(sK0,k7_relat_1(X1,k1_relat_1(sK0)))
            | ~ r1_tarski(sK0,X1) )
          & ( r1_tarski(sK0,k7_relat_1(X1,k1_relat_1(sK0)))
            | r1_tarski(sK0,X1) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ( ~ r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0)))
      | ~ r1_tarski(sK0,sK1) )
    & ( r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0)))
      | r1_tarski(sK0,sK1) )
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f31,f30])).

fof(f48,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f49,plain,
    ( r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0)))
    | r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f47,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f46,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f25])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f52,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f33])).

fof(f50,plain,
    ( ~ r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0)))
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k7_relat_1(X0,X2),k7_relat_1(X1,X2))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_100,plain,
    ( r1_tarski(k7_relat_1(X0,X2),k7_relat_1(X1,X2))
    | ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10,c_9,c_7])).

cnf(c_101,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k7_relat_1(X0,X2),k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(renaming,[status(thm)],[c_100])).

cnf(c_16414,plain,
    ( ~ r1_tarski(X0,sK1)
    | r1_tarski(k7_relat_1(X0,k1_relat_1(sK0)),k7_relat_1(sK1,k1_relat_1(sK0)))
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_101])).

cnf(c_16420,plain,
    ( r1_tarski(k7_relat_1(sK0,k1_relat_1(sK0)),k7_relat_1(sK1,k1_relat_1(sK0)))
    | ~ r1_tarski(sK0,sK1)
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_16414])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_7467,plain,
    ( ~ r1_tarski(X0,k7_relat_1(sK1,k1_relat_1(sK0)))
    | ~ r1_tarski(sK0,X0)
    | r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_16413,plain,
    ( ~ r1_tarski(k7_relat_1(X0,k1_relat_1(sK0)),k7_relat_1(sK1,k1_relat_1(sK0)))
    | ~ r1_tarski(sK0,k7_relat_1(X0,k1_relat_1(sK0)))
    | r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0))) ),
    inference(instantiation,[status(thm)],[c_7467])).

cnf(c_16416,plain,
    ( ~ r1_tarski(k7_relat_1(sK0,k1_relat_1(sK0)),k7_relat_1(sK1,k1_relat_1(sK0)))
    | r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0)))
    | ~ r1_tarski(sK0,k7_relat_1(sK0,k1_relat_1(sK0))) ),
    inference(instantiation,[status(thm)],[c_16413])).

cnf(c_16,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_723,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_6,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_729,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_12,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_727,plain,
    ( k7_relat_1(X0,X1) = X0
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1368,plain,
    ( k7_relat_1(X0,k2_xboole_0(k1_relat_1(X0),X1)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_729,c_727])).

cnf(c_4046,plain,
    ( k7_relat_1(sK1,k2_xboole_0(k1_relat_1(sK1),X0)) = sK1 ),
    inference(superposition,[status(thm)],[c_723,c_1368])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k2_xboole_0(k7_relat_1(X0,X1),k7_relat_1(X0,X2)) = k7_relat_1(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_728,plain,
    ( k2_xboole_0(k7_relat_1(X0,X1),k7_relat_1(X0,X2)) = k7_relat_1(X0,k2_xboole_0(X1,X2))
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2321,plain,
    ( k2_xboole_0(k7_relat_1(sK1,X0),k7_relat_1(sK1,X1)) = k7_relat_1(sK1,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_723,c_728])).

cnf(c_4,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_731,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_5,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2))
    | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_730,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) = iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1216,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_731,c_730])).

cnf(c_2675,plain,
    ( r1_tarski(k7_relat_1(sK1,X0),k7_relat_1(sK1,k2_xboole_0(X1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2321,c_1216])).

cnf(c_4168,plain,
    ( r1_tarski(k7_relat_1(sK1,X0),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_4046,c_2675])).

cnf(c_15,negated_conjecture,
    ( r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0)))
    | r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_724,plain,
    ( r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0))) = iProver_top
    | r1_tarski(sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_732,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2428,plain,
    ( r1_tarski(k7_relat_1(sK1,k1_relat_1(sK0)),X0) != iProver_top
    | r1_tarski(sK0,X0) = iProver_top
    | r1_tarski(sK0,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_724,c_732])).

cnf(c_4338,plain,
    ( r1_tarski(sK0,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_4168,c_2428])).

cnf(c_4362,plain,
    ( r1_tarski(sK0,sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4338])).

cnf(c_17,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_722,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_726,plain,
    ( k7_relat_1(X0,k1_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1207,plain,
    ( k7_relat_1(sK0,k1_relat_1(sK0)) = sK0 ),
    inference(superposition,[status(thm)],[c_722,c_726])).

cnf(c_721,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k7_relat_1(X0,X2),k7_relat_1(X1,X2)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_101])).

cnf(c_2256,plain,
    ( r1_tarski(sK0,X0) != iProver_top
    | r1_tarski(sK0,k7_relat_1(X0,k1_relat_1(sK0))) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1207,c_721])).

cnf(c_2302,plain,
    ( ~ r1_tarski(sK0,X0)
    | r1_tarski(sK0,k7_relat_1(X0,k1_relat_1(sK0)))
    | ~ v1_relat_1(X0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2256])).

cnf(c_2304,plain,
    ( r1_tarski(sK0,k7_relat_1(sK0,k1_relat_1(sK0)))
    | ~ r1_tarski(sK0,sK0)
    | ~ v1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_2302])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_50,plain,
    ( r1_tarski(sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_14,negated_conjecture,
    ( ~ r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0)))
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f50])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_16420,c_16416,c_4362,c_2304,c_50,c_14,c_16,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:41:19 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.29/0.96  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.29/0.96  
% 3.29/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.29/0.96  
% 3.29/0.96  ------  iProver source info
% 3.29/0.96  
% 3.29/0.96  git: date: 2020-06-30 10:37:57 +0100
% 3.29/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.29/0.96  git: non_committed_changes: false
% 3.29/0.96  git: last_make_outside_of_git: false
% 3.29/0.96  
% 3.29/0.96  ------ 
% 3.29/0.96  
% 3.29/0.96  ------ Input Options
% 3.29/0.96  
% 3.29/0.96  --out_options                           all
% 3.29/0.96  --tptp_safe_out                         true
% 3.29/0.96  --problem_path                          ""
% 3.29/0.96  --include_path                          ""
% 3.29/0.96  --clausifier                            res/vclausify_rel
% 3.29/0.96  --clausifier_options                    --mode clausify
% 3.29/0.96  --stdin                                 false
% 3.29/0.96  --stats_out                             all
% 3.29/0.96  
% 3.29/0.96  ------ General Options
% 3.29/0.96  
% 3.29/0.96  --fof                                   false
% 3.29/0.96  --time_out_real                         305.
% 3.29/0.96  --time_out_virtual                      -1.
% 3.29/0.96  --symbol_type_check                     false
% 3.29/0.96  --clausify_out                          false
% 3.29/0.96  --sig_cnt_out                           false
% 3.29/0.96  --trig_cnt_out                          false
% 3.29/0.96  --trig_cnt_out_tolerance                1.
% 3.29/0.96  --trig_cnt_out_sk_spl                   false
% 3.29/0.96  --abstr_cl_out                          false
% 3.29/0.96  
% 3.29/0.96  ------ Global Options
% 3.29/0.96  
% 3.29/0.96  --schedule                              default
% 3.29/0.96  --add_important_lit                     false
% 3.29/0.96  --prop_solver_per_cl                    1000
% 3.29/0.96  --min_unsat_core                        false
% 3.29/0.96  --soft_assumptions                      false
% 3.29/0.96  --soft_lemma_size                       3
% 3.29/0.96  --prop_impl_unit_size                   0
% 3.29/0.96  --prop_impl_unit                        []
% 3.29/0.96  --share_sel_clauses                     true
% 3.29/0.96  --reset_solvers                         false
% 3.29/0.96  --bc_imp_inh                            [conj_cone]
% 3.29/0.96  --conj_cone_tolerance                   3.
% 3.29/0.96  --extra_neg_conj                        none
% 3.29/0.96  --large_theory_mode                     true
% 3.29/0.96  --prolific_symb_bound                   200
% 3.29/0.96  --lt_threshold                          2000
% 3.29/0.96  --clause_weak_htbl                      true
% 3.29/0.96  --gc_record_bc_elim                     false
% 3.29/0.96  
% 3.29/0.96  ------ Preprocessing Options
% 3.29/0.96  
% 3.29/0.96  --preprocessing_flag                    true
% 3.29/0.96  --time_out_prep_mult                    0.1
% 3.29/0.96  --splitting_mode                        input
% 3.29/0.96  --splitting_grd                         true
% 3.29/0.96  --splitting_cvd                         false
% 3.29/0.96  --splitting_cvd_svl                     false
% 3.29/0.96  --splitting_nvd                         32
% 3.29/0.96  --sub_typing                            true
% 3.29/0.96  --prep_gs_sim                           true
% 3.29/0.96  --prep_unflatten                        true
% 3.29/0.96  --prep_res_sim                          true
% 3.29/0.96  --prep_upred                            true
% 3.29/0.96  --prep_sem_filter                       exhaustive
% 3.29/0.96  --prep_sem_filter_out                   false
% 3.29/0.96  --pred_elim                             true
% 3.29/0.96  --res_sim_input                         true
% 3.29/0.96  --eq_ax_congr_red                       true
% 3.29/0.96  --pure_diseq_elim                       true
% 3.29/0.96  --brand_transform                       false
% 3.29/0.96  --non_eq_to_eq                          false
% 3.29/0.96  --prep_def_merge                        true
% 3.29/0.96  --prep_def_merge_prop_impl              false
% 3.29/0.96  --prep_def_merge_mbd                    true
% 3.29/0.96  --prep_def_merge_tr_red                 false
% 3.29/0.96  --prep_def_merge_tr_cl                  false
% 3.29/0.96  --smt_preprocessing                     true
% 3.29/0.96  --smt_ac_axioms                         fast
% 3.29/0.96  --preprocessed_out                      false
% 3.29/0.96  --preprocessed_stats                    false
% 3.29/0.96  
% 3.29/0.96  ------ Abstraction refinement Options
% 3.29/0.96  
% 3.29/0.96  --abstr_ref                             []
% 3.29/0.96  --abstr_ref_prep                        false
% 3.29/0.96  --abstr_ref_until_sat                   false
% 3.29/0.96  --abstr_ref_sig_restrict                funpre
% 3.29/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 3.29/0.96  --abstr_ref_under                       []
% 3.29/0.96  
% 3.29/0.96  ------ SAT Options
% 3.29/0.96  
% 3.29/0.96  --sat_mode                              false
% 3.29/0.96  --sat_fm_restart_options                ""
% 3.29/0.96  --sat_gr_def                            false
% 3.29/0.96  --sat_epr_types                         true
% 3.29/0.96  --sat_non_cyclic_types                  false
% 3.29/0.96  --sat_finite_models                     false
% 3.29/0.96  --sat_fm_lemmas                         false
% 3.29/0.96  --sat_fm_prep                           false
% 3.29/0.96  --sat_fm_uc_incr                        true
% 3.29/0.96  --sat_out_model                         small
% 3.29/0.96  --sat_out_clauses                       false
% 3.29/0.96  
% 3.29/0.96  ------ QBF Options
% 3.29/0.96  
% 3.29/0.96  --qbf_mode                              false
% 3.29/0.96  --qbf_elim_univ                         false
% 3.29/0.96  --qbf_dom_inst                          none
% 3.29/0.96  --qbf_dom_pre_inst                      false
% 3.29/0.96  --qbf_sk_in                             false
% 3.29/0.96  --qbf_pred_elim                         true
% 3.29/0.96  --qbf_split                             512
% 3.29/0.96  
% 3.29/0.96  ------ BMC1 Options
% 3.29/0.96  
% 3.29/0.96  --bmc1_incremental                      false
% 3.29/0.96  --bmc1_axioms                           reachable_all
% 3.29/0.96  --bmc1_min_bound                        0
% 3.29/0.96  --bmc1_max_bound                        -1
% 3.29/0.96  --bmc1_max_bound_default                -1
% 3.29/0.96  --bmc1_symbol_reachability              true
% 3.29/0.96  --bmc1_property_lemmas                  false
% 3.29/0.96  --bmc1_k_induction                      false
% 3.29/0.96  --bmc1_non_equiv_states                 false
% 3.29/0.96  --bmc1_deadlock                         false
% 3.29/0.96  --bmc1_ucm                              false
% 3.29/0.96  --bmc1_add_unsat_core                   none
% 3.29/0.96  --bmc1_unsat_core_children              false
% 3.29/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 3.29/0.96  --bmc1_out_stat                         full
% 3.29/0.96  --bmc1_ground_init                      false
% 3.29/0.96  --bmc1_pre_inst_next_state              false
% 3.29/0.96  --bmc1_pre_inst_state                   false
% 3.29/0.96  --bmc1_pre_inst_reach_state             false
% 3.29/0.96  --bmc1_out_unsat_core                   false
% 3.29/0.96  --bmc1_aig_witness_out                  false
% 3.29/0.96  --bmc1_verbose                          false
% 3.29/0.96  --bmc1_dump_clauses_tptp                false
% 3.29/0.96  --bmc1_dump_unsat_core_tptp             false
% 3.29/0.96  --bmc1_dump_file                        -
% 3.29/0.96  --bmc1_ucm_expand_uc_limit              128
% 3.29/0.96  --bmc1_ucm_n_expand_iterations          6
% 3.29/0.96  --bmc1_ucm_extend_mode                  1
% 3.29/0.96  --bmc1_ucm_init_mode                    2
% 3.29/0.96  --bmc1_ucm_cone_mode                    none
% 3.29/0.96  --bmc1_ucm_reduced_relation_type        0
% 3.29/0.96  --bmc1_ucm_relax_model                  4
% 3.29/0.96  --bmc1_ucm_full_tr_after_sat            true
% 3.29/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 3.29/0.96  --bmc1_ucm_layered_model                none
% 3.29/0.96  --bmc1_ucm_max_lemma_size               10
% 3.29/0.96  
% 3.29/0.96  ------ AIG Options
% 3.29/0.96  
% 3.29/0.96  --aig_mode                              false
% 3.29/0.96  
% 3.29/0.96  ------ Instantiation Options
% 3.29/0.96  
% 3.29/0.96  --instantiation_flag                    true
% 3.29/0.96  --inst_sos_flag                         false
% 3.29/0.96  --inst_sos_phase                        true
% 3.29/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.29/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.29/0.96  --inst_lit_sel_side                     num_symb
% 3.29/0.96  --inst_solver_per_active                1400
% 3.29/0.96  --inst_solver_calls_frac                1.
% 3.29/0.96  --inst_passive_queue_type               priority_queues
% 3.29/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.29/0.96  --inst_passive_queues_freq              [25;2]
% 3.29/0.96  --inst_dismatching                      true
% 3.29/0.96  --inst_eager_unprocessed_to_passive     true
% 3.29/0.96  --inst_prop_sim_given                   true
% 3.29/0.96  --inst_prop_sim_new                     false
% 3.29/0.96  --inst_subs_new                         false
% 3.29/0.96  --inst_eq_res_simp                      false
% 3.29/0.96  --inst_subs_given                       false
% 3.29/0.96  --inst_orphan_elimination               true
% 3.29/0.96  --inst_learning_loop_flag               true
% 3.29/0.96  --inst_learning_start                   3000
% 3.29/0.96  --inst_learning_factor                  2
% 3.29/0.96  --inst_start_prop_sim_after_learn       3
% 3.29/0.96  --inst_sel_renew                        solver
% 3.29/0.96  --inst_lit_activity_flag                true
% 3.29/0.96  --inst_restr_to_given                   false
% 3.29/0.96  --inst_activity_threshold               500
% 3.29/0.96  --inst_out_proof                        true
% 3.29/0.96  
% 3.29/0.96  ------ Resolution Options
% 3.29/0.96  
% 3.29/0.96  --resolution_flag                       true
% 3.29/0.96  --res_lit_sel                           adaptive
% 3.29/0.96  --res_lit_sel_side                      none
% 3.29/0.96  --res_ordering                          kbo
% 3.29/0.96  --res_to_prop_solver                    active
% 3.29/0.96  --res_prop_simpl_new                    false
% 3.29/0.96  --res_prop_simpl_given                  true
% 3.29/0.96  --res_passive_queue_type                priority_queues
% 3.29/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.29/0.96  --res_passive_queues_freq               [15;5]
% 3.29/0.96  --res_forward_subs                      full
% 3.29/0.96  --res_backward_subs                     full
% 3.29/0.96  --res_forward_subs_resolution           true
% 3.29/0.96  --res_backward_subs_resolution          true
% 3.29/0.96  --res_orphan_elimination                true
% 3.29/0.96  --res_time_limit                        2.
% 3.29/0.96  --res_out_proof                         true
% 3.29/0.96  
% 3.29/0.96  ------ Superposition Options
% 3.29/0.96  
% 3.29/0.96  --superposition_flag                    true
% 3.29/0.96  --sup_passive_queue_type                priority_queues
% 3.29/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.29/0.96  --sup_passive_queues_freq               [8;1;4]
% 3.29/0.96  --demod_completeness_check              fast
% 3.29/0.96  --demod_use_ground                      true
% 3.29/0.96  --sup_to_prop_solver                    passive
% 3.29/0.96  --sup_prop_simpl_new                    true
% 3.29/0.96  --sup_prop_simpl_given                  true
% 3.29/0.96  --sup_fun_splitting                     false
% 3.29/0.96  --sup_smt_interval                      50000
% 3.29/0.96  
% 3.29/0.96  ------ Superposition Simplification Setup
% 3.29/0.96  
% 3.29/0.96  --sup_indices_passive                   []
% 3.29/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.29/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.29/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.29/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 3.29/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.29/0.96  --sup_full_bw                           [BwDemod]
% 3.29/0.96  --sup_immed_triv                        [TrivRules]
% 3.29/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.29/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.29/0.96  --sup_immed_bw_main                     []
% 3.29/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.29/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 3.29/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.29/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.29/0.96  
% 3.29/0.96  ------ Combination Options
% 3.29/0.96  
% 3.29/0.96  --comb_res_mult                         3
% 3.29/0.96  --comb_sup_mult                         2
% 3.29/0.96  --comb_inst_mult                        10
% 3.29/0.96  
% 3.29/0.96  ------ Debug Options
% 3.29/0.96  
% 3.29/0.96  --dbg_backtrace                         false
% 3.29/0.96  --dbg_dump_prop_clauses                 false
% 3.29/0.96  --dbg_dump_prop_clauses_file            -
% 3.29/0.96  --dbg_out_stat                          false
% 3.29/0.96  ------ Parsing...
% 3.29/0.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.29/0.96  
% 3.29/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.29/0.96  
% 3.29/0.96  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.29/0.96  
% 3.29/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.29/0.96  ------ Proving...
% 3.29/0.96  ------ Problem Properties 
% 3.29/0.96  
% 3.29/0.96  
% 3.29/0.96  clauses                                 15
% 3.29/0.96  conjectures                             4
% 3.29/0.96  EPR                                     6
% 3.29/0.96  Horn                                    14
% 3.29/0.96  unary                                   5
% 3.29/0.96  binary                                  5
% 3.29/0.96  lits                                    30
% 3.29/0.96  lits eq                                 4
% 3.29/0.96  fd_pure                                 0
% 3.29/0.96  fd_pseudo                               0
% 3.29/0.96  fd_cond                                 0
% 3.29/0.96  fd_pseudo_cond                          1
% 3.29/0.96  AC symbols                              0
% 3.29/0.96  
% 3.29/0.96  ------ Schedule dynamic 5 is on 
% 3.29/0.96  
% 3.29/0.96  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.29/0.96  
% 3.29/0.96  
% 3.29/0.96  ------ 
% 3.29/0.96  Current options:
% 3.29/0.96  ------ 
% 3.29/0.96  
% 3.29/0.96  ------ Input Options
% 3.29/0.96  
% 3.29/0.96  --out_options                           all
% 3.29/0.96  --tptp_safe_out                         true
% 3.29/0.96  --problem_path                          ""
% 3.29/0.96  --include_path                          ""
% 3.29/0.96  --clausifier                            res/vclausify_rel
% 3.29/0.96  --clausifier_options                    --mode clausify
% 3.29/0.96  --stdin                                 false
% 3.29/0.96  --stats_out                             all
% 3.29/0.96  
% 3.29/0.96  ------ General Options
% 3.29/0.96  
% 3.29/0.96  --fof                                   false
% 3.29/0.96  --time_out_real                         305.
% 3.29/0.96  --time_out_virtual                      -1.
% 3.29/0.96  --symbol_type_check                     false
% 3.29/0.96  --clausify_out                          false
% 3.29/0.96  --sig_cnt_out                           false
% 3.29/0.96  --trig_cnt_out                          false
% 3.29/0.96  --trig_cnt_out_tolerance                1.
% 3.29/0.96  --trig_cnt_out_sk_spl                   false
% 3.29/0.96  --abstr_cl_out                          false
% 3.29/0.96  
% 3.29/0.96  ------ Global Options
% 3.29/0.96  
% 3.29/0.96  --schedule                              default
% 3.29/0.96  --add_important_lit                     false
% 3.29/0.96  --prop_solver_per_cl                    1000
% 3.29/0.96  --min_unsat_core                        false
% 3.29/0.96  --soft_assumptions                      false
% 3.29/0.96  --soft_lemma_size                       3
% 3.29/0.96  --prop_impl_unit_size                   0
% 3.29/0.96  --prop_impl_unit                        []
% 3.29/0.96  --share_sel_clauses                     true
% 3.29/0.96  --reset_solvers                         false
% 3.29/0.96  --bc_imp_inh                            [conj_cone]
% 3.29/0.96  --conj_cone_tolerance                   3.
% 3.29/0.96  --extra_neg_conj                        none
% 3.29/0.96  --large_theory_mode                     true
% 3.29/0.96  --prolific_symb_bound                   200
% 3.29/0.96  --lt_threshold                          2000
% 3.29/0.96  --clause_weak_htbl                      true
% 3.29/0.96  --gc_record_bc_elim                     false
% 3.29/0.96  
% 3.29/0.96  ------ Preprocessing Options
% 3.29/0.96  
% 3.29/0.96  --preprocessing_flag                    true
% 3.29/0.96  --time_out_prep_mult                    0.1
% 3.29/0.96  --splitting_mode                        input
% 3.29/0.96  --splitting_grd                         true
% 3.29/0.96  --splitting_cvd                         false
% 3.29/0.96  --splitting_cvd_svl                     false
% 3.29/0.96  --splitting_nvd                         32
% 3.29/0.96  --sub_typing                            true
% 3.29/0.96  --prep_gs_sim                           true
% 3.29/0.96  --prep_unflatten                        true
% 3.29/0.96  --prep_res_sim                          true
% 3.29/0.96  --prep_upred                            true
% 3.29/0.96  --prep_sem_filter                       exhaustive
% 3.29/0.96  --prep_sem_filter_out                   false
% 3.29/0.96  --pred_elim                             true
% 3.29/0.96  --res_sim_input                         true
% 3.29/0.96  --eq_ax_congr_red                       true
% 3.29/0.96  --pure_diseq_elim                       true
% 3.29/0.96  --brand_transform                       false
% 3.29/0.96  --non_eq_to_eq                          false
% 3.29/0.96  --prep_def_merge                        true
% 3.29/0.96  --prep_def_merge_prop_impl              false
% 3.29/0.96  --prep_def_merge_mbd                    true
% 3.29/0.96  --prep_def_merge_tr_red                 false
% 3.29/0.96  --prep_def_merge_tr_cl                  false
% 3.29/0.96  --smt_preprocessing                     true
% 3.29/0.96  --smt_ac_axioms                         fast
% 3.29/0.96  --preprocessed_out                      false
% 3.29/0.96  --preprocessed_stats                    false
% 3.29/0.96  
% 3.29/0.96  ------ Abstraction refinement Options
% 3.29/0.96  
% 3.29/0.96  --abstr_ref                             []
% 3.29/0.96  --abstr_ref_prep                        false
% 3.29/0.96  --abstr_ref_until_sat                   false
% 3.29/0.96  --abstr_ref_sig_restrict                funpre
% 3.29/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 3.29/0.96  --abstr_ref_under                       []
% 3.29/0.96  
% 3.29/0.96  ------ SAT Options
% 3.29/0.96  
% 3.29/0.96  --sat_mode                              false
% 3.29/0.96  --sat_fm_restart_options                ""
% 3.29/0.96  --sat_gr_def                            false
% 3.29/0.96  --sat_epr_types                         true
% 3.29/0.96  --sat_non_cyclic_types                  false
% 3.29/0.96  --sat_finite_models                     false
% 3.29/0.96  --sat_fm_lemmas                         false
% 3.29/0.96  --sat_fm_prep                           false
% 3.29/0.96  --sat_fm_uc_incr                        true
% 3.29/0.96  --sat_out_model                         small
% 3.29/0.96  --sat_out_clauses                       false
% 3.29/0.96  
% 3.29/0.96  ------ QBF Options
% 3.29/0.96  
% 3.29/0.96  --qbf_mode                              false
% 3.29/0.96  --qbf_elim_univ                         false
% 3.29/0.96  --qbf_dom_inst                          none
% 3.29/0.96  --qbf_dom_pre_inst                      false
% 3.29/0.96  --qbf_sk_in                             false
% 3.29/0.96  --qbf_pred_elim                         true
% 3.29/0.96  --qbf_split                             512
% 3.29/0.96  
% 3.29/0.96  ------ BMC1 Options
% 3.29/0.96  
% 3.29/0.96  --bmc1_incremental                      false
% 3.29/0.96  --bmc1_axioms                           reachable_all
% 3.29/0.96  --bmc1_min_bound                        0
% 3.29/0.96  --bmc1_max_bound                        -1
% 3.29/0.96  --bmc1_max_bound_default                -1
% 3.29/0.96  --bmc1_symbol_reachability              true
% 3.29/0.96  --bmc1_property_lemmas                  false
% 3.29/0.96  --bmc1_k_induction                      false
% 3.29/0.96  --bmc1_non_equiv_states                 false
% 3.29/0.96  --bmc1_deadlock                         false
% 3.29/0.96  --bmc1_ucm                              false
% 3.29/0.96  --bmc1_add_unsat_core                   none
% 3.29/0.96  --bmc1_unsat_core_children              false
% 3.29/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 3.29/0.96  --bmc1_out_stat                         full
% 3.29/0.96  --bmc1_ground_init                      false
% 3.29/0.96  --bmc1_pre_inst_next_state              false
% 3.29/0.96  --bmc1_pre_inst_state                   false
% 3.29/0.96  --bmc1_pre_inst_reach_state             false
% 3.29/0.96  --bmc1_out_unsat_core                   false
% 3.29/0.96  --bmc1_aig_witness_out                  false
% 3.29/0.96  --bmc1_verbose                          false
% 3.29/0.96  --bmc1_dump_clauses_tptp                false
% 3.29/0.96  --bmc1_dump_unsat_core_tptp             false
% 3.29/0.96  --bmc1_dump_file                        -
% 3.29/0.96  --bmc1_ucm_expand_uc_limit              128
% 3.29/0.96  --bmc1_ucm_n_expand_iterations          6
% 3.29/0.96  --bmc1_ucm_extend_mode                  1
% 3.29/0.96  --bmc1_ucm_init_mode                    2
% 3.29/0.96  --bmc1_ucm_cone_mode                    none
% 3.29/0.96  --bmc1_ucm_reduced_relation_type        0
% 3.29/0.96  --bmc1_ucm_relax_model                  4
% 3.29/0.96  --bmc1_ucm_full_tr_after_sat            true
% 3.29/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 3.29/0.96  --bmc1_ucm_layered_model                none
% 3.29/0.96  --bmc1_ucm_max_lemma_size               10
% 3.29/0.96  
% 3.29/0.96  ------ AIG Options
% 3.29/0.96  
% 3.29/0.96  --aig_mode                              false
% 3.29/0.96  
% 3.29/0.96  ------ Instantiation Options
% 3.29/0.96  
% 3.29/0.96  --instantiation_flag                    true
% 3.29/0.96  --inst_sos_flag                         false
% 3.29/0.96  --inst_sos_phase                        true
% 3.29/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.29/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.29/0.96  --inst_lit_sel_side                     none
% 3.29/0.96  --inst_solver_per_active                1400
% 3.29/0.96  --inst_solver_calls_frac                1.
% 3.29/0.96  --inst_passive_queue_type               priority_queues
% 3.29/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.29/0.96  --inst_passive_queues_freq              [25;2]
% 3.29/0.96  --inst_dismatching                      true
% 3.29/0.96  --inst_eager_unprocessed_to_passive     true
% 3.29/0.96  --inst_prop_sim_given                   true
% 3.29/0.96  --inst_prop_sim_new                     false
% 3.29/0.96  --inst_subs_new                         false
% 3.29/0.96  --inst_eq_res_simp                      false
% 3.29/0.96  --inst_subs_given                       false
% 3.29/0.96  --inst_orphan_elimination               true
% 3.29/0.96  --inst_learning_loop_flag               true
% 3.29/0.96  --inst_learning_start                   3000
% 3.29/0.96  --inst_learning_factor                  2
% 3.29/0.96  --inst_start_prop_sim_after_learn       3
% 3.29/0.96  --inst_sel_renew                        solver
% 3.29/0.96  --inst_lit_activity_flag                true
% 3.29/0.96  --inst_restr_to_given                   false
% 3.29/0.96  --inst_activity_threshold               500
% 3.29/0.96  --inst_out_proof                        true
% 3.29/0.96  
% 3.29/0.96  ------ Resolution Options
% 3.29/0.96  
% 3.29/0.96  --resolution_flag                       false
% 3.29/0.96  --res_lit_sel                           adaptive
% 3.29/0.96  --res_lit_sel_side                      none
% 3.29/0.96  --res_ordering                          kbo
% 3.29/0.96  --res_to_prop_solver                    active
% 3.29/0.96  --res_prop_simpl_new                    false
% 3.29/0.96  --res_prop_simpl_given                  true
% 3.29/0.96  --res_passive_queue_type                priority_queues
% 3.29/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.29/0.96  --res_passive_queues_freq               [15;5]
% 3.29/0.96  --res_forward_subs                      full
% 3.29/0.96  --res_backward_subs                     full
% 3.29/0.96  --res_forward_subs_resolution           true
% 3.29/0.96  --res_backward_subs_resolution          true
% 3.29/0.96  --res_orphan_elimination                true
% 3.29/0.96  --res_time_limit                        2.
% 3.29/0.96  --res_out_proof                         true
% 3.29/0.96  
% 3.29/0.96  ------ Superposition Options
% 3.29/0.96  
% 3.29/0.96  --superposition_flag                    true
% 3.29/0.96  --sup_passive_queue_type                priority_queues
% 3.29/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.29/0.96  --sup_passive_queues_freq               [8;1;4]
% 3.29/0.96  --demod_completeness_check              fast
% 3.29/0.96  --demod_use_ground                      true
% 3.29/0.96  --sup_to_prop_solver                    passive
% 3.29/0.96  --sup_prop_simpl_new                    true
% 3.29/0.96  --sup_prop_simpl_given                  true
% 3.29/0.96  --sup_fun_splitting                     false
% 3.29/0.96  --sup_smt_interval                      50000
% 3.29/0.96  
% 3.29/0.96  ------ Superposition Simplification Setup
% 3.29/0.96  
% 3.29/0.96  --sup_indices_passive                   []
% 3.29/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.29/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.29/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.29/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 3.29/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.29/0.96  --sup_full_bw                           [BwDemod]
% 3.29/0.96  --sup_immed_triv                        [TrivRules]
% 3.29/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.29/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.29/0.96  --sup_immed_bw_main                     []
% 3.29/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.29/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 3.29/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.29/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.29/0.96  
% 3.29/0.96  ------ Combination Options
% 3.29/0.96  
% 3.29/0.96  --comb_res_mult                         3
% 3.29/0.96  --comb_sup_mult                         2
% 3.29/0.96  --comb_inst_mult                        10
% 3.29/0.96  
% 3.29/0.96  ------ Debug Options
% 3.29/0.96  
% 3.29/0.96  --dbg_backtrace                         false
% 3.29/0.96  --dbg_dump_prop_clauses                 false
% 3.29/0.96  --dbg_dump_prop_clauses_file            -
% 3.29/0.96  --dbg_out_stat                          false
% 3.29/0.96  
% 3.29/0.96  
% 3.29/0.96  
% 3.29/0.96  
% 3.29/0.96  ------ Proving...
% 3.29/0.96  
% 3.29/0.96  
% 3.29/0.96  % SZS status Theorem for theBenchmark.p
% 3.29/0.96  
% 3.29/0.96  % SZS output start CNFRefutation for theBenchmark.p
% 3.29/0.96  
% 3.29/0.96  fof(f8,axiom,(
% 3.29/0.96    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)))))),
% 3.29/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/0.96  
% 3.29/0.96  fof(f18,plain,(
% 3.29/0.96    ! [X0,X1] : (! [X2] : ((r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 3.29/0.96    inference(ennf_transformation,[],[f8])).
% 3.29/0.96  
% 3.29/0.96  fof(f19,plain,(
% 3.29/0.96    ! [X0,X1] : (! [X2] : (r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 3.29/0.96    inference(flattening,[],[f18])).
% 3.29/0.96  
% 3.29/0.96  fof(f43,plain,(
% 3.29/0.96    ( ! [X2,X0,X1] : (r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 3.29/0.96    inference(cnf_transformation,[],[f19])).
% 3.29/0.96  
% 3.29/0.96  fof(f7,axiom,(
% 3.29/0.96    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.29/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/0.96  
% 3.29/0.96  fof(f17,plain,(
% 3.29/0.96    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.29/0.96    inference(ennf_transformation,[],[f7])).
% 3.29/0.96  
% 3.29/0.96  fof(f42,plain,(
% 3.29/0.96    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.29/0.96    inference(cnf_transformation,[],[f17])).
% 3.29/0.96  
% 3.29/0.96  fof(f6,axiom,(
% 3.29/0.96    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.29/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/0.96  
% 3.29/0.96  fof(f27,plain,(
% 3.29/0.96    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.29/0.96    inference(nnf_transformation,[],[f6])).
% 3.29/0.96  
% 3.29/0.96  fof(f41,plain,(
% 3.29/0.96    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.29/0.96    inference(cnf_transformation,[],[f27])).
% 3.29/0.96  
% 3.29/0.96  fof(f2,axiom,(
% 3.29/0.96    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.29/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/0.96  
% 3.29/0.96  fof(f14,plain,(
% 3.29/0.96    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.29/0.96    inference(ennf_transformation,[],[f2])).
% 3.29/0.96  
% 3.29/0.96  fof(f15,plain,(
% 3.29/0.96    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.29/0.96    inference(flattening,[],[f14])).
% 3.29/0.96  
% 3.29/0.96  fof(f36,plain,(
% 3.29/0.96    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 3.29/0.96    inference(cnf_transformation,[],[f15])).
% 3.29/0.96  
% 3.29/0.96  fof(f12,conjecture,(
% 3.29/0.96    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) <=> r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))))))),
% 3.29/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/0.96  
% 3.29/0.96  fof(f13,negated_conjecture,(
% 3.29/0.96    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) <=> r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))))))),
% 3.29/0.96    inference(negated_conjecture,[],[f12])).
% 3.29/0.96  
% 3.29/0.96  fof(f24,plain,(
% 3.29/0.96    ? [X0] : (? [X1] : ((r1_tarski(X0,X1) <~> r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0)))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 3.29/0.96    inference(ennf_transformation,[],[f13])).
% 3.29/0.96  
% 3.29/0.96  fof(f28,plain,(
% 3.29/0.96    ? [X0] : (? [X1] : (((~r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))) | r1_tarski(X0,X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 3.29/0.96    inference(nnf_transformation,[],[f24])).
% 3.29/0.96  
% 3.29/0.96  fof(f29,plain,(
% 3.29/0.96    ? [X0] : (? [X1] : ((~r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))) | r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 3.29/0.96    inference(flattening,[],[f28])).
% 3.29/0.96  
% 3.29/0.96  fof(f31,plain,(
% 3.29/0.96    ( ! [X0] : (? [X1] : ((~r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))) | r1_tarski(X0,X1)) & v1_relat_1(X1)) => ((~r1_tarski(X0,k7_relat_1(sK1,k1_relat_1(X0))) | ~r1_tarski(X0,sK1)) & (r1_tarski(X0,k7_relat_1(sK1,k1_relat_1(X0))) | r1_tarski(X0,sK1)) & v1_relat_1(sK1))) )),
% 3.29/0.96    introduced(choice_axiom,[])).
% 3.29/0.96  
% 3.29/0.96  fof(f30,plain,(
% 3.29/0.96    ? [X0] : (? [X1] : ((~r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))) | r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : ((~r1_tarski(sK0,k7_relat_1(X1,k1_relat_1(sK0))) | ~r1_tarski(sK0,X1)) & (r1_tarski(sK0,k7_relat_1(X1,k1_relat_1(sK0))) | r1_tarski(sK0,X1)) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 3.29/0.96    introduced(choice_axiom,[])).
% 3.29/0.96  
% 3.29/0.96  fof(f32,plain,(
% 3.29/0.96    ((~r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0))) | ~r1_tarski(sK0,sK1)) & (r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0))) | r1_tarski(sK0,sK1)) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 3.29/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f31,f30])).
% 3.29/0.96  
% 3.29/0.96  fof(f48,plain,(
% 3.29/0.96    v1_relat_1(sK1)),
% 3.29/0.96    inference(cnf_transformation,[],[f32])).
% 3.29/0.96  
% 3.29/0.96  fof(f5,axiom,(
% 3.29/0.96    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.29/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/0.96  
% 3.29/0.96  fof(f39,plain,(
% 3.29/0.96    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.29/0.96    inference(cnf_transformation,[],[f5])).
% 3.29/0.96  
% 3.29/0.96  fof(f10,axiom,(
% 3.29/0.96    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 3.29/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/0.96  
% 3.29/0.96  fof(f21,plain,(
% 3.29/0.96    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.29/0.96    inference(ennf_transformation,[],[f10])).
% 3.29/0.96  
% 3.29/0.96  fof(f22,plain,(
% 3.29/0.96    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.29/0.96    inference(flattening,[],[f21])).
% 3.29/0.96  
% 3.29/0.96  fof(f45,plain,(
% 3.29/0.96    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.29/0.96    inference(cnf_transformation,[],[f22])).
% 3.29/0.96  
% 3.29/0.96  fof(f9,axiom,(
% 3.29/0.96    ! [X0,X1,X2] : (v1_relat_1(X2) => k2_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k2_xboole_0(X0,X1)))),
% 3.29/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/0.96  
% 3.29/0.96  fof(f20,plain,(
% 3.29/0.96    ! [X0,X1,X2] : (k2_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k2_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 3.29/0.96    inference(ennf_transformation,[],[f9])).
% 3.29/0.96  
% 3.29/0.96  fof(f44,plain,(
% 3.29/0.96    ( ! [X2,X0,X1] : (k2_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k2_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 3.29/0.96    inference(cnf_transformation,[],[f20])).
% 3.29/0.96  
% 3.29/0.96  fof(f3,axiom,(
% 3.29/0.96    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.29/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/0.96  
% 3.29/0.96  fof(f37,plain,(
% 3.29/0.96    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.29/0.96    inference(cnf_transformation,[],[f3])).
% 3.29/0.96  
% 3.29/0.96  fof(f4,axiom,(
% 3.29/0.96    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 3.29/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/0.96  
% 3.29/0.96  fof(f16,plain,(
% 3.29/0.96    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 3.29/0.96    inference(ennf_transformation,[],[f4])).
% 3.29/0.96  
% 3.29/0.96  fof(f38,plain,(
% 3.29/0.96    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 3.29/0.96    inference(cnf_transformation,[],[f16])).
% 3.29/0.96  
% 3.29/0.96  fof(f49,plain,(
% 3.29/0.96    r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0))) | r1_tarski(sK0,sK1)),
% 3.29/0.96    inference(cnf_transformation,[],[f32])).
% 3.29/0.96  
% 3.29/0.96  fof(f47,plain,(
% 3.29/0.96    v1_relat_1(sK0)),
% 3.29/0.96    inference(cnf_transformation,[],[f32])).
% 3.29/0.96  
% 3.29/0.96  fof(f11,axiom,(
% 3.29/0.96    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 3.29/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/0.96  
% 3.29/0.96  fof(f23,plain,(
% 3.29/0.96    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 3.29/0.96    inference(ennf_transformation,[],[f11])).
% 3.29/0.96  
% 3.29/0.96  fof(f46,plain,(
% 3.29/0.96    ( ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 3.29/0.96    inference(cnf_transformation,[],[f23])).
% 3.29/0.96  
% 3.29/0.96  fof(f1,axiom,(
% 3.29/0.96    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.29/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/0.96  
% 3.29/0.96  fof(f25,plain,(
% 3.29/0.96    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.29/0.96    inference(nnf_transformation,[],[f1])).
% 3.29/0.96  
% 3.29/0.96  fof(f26,plain,(
% 3.29/0.96    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.29/0.96    inference(flattening,[],[f25])).
% 3.29/0.96  
% 3.29/0.96  fof(f33,plain,(
% 3.29/0.96    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.29/0.96    inference(cnf_transformation,[],[f26])).
% 3.29/0.96  
% 3.29/0.96  fof(f52,plain,(
% 3.29/0.96    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.29/0.96    inference(equality_resolution,[],[f33])).
% 3.29/0.96  
% 3.29/0.96  fof(f50,plain,(
% 3.29/0.96    ~r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0))) | ~r1_tarski(sK0,sK1)),
% 3.29/0.96    inference(cnf_transformation,[],[f32])).
% 3.29/0.96  
% 3.29/0.96  cnf(c_10,plain,
% 3.29/0.96      ( ~ r1_tarski(X0,X1)
% 3.29/0.96      | r1_tarski(k7_relat_1(X0,X2),k7_relat_1(X1,X2))
% 3.29/0.96      | ~ v1_relat_1(X0)
% 3.29/0.96      | ~ v1_relat_1(X1) ),
% 3.29/0.96      inference(cnf_transformation,[],[f43]) ).
% 3.29/0.96  
% 3.29/0.96  cnf(c_9,plain,
% 3.29/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.29/0.96      | ~ v1_relat_1(X1)
% 3.29/0.96      | v1_relat_1(X0) ),
% 3.29/0.96      inference(cnf_transformation,[],[f42]) ).
% 3.29/0.96  
% 3.29/0.96  cnf(c_7,plain,
% 3.29/0.96      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.29/0.96      inference(cnf_transformation,[],[f41]) ).
% 3.29/0.96  
% 3.29/0.96  cnf(c_100,plain,
% 3.29/0.96      ( r1_tarski(k7_relat_1(X0,X2),k7_relat_1(X1,X2))
% 3.29/0.96      | ~ r1_tarski(X0,X1)
% 3.29/0.96      | ~ v1_relat_1(X1) ),
% 3.29/0.96      inference(global_propositional_subsumption,
% 3.29/0.96                [status(thm)],
% 3.29/0.96                [c_10,c_9,c_7]) ).
% 3.29/0.96  
% 3.29/0.96  cnf(c_101,plain,
% 3.29/0.96      ( ~ r1_tarski(X0,X1)
% 3.29/0.96      | r1_tarski(k7_relat_1(X0,X2),k7_relat_1(X1,X2))
% 3.29/0.96      | ~ v1_relat_1(X1) ),
% 3.29/0.96      inference(renaming,[status(thm)],[c_100]) ).
% 3.29/0.96  
% 3.29/0.96  cnf(c_16414,plain,
% 3.29/0.96      ( ~ r1_tarski(X0,sK1)
% 3.29/0.96      | r1_tarski(k7_relat_1(X0,k1_relat_1(sK0)),k7_relat_1(sK1,k1_relat_1(sK0)))
% 3.29/0.96      | ~ v1_relat_1(sK1) ),
% 3.29/0.96      inference(instantiation,[status(thm)],[c_101]) ).
% 3.29/0.96  
% 3.29/0.96  cnf(c_16420,plain,
% 3.29/0.96      ( r1_tarski(k7_relat_1(sK0,k1_relat_1(sK0)),k7_relat_1(sK1,k1_relat_1(sK0)))
% 3.29/0.96      | ~ r1_tarski(sK0,sK1)
% 3.29/0.96      | ~ v1_relat_1(sK1) ),
% 3.29/0.96      inference(instantiation,[status(thm)],[c_16414]) ).
% 3.29/0.96  
% 3.29/0.96  cnf(c_3,plain,
% 3.29/0.96      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 3.29/0.96      inference(cnf_transformation,[],[f36]) ).
% 3.29/0.96  
% 3.29/0.96  cnf(c_7467,plain,
% 3.29/0.96      ( ~ r1_tarski(X0,k7_relat_1(sK1,k1_relat_1(sK0)))
% 3.29/0.96      | ~ r1_tarski(sK0,X0)
% 3.29/0.96      | r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0))) ),
% 3.29/0.96      inference(instantiation,[status(thm)],[c_3]) ).
% 3.29/0.96  
% 3.29/0.96  cnf(c_16413,plain,
% 3.29/0.96      ( ~ r1_tarski(k7_relat_1(X0,k1_relat_1(sK0)),k7_relat_1(sK1,k1_relat_1(sK0)))
% 3.29/0.96      | ~ r1_tarski(sK0,k7_relat_1(X0,k1_relat_1(sK0)))
% 3.29/0.96      | r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0))) ),
% 3.29/0.96      inference(instantiation,[status(thm)],[c_7467]) ).
% 3.29/0.96  
% 3.29/0.96  cnf(c_16416,plain,
% 3.29/0.96      ( ~ r1_tarski(k7_relat_1(sK0,k1_relat_1(sK0)),k7_relat_1(sK1,k1_relat_1(sK0)))
% 3.29/0.96      | r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0)))
% 3.29/0.96      | ~ r1_tarski(sK0,k7_relat_1(sK0,k1_relat_1(sK0))) ),
% 3.29/0.96      inference(instantiation,[status(thm)],[c_16413]) ).
% 3.29/0.96  
% 3.29/0.96  cnf(c_16,negated_conjecture,
% 3.29/0.96      ( v1_relat_1(sK1) ),
% 3.29/0.96      inference(cnf_transformation,[],[f48]) ).
% 3.29/0.96  
% 3.29/0.96  cnf(c_723,plain,
% 3.29/0.96      ( v1_relat_1(sK1) = iProver_top ),
% 3.29/0.96      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.29/0.96  
% 3.29/0.96  cnf(c_6,plain,
% 3.29/0.96      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 3.29/0.96      inference(cnf_transformation,[],[f39]) ).
% 3.29/0.96  
% 3.29/0.96  cnf(c_729,plain,
% 3.29/0.96      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 3.29/0.96      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.29/0.96  
% 3.29/0.96  cnf(c_12,plain,
% 3.29/0.96      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 3.29/0.96      | ~ v1_relat_1(X0)
% 3.29/0.96      | k7_relat_1(X0,X1) = X0 ),
% 3.29/0.96      inference(cnf_transformation,[],[f45]) ).
% 3.29/0.96  
% 3.29/0.96  cnf(c_727,plain,
% 3.29/0.96      ( k7_relat_1(X0,X1) = X0
% 3.29/0.96      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 3.29/0.96      | v1_relat_1(X0) != iProver_top ),
% 3.29/0.96      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.29/0.96  
% 3.29/0.96  cnf(c_1368,plain,
% 3.29/0.96      ( k7_relat_1(X0,k2_xboole_0(k1_relat_1(X0),X1)) = X0
% 3.29/0.96      | v1_relat_1(X0) != iProver_top ),
% 3.29/0.96      inference(superposition,[status(thm)],[c_729,c_727]) ).
% 3.29/0.96  
% 3.29/0.96  cnf(c_4046,plain,
% 3.29/0.96      ( k7_relat_1(sK1,k2_xboole_0(k1_relat_1(sK1),X0)) = sK1 ),
% 3.29/0.96      inference(superposition,[status(thm)],[c_723,c_1368]) ).
% 3.29/0.96  
% 3.29/0.96  cnf(c_11,plain,
% 3.29/0.96      ( ~ v1_relat_1(X0)
% 3.29/0.96      | k2_xboole_0(k7_relat_1(X0,X1),k7_relat_1(X0,X2)) = k7_relat_1(X0,k2_xboole_0(X1,X2)) ),
% 3.29/0.96      inference(cnf_transformation,[],[f44]) ).
% 3.29/0.96  
% 3.29/0.96  cnf(c_728,plain,
% 3.29/0.96      ( k2_xboole_0(k7_relat_1(X0,X1),k7_relat_1(X0,X2)) = k7_relat_1(X0,k2_xboole_0(X1,X2))
% 3.29/0.96      | v1_relat_1(X0) != iProver_top ),
% 3.29/0.96      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.29/0.96  
% 3.29/0.96  cnf(c_2321,plain,
% 3.29/0.96      ( k2_xboole_0(k7_relat_1(sK1,X0),k7_relat_1(sK1,X1)) = k7_relat_1(sK1,k2_xboole_0(X0,X1)) ),
% 3.29/0.96      inference(superposition,[status(thm)],[c_723,c_728]) ).
% 3.29/0.96  
% 3.29/0.96  cnf(c_4,plain,
% 3.29/0.96      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 3.29/0.96      inference(cnf_transformation,[],[f37]) ).
% 3.29/0.96  
% 3.29/0.96  cnf(c_731,plain,
% 3.29/0.96      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 3.29/0.96      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.29/0.96  
% 3.29/0.96  cnf(c_5,plain,
% 3.29/0.96      ( r1_tarski(X0,k2_xboole_0(X1,X2))
% 3.29/0.96      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ),
% 3.29/0.96      inference(cnf_transformation,[],[f38]) ).
% 3.29/0.96  
% 3.29/0.96  cnf(c_730,plain,
% 3.29/0.96      ( r1_tarski(X0,k2_xboole_0(X1,X2)) = iProver_top
% 3.29/0.96      | r1_tarski(k4_xboole_0(X0,X1),X2) != iProver_top ),
% 3.29/0.96      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.29/0.96  
% 3.29/0.96  cnf(c_1216,plain,
% 3.29/0.96      ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
% 3.29/0.96      inference(superposition,[status(thm)],[c_731,c_730]) ).
% 3.29/0.96  
% 3.29/0.96  cnf(c_2675,plain,
% 3.29/0.96      ( r1_tarski(k7_relat_1(sK1,X0),k7_relat_1(sK1,k2_xboole_0(X1,X0))) = iProver_top ),
% 3.29/0.96      inference(superposition,[status(thm)],[c_2321,c_1216]) ).
% 3.29/0.96  
% 3.29/0.96  cnf(c_4168,plain,
% 3.29/0.96      ( r1_tarski(k7_relat_1(sK1,X0),sK1) = iProver_top ),
% 3.29/0.96      inference(superposition,[status(thm)],[c_4046,c_2675]) ).
% 3.29/0.96  
% 3.29/0.96  cnf(c_15,negated_conjecture,
% 3.29/0.96      ( r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0)))
% 3.29/0.96      | r1_tarski(sK0,sK1) ),
% 3.29/0.96      inference(cnf_transformation,[],[f49]) ).
% 3.29/0.96  
% 3.29/0.96  cnf(c_724,plain,
% 3.29/0.96      ( r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0))) = iProver_top
% 3.29/0.96      | r1_tarski(sK0,sK1) = iProver_top ),
% 3.29/0.96      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.29/0.96  
% 3.29/0.96  cnf(c_732,plain,
% 3.29/0.96      ( r1_tarski(X0,X1) != iProver_top
% 3.29/0.96      | r1_tarski(X1,X2) != iProver_top
% 3.29/0.96      | r1_tarski(X0,X2) = iProver_top ),
% 3.29/0.96      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.29/0.96  
% 3.29/0.96  cnf(c_2428,plain,
% 3.29/0.96      ( r1_tarski(k7_relat_1(sK1,k1_relat_1(sK0)),X0) != iProver_top
% 3.29/0.96      | r1_tarski(sK0,X0) = iProver_top
% 3.29/0.96      | r1_tarski(sK0,sK1) = iProver_top ),
% 3.29/0.96      inference(superposition,[status(thm)],[c_724,c_732]) ).
% 3.29/0.96  
% 3.29/0.96  cnf(c_4338,plain,
% 3.29/0.96      ( r1_tarski(sK0,sK1) = iProver_top ),
% 3.29/0.96      inference(superposition,[status(thm)],[c_4168,c_2428]) ).
% 3.29/0.96  
% 3.29/0.96  cnf(c_4362,plain,
% 3.29/0.96      ( r1_tarski(sK0,sK1) ),
% 3.29/0.96      inference(predicate_to_equality_rev,[status(thm)],[c_4338]) ).
% 3.29/0.96  
% 3.29/0.96  cnf(c_17,negated_conjecture,
% 3.29/0.96      ( v1_relat_1(sK0) ),
% 3.29/0.96      inference(cnf_transformation,[],[f47]) ).
% 3.29/0.96  
% 3.29/0.96  cnf(c_722,plain,
% 3.29/0.96      ( v1_relat_1(sK0) = iProver_top ),
% 3.29/0.96      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.29/0.96  
% 3.29/0.96  cnf(c_13,plain,
% 3.29/0.96      ( ~ v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0 ),
% 3.29/0.96      inference(cnf_transformation,[],[f46]) ).
% 3.29/0.96  
% 3.29/0.96  cnf(c_726,plain,
% 3.29/0.96      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
% 3.29/0.96      | v1_relat_1(X0) != iProver_top ),
% 3.29/0.96      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.29/0.96  
% 3.29/0.96  cnf(c_1207,plain,
% 3.29/0.96      ( k7_relat_1(sK0,k1_relat_1(sK0)) = sK0 ),
% 3.29/0.96      inference(superposition,[status(thm)],[c_722,c_726]) ).
% 3.29/0.96  
% 3.29/0.96  cnf(c_721,plain,
% 3.29/0.96      ( r1_tarski(X0,X1) != iProver_top
% 3.29/0.96      | r1_tarski(k7_relat_1(X0,X2),k7_relat_1(X1,X2)) = iProver_top
% 3.29/0.96      | v1_relat_1(X1) != iProver_top ),
% 3.29/0.96      inference(predicate_to_equality,[status(thm)],[c_101]) ).
% 3.29/0.96  
% 3.29/0.96  cnf(c_2256,plain,
% 3.29/0.96      ( r1_tarski(sK0,X0) != iProver_top
% 3.29/0.96      | r1_tarski(sK0,k7_relat_1(X0,k1_relat_1(sK0))) = iProver_top
% 3.29/0.96      | v1_relat_1(X0) != iProver_top ),
% 3.29/0.96      inference(superposition,[status(thm)],[c_1207,c_721]) ).
% 3.29/0.96  
% 3.29/0.96  cnf(c_2302,plain,
% 3.29/0.96      ( ~ r1_tarski(sK0,X0)
% 3.29/0.96      | r1_tarski(sK0,k7_relat_1(X0,k1_relat_1(sK0)))
% 3.29/0.96      | ~ v1_relat_1(X0) ),
% 3.29/0.96      inference(predicate_to_equality_rev,[status(thm)],[c_2256]) ).
% 3.29/0.96  
% 3.29/0.96  cnf(c_2304,plain,
% 3.29/0.96      ( r1_tarski(sK0,k7_relat_1(sK0,k1_relat_1(sK0)))
% 3.29/0.96      | ~ r1_tarski(sK0,sK0)
% 3.29/0.96      | ~ v1_relat_1(sK0) ),
% 3.29/0.96      inference(instantiation,[status(thm)],[c_2302]) ).
% 3.29/0.96  
% 3.29/0.96  cnf(c_2,plain,
% 3.29/0.96      ( r1_tarski(X0,X0) ),
% 3.29/0.96      inference(cnf_transformation,[],[f52]) ).
% 3.29/0.96  
% 3.29/0.96  cnf(c_50,plain,
% 3.29/0.96      ( r1_tarski(sK0,sK0) ),
% 3.29/0.96      inference(instantiation,[status(thm)],[c_2]) ).
% 3.29/0.96  
% 3.29/0.96  cnf(c_14,negated_conjecture,
% 3.29/0.96      ( ~ r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0)))
% 3.29/0.96      | ~ r1_tarski(sK0,sK1) ),
% 3.29/0.96      inference(cnf_transformation,[],[f50]) ).
% 3.29/0.96  
% 3.29/0.96  cnf(contradiction,plain,
% 3.29/0.96      ( $false ),
% 3.29/0.96      inference(minisat,
% 3.29/0.96                [status(thm)],
% 3.29/0.96                [c_16420,c_16416,c_4362,c_2304,c_50,c_14,c_16,c_17]) ).
% 3.29/0.96  
% 3.29/0.96  
% 3.29/0.96  % SZS output end CNFRefutation for theBenchmark.p
% 3.29/0.96  
% 3.29/0.96  ------                               Statistics
% 3.29/0.96  
% 3.29/0.96  ------ General
% 3.29/0.96  
% 3.29/0.96  abstr_ref_over_cycles:                  0
% 3.29/0.96  abstr_ref_under_cycles:                 0
% 3.29/0.96  gc_basic_clause_elim:                   0
% 3.29/0.96  forced_gc_time:                         0
% 3.29/0.96  parsing_time:                           0.009
% 3.29/0.96  unif_index_cands_time:                  0.
% 3.29/0.96  unif_index_add_time:                    0.
% 3.29/0.96  orderings_time:                         0.
% 3.29/0.96  out_proof_time:                         0.009
% 3.29/0.96  total_time:                             0.449
% 3.29/0.96  num_of_symbols:                         41
% 3.29/0.96  num_of_terms:                           18905
% 3.29/0.96  
% 3.29/0.96  ------ Preprocessing
% 3.29/0.96  
% 3.29/0.96  num_of_splits:                          0
% 3.29/0.96  num_of_split_atoms:                     0
% 3.29/0.96  num_of_reused_defs:                     0
% 3.29/0.96  num_eq_ax_congr_red:                    8
% 3.29/0.96  num_of_sem_filtered_clauses:            1
% 3.29/0.96  num_of_subtypes:                        0
% 3.29/0.96  monotx_restored_types:                  0
% 3.29/0.96  sat_num_of_epr_types:                   0
% 3.29/0.96  sat_num_of_non_cyclic_types:            0
% 3.29/0.96  sat_guarded_non_collapsed_types:        0
% 3.29/0.96  num_pure_diseq_elim:                    0
% 3.29/0.96  simp_replaced_by:                       0
% 3.29/0.96  res_preprocessed:                       77
% 3.29/0.96  prep_upred:                             0
% 3.29/0.96  prep_unflattend:                        0
% 3.29/0.96  smt_new_axioms:                         0
% 3.29/0.96  pred_elim_cands:                        2
% 3.29/0.96  pred_elim:                              1
% 3.29/0.96  pred_elim_cl:                           2
% 3.29/0.96  pred_elim_cycles:                       3
% 3.29/0.96  merged_defs:                            10
% 3.29/0.96  merged_defs_ncl:                        0
% 3.29/0.96  bin_hyper_res:                          11
% 3.29/0.96  prep_cycles:                            4
% 3.29/0.96  pred_elim_time:                         0.
% 3.29/0.96  splitting_time:                         0.
% 3.29/0.96  sem_filter_time:                        0.
% 3.29/0.96  monotx_time:                            0.
% 3.29/0.96  subtype_inf_time:                       0.
% 3.29/0.96  
% 3.29/0.96  ------ Problem properties
% 3.29/0.96  
% 3.29/0.96  clauses:                                15
% 3.29/0.96  conjectures:                            4
% 3.29/0.96  epr:                                    6
% 3.29/0.96  horn:                                   14
% 3.29/0.96  ground:                                 4
% 3.29/0.96  unary:                                  5
% 3.29/0.96  binary:                                 5
% 3.29/0.96  lits:                                   30
% 3.29/0.96  lits_eq:                                4
% 3.29/0.96  fd_pure:                                0
% 3.29/0.96  fd_pseudo:                              0
% 3.29/0.96  fd_cond:                                0
% 3.29/0.96  fd_pseudo_cond:                         1
% 3.29/0.96  ac_symbols:                             0
% 3.29/0.96  
% 3.29/0.96  ------ Propositional Solver
% 3.29/0.96  
% 3.29/0.96  prop_solver_calls:                      30
% 3.29/0.96  prop_fast_solver_calls:                 492
% 3.29/0.96  smt_solver_calls:                       0
% 3.29/0.96  smt_fast_solver_calls:                  0
% 3.29/0.96  prop_num_of_clauses:                    6755
% 3.29/0.96  prop_preprocess_simplified:             14593
% 3.29/0.96  prop_fo_subsumed:                       1
% 3.29/0.96  prop_solver_time:                       0.
% 3.29/0.96  smt_solver_time:                        0.
% 3.29/0.96  smt_fast_solver_time:                   0.
% 3.29/0.96  prop_fast_solver_time:                  0.
% 3.29/0.96  prop_unsat_core_time:                   0.
% 3.29/0.96  
% 3.29/0.96  ------ QBF
% 3.29/0.96  
% 3.29/0.96  qbf_q_res:                              0
% 3.29/0.96  qbf_num_tautologies:                    0
% 3.29/0.96  qbf_prep_cycles:                        0
% 3.29/0.96  
% 3.29/0.96  ------ BMC1
% 3.29/0.96  
% 3.29/0.96  bmc1_current_bound:                     -1
% 3.29/0.96  bmc1_last_solved_bound:                 -1
% 3.29/0.96  bmc1_unsat_core_size:                   -1
% 3.29/0.96  bmc1_unsat_core_parents_size:           -1
% 3.29/0.96  bmc1_merge_next_fun:                    0
% 3.29/0.96  bmc1_unsat_core_clauses_time:           0.
% 3.29/0.96  
% 3.29/0.96  ------ Instantiation
% 3.29/0.96  
% 3.29/0.96  inst_num_of_clauses:                    1587
% 3.29/0.96  inst_num_in_passive:                    1104
% 3.29/0.96  inst_num_in_active:                     478
% 3.29/0.96  inst_num_in_unprocessed:                4
% 3.29/0.96  inst_num_of_loops:                      525
% 3.29/0.96  inst_num_of_learning_restarts:          0
% 3.29/0.96  inst_num_moves_active_passive:          42
% 3.29/0.96  inst_lit_activity:                      0
% 3.29/0.96  inst_lit_activity_moves:                0
% 3.29/0.96  inst_num_tautologies:                   0
% 3.29/0.96  inst_num_prop_implied:                  0
% 3.29/0.96  inst_num_existing_simplified:           0
% 3.29/0.96  inst_num_eq_res_simplified:             0
% 3.29/0.96  inst_num_child_elim:                    0
% 3.29/0.96  inst_num_of_dismatching_blockings:      789
% 3.29/0.96  inst_num_of_non_proper_insts:           1406
% 3.29/0.96  inst_num_of_duplicates:                 0
% 3.29/0.96  inst_inst_num_from_inst_to_res:         0
% 3.29/0.96  inst_dismatching_checking_time:         0.
% 3.29/0.96  
% 3.29/0.96  ------ Resolution
% 3.29/0.96  
% 3.29/0.96  res_num_of_clauses:                     0
% 3.29/0.96  res_num_in_passive:                     0
% 3.29/0.96  res_num_in_active:                      0
% 3.29/0.96  res_num_of_loops:                       81
% 3.29/0.96  res_forward_subset_subsumed:            195
% 3.29/0.96  res_backward_subset_subsumed:           4
% 3.29/0.96  res_forward_subsumed:                   0
% 3.29/0.96  res_backward_subsumed:                  0
% 3.29/0.96  res_forward_subsumption_resolution:     0
% 3.29/0.96  res_backward_subsumption_resolution:    0
% 3.29/0.96  res_clause_to_clause_subsumption:       1800
% 3.29/0.96  res_orphan_elimination:                 0
% 3.29/0.96  res_tautology_del:                      202
% 3.29/0.96  res_num_eq_res_simplified:              0
% 3.29/0.96  res_num_sel_changes:                    0
% 3.29/0.96  res_moves_from_active_to_pass:          0
% 3.29/0.96  
% 3.29/0.96  ------ Superposition
% 3.29/0.96  
% 3.29/0.96  sup_time_total:                         0.
% 3.29/0.96  sup_time_generating:                    0.
% 3.29/0.96  sup_time_sim_full:                      0.
% 3.29/0.96  sup_time_sim_immed:                     0.
% 3.29/0.96  
% 3.29/0.96  sup_num_of_clauses:                     429
% 3.29/0.96  sup_num_in_active:                      99
% 3.29/0.96  sup_num_in_passive:                     330
% 3.29/0.96  sup_num_of_loops:                       104
% 3.29/0.96  sup_fw_superposition:                   445
% 3.29/0.96  sup_bw_superposition:                   448
% 3.29/0.96  sup_immediate_simplified:               198
% 3.29/0.96  sup_given_eliminated:                   1
% 3.29/0.96  comparisons_done:                       0
% 3.29/0.96  comparisons_avoided:                    0
% 3.29/0.96  
% 3.29/0.96  ------ Simplifications
% 3.29/0.96  
% 3.29/0.96  
% 3.29/0.96  sim_fw_subset_subsumed:                 48
% 3.29/0.96  sim_bw_subset_subsumed:                 4
% 3.29/0.96  sim_fw_subsumed:                        51
% 3.29/0.96  sim_bw_subsumed:                        0
% 3.29/0.96  sim_fw_subsumption_res:                 0
% 3.29/0.96  sim_bw_subsumption_res:                 0
% 3.29/0.96  sim_tautology_del:                      27
% 3.29/0.96  sim_eq_tautology_del:                   1
% 3.29/0.96  sim_eq_res_simp:                        0
% 3.29/0.96  sim_fw_demodulated:                     19
% 3.29/0.96  sim_bw_demodulated:                     5
% 3.29/0.96  sim_light_normalised:                   97
% 3.29/0.96  sim_joinable_taut:                      0
% 3.29/0.96  sim_joinable_simp:                      0
% 3.29/0.96  sim_ac_normalised:                      0
% 3.29/0.96  sim_smt_subsumption:                    0
% 3.29/0.96  
%------------------------------------------------------------------------------
