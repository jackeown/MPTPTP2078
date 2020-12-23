%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:54:57 EST 2020

% Result     : Theorem 7.59s
% Output     : CNFRefutation 7.79s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 350 expanded)
%              Number of clauses        :   77 ( 140 expanded)
%              Number of leaves         :   18 (  69 expanded)
%              Depth                    :   22
%              Number of atoms          :  356 ( 804 expanded)
%              Number of equality atoms :  120 ( 147 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f63,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f47,f42])).

fof(f65,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f40,f63])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f32,plain,(
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

fof(f33,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f69,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v4_relat_1(X1,X0)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1))
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f37,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ~ r1_tarski(k3_relat_1(sK3),k2_xboole_0(sK1,sK2))
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ~ r1_tarski(k3_relat_1(sK3),k2_xboole_0(sK1,sK2))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f29,f37])).

fof(f61,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f38])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f14,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f57,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f67,plain,(
    ! [X0] :
      ( k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f57,f63])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f41,f63])).

fof(f62,plain,(
    ~ r1_tarski(k3_relat_1(sK3),k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f38])).

fof(f68,plain,(
    ~ r1_tarski(k3_relat_1(sK3),k3_tarski(k1_enumset1(sK1,sK1,sK2))) ),
    inference(definition_unfolding,[],[f62,f63])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f39,f63])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v5_relat_1(X1,X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_1,plain,
    ( r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_792,plain,
    ( r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_786,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_788,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_8,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_785,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_10,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_783,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2381,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r1_tarski(X2,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_785,c_783])).

cnf(c_4696,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(k1_zfmisc_1(X2),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_788,c_2381])).

cnf(c_4941,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_786,c_4696])).

cnf(c_5502,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k3_tarski(k1_enumset1(X1,X1,X2)))) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_792,c_4941])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_784,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_5581,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5502,c_784])).

cnf(c_12,plain,
    ( v4_relat_1(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_782,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_5850,plain,
    ( v4_relat_1(X0,k3_tarski(k1_enumset1(X1,X1,X2))) = iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5581,c_782])).

cnf(c_15,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_779,plain,
    ( v5_relat_1(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_13,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_781,plain,
    ( v4_relat_1(X0,X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_773,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1179,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_773,c_784])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_161,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_8])).

cnf(c_162,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_161])).

cnf(c_203,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_11,c_162])).

cnf(c_772,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_203])).

cnf(c_3078,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1179,c_772])).

cnf(c_1043,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) ),
    inference(resolution,[status(thm)],[c_9,c_21])).

cnf(c_1099,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
    | v1_relat_1(sK3) ),
    inference(resolution,[status(thm)],[c_203,c_1043])).

cnf(c_17,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1196,plain,
    ( v1_relat_1(sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1099,c_17])).

cnf(c_1197,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1196])).

cnf(c_8900,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3078,c_1197])).

cnf(c_16,plain,
    ( ~ v1_relat_1(X0)
    | k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_778,plain,
    ( k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_8905,plain,
    ( k3_tarski(k1_enumset1(k1_relat_1(sK3),k1_relat_1(sK3),k2_relat_1(sK3))) = k3_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_8900,c_778])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_791,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_9119,plain,
    ( r1_tarski(k3_relat_1(sK3),X0) = iProver_top
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8905,c_791])).

cnf(c_11166,plain,
    ( v4_relat_1(sK3,X0) != iProver_top
    | r1_tarski(k3_relat_1(sK3),X0) = iProver_top
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_781,c_9119])).

cnf(c_28201,plain,
    ( r1_tarski(k2_relat_1(sK3),X0) != iProver_top
    | r1_tarski(k3_relat_1(sK3),X0) = iProver_top
    | v4_relat_1(sK3,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11166,c_1197])).

cnf(c_28202,plain,
    ( v4_relat_1(sK3,X0) != iProver_top
    | r1_tarski(k3_relat_1(sK3),X0) = iProver_top
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_28201])).

cnf(c_28213,plain,
    ( v5_relat_1(sK3,X0) != iProver_top
    | v4_relat_1(sK3,X0) != iProver_top
    | r1_tarski(k3_relat_1(sK3),X0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_779,c_28202])).

cnf(c_28694,plain,
    ( r1_tarski(k3_relat_1(sK3),X0) = iProver_top
    | v4_relat_1(sK3,X0) != iProver_top
    | v5_relat_1(sK3,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_28213,c_1197])).

cnf(c_28695,plain,
    ( v5_relat_1(sK3,X0) != iProver_top
    | v4_relat_1(sK3,X0) != iProver_top
    | r1_tarski(k3_relat_1(sK3),X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_28694])).

cnf(c_20,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(sK3),k3_tarski(k1_enumset1(sK1,sK1,sK2))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_774,plain,
    ( r1_tarski(k3_relat_1(sK3),k3_tarski(k1_enumset1(sK1,sK1,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_28711,plain,
    ( v5_relat_1(sK3,k3_tarski(k1_enumset1(sK1,sK1,sK2))) != iProver_top
    | v4_relat_1(sK3,k3_tarski(k1_enumset1(sK1,sK1,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_28695,c_774])).

cnf(c_22,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_18,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1009,plain,
    ( v5_relat_1(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1010,plain,
    ( v5_relat_1(sK3,sK2) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1009])).

cnf(c_1123,plain,
    ( ~ v5_relat_1(sK3,sK2)
    | r1_tarski(k2_relat_1(sK3),sK2)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1124,plain,
    ( v5_relat_1(sK3,sK2) != iProver_top
    | r1_tarski(k2_relat_1(sK3),sK2) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1123])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1277,plain,
    ( r1_tarski(k2_relat_1(sK3),k3_tarski(k1_enumset1(X0,X0,sK2)))
    | ~ r1_tarski(k2_relat_1(sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1287,plain,
    ( r1_tarski(k2_relat_1(sK3),k3_tarski(k1_enumset1(X0,X0,sK2))) = iProver_top
    | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1277])).

cnf(c_1289,plain,
    ( r1_tarski(k2_relat_1(sK3),k3_tarski(k1_enumset1(sK1,sK1,sK2))) = iProver_top
    | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1287])).

cnf(c_14,plain,
    ( v5_relat_1(X0,X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1955,plain,
    ( v5_relat_1(sK3,X0)
    | ~ r1_tarski(k2_relat_1(sK3),X0)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_3297,plain,
    ( v5_relat_1(sK3,k3_tarski(k1_enumset1(X0,X0,sK2)))
    | ~ r1_tarski(k2_relat_1(sK3),k3_tarski(k1_enumset1(X0,X0,sK2)))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1955])).

cnf(c_3298,plain,
    ( v5_relat_1(sK3,k3_tarski(k1_enumset1(X0,X0,sK2))) = iProver_top
    | r1_tarski(k2_relat_1(sK3),k3_tarski(k1_enumset1(X0,X0,sK2))) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3297])).

cnf(c_3300,plain,
    ( v5_relat_1(sK3,k3_tarski(k1_enumset1(sK1,sK1,sK2))) = iProver_top
    | r1_tarski(k2_relat_1(sK3),k3_tarski(k1_enumset1(sK1,sK1,sK2))) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3298])).

cnf(c_29112,plain,
    ( v4_relat_1(sK3,k3_tarski(k1_enumset1(sK1,sK1,sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_28711,c_22,c_1010,c_1124,c_1197,c_1289,c_3300])).

cnf(c_29117,plain,
    ( r1_tarski(k1_relat_1(sK3),sK1) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5850,c_29112])).

cnf(c_1126,plain,
    ( ~ v4_relat_1(sK3,sK1)
    | r1_tarski(k1_relat_1(sK3),sK1)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1127,plain,
    ( v4_relat_1(sK3,sK1) != iProver_top
    | r1_tarski(k1_relat_1(sK3),sK1) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1126])).

cnf(c_19,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1012,plain,
    ( v4_relat_1(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_1013,plain,
    ( v4_relat_1(sK3,sK1) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1012])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_29117,c_1197,c_1127,c_1013,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:04:31 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.59/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.59/1.49  
% 7.59/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.59/1.49  
% 7.59/1.49  ------  iProver source info
% 7.59/1.49  
% 7.59/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.59/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.59/1.49  git: non_committed_changes: false
% 7.59/1.49  git: last_make_outside_of_git: false
% 7.59/1.49  
% 7.59/1.49  ------ 
% 7.59/1.49  
% 7.59/1.49  ------ Input Options
% 7.59/1.49  
% 7.59/1.49  --out_options                           all
% 7.59/1.49  --tptp_safe_out                         true
% 7.59/1.49  --problem_path                          ""
% 7.59/1.49  --include_path                          ""
% 7.59/1.49  --clausifier                            res/vclausify_rel
% 7.59/1.49  --clausifier_options                    --mode clausify
% 7.59/1.49  --stdin                                 false
% 7.59/1.49  --stats_out                             sel
% 7.59/1.49  
% 7.59/1.49  ------ General Options
% 7.59/1.49  
% 7.59/1.49  --fof                                   false
% 7.59/1.49  --time_out_real                         604.99
% 7.59/1.49  --time_out_virtual                      -1.
% 7.59/1.49  --symbol_type_check                     false
% 7.59/1.49  --clausify_out                          false
% 7.59/1.49  --sig_cnt_out                           false
% 7.59/1.49  --trig_cnt_out                          false
% 7.59/1.49  --trig_cnt_out_tolerance                1.
% 7.59/1.49  --trig_cnt_out_sk_spl                   false
% 7.59/1.49  --abstr_cl_out                          false
% 7.59/1.49  
% 7.59/1.49  ------ Global Options
% 7.59/1.49  
% 7.59/1.49  --schedule                              none
% 7.59/1.49  --add_important_lit                     false
% 7.59/1.49  --prop_solver_per_cl                    1000
% 7.59/1.49  --min_unsat_core                        false
% 7.59/1.49  --soft_assumptions                      false
% 7.59/1.49  --soft_lemma_size                       3
% 7.59/1.49  --prop_impl_unit_size                   0
% 7.59/1.49  --prop_impl_unit                        []
% 7.59/1.49  --share_sel_clauses                     true
% 7.59/1.49  --reset_solvers                         false
% 7.59/1.49  --bc_imp_inh                            [conj_cone]
% 7.59/1.49  --conj_cone_tolerance                   3.
% 7.59/1.49  --extra_neg_conj                        none
% 7.59/1.49  --large_theory_mode                     true
% 7.59/1.49  --prolific_symb_bound                   200
% 7.59/1.49  --lt_threshold                          2000
% 7.59/1.49  --clause_weak_htbl                      true
% 7.59/1.49  --gc_record_bc_elim                     false
% 7.59/1.49  
% 7.59/1.49  ------ Preprocessing Options
% 7.59/1.49  
% 7.59/1.49  --preprocessing_flag                    true
% 7.59/1.49  --time_out_prep_mult                    0.1
% 7.59/1.49  --splitting_mode                        input
% 7.59/1.49  --splitting_grd                         true
% 7.59/1.49  --splitting_cvd                         false
% 7.59/1.49  --splitting_cvd_svl                     false
% 7.59/1.49  --splitting_nvd                         32
% 7.59/1.49  --sub_typing                            true
% 7.59/1.49  --prep_gs_sim                           false
% 7.59/1.49  --prep_unflatten                        true
% 7.59/1.49  --prep_res_sim                          true
% 7.59/1.49  --prep_upred                            true
% 7.59/1.49  --prep_sem_filter                       exhaustive
% 7.59/1.49  --prep_sem_filter_out                   false
% 7.59/1.49  --pred_elim                             false
% 7.59/1.49  --res_sim_input                         true
% 7.59/1.49  --eq_ax_congr_red                       true
% 7.59/1.49  --pure_diseq_elim                       true
% 7.59/1.49  --brand_transform                       false
% 7.59/1.49  --non_eq_to_eq                          false
% 7.59/1.49  --prep_def_merge                        true
% 7.59/1.49  --prep_def_merge_prop_impl              false
% 7.59/1.49  --prep_def_merge_mbd                    true
% 7.59/1.49  --prep_def_merge_tr_red                 false
% 7.59/1.49  --prep_def_merge_tr_cl                  false
% 7.59/1.49  --smt_preprocessing                     true
% 7.59/1.49  --smt_ac_axioms                         fast
% 7.59/1.49  --preprocessed_out                      false
% 7.59/1.49  --preprocessed_stats                    false
% 7.59/1.49  
% 7.59/1.49  ------ Abstraction refinement Options
% 7.59/1.49  
% 7.59/1.49  --abstr_ref                             []
% 7.59/1.49  --abstr_ref_prep                        false
% 7.59/1.49  --abstr_ref_until_sat                   false
% 7.59/1.49  --abstr_ref_sig_restrict                funpre
% 7.59/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.59/1.49  --abstr_ref_under                       []
% 7.59/1.49  
% 7.59/1.49  ------ SAT Options
% 7.59/1.49  
% 7.59/1.49  --sat_mode                              false
% 7.59/1.49  --sat_fm_restart_options                ""
% 7.59/1.49  --sat_gr_def                            false
% 7.59/1.49  --sat_epr_types                         true
% 7.59/1.49  --sat_non_cyclic_types                  false
% 7.59/1.49  --sat_finite_models                     false
% 7.59/1.49  --sat_fm_lemmas                         false
% 7.59/1.49  --sat_fm_prep                           false
% 7.59/1.49  --sat_fm_uc_incr                        true
% 7.59/1.49  --sat_out_model                         small
% 7.59/1.49  --sat_out_clauses                       false
% 7.59/1.49  
% 7.59/1.49  ------ QBF Options
% 7.59/1.49  
% 7.59/1.49  --qbf_mode                              false
% 7.59/1.49  --qbf_elim_univ                         false
% 7.59/1.49  --qbf_dom_inst                          none
% 7.59/1.49  --qbf_dom_pre_inst                      false
% 7.59/1.49  --qbf_sk_in                             false
% 7.59/1.49  --qbf_pred_elim                         true
% 7.59/1.49  --qbf_split                             512
% 7.59/1.49  
% 7.59/1.49  ------ BMC1 Options
% 7.59/1.49  
% 7.59/1.49  --bmc1_incremental                      false
% 7.59/1.49  --bmc1_axioms                           reachable_all
% 7.59/1.49  --bmc1_min_bound                        0
% 7.59/1.49  --bmc1_max_bound                        -1
% 7.59/1.49  --bmc1_max_bound_default                -1
% 7.59/1.49  --bmc1_symbol_reachability              true
% 7.59/1.49  --bmc1_property_lemmas                  false
% 7.59/1.49  --bmc1_k_induction                      false
% 7.59/1.49  --bmc1_non_equiv_states                 false
% 7.59/1.49  --bmc1_deadlock                         false
% 7.59/1.49  --bmc1_ucm                              false
% 7.59/1.49  --bmc1_add_unsat_core                   none
% 7.59/1.49  --bmc1_unsat_core_children              false
% 7.59/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.59/1.49  --bmc1_out_stat                         full
% 7.59/1.49  --bmc1_ground_init                      false
% 7.59/1.49  --bmc1_pre_inst_next_state              false
% 7.59/1.49  --bmc1_pre_inst_state                   false
% 7.59/1.49  --bmc1_pre_inst_reach_state             false
% 7.59/1.49  --bmc1_out_unsat_core                   false
% 7.59/1.49  --bmc1_aig_witness_out                  false
% 7.59/1.49  --bmc1_verbose                          false
% 7.59/1.49  --bmc1_dump_clauses_tptp                false
% 7.59/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.59/1.49  --bmc1_dump_file                        -
% 7.59/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.59/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.59/1.49  --bmc1_ucm_extend_mode                  1
% 7.59/1.49  --bmc1_ucm_init_mode                    2
% 7.59/1.49  --bmc1_ucm_cone_mode                    none
% 7.59/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.59/1.49  --bmc1_ucm_relax_model                  4
% 7.59/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.59/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.59/1.49  --bmc1_ucm_layered_model                none
% 7.59/1.49  --bmc1_ucm_max_lemma_size               10
% 7.59/1.49  
% 7.59/1.49  ------ AIG Options
% 7.59/1.49  
% 7.59/1.49  --aig_mode                              false
% 7.59/1.49  
% 7.59/1.49  ------ Instantiation Options
% 7.59/1.49  
% 7.59/1.49  --instantiation_flag                    true
% 7.59/1.49  --inst_sos_flag                         false
% 7.59/1.49  --inst_sos_phase                        true
% 7.59/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.59/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.59/1.49  --inst_lit_sel_side                     num_symb
% 7.59/1.49  --inst_solver_per_active                1400
% 7.59/1.49  --inst_solver_calls_frac                1.
% 7.59/1.49  --inst_passive_queue_type               priority_queues
% 7.59/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.59/1.49  --inst_passive_queues_freq              [25;2]
% 7.59/1.49  --inst_dismatching                      true
% 7.59/1.49  --inst_eager_unprocessed_to_passive     true
% 7.59/1.49  --inst_prop_sim_given                   true
% 7.59/1.49  --inst_prop_sim_new                     false
% 7.59/1.49  --inst_subs_new                         false
% 7.59/1.49  --inst_eq_res_simp                      false
% 7.59/1.49  --inst_subs_given                       false
% 7.59/1.49  --inst_orphan_elimination               true
% 7.59/1.49  --inst_learning_loop_flag               true
% 7.59/1.49  --inst_learning_start                   3000
% 7.59/1.49  --inst_learning_factor                  2
% 7.59/1.49  --inst_start_prop_sim_after_learn       3
% 7.59/1.49  --inst_sel_renew                        solver
% 7.59/1.49  --inst_lit_activity_flag                true
% 7.59/1.49  --inst_restr_to_given                   false
% 7.59/1.49  --inst_activity_threshold               500
% 7.59/1.49  --inst_out_proof                        true
% 7.59/1.49  
% 7.59/1.49  ------ Resolution Options
% 7.59/1.49  
% 7.59/1.49  --resolution_flag                       true
% 7.59/1.49  --res_lit_sel                           adaptive
% 7.59/1.49  --res_lit_sel_side                      none
% 7.59/1.49  --res_ordering                          kbo
% 7.59/1.49  --res_to_prop_solver                    active
% 7.59/1.49  --res_prop_simpl_new                    false
% 7.59/1.49  --res_prop_simpl_given                  true
% 7.59/1.49  --res_passive_queue_type                priority_queues
% 7.59/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.59/1.49  --res_passive_queues_freq               [15;5]
% 7.59/1.49  --res_forward_subs                      full
% 7.59/1.49  --res_backward_subs                     full
% 7.59/1.49  --res_forward_subs_resolution           true
% 7.59/1.49  --res_backward_subs_resolution          true
% 7.59/1.49  --res_orphan_elimination                true
% 7.59/1.49  --res_time_limit                        2.
% 7.59/1.49  --res_out_proof                         true
% 7.59/1.49  
% 7.59/1.49  ------ Superposition Options
% 7.59/1.49  
% 7.59/1.49  --superposition_flag                    true
% 7.59/1.49  --sup_passive_queue_type                priority_queues
% 7.59/1.49  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.59/1.49  --sup_passive_queues_freq               [1;4]
% 7.59/1.49  --demod_completeness_check              fast
% 7.59/1.49  --demod_use_ground                      true
% 7.59/1.49  --sup_to_prop_solver                    passive
% 7.59/1.49  --sup_prop_simpl_new                    true
% 7.59/1.49  --sup_prop_simpl_given                  true
% 7.59/1.49  --sup_fun_splitting                     false
% 7.59/1.49  --sup_smt_interval                      50000
% 7.59/1.49  
% 7.59/1.49  ------ Superposition Simplification Setup
% 7.59/1.49  
% 7.59/1.49  --sup_indices_passive                   []
% 7.59/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.59/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.59/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.59/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.59/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.59/1.49  --sup_full_bw                           [BwDemod]
% 7.59/1.49  --sup_immed_triv                        [TrivRules]
% 7.59/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.59/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.59/1.49  --sup_immed_bw_main                     []
% 7.59/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.59/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.59/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.59/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.59/1.49  
% 7.59/1.49  ------ Combination Options
% 7.59/1.49  
% 7.59/1.49  --comb_res_mult                         3
% 7.59/1.49  --comb_sup_mult                         2
% 7.59/1.49  --comb_inst_mult                        10
% 7.59/1.49  
% 7.59/1.49  ------ Debug Options
% 7.59/1.49  
% 7.59/1.49  --dbg_backtrace                         false
% 7.59/1.49  --dbg_dump_prop_clauses                 false
% 7.59/1.49  --dbg_dump_prop_clauses_file            -
% 7.59/1.49  --dbg_out_stat                          false
% 7.59/1.49  ------ Parsing...
% 7.59/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.59/1.49  
% 7.59/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 7.59/1.49  
% 7.59/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.59/1.49  
% 7.59/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.59/1.49  ------ Proving...
% 7.59/1.49  ------ Problem Properties 
% 7.59/1.49  
% 7.59/1.49  
% 7.59/1.49  clauses                                 22
% 7.59/1.49  conjectures                             2
% 7.59/1.49  EPR                                     1
% 7.59/1.49  Horn                                    21
% 7.59/1.49  unary                                   4
% 7.59/1.49  binary                                  9
% 7.59/1.49  lits                                    49
% 7.59/1.49  lits eq                                 3
% 7.59/1.49  fd_pure                                 0
% 7.59/1.49  fd_pseudo                               0
% 7.59/1.49  fd_cond                                 0
% 7.59/1.49  fd_pseudo_cond                          2
% 7.59/1.49  AC symbols                              0
% 7.59/1.49  
% 7.59/1.49  ------ Input Options Time Limit: Unbounded
% 7.59/1.49  
% 7.59/1.49  
% 7.59/1.49  ------ 
% 7.59/1.49  Current options:
% 7.59/1.49  ------ 
% 7.59/1.49  
% 7.59/1.49  ------ Input Options
% 7.59/1.49  
% 7.59/1.49  --out_options                           all
% 7.59/1.49  --tptp_safe_out                         true
% 7.59/1.49  --problem_path                          ""
% 7.59/1.49  --include_path                          ""
% 7.59/1.49  --clausifier                            res/vclausify_rel
% 7.59/1.49  --clausifier_options                    --mode clausify
% 7.59/1.49  --stdin                                 false
% 7.59/1.49  --stats_out                             sel
% 7.59/1.49  
% 7.59/1.49  ------ General Options
% 7.59/1.49  
% 7.59/1.49  --fof                                   false
% 7.59/1.49  --time_out_real                         604.99
% 7.59/1.49  --time_out_virtual                      -1.
% 7.59/1.49  --symbol_type_check                     false
% 7.59/1.49  --clausify_out                          false
% 7.59/1.49  --sig_cnt_out                           false
% 7.59/1.49  --trig_cnt_out                          false
% 7.59/1.49  --trig_cnt_out_tolerance                1.
% 7.59/1.49  --trig_cnt_out_sk_spl                   false
% 7.59/1.49  --abstr_cl_out                          false
% 7.59/1.49  
% 7.59/1.49  ------ Global Options
% 7.59/1.49  
% 7.59/1.49  --schedule                              none
% 7.59/1.49  --add_important_lit                     false
% 7.59/1.49  --prop_solver_per_cl                    1000
% 7.59/1.49  --min_unsat_core                        false
% 7.59/1.49  --soft_assumptions                      false
% 7.59/1.49  --soft_lemma_size                       3
% 7.59/1.49  --prop_impl_unit_size                   0
% 7.59/1.49  --prop_impl_unit                        []
% 7.59/1.49  --share_sel_clauses                     true
% 7.59/1.49  --reset_solvers                         false
% 7.59/1.49  --bc_imp_inh                            [conj_cone]
% 7.59/1.49  --conj_cone_tolerance                   3.
% 7.59/1.49  --extra_neg_conj                        none
% 7.59/1.49  --large_theory_mode                     true
% 7.59/1.49  --prolific_symb_bound                   200
% 7.59/1.49  --lt_threshold                          2000
% 7.59/1.49  --clause_weak_htbl                      true
% 7.59/1.49  --gc_record_bc_elim                     false
% 7.59/1.49  
% 7.59/1.49  ------ Preprocessing Options
% 7.59/1.49  
% 7.59/1.49  --preprocessing_flag                    true
% 7.59/1.49  --time_out_prep_mult                    0.1
% 7.59/1.49  --splitting_mode                        input
% 7.59/1.49  --splitting_grd                         true
% 7.59/1.49  --splitting_cvd                         false
% 7.59/1.49  --splitting_cvd_svl                     false
% 7.59/1.49  --splitting_nvd                         32
% 7.59/1.49  --sub_typing                            true
% 7.59/1.49  --prep_gs_sim                           false
% 7.59/1.49  --prep_unflatten                        true
% 7.59/1.49  --prep_res_sim                          true
% 7.59/1.49  --prep_upred                            true
% 7.59/1.49  --prep_sem_filter                       exhaustive
% 7.59/1.49  --prep_sem_filter_out                   false
% 7.59/1.49  --pred_elim                             false
% 7.59/1.49  --res_sim_input                         true
% 7.59/1.49  --eq_ax_congr_red                       true
% 7.59/1.49  --pure_diseq_elim                       true
% 7.59/1.49  --brand_transform                       false
% 7.59/1.49  --non_eq_to_eq                          false
% 7.59/1.49  --prep_def_merge                        true
% 7.59/1.49  --prep_def_merge_prop_impl              false
% 7.59/1.49  --prep_def_merge_mbd                    true
% 7.59/1.49  --prep_def_merge_tr_red                 false
% 7.59/1.49  --prep_def_merge_tr_cl                  false
% 7.59/1.49  --smt_preprocessing                     true
% 7.59/1.49  --smt_ac_axioms                         fast
% 7.59/1.49  --preprocessed_out                      false
% 7.59/1.49  --preprocessed_stats                    false
% 7.59/1.49  
% 7.59/1.49  ------ Abstraction refinement Options
% 7.59/1.49  
% 7.59/1.49  --abstr_ref                             []
% 7.59/1.49  --abstr_ref_prep                        false
% 7.59/1.49  --abstr_ref_until_sat                   false
% 7.59/1.49  --abstr_ref_sig_restrict                funpre
% 7.59/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.59/1.49  --abstr_ref_under                       []
% 7.59/1.49  
% 7.59/1.49  ------ SAT Options
% 7.59/1.49  
% 7.59/1.49  --sat_mode                              false
% 7.59/1.49  --sat_fm_restart_options                ""
% 7.59/1.49  --sat_gr_def                            false
% 7.59/1.49  --sat_epr_types                         true
% 7.59/1.49  --sat_non_cyclic_types                  false
% 7.59/1.49  --sat_finite_models                     false
% 7.59/1.49  --sat_fm_lemmas                         false
% 7.59/1.49  --sat_fm_prep                           false
% 7.59/1.49  --sat_fm_uc_incr                        true
% 7.59/1.49  --sat_out_model                         small
% 7.59/1.49  --sat_out_clauses                       false
% 7.59/1.49  
% 7.59/1.49  ------ QBF Options
% 7.59/1.49  
% 7.59/1.49  --qbf_mode                              false
% 7.59/1.49  --qbf_elim_univ                         false
% 7.59/1.49  --qbf_dom_inst                          none
% 7.59/1.49  --qbf_dom_pre_inst                      false
% 7.59/1.49  --qbf_sk_in                             false
% 7.59/1.49  --qbf_pred_elim                         true
% 7.59/1.49  --qbf_split                             512
% 7.59/1.49  
% 7.59/1.49  ------ BMC1 Options
% 7.59/1.49  
% 7.59/1.49  --bmc1_incremental                      false
% 7.59/1.49  --bmc1_axioms                           reachable_all
% 7.59/1.49  --bmc1_min_bound                        0
% 7.59/1.49  --bmc1_max_bound                        -1
% 7.59/1.49  --bmc1_max_bound_default                -1
% 7.59/1.49  --bmc1_symbol_reachability              true
% 7.59/1.49  --bmc1_property_lemmas                  false
% 7.59/1.49  --bmc1_k_induction                      false
% 7.59/1.49  --bmc1_non_equiv_states                 false
% 7.59/1.49  --bmc1_deadlock                         false
% 7.59/1.49  --bmc1_ucm                              false
% 7.59/1.49  --bmc1_add_unsat_core                   none
% 7.59/1.49  --bmc1_unsat_core_children              false
% 7.59/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.59/1.49  --bmc1_out_stat                         full
% 7.59/1.49  --bmc1_ground_init                      false
% 7.59/1.49  --bmc1_pre_inst_next_state              false
% 7.59/1.49  --bmc1_pre_inst_state                   false
% 7.59/1.49  --bmc1_pre_inst_reach_state             false
% 7.59/1.49  --bmc1_out_unsat_core                   false
% 7.59/1.49  --bmc1_aig_witness_out                  false
% 7.59/1.49  --bmc1_verbose                          false
% 7.59/1.49  --bmc1_dump_clauses_tptp                false
% 7.59/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.59/1.49  --bmc1_dump_file                        -
% 7.59/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.59/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.59/1.49  --bmc1_ucm_extend_mode                  1
% 7.59/1.49  --bmc1_ucm_init_mode                    2
% 7.59/1.49  --bmc1_ucm_cone_mode                    none
% 7.59/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.59/1.49  --bmc1_ucm_relax_model                  4
% 7.59/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.59/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.59/1.49  --bmc1_ucm_layered_model                none
% 7.59/1.49  --bmc1_ucm_max_lemma_size               10
% 7.59/1.49  
% 7.59/1.49  ------ AIG Options
% 7.59/1.49  
% 7.59/1.49  --aig_mode                              false
% 7.59/1.49  
% 7.59/1.49  ------ Instantiation Options
% 7.59/1.49  
% 7.59/1.49  --instantiation_flag                    true
% 7.59/1.49  --inst_sos_flag                         false
% 7.59/1.49  --inst_sos_phase                        true
% 7.59/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.59/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.59/1.49  --inst_lit_sel_side                     num_symb
% 7.59/1.49  --inst_solver_per_active                1400
% 7.59/1.49  --inst_solver_calls_frac                1.
% 7.59/1.49  --inst_passive_queue_type               priority_queues
% 7.59/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.59/1.49  --inst_passive_queues_freq              [25;2]
% 7.59/1.49  --inst_dismatching                      true
% 7.59/1.49  --inst_eager_unprocessed_to_passive     true
% 7.59/1.49  --inst_prop_sim_given                   true
% 7.59/1.49  --inst_prop_sim_new                     false
% 7.59/1.49  --inst_subs_new                         false
% 7.59/1.49  --inst_eq_res_simp                      false
% 7.59/1.49  --inst_subs_given                       false
% 7.59/1.49  --inst_orphan_elimination               true
% 7.59/1.49  --inst_learning_loop_flag               true
% 7.59/1.49  --inst_learning_start                   3000
% 7.59/1.49  --inst_learning_factor                  2
% 7.59/1.49  --inst_start_prop_sim_after_learn       3
% 7.59/1.49  --inst_sel_renew                        solver
% 7.59/1.49  --inst_lit_activity_flag                true
% 7.59/1.49  --inst_restr_to_given                   false
% 7.59/1.49  --inst_activity_threshold               500
% 7.59/1.49  --inst_out_proof                        true
% 7.59/1.49  
% 7.59/1.49  ------ Resolution Options
% 7.59/1.49  
% 7.59/1.49  --resolution_flag                       true
% 7.59/1.49  --res_lit_sel                           adaptive
% 7.59/1.49  --res_lit_sel_side                      none
% 7.59/1.49  --res_ordering                          kbo
% 7.59/1.49  --res_to_prop_solver                    active
% 7.59/1.49  --res_prop_simpl_new                    false
% 7.59/1.49  --res_prop_simpl_given                  true
% 7.59/1.49  --res_passive_queue_type                priority_queues
% 7.59/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.59/1.49  --res_passive_queues_freq               [15;5]
% 7.59/1.49  --res_forward_subs                      full
% 7.59/1.49  --res_backward_subs                     full
% 7.59/1.49  --res_forward_subs_resolution           true
% 7.59/1.49  --res_backward_subs_resolution          true
% 7.59/1.49  --res_orphan_elimination                true
% 7.59/1.49  --res_time_limit                        2.
% 7.59/1.49  --res_out_proof                         true
% 7.59/1.49  
% 7.59/1.49  ------ Superposition Options
% 7.59/1.49  
% 7.59/1.49  --superposition_flag                    true
% 7.59/1.49  --sup_passive_queue_type                priority_queues
% 7.59/1.49  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.59/1.49  --sup_passive_queues_freq               [1;4]
% 7.59/1.49  --demod_completeness_check              fast
% 7.59/1.49  --demod_use_ground                      true
% 7.59/1.49  --sup_to_prop_solver                    passive
% 7.59/1.49  --sup_prop_simpl_new                    true
% 7.59/1.49  --sup_prop_simpl_given                  true
% 7.59/1.49  --sup_fun_splitting                     false
% 7.59/1.49  --sup_smt_interval                      50000
% 7.59/1.49  
% 7.59/1.49  ------ Superposition Simplification Setup
% 7.59/1.49  
% 7.59/1.49  --sup_indices_passive                   []
% 7.59/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.59/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.59/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.59/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.59/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.59/1.49  --sup_full_bw                           [BwDemod]
% 7.59/1.49  --sup_immed_triv                        [TrivRules]
% 7.59/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.59/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.59/1.49  --sup_immed_bw_main                     []
% 7.59/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.59/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.59/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.59/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.59/1.49  
% 7.59/1.49  ------ Combination Options
% 7.59/1.49  
% 7.59/1.49  --comb_res_mult                         3
% 7.59/1.49  --comb_sup_mult                         2
% 7.59/1.49  --comb_inst_mult                        10
% 7.59/1.49  
% 7.59/1.49  ------ Debug Options
% 7.59/1.49  
% 7.59/1.49  --dbg_backtrace                         false
% 7.59/1.49  --dbg_dump_prop_clauses                 false
% 7.59/1.49  --dbg_dump_prop_clauses_file            -
% 7.59/1.49  --dbg_out_stat                          false
% 7.59/1.49  
% 7.59/1.49  
% 7.59/1.49  
% 7.59/1.49  
% 7.59/1.49  ------ Proving...
% 7.59/1.49  
% 7.59/1.49  
% 7.59/1.49  % SZS status Theorem for theBenchmark.p
% 7.59/1.49  
% 7.59/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.59/1.49  
% 7.59/1.49  fof(f2,axiom,(
% 7.59/1.49    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 7.59/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.49  
% 7.59/1.49  fof(f40,plain,(
% 7.59/1.49    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 7.59/1.49    inference(cnf_transformation,[],[f2])).
% 7.59/1.49  
% 7.59/1.49  fof(f6,axiom,(
% 7.79/1.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 7.79/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.79/1.49  
% 7.79/1.49  fof(f47,plain,(
% 7.79/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 7.79/1.49    inference(cnf_transformation,[],[f6])).
% 7.79/1.49  
% 7.79/1.49  fof(f4,axiom,(
% 7.79/1.49    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 7.79/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.79/1.49  
% 7.79/1.49  fof(f42,plain,(
% 7.79/1.49    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 7.79/1.49    inference(cnf_transformation,[],[f4])).
% 7.79/1.49  
% 7.79/1.49  fof(f63,plain,(
% 7.79/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 7.79/1.49    inference(definition_unfolding,[],[f47,f42])).
% 7.79/1.49  
% 7.79/1.49  fof(f65,plain,(
% 7.79/1.49    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1)))) )),
% 7.79/1.49    inference(definition_unfolding,[],[f40,f63])).
% 7.79/1.49  
% 7.79/1.49  fof(f7,axiom,(
% 7.79/1.49    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)))),
% 7.79/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.79/1.49  
% 7.79/1.49  fof(f21,plain,(
% 7.79/1.49    ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 7.79/1.49    inference(ennf_transformation,[],[f7])).
% 7.79/1.49  
% 7.79/1.49  fof(f48,plain,(
% 7.79/1.49    ( ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.79/1.49    inference(cnf_transformation,[],[f21])).
% 7.79/1.49  
% 7.79/1.49  fof(f5,axiom,(
% 7.79/1.49    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 7.79/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.79/1.49  
% 7.79/1.49  fof(f30,plain,(
% 7.79/1.49    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 7.79/1.49    inference(nnf_transformation,[],[f5])).
% 7.79/1.49  
% 7.79/1.49  fof(f31,plain,(
% 7.79/1.49    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 7.79/1.49    inference(rectify,[],[f30])).
% 7.79/1.49  
% 7.79/1.49  fof(f32,plain,(
% 7.79/1.49    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 7.79/1.49    introduced(choice_axiom,[])).
% 7.79/1.49  
% 7.79/1.49  fof(f33,plain,(
% 7.79/1.49    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 7.79/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).
% 7.79/1.49  
% 7.79/1.49  fof(f44,plain,(
% 7.79/1.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 7.79/1.49    inference(cnf_transformation,[],[f33])).
% 7.79/1.49  
% 7.79/1.49  fof(f69,plain,(
% 7.79/1.49    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 7.79/1.49    inference(equality_resolution,[],[f44])).
% 7.79/1.49  
% 7.79/1.49  fof(f8,axiom,(
% 7.79/1.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.79/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.79/1.49  
% 7.79/1.49  fof(f34,plain,(
% 7.79/1.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.79/1.49    inference(nnf_transformation,[],[f8])).
% 7.79/1.49  
% 7.79/1.49  fof(f50,plain,(
% 7.79/1.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.79/1.49    inference(cnf_transformation,[],[f34])).
% 7.79/1.49  
% 7.79/1.49  fof(f9,axiom,(
% 7.79/1.49    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 7.79/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.79/1.49  
% 7.79/1.49  fof(f22,plain,(
% 7.79/1.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 7.79/1.49    inference(ennf_transformation,[],[f9])).
% 7.79/1.49  
% 7.79/1.49  fof(f23,plain,(
% 7.79/1.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 7.79/1.49    inference(flattening,[],[f22])).
% 7.79/1.49  
% 7.79/1.49  fof(f51,plain,(
% 7.79/1.49    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 7.79/1.49    inference(cnf_transformation,[],[f23])).
% 7.79/1.49  
% 7.79/1.49  fof(f49,plain,(
% 7.79/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.79/1.49    inference(cnf_transformation,[],[f34])).
% 7.79/1.49  
% 7.79/1.49  fof(f11,axiom,(
% 7.79/1.49    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 7.79/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.79/1.49  
% 7.79/1.49  fof(f25,plain,(
% 7.79/1.49    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.79/1.49    inference(ennf_transformation,[],[f11])).
% 7.79/1.49  
% 7.79/1.49  fof(f35,plain,(
% 7.79/1.49    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.79/1.49    inference(nnf_transformation,[],[f25])).
% 7.79/1.49  
% 7.79/1.49  fof(f54,plain,(
% 7.79/1.49    ( ! [X0,X1] : (v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 7.79/1.49    inference(cnf_transformation,[],[f35])).
% 7.79/1.49  
% 7.79/1.49  fof(f12,axiom,(
% 7.79/1.49    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 7.79/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.79/1.49  
% 7.79/1.49  fof(f26,plain,(
% 7.79/1.49    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.79/1.49    inference(ennf_transformation,[],[f12])).
% 7.79/1.49  
% 7.79/1.49  fof(f36,plain,(
% 7.79/1.49    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.79/1.49    inference(nnf_transformation,[],[f26])).
% 7.79/1.49  
% 7.79/1.49  fof(f55,plain,(
% 7.79/1.49    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.79/1.49    inference(cnf_transformation,[],[f36])).
% 7.79/1.49  
% 7.79/1.49  fof(f53,plain,(
% 7.79/1.49    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.79/1.49    inference(cnf_transformation,[],[f35])).
% 7.79/1.49  
% 7.79/1.49  fof(f16,conjecture,(
% 7.79/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)))),
% 7.79/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.79/1.49  
% 7.79/1.49  fof(f17,negated_conjecture,(
% 7.79/1.49    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)))),
% 7.79/1.49    inference(negated_conjecture,[],[f16])).
% 7.79/1.49  
% 7.79/1.49  fof(f29,plain,(
% 7.79/1.49    ? [X0,X1,X2] : (~r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.79/1.49    inference(ennf_transformation,[],[f17])).
% 7.79/1.49  
% 7.79/1.49  fof(f37,plain,(
% 7.79/1.49    ? [X0,X1,X2] : (~r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (~r1_tarski(k3_relat_1(sK3),k2_xboole_0(sK1,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))))),
% 7.79/1.49    introduced(choice_axiom,[])).
% 7.79/1.49  
% 7.79/1.49  fof(f38,plain,(
% 7.79/1.49    ~r1_tarski(k3_relat_1(sK3),k2_xboole_0(sK1,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 7.79/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f29,f37])).
% 7.79/1.49  
% 7.79/1.49  fof(f61,plain,(
% 7.79/1.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 7.79/1.49    inference(cnf_transformation,[],[f38])).
% 7.79/1.49  
% 7.79/1.49  fof(f10,axiom,(
% 7.79/1.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 7.79/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.79/1.49  
% 7.79/1.49  fof(f24,plain,(
% 7.79/1.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 7.79/1.49    inference(ennf_transformation,[],[f10])).
% 7.79/1.49  
% 7.79/1.49  fof(f52,plain,(
% 7.79/1.49    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 7.79/1.49    inference(cnf_transformation,[],[f24])).
% 7.79/1.49  
% 7.79/1.49  fof(f14,axiom,(
% 7.79/1.49    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 7.79/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.79/1.49  
% 7.79/1.49  fof(f58,plain,(
% 7.79/1.49    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 7.79/1.49    inference(cnf_transformation,[],[f14])).
% 7.79/1.49  
% 7.79/1.49  fof(f13,axiom,(
% 7.79/1.49    ! [X0] : (v1_relat_1(X0) => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0))),
% 7.79/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.79/1.49  
% 7.79/1.49  fof(f27,plain,(
% 7.79/1.49    ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0))),
% 7.79/1.49    inference(ennf_transformation,[],[f13])).
% 7.79/1.49  
% 7.79/1.49  fof(f57,plain,(
% 7.79/1.49    ( ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 7.79/1.49    inference(cnf_transformation,[],[f27])).
% 7.79/1.49  
% 7.79/1.49  fof(f67,plain,(
% 7.79/1.49    ( ! [X0] : (k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 7.79/1.49    inference(definition_unfolding,[],[f57,f63])).
% 7.79/1.49  
% 7.79/1.49  fof(f3,axiom,(
% 7.79/1.49    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 7.79/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.79/1.49  
% 7.79/1.49  fof(f19,plain,(
% 7.79/1.49    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 7.79/1.49    inference(ennf_transformation,[],[f3])).
% 7.79/1.49  
% 7.79/1.49  fof(f20,plain,(
% 7.79/1.49    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 7.79/1.49    inference(flattening,[],[f19])).
% 7.79/1.49  
% 7.79/1.49  fof(f41,plain,(
% 7.79/1.49    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 7.79/1.49    inference(cnf_transformation,[],[f20])).
% 7.79/1.49  
% 7.79/1.49  fof(f66,plain,(
% 7.79/1.49    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 7.79/1.49    inference(definition_unfolding,[],[f41,f63])).
% 7.79/1.49  
% 7.79/1.49  fof(f62,plain,(
% 7.79/1.49    ~r1_tarski(k3_relat_1(sK3),k2_xboole_0(sK1,sK2))),
% 7.79/1.49    inference(cnf_transformation,[],[f38])).
% 7.79/1.49  
% 7.79/1.49  fof(f68,plain,(
% 7.79/1.49    ~r1_tarski(k3_relat_1(sK3),k3_tarski(k1_enumset1(sK1,sK1,sK2)))),
% 7.79/1.49    inference(definition_unfolding,[],[f62,f63])).
% 7.79/1.49  
% 7.79/1.49  fof(f15,axiom,(
% 7.79/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.79/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.79/1.49  
% 7.79/1.49  fof(f28,plain,(
% 7.79/1.49    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.79/1.49    inference(ennf_transformation,[],[f15])).
% 7.79/1.49  
% 7.79/1.49  fof(f60,plain,(
% 7.79/1.49    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.79/1.49    inference(cnf_transformation,[],[f28])).
% 7.79/1.49  
% 7.79/1.49  fof(f1,axiom,(
% 7.79/1.49    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 7.79/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.79/1.49  
% 7.79/1.49  fof(f18,plain,(
% 7.79/1.49    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 7.79/1.49    inference(ennf_transformation,[],[f1])).
% 7.79/1.49  
% 7.79/1.49  fof(f39,plain,(
% 7.79/1.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 7.79/1.49    inference(cnf_transformation,[],[f18])).
% 7.79/1.49  
% 7.79/1.49  fof(f64,plain,(
% 7.79/1.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1))) | ~r1_tarski(X0,X1)) )),
% 7.79/1.49    inference(definition_unfolding,[],[f39,f63])).
% 7.79/1.49  
% 7.79/1.49  fof(f56,plain,(
% 7.79/1.49    ( ! [X0,X1] : (v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 7.79/1.49    inference(cnf_transformation,[],[f36])).
% 7.79/1.49  
% 7.79/1.49  fof(f59,plain,(
% 7.79/1.49    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.79/1.49    inference(cnf_transformation,[],[f28])).
% 7.79/1.49  
% 7.79/1.49  cnf(c_1,plain,
% 7.79/1.49      ( r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
% 7.79/1.49      inference(cnf_transformation,[],[f65]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_792,plain,
% 7.79/1.49      ( r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) = iProver_top ),
% 7.79/1.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_7,plain,
% 7.79/1.49      ( ~ r1_tarski(X0,X1) | r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ),
% 7.79/1.49      inference(cnf_transformation,[],[f48]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_786,plain,
% 7.79/1.49      ( r1_tarski(X0,X1) != iProver_top
% 7.79/1.49      | r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = iProver_top ),
% 7.79/1.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_5,plain,
% 7.79/1.49      ( r2_hidden(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.79/1.49      inference(cnf_transformation,[],[f69]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_788,plain,
% 7.79/1.49      ( r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top
% 7.79/1.49      | r1_tarski(X0,X1) != iProver_top ),
% 7.79/1.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_8,plain,
% 7.79/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.79/1.49      inference(cnf_transformation,[],[f50]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_785,plain,
% 7.79/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 7.79/1.49      | r1_tarski(X0,X1) != iProver_top ),
% 7.79/1.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_10,plain,
% 7.79/1.49      ( m1_subset_1(X0,X1)
% 7.79/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.79/1.49      | ~ r2_hidden(X0,X2) ),
% 7.79/1.49      inference(cnf_transformation,[],[f51]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_783,plain,
% 7.79/1.49      ( m1_subset_1(X0,X1) = iProver_top
% 7.79/1.49      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 7.79/1.49      | r2_hidden(X0,X2) != iProver_top ),
% 7.79/1.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_2381,plain,
% 7.79/1.49      ( m1_subset_1(X0,X1) = iProver_top
% 7.79/1.49      | r2_hidden(X0,X2) != iProver_top
% 7.79/1.49      | r1_tarski(X2,X1) != iProver_top ),
% 7.79/1.49      inference(superposition,[status(thm)],[c_785,c_783]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_4696,plain,
% 7.79/1.49      ( m1_subset_1(X0,X1) = iProver_top
% 7.79/1.49      | r1_tarski(X0,X2) != iProver_top
% 7.79/1.49      | r1_tarski(k1_zfmisc_1(X2),X1) != iProver_top ),
% 7.79/1.49      inference(superposition,[status(thm)],[c_788,c_2381]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_4941,plain,
% 7.79/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 7.79/1.49      | r1_tarski(X2,X1) != iProver_top
% 7.79/1.49      | r1_tarski(X0,X2) != iProver_top ),
% 7.79/1.49      inference(superposition,[status(thm)],[c_786,c_4696]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_5502,plain,
% 7.79/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k3_tarski(k1_enumset1(X1,X1,X2)))) = iProver_top
% 7.79/1.49      | r1_tarski(X0,X1) != iProver_top ),
% 7.79/1.49      inference(superposition,[status(thm)],[c_792,c_4941]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_9,plain,
% 7.79/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.79/1.49      inference(cnf_transformation,[],[f49]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_784,plain,
% 7.79/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.79/1.49      | r1_tarski(X0,X1) = iProver_top ),
% 7.79/1.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_5581,plain,
% 7.79/1.49      ( r1_tarski(X0,X1) != iProver_top
% 7.79/1.49      | r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2))) = iProver_top ),
% 7.79/1.49      inference(superposition,[status(thm)],[c_5502,c_784]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_12,plain,
% 7.79/1.49      ( v4_relat_1(X0,X1)
% 7.79/1.49      | ~ r1_tarski(k1_relat_1(X0),X1)
% 7.79/1.49      | ~ v1_relat_1(X0) ),
% 7.79/1.49      inference(cnf_transformation,[],[f54]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_782,plain,
% 7.79/1.49      ( v4_relat_1(X0,X1) = iProver_top
% 7.79/1.49      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 7.79/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.79/1.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_5850,plain,
% 7.79/1.49      ( v4_relat_1(X0,k3_tarski(k1_enumset1(X1,X1,X2))) = iProver_top
% 7.79/1.49      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 7.79/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.79/1.49      inference(superposition,[status(thm)],[c_5581,c_782]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_15,plain,
% 7.79/1.49      ( ~ v5_relat_1(X0,X1)
% 7.79/1.49      | r1_tarski(k2_relat_1(X0),X1)
% 7.79/1.49      | ~ v1_relat_1(X0) ),
% 7.79/1.49      inference(cnf_transformation,[],[f55]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_779,plain,
% 7.79/1.49      ( v5_relat_1(X0,X1) != iProver_top
% 7.79/1.49      | r1_tarski(k2_relat_1(X0),X1) = iProver_top
% 7.79/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.79/1.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_13,plain,
% 7.79/1.49      ( ~ v4_relat_1(X0,X1)
% 7.79/1.49      | r1_tarski(k1_relat_1(X0),X1)
% 7.79/1.49      | ~ v1_relat_1(X0) ),
% 7.79/1.49      inference(cnf_transformation,[],[f53]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_781,plain,
% 7.79/1.49      ( v4_relat_1(X0,X1) != iProver_top
% 7.79/1.49      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 7.79/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.79/1.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_21,negated_conjecture,
% 7.79/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 7.79/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_773,plain,
% 7.79/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 7.79/1.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_1179,plain,
% 7.79/1.49      ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
% 7.79/1.49      inference(superposition,[status(thm)],[c_773,c_784]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_11,plain,
% 7.79/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.79/1.49      | ~ v1_relat_1(X1)
% 7.79/1.49      | v1_relat_1(X0) ),
% 7.79/1.49      inference(cnf_transformation,[],[f52]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_161,plain,
% 7.79/1.49      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.79/1.49      inference(prop_impl,[status(thm)],[c_8]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_162,plain,
% 7.79/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.79/1.49      inference(renaming,[status(thm)],[c_161]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_203,plain,
% 7.79/1.49      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 7.79/1.49      inference(bin_hyper_res,[status(thm)],[c_11,c_162]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_772,plain,
% 7.79/1.49      ( r1_tarski(X0,X1) != iProver_top
% 7.79/1.49      | v1_relat_1(X1) != iProver_top
% 7.79/1.49      | v1_relat_1(X0) = iProver_top ),
% 7.79/1.49      inference(predicate_to_equality,[status(thm)],[c_203]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_3078,plain,
% 7.79/1.49      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
% 7.79/1.49      | v1_relat_1(sK3) = iProver_top ),
% 7.79/1.49      inference(superposition,[status(thm)],[c_1179,c_772]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_1043,plain,
% 7.79/1.49      ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) ),
% 7.79/1.49      inference(resolution,[status(thm)],[c_9,c_21]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_1099,plain,
% 7.79/1.49      ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK2)) | v1_relat_1(sK3) ),
% 7.79/1.49      inference(resolution,[status(thm)],[c_203,c_1043]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_17,plain,
% 7.79/1.49      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 7.79/1.49      inference(cnf_transformation,[],[f58]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_1196,plain,
% 7.79/1.49      ( v1_relat_1(sK3) ),
% 7.79/1.49      inference(forward_subsumption_resolution,
% 7.79/1.49                [status(thm)],
% 7.79/1.49                [c_1099,c_17]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_1197,plain,
% 7.79/1.49      ( v1_relat_1(sK3) = iProver_top ),
% 7.79/1.49      inference(predicate_to_equality,[status(thm)],[c_1196]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_8900,plain,
% 7.79/1.49      ( v1_relat_1(sK3) = iProver_top ),
% 7.79/1.49      inference(global_propositional_subsumption,
% 7.79/1.49                [status(thm)],
% 7.79/1.49                [c_3078,c_1197]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_16,plain,
% 7.79/1.49      ( ~ v1_relat_1(X0)
% 7.79/1.49      | k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) ),
% 7.79/1.49      inference(cnf_transformation,[],[f67]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_778,plain,
% 7.79/1.49      ( k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
% 7.79/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.79/1.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_8905,plain,
% 7.79/1.49      ( k3_tarski(k1_enumset1(k1_relat_1(sK3),k1_relat_1(sK3),k2_relat_1(sK3))) = k3_relat_1(sK3) ),
% 7.79/1.49      inference(superposition,[status(thm)],[c_8900,c_778]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_2,plain,
% 7.79/1.49      ( ~ r1_tarski(X0,X1)
% 7.79/1.49      | ~ r1_tarski(X2,X1)
% 7.79/1.49      | r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) ),
% 7.79/1.49      inference(cnf_transformation,[],[f66]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_791,plain,
% 7.79/1.49      ( r1_tarski(X0,X1) != iProver_top
% 7.79/1.49      | r1_tarski(X2,X1) != iProver_top
% 7.79/1.49      | r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) = iProver_top ),
% 7.79/1.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_9119,plain,
% 7.79/1.49      ( r1_tarski(k3_relat_1(sK3),X0) = iProver_top
% 7.79/1.49      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top
% 7.79/1.49      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
% 7.79/1.49      inference(superposition,[status(thm)],[c_8905,c_791]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_11166,plain,
% 7.79/1.49      ( v4_relat_1(sK3,X0) != iProver_top
% 7.79/1.49      | r1_tarski(k3_relat_1(sK3),X0) = iProver_top
% 7.79/1.49      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top
% 7.79/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.79/1.49      inference(superposition,[status(thm)],[c_781,c_9119]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_28201,plain,
% 7.79/1.49      ( r1_tarski(k2_relat_1(sK3),X0) != iProver_top
% 7.79/1.49      | r1_tarski(k3_relat_1(sK3),X0) = iProver_top
% 7.79/1.49      | v4_relat_1(sK3,X0) != iProver_top ),
% 7.79/1.49      inference(global_propositional_subsumption,
% 7.79/1.49                [status(thm)],
% 7.79/1.49                [c_11166,c_1197]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_28202,plain,
% 7.79/1.49      ( v4_relat_1(sK3,X0) != iProver_top
% 7.79/1.49      | r1_tarski(k3_relat_1(sK3),X0) = iProver_top
% 7.79/1.49      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
% 7.79/1.49      inference(renaming,[status(thm)],[c_28201]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_28213,plain,
% 7.79/1.49      ( v5_relat_1(sK3,X0) != iProver_top
% 7.79/1.49      | v4_relat_1(sK3,X0) != iProver_top
% 7.79/1.49      | r1_tarski(k3_relat_1(sK3),X0) = iProver_top
% 7.79/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.79/1.49      inference(superposition,[status(thm)],[c_779,c_28202]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_28694,plain,
% 7.79/1.49      ( r1_tarski(k3_relat_1(sK3),X0) = iProver_top
% 7.79/1.49      | v4_relat_1(sK3,X0) != iProver_top
% 7.79/1.49      | v5_relat_1(sK3,X0) != iProver_top ),
% 7.79/1.49      inference(global_propositional_subsumption,
% 7.79/1.49                [status(thm)],
% 7.79/1.49                [c_28213,c_1197]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_28695,plain,
% 7.79/1.49      ( v5_relat_1(sK3,X0) != iProver_top
% 7.79/1.49      | v4_relat_1(sK3,X0) != iProver_top
% 7.79/1.49      | r1_tarski(k3_relat_1(sK3),X0) = iProver_top ),
% 7.79/1.49      inference(renaming,[status(thm)],[c_28694]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_20,negated_conjecture,
% 7.79/1.49      ( ~ r1_tarski(k3_relat_1(sK3),k3_tarski(k1_enumset1(sK1,sK1,sK2))) ),
% 7.79/1.49      inference(cnf_transformation,[],[f68]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_774,plain,
% 7.79/1.49      ( r1_tarski(k3_relat_1(sK3),k3_tarski(k1_enumset1(sK1,sK1,sK2))) != iProver_top ),
% 7.79/1.49      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_28711,plain,
% 7.79/1.49      ( v5_relat_1(sK3,k3_tarski(k1_enumset1(sK1,sK1,sK2))) != iProver_top
% 7.79/1.49      | v4_relat_1(sK3,k3_tarski(k1_enumset1(sK1,sK1,sK2))) != iProver_top ),
% 7.79/1.49      inference(superposition,[status(thm)],[c_28695,c_774]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_22,plain,
% 7.79/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 7.79/1.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_18,plain,
% 7.79/1.49      ( v5_relat_1(X0,X1)
% 7.79/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 7.79/1.49      inference(cnf_transformation,[],[f60]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_1009,plain,
% 7.79/1.49      ( v5_relat_1(sK3,sK2)
% 7.79/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 7.79/1.49      inference(instantiation,[status(thm)],[c_18]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_1010,plain,
% 7.79/1.49      ( v5_relat_1(sK3,sK2) = iProver_top
% 7.79/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
% 7.79/1.49      inference(predicate_to_equality,[status(thm)],[c_1009]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_1123,plain,
% 7.79/1.49      ( ~ v5_relat_1(sK3,sK2)
% 7.79/1.49      | r1_tarski(k2_relat_1(sK3),sK2)
% 7.79/1.49      | ~ v1_relat_1(sK3) ),
% 7.79/1.49      inference(instantiation,[status(thm)],[c_15]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_1124,plain,
% 7.79/1.49      ( v5_relat_1(sK3,sK2) != iProver_top
% 7.79/1.49      | r1_tarski(k2_relat_1(sK3),sK2) = iProver_top
% 7.79/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.79/1.49      inference(predicate_to_equality,[status(thm)],[c_1123]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_0,plain,
% 7.79/1.49      ( ~ r1_tarski(X0,X1)
% 7.79/1.49      | r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1))) ),
% 7.79/1.49      inference(cnf_transformation,[],[f64]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_1277,plain,
% 7.79/1.49      ( r1_tarski(k2_relat_1(sK3),k3_tarski(k1_enumset1(X0,X0,sK2)))
% 7.79/1.49      | ~ r1_tarski(k2_relat_1(sK3),sK2) ),
% 7.79/1.49      inference(instantiation,[status(thm)],[c_0]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_1287,plain,
% 7.79/1.49      ( r1_tarski(k2_relat_1(sK3),k3_tarski(k1_enumset1(X0,X0,sK2))) = iProver_top
% 7.79/1.49      | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top ),
% 7.79/1.49      inference(predicate_to_equality,[status(thm)],[c_1277]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_1289,plain,
% 7.79/1.49      ( r1_tarski(k2_relat_1(sK3),k3_tarski(k1_enumset1(sK1,sK1,sK2))) = iProver_top
% 7.79/1.49      | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top ),
% 7.79/1.49      inference(instantiation,[status(thm)],[c_1287]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_14,plain,
% 7.79/1.49      ( v5_relat_1(X0,X1)
% 7.79/1.49      | ~ r1_tarski(k2_relat_1(X0),X1)
% 7.79/1.49      | ~ v1_relat_1(X0) ),
% 7.79/1.49      inference(cnf_transformation,[],[f56]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_1955,plain,
% 7.79/1.49      ( v5_relat_1(sK3,X0)
% 7.79/1.49      | ~ r1_tarski(k2_relat_1(sK3),X0)
% 7.79/1.49      | ~ v1_relat_1(sK3) ),
% 7.79/1.49      inference(instantiation,[status(thm)],[c_14]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_3297,plain,
% 7.79/1.49      ( v5_relat_1(sK3,k3_tarski(k1_enumset1(X0,X0,sK2)))
% 7.79/1.49      | ~ r1_tarski(k2_relat_1(sK3),k3_tarski(k1_enumset1(X0,X0,sK2)))
% 7.79/1.49      | ~ v1_relat_1(sK3) ),
% 7.79/1.49      inference(instantiation,[status(thm)],[c_1955]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_3298,plain,
% 7.79/1.49      ( v5_relat_1(sK3,k3_tarski(k1_enumset1(X0,X0,sK2))) = iProver_top
% 7.79/1.49      | r1_tarski(k2_relat_1(sK3),k3_tarski(k1_enumset1(X0,X0,sK2))) != iProver_top
% 7.79/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.79/1.49      inference(predicate_to_equality,[status(thm)],[c_3297]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_3300,plain,
% 7.79/1.49      ( v5_relat_1(sK3,k3_tarski(k1_enumset1(sK1,sK1,sK2))) = iProver_top
% 7.79/1.49      | r1_tarski(k2_relat_1(sK3),k3_tarski(k1_enumset1(sK1,sK1,sK2))) != iProver_top
% 7.79/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.79/1.49      inference(instantiation,[status(thm)],[c_3298]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_29112,plain,
% 7.79/1.49      ( v4_relat_1(sK3,k3_tarski(k1_enumset1(sK1,sK1,sK2))) != iProver_top ),
% 7.79/1.49      inference(global_propositional_subsumption,
% 7.79/1.49                [status(thm)],
% 7.79/1.49                [c_28711,c_22,c_1010,c_1124,c_1197,c_1289,c_3300]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_29117,plain,
% 7.79/1.49      ( r1_tarski(k1_relat_1(sK3),sK1) != iProver_top
% 7.79/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.79/1.49      inference(superposition,[status(thm)],[c_5850,c_29112]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_1126,plain,
% 7.79/1.49      ( ~ v4_relat_1(sK3,sK1)
% 7.79/1.49      | r1_tarski(k1_relat_1(sK3),sK1)
% 7.79/1.49      | ~ v1_relat_1(sK3) ),
% 7.79/1.49      inference(instantiation,[status(thm)],[c_13]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_1127,plain,
% 7.79/1.49      ( v4_relat_1(sK3,sK1) != iProver_top
% 7.79/1.49      | r1_tarski(k1_relat_1(sK3),sK1) = iProver_top
% 7.79/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.79/1.49      inference(predicate_to_equality,[status(thm)],[c_1126]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_19,plain,
% 7.79/1.49      ( v4_relat_1(X0,X1)
% 7.79/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.79/1.49      inference(cnf_transformation,[],[f59]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_1012,plain,
% 7.79/1.49      ( v4_relat_1(sK3,sK1)
% 7.79/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 7.79/1.49      inference(instantiation,[status(thm)],[c_19]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(c_1013,plain,
% 7.79/1.49      ( v4_relat_1(sK3,sK1) = iProver_top
% 7.79/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
% 7.79/1.49      inference(predicate_to_equality,[status(thm)],[c_1012]) ).
% 7.79/1.49  
% 7.79/1.49  cnf(contradiction,plain,
% 7.79/1.49      ( $false ),
% 7.79/1.49      inference(minisat,[status(thm)],[c_29117,c_1197,c_1127,c_1013,c_22]) ).
% 7.79/1.49  
% 7.79/1.49  
% 7.79/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.79/1.49  
% 7.79/1.49  ------                               Statistics
% 7.79/1.49  
% 7.79/1.49  ------ Selected
% 7.79/1.49  
% 7.79/1.49  total_time:                             0.911
% 7.79/1.49  
%------------------------------------------------------------------------------
