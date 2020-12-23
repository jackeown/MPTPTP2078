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
% DateTime   : Thu Dec  3 11:43:12 EST 2020

% Result     : Theorem 2.60s
% Output     : CNFRefutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 185 expanded)
%              Number of clauses        :   43 (  48 expanded)
%              Number of leaves         :   18 (  47 expanded)
%              Depth                    :   15
%              Number of atoms          :  296 ( 589 expanded)
%              Number of equality atoms :   51 (  73 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f12,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
             => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
     => ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(sK5))
        & r1_tarski(X0,sK5)
        & v1_relat_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
            & r1_tarski(X0,X1)
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(sK4),k3_relat_1(X1))
          & r1_tarski(sK4,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ~ r1_tarski(k3_relat_1(sK4),k3_relat_1(sK5))
    & r1_tarski(sK4,sK5)
    & v1_relat_1(sK5)
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f25,f38,f37])).

fof(f60,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f39])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f54,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f63,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f46,f45])).

fof(f66,plain,(
    ! [X0] :
      ( k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f54,f63])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k2_enumset1(X2,X2,X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f43,f63])).

fof(f59,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f39])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k2_enumset1(X0,X0,X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f44,f63])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k3_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f61,plain,(
    r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f39])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f31])).

fof(f35,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK2(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK1(X0,X1),X3),X0)
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK1(X0,X1),X4),X0)
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK1(X0,X1),X3),X0)
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f32,f35,f34,f33])).

fof(f50,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f68,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f50])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f62,plain,(
    ~ r1_tarski(k3_relat_1(sK4),k3_relat_1(sK5)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_5,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_124,plain,
    ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13,c_7,c_5])).

cnf(c_125,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(renaming,[status(thm)],[c_124])).

cnf(c_774,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_125])).

cnf(c_19,negated_conjecture,
    ( v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_777,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_782,plain,
    ( k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1319,plain,
    ( k3_tarski(k2_enumset1(k1_relat_1(sK5),k1_relat_1(sK5),k1_relat_1(sK5),k2_relat_1(sK5))) = k3_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_777,c_782])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k3_tarski(k2_enumset1(X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_788,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k3_tarski(k2_enumset1(X2,X2,X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1478,plain,
    ( r1_tarski(X0,k3_relat_1(sK5)) = iProver_top
    | r1_tarski(X0,k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1319,c_788])).

cnf(c_1620,plain,
    ( r1_tarski(X0,sK5) != iProver_top
    | r1_tarski(k2_relat_1(X0),k3_relat_1(sK5)) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_774,c_1478])).

cnf(c_22,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1749,plain,
    ( r1_tarski(k2_relat_1(X0),k3_relat_1(sK5)) = iProver_top
    | r1_tarski(X0,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1620,c_22])).

cnf(c_1750,plain,
    ( r1_tarski(X0,sK5) != iProver_top
    | r1_tarski(k2_relat_1(X0),k3_relat_1(sK5)) = iProver_top ),
    inference(renaming,[status(thm)],[c_1749])).

cnf(c_20,negated_conjecture,
    ( v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_776,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1320,plain,
    ( k3_tarski(k2_enumset1(k1_relat_1(sK4),k1_relat_1(sK4),k1_relat_1(sK4),k2_relat_1(sK4))) = k3_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_776,c_782])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k3_tarski(k2_enumset1(X0,X0,X0,X2)),X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_787,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k3_tarski(k2_enumset1(X0,X0,X0,X2)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2938,plain,
    ( r1_tarski(k3_relat_1(sK4),X0) = iProver_top
    | r1_tarski(k2_relat_1(sK4),X0) != iProver_top
    | r1_tarski(k1_relat_1(sK4),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1320,c_787])).

cnf(c_3599,plain,
    ( r1_tarski(k3_relat_1(sK4),k3_relat_1(sK5)) = iProver_top
    | r1_tarski(k1_relat_1(sK4),k3_relat_1(sK5)) != iProver_top
    | r1_tarski(sK4,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1750,c_2938])).

cnf(c_16,plain,
    ( r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_18,negated_conjecture,
    ( r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1016,plain,
    ( r2_hidden(X0,sK5)
    | ~ r2_hidden(X0,sK4) ),
    inference(resolution,[status(thm)],[c_2,c_18])).

cnf(c_1775,plain,
    ( r2_hidden(X0,k3_relat_1(sK5))
    | ~ r2_hidden(k4_tarski(X0,X1),sK4)
    | ~ v1_relat_1(sK5) ),
    inference(resolution,[status(thm)],[c_16,c_1016])).

cnf(c_1778,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK4)
    | r2_hidden(X0,k3_relat_1(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1775,c_19])).

cnf(c_1779,plain,
    ( r2_hidden(X0,k3_relat_1(sK5))
    | ~ r2_hidden(k4_tarski(X0,X1),sK4) ),
    inference(renaming,[status(thm)],[c_1778])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,sK3(X1,X0)),X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2442,plain,
    ( r2_hidden(X0,k3_relat_1(sK5))
    | ~ r2_hidden(X0,k1_relat_1(sK4)) ),
    inference(resolution,[status(thm)],[c_1779,c_11])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_2472,plain,
    ( ~ r2_hidden(sK0(X0,k3_relat_1(sK5)),k1_relat_1(sK4))
    | r1_tarski(X0,k3_relat_1(sK5)) ),
    inference(resolution,[status(thm)],[c_2442,c_0])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_2827,plain,
    ( r1_tarski(k1_relat_1(sK4),k3_relat_1(sK5)) ),
    inference(resolution,[status(thm)],[c_2472,c_1])).

cnf(c_2828,plain,
    ( r1_tarski(k1_relat_1(sK4),k3_relat_1(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2827])).

cnf(c_17,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(sK4),k3_relat_1(sK5)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_24,plain,
    ( r1_tarski(k3_relat_1(sK4),k3_relat_1(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_23,plain,
    ( r1_tarski(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3599,c_2828,c_24,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:09:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.60/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.00  
% 2.60/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.60/1.00  
% 2.60/1.00  ------  iProver source info
% 2.60/1.00  
% 2.60/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.60/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.60/1.00  git: non_committed_changes: false
% 2.60/1.00  git: last_make_outside_of_git: false
% 2.60/1.00  
% 2.60/1.00  ------ 
% 2.60/1.00  ------ Parsing...
% 2.60/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.60/1.00  
% 2.60/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.60/1.00  
% 2.60/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.60/1.00  
% 2.60/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.60/1.00  ------ Proving...
% 2.60/1.00  ------ Problem Properties 
% 2.60/1.00  
% 2.60/1.00  
% 2.60/1.00  clauses                                 19
% 2.60/1.00  conjectures                             4
% 2.60/1.00  EPR                                     5
% 2.60/1.00  Horn                                    17
% 2.60/1.00  unary                                   4
% 2.60/1.00  binary                                  6
% 2.60/1.00  lits                                    43
% 2.60/1.00  lits eq                                 3
% 2.60/1.00  fd_pure                                 0
% 2.60/1.00  fd_pseudo                               0
% 2.60/1.00  fd_cond                                 0
% 2.60/1.00  fd_pseudo_cond                          2
% 2.60/1.00  AC symbols                              0
% 2.60/1.00  
% 2.60/1.00  ------ Input Options Time Limit: Unbounded
% 2.60/1.00  
% 2.60/1.00  
% 2.60/1.00  ------ 
% 2.60/1.00  Current options:
% 2.60/1.00  ------ 
% 2.60/1.00  
% 2.60/1.00  
% 2.60/1.00  
% 2.60/1.00  
% 2.60/1.00  ------ Proving...
% 2.60/1.00  
% 2.60/1.00  
% 2.60/1.00  % SZS status Theorem for theBenchmark.p
% 2.60/1.00  
% 2.60/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.60/1.00  
% 2.60/1.00  fof(f10,axiom,(
% 2.60/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 2.60/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f20,plain,(
% 2.60/1.00    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.60/1.00    inference(ennf_transformation,[],[f10])).
% 2.60/1.00  
% 2.60/1.00  fof(f21,plain,(
% 2.60/1.00    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.60/1.00    inference(flattening,[],[f20])).
% 2.60/1.00  
% 2.60/1.00  fof(f56,plain,(
% 2.60/1.00    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f21])).
% 2.60/1.00  
% 2.60/1.00  fof(f7,axiom,(
% 2.60/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.60/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f18,plain,(
% 2.60/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.60/1.00    inference(ennf_transformation,[],[f7])).
% 2.60/1.00  
% 2.60/1.00  fof(f49,plain,(
% 2.60/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f18])).
% 2.60/1.00  
% 2.60/1.00  fof(f6,axiom,(
% 2.60/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.60/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f30,plain,(
% 2.60/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.60/1.00    inference(nnf_transformation,[],[f6])).
% 2.60/1.00  
% 2.60/1.00  fof(f48,plain,(
% 2.60/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f30])).
% 2.60/1.00  
% 2.60/1.00  fof(f12,conjecture,(
% 2.60/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 2.60/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f13,negated_conjecture,(
% 2.60/1.00    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 2.60/1.00    inference(negated_conjecture,[],[f12])).
% 2.60/1.00  
% 2.60/1.00  fof(f24,plain,(
% 2.60/1.00    ? [X0] : (? [X1] : ((~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 2.60/1.00    inference(ennf_transformation,[],[f13])).
% 2.60/1.00  
% 2.60/1.00  fof(f25,plain,(
% 2.60/1.00    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 2.60/1.00    inference(flattening,[],[f24])).
% 2.60/1.00  
% 2.60/1.00  fof(f38,plain,(
% 2.60/1.00    ( ! [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) => (~r1_tarski(k3_relat_1(X0),k3_relat_1(sK5)) & r1_tarski(X0,sK5) & v1_relat_1(sK5))) )),
% 2.60/1.00    introduced(choice_axiom,[])).
% 2.60/1.00  
% 2.60/1.00  fof(f37,plain,(
% 2.60/1.00    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k3_relat_1(sK4),k3_relat_1(X1)) & r1_tarski(sK4,X1) & v1_relat_1(X1)) & v1_relat_1(sK4))),
% 2.60/1.00    introduced(choice_axiom,[])).
% 2.60/1.00  
% 2.60/1.00  fof(f39,plain,(
% 2.60/1.00    (~r1_tarski(k3_relat_1(sK4),k3_relat_1(sK5)) & r1_tarski(sK4,sK5) & v1_relat_1(sK5)) & v1_relat_1(sK4)),
% 2.60/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f25,f38,f37])).
% 2.60/1.00  
% 2.60/1.00  fof(f60,plain,(
% 2.60/1.00    v1_relat_1(sK5)),
% 2.60/1.00    inference(cnf_transformation,[],[f39])).
% 2.60/1.00  
% 2.60/1.00  fof(f9,axiom,(
% 2.60/1.00    ! [X0] : (v1_relat_1(X0) => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0))),
% 2.60/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f19,plain,(
% 2.60/1.00    ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0))),
% 2.60/1.00    inference(ennf_transformation,[],[f9])).
% 2.60/1.00  
% 2.60/1.00  fof(f54,plain,(
% 2.60/1.00    ( ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f19])).
% 2.60/1.00  
% 2.60/1.00  fof(f5,axiom,(
% 2.60/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.60/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f46,plain,(
% 2.60/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.60/1.00    inference(cnf_transformation,[],[f5])).
% 2.60/1.00  
% 2.60/1.00  fof(f4,axiom,(
% 2.60/1.00    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)),
% 2.60/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f45,plain,(
% 2.60/1.00    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f4])).
% 2.60/1.00  
% 2.60/1.00  fof(f63,plain,(
% 2.60/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 2.60/1.00    inference(definition_unfolding,[],[f46,f45])).
% 2.60/1.00  
% 2.60/1.00  fof(f66,plain,(
% 2.60/1.00    ( ! [X0] : (k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.60/1.00    inference(definition_unfolding,[],[f54,f63])).
% 2.60/1.00  
% 2.60/1.00  fof(f2,axiom,(
% 2.60/1.00    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 2.60/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f15,plain,(
% 2.60/1.00    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 2.60/1.00    inference(ennf_transformation,[],[f2])).
% 2.60/1.00  
% 2.60/1.00  fof(f43,plain,(
% 2.60/1.00    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f15])).
% 2.60/1.00  
% 2.60/1.00  fof(f64,plain,(
% 2.60/1.00    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k2_enumset1(X2,X2,X2,X1))) | ~r1_tarski(X0,X1)) )),
% 2.60/1.00    inference(definition_unfolding,[],[f43,f63])).
% 2.60/1.00  
% 2.60/1.00  fof(f59,plain,(
% 2.60/1.00    v1_relat_1(sK4)),
% 2.60/1.00    inference(cnf_transformation,[],[f39])).
% 2.60/1.00  
% 2.60/1.00  fof(f3,axiom,(
% 2.60/1.00    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 2.60/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f16,plain,(
% 2.60/1.00    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 2.60/1.00    inference(ennf_transformation,[],[f3])).
% 2.60/1.00  
% 2.60/1.00  fof(f17,plain,(
% 2.60/1.00    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 2.60/1.00    inference(flattening,[],[f16])).
% 2.60/1.00  
% 2.60/1.00  fof(f44,plain,(
% 2.60/1.00    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f17])).
% 2.60/1.00  
% 2.60/1.00  fof(f65,plain,(
% 2.60/1.00    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k2_enumset1(X0,X0,X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.60/1.00    inference(definition_unfolding,[],[f44,f63])).
% 2.60/1.00  
% 2.60/1.00  fof(f11,axiom,(
% 2.60/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)))))),
% 2.60/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f22,plain,(
% 2.60/1.00    ! [X0,X1,X2] : (((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 2.60/1.00    inference(ennf_transformation,[],[f11])).
% 2.60/1.00  
% 2.60/1.00  fof(f23,plain,(
% 2.60/1.00    ! [X0,X1,X2] : ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 2.60/1.00    inference(flattening,[],[f22])).
% 2.60/1.00  
% 2.60/1.00  fof(f57,plain,(
% 2.60/1.00    ( ! [X2,X0,X1] : (r2_hidden(X0,k3_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f23])).
% 2.60/1.00  
% 2.60/1.00  fof(f1,axiom,(
% 2.60/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.60/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f14,plain,(
% 2.60/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.60/1.00    inference(ennf_transformation,[],[f1])).
% 2.60/1.00  
% 2.60/1.00  fof(f26,plain,(
% 2.60/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.60/1.00    inference(nnf_transformation,[],[f14])).
% 2.60/1.00  
% 2.60/1.00  fof(f27,plain,(
% 2.60/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.60/1.00    inference(rectify,[],[f26])).
% 2.60/1.00  
% 2.60/1.00  fof(f28,plain,(
% 2.60/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.60/1.00    introduced(choice_axiom,[])).
% 2.60/1.00  
% 2.60/1.00  fof(f29,plain,(
% 2.60/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.60/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).
% 2.60/1.00  
% 2.60/1.00  fof(f40,plain,(
% 2.60/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f29])).
% 2.60/1.00  
% 2.60/1.00  fof(f61,plain,(
% 2.60/1.00    r1_tarski(sK4,sK5)),
% 2.60/1.00    inference(cnf_transformation,[],[f39])).
% 2.60/1.00  
% 2.60/1.00  fof(f8,axiom,(
% 2.60/1.00    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 2.60/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f31,plain,(
% 2.60/1.00    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 2.60/1.00    inference(nnf_transformation,[],[f8])).
% 2.60/1.00  
% 2.60/1.00  fof(f32,plain,(
% 2.60/1.00    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 2.60/1.00    inference(rectify,[],[f31])).
% 2.60/1.00  
% 2.60/1.00  fof(f35,plain,(
% 2.60/1.00    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0))),
% 2.60/1.00    introduced(choice_axiom,[])).
% 2.60/1.00  
% 2.60/1.00  fof(f34,plain,(
% 2.60/1.00    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) => r2_hidden(k4_tarski(X2,sK2(X0,X1)),X0))) )),
% 2.60/1.00    introduced(choice_axiom,[])).
% 2.60/1.00  
% 2.60/1.00  fof(f33,plain,(
% 2.60/1.00    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK1(X0,X1),X3),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK1(X0,X1),X4),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 2.60/1.00    introduced(choice_axiom,[])).
% 2.60/1.00  
% 2.60/1.00  fof(f36,plain,(
% 2.60/1.00    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK1(X0,X1),X3),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 2.60/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f32,f35,f34,f33])).
% 2.60/1.00  
% 2.60/1.00  fof(f50,plain,(
% 2.60/1.00    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 2.60/1.00    inference(cnf_transformation,[],[f36])).
% 2.60/1.00  
% 2.60/1.00  fof(f68,plain,(
% 2.60/1.00    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 2.60/1.00    inference(equality_resolution,[],[f50])).
% 2.60/1.00  
% 2.60/1.00  fof(f42,plain,(
% 2.60/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f29])).
% 2.60/1.00  
% 2.60/1.00  fof(f41,plain,(
% 2.60/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f29])).
% 2.60/1.00  
% 2.60/1.00  fof(f62,plain,(
% 2.60/1.00    ~r1_tarski(k3_relat_1(sK4),k3_relat_1(sK5))),
% 2.60/1.00    inference(cnf_transformation,[],[f39])).
% 2.60/1.00  
% 2.60/1.00  cnf(c_13,plain,
% 2.60/1.00      ( ~ r1_tarski(X0,X1)
% 2.60/1.00      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 2.60/1.00      | ~ v1_relat_1(X0)
% 2.60/1.00      | ~ v1_relat_1(X1) ),
% 2.60/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_7,plain,
% 2.60/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.60/1.00      | ~ v1_relat_1(X1)
% 2.60/1.00      | v1_relat_1(X0) ),
% 2.60/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_5,plain,
% 2.60/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.60/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_124,plain,
% 2.60/1.00      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 2.60/1.00      | ~ r1_tarski(X0,X1)
% 2.60/1.00      | ~ v1_relat_1(X1) ),
% 2.60/1.00      inference(global_propositional_subsumption,
% 2.60/1.00                [status(thm)],
% 2.60/1.00                [c_13,c_7,c_5]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_125,plain,
% 2.60/1.00      ( ~ r1_tarski(X0,X1)
% 2.60/1.00      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 2.60/1.00      | ~ v1_relat_1(X1) ),
% 2.60/1.00      inference(renaming,[status(thm)],[c_124]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_774,plain,
% 2.60/1.00      ( r1_tarski(X0,X1) != iProver_top
% 2.60/1.00      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
% 2.60/1.00      | v1_relat_1(X1) != iProver_top ),
% 2.60/1.00      inference(predicate_to_equality,[status(thm)],[c_125]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_19,negated_conjecture,
% 2.60/1.00      ( v1_relat_1(sK5) ),
% 2.60/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_777,plain,
% 2.60/1.00      ( v1_relat_1(sK5) = iProver_top ),
% 2.60/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_12,plain,
% 2.60/1.00      ( ~ v1_relat_1(X0)
% 2.60/1.00      | k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) ),
% 2.60/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_782,plain,
% 2.60/1.00      ( k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
% 2.60/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.60/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1319,plain,
% 2.60/1.00      ( k3_tarski(k2_enumset1(k1_relat_1(sK5),k1_relat_1(sK5),k1_relat_1(sK5),k2_relat_1(sK5))) = k3_relat_1(sK5) ),
% 2.60/1.00      inference(superposition,[status(thm)],[c_777,c_782]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_3,plain,
% 2.60/1.00      ( ~ r1_tarski(X0,X1)
% 2.60/1.00      | r1_tarski(X0,k3_tarski(k2_enumset1(X2,X2,X2,X1))) ),
% 2.60/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_788,plain,
% 2.60/1.00      ( r1_tarski(X0,X1) != iProver_top
% 2.60/1.00      | r1_tarski(X0,k3_tarski(k2_enumset1(X2,X2,X2,X1))) = iProver_top ),
% 2.60/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1478,plain,
% 2.60/1.00      ( r1_tarski(X0,k3_relat_1(sK5)) = iProver_top
% 2.60/1.00      | r1_tarski(X0,k2_relat_1(sK5)) != iProver_top ),
% 2.60/1.00      inference(superposition,[status(thm)],[c_1319,c_788]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1620,plain,
% 2.60/1.00      ( r1_tarski(X0,sK5) != iProver_top
% 2.60/1.00      | r1_tarski(k2_relat_1(X0),k3_relat_1(sK5)) = iProver_top
% 2.60/1.00      | v1_relat_1(sK5) != iProver_top ),
% 2.60/1.00      inference(superposition,[status(thm)],[c_774,c_1478]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_22,plain,
% 2.60/1.00      ( v1_relat_1(sK5) = iProver_top ),
% 2.60/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1749,plain,
% 2.60/1.00      ( r1_tarski(k2_relat_1(X0),k3_relat_1(sK5)) = iProver_top
% 2.60/1.00      | r1_tarski(X0,sK5) != iProver_top ),
% 2.60/1.00      inference(global_propositional_subsumption,
% 2.60/1.00                [status(thm)],
% 2.60/1.00                [c_1620,c_22]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1750,plain,
% 2.60/1.00      ( r1_tarski(X0,sK5) != iProver_top
% 2.60/1.00      | r1_tarski(k2_relat_1(X0),k3_relat_1(sK5)) = iProver_top ),
% 2.60/1.00      inference(renaming,[status(thm)],[c_1749]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_20,negated_conjecture,
% 2.60/1.00      ( v1_relat_1(sK4) ),
% 2.60/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_776,plain,
% 2.60/1.00      ( v1_relat_1(sK4) = iProver_top ),
% 2.60/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1320,plain,
% 2.60/1.00      ( k3_tarski(k2_enumset1(k1_relat_1(sK4),k1_relat_1(sK4),k1_relat_1(sK4),k2_relat_1(sK4))) = k3_relat_1(sK4) ),
% 2.60/1.00      inference(superposition,[status(thm)],[c_776,c_782]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_4,plain,
% 2.60/1.00      ( ~ r1_tarski(X0,X1)
% 2.60/1.00      | ~ r1_tarski(X2,X1)
% 2.60/1.00      | r1_tarski(k3_tarski(k2_enumset1(X0,X0,X0,X2)),X1) ),
% 2.60/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_787,plain,
% 2.60/1.00      ( r1_tarski(X0,X1) != iProver_top
% 2.60/1.00      | r1_tarski(X2,X1) != iProver_top
% 2.60/1.00      | r1_tarski(k3_tarski(k2_enumset1(X0,X0,X0,X2)),X1) = iProver_top ),
% 2.60/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_2938,plain,
% 2.60/1.00      ( r1_tarski(k3_relat_1(sK4),X0) = iProver_top
% 2.60/1.00      | r1_tarski(k2_relat_1(sK4),X0) != iProver_top
% 2.60/1.00      | r1_tarski(k1_relat_1(sK4),X0) != iProver_top ),
% 2.60/1.00      inference(superposition,[status(thm)],[c_1320,c_787]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_3599,plain,
% 2.60/1.00      ( r1_tarski(k3_relat_1(sK4),k3_relat_1(sK5)) = iProver_top
% 2.60/1.00      | r1_tarski(k1_relat_1(sK4),k3_relat_1(sK5)) != iProver_top
% 2.60/1.00      | r1_tarski(sK4,sK5) != iProver_top ),
% 2.60/1.00      inference(superposition,[status(thm)],[c_1750,c_2938]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_16,plain,
% 2.60/1.00      ( r2_hidden(X0,k3_relat_1(X1))
% 2.60/1.00      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 2.60/1.00      | ~ v1_relat_1(X1) ),
% 2.60/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_2,plain,
% 2.60/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 2.60/1.00      inference(cnf_transformation,[],[f40]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_18,negated_conjecture,
% 2.60/1.00      ( r1_tarski(sK4,sK5) ),
% 2.60/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1016,plain,
% 2.60/1.00      ( r2_hidden(X0,sK5) | ~ r2_hidden(X0,sK4) ),
% 2.60/1.00      inference(resolution,[status(thm)],[c_2,c_18]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1775,plain,
% 2.60/1.00      ( r2_hidden(X0,k3_relat_1(sK5))
% 2.60/1.00      | ~ r2_hidden(k4_tarski(X0,X1),sK4)
% 2.60/1.00      | ~ v1_relat_1(sK5) ),
% 2.60/1.00      inference(resolution,[status(thm)],[c_16,c_1016]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1778,plain,
% 2.60/1.00      ( ~ r2_hidden(k4_tarski(X0,X1),sK4)
% 2.60/1.00      | r2_hidden(X0,k3_relat_1(sK5)) ),
% 2.60/1.00      inference(global_propositional_subsumption,
% 2.60/1.00                [status(thm)],
% 2.60/1.00                [c_1775,c_19]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1779,plain,
% 2.60/1.00      ( r2_hidden(X0,k3_relat_1(sK5))
% 2.60/1.00      | ~ r2_hidden(k4_tarski(X0,X1),sK4) ),
% 2.60/1.00      inference(renaming,[status(thm)],[c_1778]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_11,plain,
% 2.60/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.60/1.00      | r2_hidden(k4_tarski(X0,sK3(X1,X0)),X1) ),
% 2.60/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_2442,plain,
% 2.60/1.00      ( r2_hidden(X0,k3_relat_1(sK5)) | ~ r2_hidden(X0,k1_relat_1(sK4)) ),
% 2.60/1.00      inference(resolution,[status(thm)],[c_1779,c_11]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_0,plain,
% 2.60/1.00      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 2.60/1.00      inference(cnf_transformation,[],[f42]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_2472,plain,
% 2.60/1.00      ( ~ r2_hidden(sK0(X0,k3_relat_1(sK5)),k1_relat_1(sK4))
% 2.60/1.00      | r1_tarski(X0,k3_relat_1(sK5)) ),
% 2.60/1.00      inference(resolution,[status(thm)],[c_2442,c_0]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1,plain,
% 2.60/1.00      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 2.60/1.00      inference(cnf_transformation,[],[f41]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_2827,plain,
% 2.60/1.00      ( r1_tarski(k1_relat_1(sK4),k3_relat_1(sK5)) ),
% 2.60/1.00      inference(resolution,[status(thm)],[c_2472,c_1]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_2828,plain,
% 2.60/1.00      ( r1_tarski(k1_relat_1(sK4),k3_relat_1(sK5)) = iProver_top ),
% 2.60/1.00      inference(predicate_to_equality,[status(thm)],[c_2827]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_17,negated_conjecture,
% 2.60/1.00      ( ~ r1_tarski(k3_relat_1(sK4),k3_relat_1(sK5)) ),
% 2.60/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_24,plain,
% 2.60/1.00      ( r1_tarski(k3_relat_1(sK4),k3_relat_1(sK5)) != iProver_top ),
% 2.60/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_23,plain,
% 2.60/1.00      ( r1_tarski(sK4,sK5) = iProver_top ),
% 2.60/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(contradiction,plain,
% 2.60/1.00      ( $false ),
% 2.60/1.00      inference(minisat,[status(thm)],[c_3599,c_2828,c_24,c_23]) ).
% 2.60/1.00  
% 2.60/1.00  
% 2.60/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.60/1.00  
% 2.60/1.00  ------                               Statistics
% 2.60/1.00  
% 2.60/1.00  ------ Selected
% 2.60/1.00  
% 2.60/1.00  total_time:                             0.096
% 2.60/1.00  
%------------------------------------------------------------------------------
