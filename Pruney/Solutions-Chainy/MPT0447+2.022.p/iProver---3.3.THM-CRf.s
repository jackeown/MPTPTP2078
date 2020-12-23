%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:43:13 EST 2020

% Result     : Theorem 3.88s
% Output     : CNFRefutation 3.88s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 192 expanded)
%              Number of clauses        :   59 (  64 expanded)
%              Number of leaves         :   22 (  49 expanded)
%              Depth                    :   15
%              Number of atoms          :  348 ( 631 expanded)
%              Number of equality atoms :   79 (  91 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
             => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
     => ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(sK5))
        & r1_tarski(X0,sK5)
        & v1_relat_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
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

fof(f40,plain,
    ( ~ r1_tarski(k3_relat_1(sK4),k3_relat_1(sK5))
    & r1_tarski(sK4,sK5)
    & v1_relat_1(sK5)
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f26,f39,f38])).

fof(f61,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f40])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f55,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f66,plain,(
    ! [X0] :
      ( k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f55,f47])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f64,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f45,f47])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f46,f47])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f27,plain,(
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

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f62,plain,(
    r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f40])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f32])).

fof(f36,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK3(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK2(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0)
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK1(X0,X1)),X0)
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0)
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0)
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK3(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f33,f36,f35,f34])).

fof(f51,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f68,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK3(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f51])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f63,plain,(
    ~ r1_tarski(k3_relat_1(sK4),k3_relat_1(sK5)) ),
    inference(cnf_transformation,[],[f40])).

fof(f60,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_20,negated_conjecture,
    ( v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_742,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_747,plain,
    ( k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1319,plain,
    ( k3_tarski(k2_tarski(k1_relat_1(sK5),k2_relat_1(sK5))) = k3_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_742,c_747])).

cnf(c_4,plain,
    ( r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_755,plain,
    ( r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1471,plain,
    ( r1_tarski(k1_relat_1(sK5),k3_relat_1(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1319,c_755])).

cnf(c_15,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_6,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_224,plain,
    ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15,c_8,c_6])).

cnf(c_225,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(renaming,[status(thm)],[c_224])).

cnf(c_739,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_225])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_756,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2152,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_relat_1(X1),X2) != iProver_top
    | r1_tarski(k1_relat_1(X0),X2) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_739,c_756])).

cnf(c_12757,plain,
    ( r1_tarski(X0,sK5) != iProver_top
    | r1_tarski(k1_relat_1(X0),k3_relat_1(sK5)) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1471,c_2152])).

cnf(c_12827,plain,
    ( r1_tarski(k1_relat_1(sK4),k3_relat_1(sK5)) = iProver_top
    | r1_tarski(sK4,sK5) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_12757])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_5868,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | r1_tarski(k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))),X1) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_8043,plain,
    ( ~ r1_tarski(k1_relat_1(X0),k3_relat_1(sK5))
    | ~ r1_tarski(k2_relat_1(X0),k3_relat_1(sK5))
    | r1_tarski(k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))),k3_relat_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_5868])).

cnf(c_8057,plain,
    ( r1_tarski(k1_relat_1(X0),k3_relat_1(sK5)) != iProver_top
    | r1_tarski(k2_relat_1(X0),k3_relat_1(sK5)) != iProver_top
    | r1_tarski(k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))),k3_relat_1(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8043])).

cnf(c_8059,plain,
    ( r1_tarski(k1_relat_1(sK4),k3_relat_1(sK5)) != iProver_top
    | r1_tarski(k2_relat_1(sK4),k3_relat_1(sK5)) != iProver_top
    | r1_tarski(k3_tarski(k2_tarski(k1_relat_1(sK4),k2_relat_1(sK4))),k3_relat_1(sK5)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_8057])).

cnf(c_16,plain,
    ( r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_19,negated_conjecture,
    ( r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1107,plain,
    ( r2_hidden(X0,sK5)
    | ~ r2_hidden(X0,sK4) ),
    inference(resolution,[status(thm)],[c_2,c_19])).

cnf(c_2383,plain,
    ( r2_hidden(X0,k3_relat_1(sK5))
    | ~ r2_hidden(k4_tarski(X1,X0),sK4)
    | ~ v1_relat_1(sK5) ),
    inference(resolution,[status(thm)],[c_16,c_1107])).

cnf(c_2398,plain,
    ( ~ r2_hidden(k4_tarski(X1,X0),sK4)
    | r2_hidden(X0,k3_relat_1(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2383,c_20])).

cnf(c_2399,plain,
    ( r2_hidden(X0,k3_relat_1(sK5))
    | ~ r2_hidden(k4_tarski(X1,X0),sK4) ),
    inference(renaming,[status(thm)],[c_2398])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(k4_tarski(sK3(X1,X0),X0),X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2537,plain,
    ( r2_hidden(X0,k3_relat_1(sK5))
    | ~ r2_hidden(X0,k2_relat_1(sK4)) ),
    inference(resolution,[status(thm)],[c_2399,c_12])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_2569,plain,
    ( ~ r2_hidden(sK0(X0,k3_relat_1(sK5)),k2_relat_1(sK4))
    | r1_tarski(X0,k3_relat_1(sK5)) ),
    inference(resolution,[status(thm)],[c_2537,c_0])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_2806,plain,
    ( r1_tarski(k2_relat_1(sK4),k3_relat_1(sK5)) ),
    inference(resolution,[status(thm)],[c_2569,c_1])).

cnf(c_2807,plain,
    ( r1_tarski(k2_relat_1(sK4),k3_relat_1(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2806])).

cnf(c_255,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_974,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_relat_1(sK4),k3_relat_1(sK5))
    | k3_relat_1(sK5) != X1
    | k3_relat_1(sK4) != X0 ),
    inference(instantiation,[status(thm)],[c_255])).

cnf(c_1962,plain,
    ( r1_tarski(k3_relat_1(sK4),k3_relat_1(sK5))
    | ~ r1_tarski(k3_tarski(k2_tarski(k1_relat_1(sK4),k2_relat_1(sK4))),X0)
    | k3_relat_1(sK5) != X0
    | k3_relat_1(sK4) != k3_tarski(k2_tarski(k1_relat_1(sK4),k2_relat_1(sK4))) ),
    inference(instantiation,[status(thm)],[c_974])).

cnf(c_2612,plain,
    ( r1_tarski(k3_relat_1(sK4),k3_relat_1(sK5))
    | ~ r1_tarski(k3_tarski(k2_tarski(k1_relat_1(sK4),k2_relat_1(sK4))),k3_relat_1(sK5))
    | k3_relat_1(sK5) != k3_relat_1(sK5)
    | k3_relat_1(sK4) != k3_tarski(k2_tarski(k1_relat_1(sK4),k2_relat_1(sK4))) ),
    inference(instantiation,[status(thm)],[c_1962])).

cnf(c_2613,plain,
    ( k3_relat_1(sK5) != k3_relat_1(sK5)
    | k3_relat_1(sK4) != k3_tarski(k2_tarski(k1_relat_1(sK4),k2_relat_1(sK4)))
    | r1_tarski(k3_relat_1(sK4),k3_relat_1(sK5)) = iProver_top
    | r1_tarski(k3_tarski(k2_tarski(k1_relat_1(sK4),k2_relat_1(sK4))),k3_relat_1(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2612])).

cnf(c_254,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1053,plain,
    ( X0 != X1
    | k3_relat_1(sK4) != X1
    | k3_relat_1(sK4) = X0 ),
    inference(instantiation,[status(thm)],[c_254])).

cnf(c_1274,plain,
    ( X0 != k3_relat_1(sK4)
    | k3_relat_1(sK4) = X0
    | k3_relat_1(sK4) != k3_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1053])).

cnf(c_1645,plain,
    ( k3_relat_1(sK4) != k3_relat_1(sK4)
    | k3_relat_1(sK4) = k3_tarski(k2_tarski(k1_relat_1(sK4),k2_relat_1(sK4)))
    | k3_tarski(k2_tarski(k1_relat_1(sK4),k2_relat_1(sK4))) != k3_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1274])).

cnf(c_253,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1278,plain,
    ( k3_relat_1(sK5) = k3_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_253])).

cnf(c_272,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_253])).

cnf(c_262,plain,
    ( X0 != X1
    | k3_relat_1(X0) = k3_relat_1(X1) ),
    theory(equality)).

cnf(c_270,plain,
    ( k3_relat_1(sK4) = k3_relat_1(sK4)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_262])).

cnf(c_37,plain,
    ( ~ v1_relat_1(sK4)
    | k3_tarski(k2_tarski(k1_relat_1(sK4),k2_relat_1(sK4))) = k3_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_18,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(sK4),k3_relat_1(sK5)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_25,plain,
    ( r1_tarski(k3_relat_1(sK4),k3_relat_1(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_24,plain,
    ( r1_tarski(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_23,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_21,negated_conjecture,
    ( v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f60])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12827,c_8059,c_2807,c_2613,c_1645,c_1278,c_272,c_270,c_37,c_25,c_24,c_23,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:34:26 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.88/1.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.88/1.03  
% 3.88/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.88/1.03  
% 3.88/1.03  ------  iProver source info
% 3.88/1.03  
% 3.88/1.03  git: date: 2020-06-30 10:37:57 +0100
% 3.88/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.88/1.03  git: non_committed_changes: false
% 3.88/1.03  git: last_make_outside_of_git: false
% 3.88/1.03  
% 3.88/1.03  ------ 
% 3.88/1.03  ------ Parsing...
% 3.88/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.88/1.03  
% 3.88/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.88/1.03  
% 3.88/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.88/1.03  
% 3.88/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.88/1.03  ------ Proving...
% 3.88/1.03  ------ Problem Properties 
% 3.88/1.03  
% 3.88/1.03  
% 3.88/1.03  clauses                                 22
% 3.88/1.03  conjectures                             4
% 3.88/1.03  EPR                                     6
% 3.88/1.03  Horn                                    20
% 3.88/1.03  unary                                   5
% 3.88/1.03  binary                                  7
% 3.88/1.03  lits                                    49
% 3.88/1.03  lits eq                                 3
% 3.88/1.03  fd_pure                                 0
% 3.88/1.03  fd_pseudo                               0
% 3.88/1.03  fd_cond                                 0
% 3.88/1.03  fd_pseudo_cond                          2
% 3.88/1.03  AC symbols                              0
% 3.88/1.03  
% 3.88/1.03  ------ Input Options Time Limit: Unbounded
% 3.88/1.03  
% 3.88/1.03  
% 3.88/1.03  ------ 
% 3.88/1.03  Current options:
% 3.88/1.03  ------ 
% 3.88/1.03  
% 3.88/1.03  
% 3.88/1.03  
% 3.88/1.03  
% 3.88/1.03  ------ Proving...
% 3.88/1.03  
% 3.88/1.03  
% 3.88/1.03  % SZS status Theorem for theBenchmark.p
% 3.88/1.03  
% 3.88/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 3.88/1.03  
% 3.88/1.03  fof(f12,conjecture,(
% 3.88/1.03    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 3.88/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/1.03  
% 3.88/1.03  fof(f13,negated_conjecture,(
% 3.88/1.03    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 3.88/1.03    inference(negated_conjecture,[],[f12])).
% 3.88/1.03  
% 3.88/1.03  fof(f25,plain,(
% 3.88/1.03    ? [X0] : (? [X1] : ((~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 3.88/1.03    inference(ennf_transformation,[],[f13])).
% 3.88/1.03  
% 3.88/1.03  fof(f26,plain,(
% 3.88/1.03    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 3.88/1.03    inference(flattening,[],[f25])).
% 3.88/1.03  
% 3.88/1.03  fof(f39,plain,(
% 3.88/1.03    ( ! [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) => (~r1_tarski(k3_relat_1(X0),k3_relat_1(sK5)) & r1_tarski(X0,sK5) & v1_relat_1(sK5))) )),
% 3.88/1.03    introduced(choice_axiom,[])).
% 3.88/1.03  
% 3.88/1.03  fof(f38,plain,(
% 3.88/1.03    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k3_relat_1(sK4),k3_relat_1(X1)) & r1_tarski(sK4,X1) & v1_relat_1(X1)) & v1_relat_1(sK4))),
% 3.88/1.03    introduced(choice_axiom,[])).
% 3.88/1.03  
% 3.88/1.03  fof(f40,plain,(
% 3.88/1.03    (~r1_tarski(k3_relat_1(sK4),k3_relat_1(sK5)) & r1_tarski(sK4,sK5) & v1_relat_1(sK5)) & v1_relat_1(sK4)),
% 3.88/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f26,f39,f38])).
% 3.88/1.03  
% 3.88/1.03  fof(f61,plain,(
% 3.88/1.03    v1_relat_1(sK5)),
% 3.88/1.03    inference(cnf_transformation,[],[f40])).
% 3.88/1.03  
% 3.88/1.03  fof(f9,axiom,(
% 3.88/1.03    ! [X0] : (v1_relat_1(X0) => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0))),
% 3.88/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/1.03  
% 3.88/1.03  fof(f20,plain,(
% 3.88/1.03    ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0))),
% 3.88/1.03    inference(ennf_transformation,[],[f9])).
% 3.88/1.03  
% 3.88/1.03  fof(f55,plain,(
% 3.88/1.03    ( ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.88/1.03    inference(cnf_transformation,[],[f20])).
% 3.88/1.03  
% 3.88/1.03  fof(f5,axiom,(
% 3.88/1.03    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.88/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/1.03  
% 3.88/1.03  fof(f47,plain,(
% 3.88/1.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.88/1.03    inference(cnf_transformation,[],[f5])).
% 3.88/1.03  
% 3.88/1.03  fof(f66,plain,(
% 3.88/1.03    ( ! [X0] : (k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.88/1.03    inference(definition_unfolding,[],[f55,f47])).
% 3.88/1.03  
% 3.88/1.03  fof(f3,axiom,(
% 3.88/1.03    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.88/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/1.03  
% 3.88/1.03  fof(f45,plain,(
% 3.88/1.03    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.88/1.03    inference(cnf_transformation,[],[f3])).
% 3.88/1.03  
% 3.88/1.03  fof(f64,plain,(
% 3.88/1.03    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) )),
% 3.88/1.03    inference(definition_unfolding,[],[f45,f47])).
% 3.88/1.03  
% 3.88/1.03  fof(f10,axiom,(
% 3.88/1.03    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 3.88/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/1.03  
% 3.88/1.03  fof(f21,plain,(
% 3.88/1.03    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.88/1.03    inference(ennf_transformation,[],[f10])).
% 3.88/1.03  
% 3.88/1.03  fof(f22,plain,(
% 3.88/1.03    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.88/1.03    inference(flattening,[],[f21])).
% 3.88/1.03  
% 3.88/1.03  fof(f56,plain,(
% 3.88/1.03    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.88/1.03    inference(cnf_transformation,[],[f22])).
% 3.88/1.03  
% 3.88/1.03  fof(f7,axiom,(
% 3.88/1.03    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.88/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/1.03  
% 3.88/1.03  fof(f19,plain,(
% 3.88/1.03    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.88/1.03    inference(ennf_transformation,[],[f7])).
% 3.88/1.03  
% 3.88/1.03  fof(f50,plain,(
% 3.88/1.03    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.88/1.03    inference(cnf_transformation,[],[f19])).
% 3.88/1.03  
% 3.88/1.03  fof(f6,axiom,(
% 3.88/1.03    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.88/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/1.03  
% 3.88/1.03  fof(f31,plain,(
% 3.88/1.03    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.88/1.03    inference(nnf_transformation,[],[f6])).
% 3.88/1.03  
% 3.88/1.03  fof(f49,plain,(
% 3.88/1.03    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.88/1.03    inference(cnf_transformation,[],[f31])).
% 3.88/1.03  
% 3.88/1.03  fof(f2,axiom,(
% 3.88/1.03    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.88/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/1.03  
% 3.88/1.03  fof(f15,plain,(
% 3.88/1.03    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.88/1.03    inference(ennf_transformation,[],[f2])).
% 3.88/1.03  
% 3.88/1.03  fof(f16,plain,(
% 3.88/1.03    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.88/1.03    inference(flattening,[],[f15])).
% 3.88/1.03  
% 3.88/1.03  fof(f44,plain,(
% 3.88/1.03    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 3.88/1.03    inference(cnf_transformation,[],[f16])).
% 3.88/1.03  
% 3.88/1.03  fof(f4,axiom,(
% 3.88/1.03    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 3.88/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/1.03  
% 3.88/1.03  fof(f17,plain,(
% 3.88/1.03    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 3.88/1.03    inference(ennf_transformation,[],[f4])).
% 3.88/1.03  
% 3.88/1.03  fof(f18,plain,(
% 3.88/1.03    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 3.88/1.03    inference(flattening,[],[f17])).
% 3.88/1.03  
% 3.88/1.03  fof(f46,plain,(
% 3.88/1.03    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 3.88/1.03    inference(cnf_transformation,[],[f18])).
% 3.88/1.03  
% 3.88/1.03  fof(f65,plain,(
% 3.88/1.03    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 3.88/1.03    inference(definition_unfolding,[],[f46,f47])).
% 3.88/1.03  
% 3.88/1.03  fof(f11,axiom,(
% 3.88/1.03    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)))))),
% 3.88/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/1.03  
% 3.88/1.03  fof(f23,plain,(
% 3.88/1.03    ! [X0,X1,X2] : (((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 3.88/1.03    inference(ennf_transformation,[],[f11])).
% 3.88/1.03  
% 3.88/1.03  fof(f24,plain,(
% 3.88/1.03    ! [X0,X1,X2] : ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 3.88/1.03    inference(flattening,[],[f23])).
% 3.88/1.03  
% 3.88/1.03  fof(f59,plain,(
% 3.88/1.03    ( ! [X2,X0,X1] : (r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 3.88/1.03    inference(cnf_transformation,[],[f24])).
% 3.88/1.03  
% 3.88/1.03  fof(f1,axiom,(
% 3.88/1.03    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.88/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/1.03  
% 3.88/1.03  fof(f14,plain,(
% 3.88/1.03    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.88/1.03    inference(ennf_transformation,[],[f1])).
% 3.88/1.03  
% 3.88/1.03  fof(f27,plain,(
% 3.88/1.03    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.88/1.03    inference(nnf_transformation,[],[f14])).
% 3.88/1.03  
% 3.88/1.03  fof(f28,plain,(
% 3.88/1.03    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.88/1.03    inference(rectify,[],[f27])).
% 3.88/1.03  
% 3.88/1.03  fof(f29,plain,(
% 3.88/1.03    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.88/1.03    introduced(choice_axiom,[])).
% 3.88/1.03  
% 3.88/1.03  fof(f30,plain,(
% 3.88/1.03    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.88/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).
% 3.88/1.03  
% 3.88/1.03  fof(f41,plain,(
% 3.88/1.03    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.88/1.03    inference(cnf_transformation,[],[f30])).
% 3.88/1.03  
% 3.88/1.03  fof(f62,plain,(
% 3.88/1.03    r1_tarski(sK4,sK5)),
% 3.88/1.03    inference(cnf_transformation,[],[f40])).
% 3.88/1.03  
% 3.88/1.03  fof(f8,axiom,(
% 3.88/1.03    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 3.88/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/1.03  
% 3.88/1.03  fof(f32,plain,(
% 3.88/1.03    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 3.88/1.03    inference(nnf_transformation,[],[f8])).
% 3.88/1.03  
% 3.88/1.03  fof(f33,plain,(
% 3.88/1.03    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 3.88/1.03    inference(rectify,[],[f32])).
% 3.88/1.03  
% 3.88/1.03  fof(f36,plain,(
% 3.88/1.03    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK3(X0,X5),X5),X0))),
% 3.88/1.03    introduced(choice_axiom,[])).
% 3.88/1.03  
% 3.88/1.03  fof(f35,plain,(
% 3.88/1.03    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) => r2_hidden(k4_tarski(sK2(X0,X1),X2),X0))) )),
% 3.88/1.03    introduced(choice_axiom,[])).
% 3.88/1.03  
% 3.88/1.03  fof(f34,plain,(
% 3.88/1.03    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK1(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 3.88/1.03    introduced(choice_axiom,[])).
% 3.88/1.03  
% 3.88/1.03  fof(f37,plain,(
% 3.88/1.03    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK3(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 3.88/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f33,f36,f35,f34])).
% 3.88/1.03  
% 3.88/1.03  fof(f51,plain,(
% 3.88/1.03    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK3(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 3.88/1.03    inference(cnf_transformation,[],[f37])).
% 3.88/1.03  
% 3.88/1.03  fof(f68,plain,(
% 3.88/1.03    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK3(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 3.88/1.03    inference(equality_resolution,[],[f51])).
% 3.88/1.03  
% 3.88/1.03  fof(f43,plain,(
% 3.88/1.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.88/1.03    inference(cnf_transformation,[],[f30])).
% 3.88/1.03  
% 3.88/1.03  fof(f42,plain,(
% 3.88/1.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.88/1.03    inference(cnf_transformation,[],[f30])).
% 3.88/1.03  
% 3.88/1.03  fof(f63,plain,(
% 3.88/1.03    ~r1_tarski(k3_relat_1(sK4),k3_relat_1(sK5))),
% 3.88/1.03    inference(cnf_transformation,[],[f40])).
% 3.88/1.03  
% 3.88/1.03  fof(f60,plain,(
% 3.88/1.03    v1_relat_1(sK4)),
% 3.88/1.03    inference(cnf_transformation,[],[f40])).
% 3.88/1.03  
% 3.88/1.03  cnf(c_20,negated_conjecture,
% 3.88/1.03      ( v1_relat_1(sK5) ),
% 3.88/1.03      inference(cnf_transformation,[],[f61]) ).
% 3.88/1.03  
% 3.88/1.03  cnf(c_742,plain,
% 3.88/1.03      ( v1_relat_1(sK5) = iProver_top ),
% 3.88/1.03      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.88/1.03  
% 3.88/1.03  cnf(c_13,plain,
% 3.88/1.03      ( ~ v1_relat_1(X0)
% 3.88/1.03      | k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) ),
% 3.88/1.03      inference(cnf_transformation,[],[f66]) ).
% 3.88/1.03  
% 3.88/1.03  cnf(c_747,plain,
% 3.88/1.03      ( k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
% 3.88/1.03      | v1_relat_1(X0) != iProver_top ),
% 3.88/1.03      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.88/1.03  
% 3.88/1.03  cnf(c_1319,plain,
% 3.88/1.03      ( k3_tarski(k2_tarski(k1_relat_1(sK5),k2_relat_1(sK5))) = k3_relat_1(sK5) ),
% 3.88/1.03      inference(superposition,[status(thm)],[c_742,c_747]) ).
% 3.88/1.03  
% 3.88/1.03  cnf(c_4,plain,
% 3.88/1.03      ( r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
% 3.88/1.03      inference(cnf_transformation,[],[f64]) ).
% 3.88/1.03  
% 3.88/1.03  cnf(c_755,plain,
% 3.88/1.03      ( r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) = iProver_top ),
% 3.88/1.03      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.88/1.03  
% 3.88/1.03  cnf(c_1471,plain,
% 3.88/1.03      ( r1_tarski(k1_relat_1(sK5),k3_relat_1(sK5)) = iProver_top ),
% 3.88/1.03      inference(superposition,[status(thm)],[c_1319,c_755]) ).
% 3.88/1.03  
% 3.88/1.03  cnf(c_15,plain,
% 3.88/1.03      ( ~ r1_tarski(X0,X1)
% 3.88/1.03      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 3.88/1.03      | ~ v1_relat_1(X0)
% 3.88/1.03      | ~ v1_relat_1(X1) ),
% 3.88/1.03      inference(cnf_transformation,[],[f56]) ).
% 3.88/1.03  
% 3.88/1.03  cnf(c_8,plain,
% 3.88/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.88/1.03      | ~ v1_relat_1(X1)
% 3.88/1.03      | v1_relat_1(X0) ),
% 3.88/1.03      inference(cnf_transformation,[],[f50]) ).
% 3.88/1.03  
% 3.88/1.03  cnf(c_6,plain,
% 3.88/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.88/1.03      inference(cnf_transformation,[],[f49]) ).
% 3.88/1.03  
% 3.88/1.03  cnf(c_224,plain,
% 3.88/1.03      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 3.88/1.03      | ~ r1_tarski(X0,X1)
% 3.88/1.03      | ~ v1_relat_1(X1) ),
% 3.88/1.03      inference(global_propositional_subsumption,
% 3.88/1.03                [status(thm)],
% 3.88/1.03                [c_15,c_8,c_6]) ).
% 3.88/1.03  
% 3.88/1.03  cnf(c_225,plain,
% 3.88/1.03      ( ~ r1_tarski(X0,X1)
% 3.88/1.03      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 3.88/1.03      | ~ v1_relat_1(X1) ),
% 3.88/1.03      inference(renaming,[status(thm)],[c_224]) ).
% 3.88/1.03  
% 3.88/1.03  cnf(c_739,plain,
% 3.88/1.03      ( r1_tarski(X0,X1) != iProver_top
% 3.88/1.03      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) = iProver_top
% 3.88/1.03      | v1_relat_1(X1) != iProver_top ),
% 3.88/1.03      inference(predicate_to_equality,[status(thm)],[c_225]) ).
% 3.88/1.03  
% 3.88/1.03  cnf(c_3,plain,
% 3.88/1.03      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 3.88/1.03      inference(cnf_transformation,[],[f44]) ).
% 3.88/1.03  
% 3.88/1.03  cnf(c_756,plain,
% 3.88/1.03      ( r1_tarski(X0,X1) != iProver_top
% 3.88/1.03      | r1_tarski(X1,X2) != iProver_top
% 3.88/1.03      | r1_tarski(X0,X2) = iProver_top ),
% 3.88/1.03      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.88/1.03  
% 3.88/1.03  cnf(c_2152,plain,
% 3.88/1.03      ( r1_tarski(X0,X1) != iProver_top
% 3.88/1.03      | r1_tarski(k1_relat_1(X1),X2) != iProver_top
% 3.88/1.03      | r1_tarski(k1_relat_1(X0),X2) = iProver_top
% 3.88/1.03      | v1_relat_1(X1) != iProver_top ),
% 3.88/1.03      inference(superposition,[status(thm)],[c_739,c_756]) ).
% 3.88/1.03  
% 3.88/1.03  cnf(c_12757,plain,
% 3.88/1.03      ( r1_tarski(X0,sK5) != iProver_top
% 3.88/1.03      | r1_tarski(k1_relat_1(X0),k3_relat_1(sK5)) = iProver_top
% 3.88/1.03      | v1_relat_1(sK5) != iProver_top ),
% 3.88/1.03      inference(superposition,[status(thm)],[c_1471,c_2152]) ).
% 3.88/1.03  
% 3.88/1.03  cnf(c_12827,plain,
% 3.88/1.03      ( r1_tarski(k1_relat_1(sK4),k3_relat_1(sK5)) = iProver_top
% 3.88/1.03      | r1_tarski(sK4,sK5) != iProver_top
% 3.88/1.03      | v1_relat_1(sK5) != iProver_top ),
% 3.88/1.03      inference(instantiation,[status(thm)],[c_12757]) ).
% 3.88/1.03  
% 3.88/1.03  cnf(c_5,plain,
% 3.88/1.03      ( ~ r1_tarski(X0,X1)
% 3.88/1.03      | ~ r1_tarski(X2,X1)
% 3.88/1.03      | r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) ),
% 3.88/1.03      inference(cnf_transformation,[],[f65]) ).
% 3.88/1.03  
% 3.88/1.03  cnf(c_5868,plain,
% 3.88/1.03      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 3.88/1.03      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.88/1.03      | r1_tarski(k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))),X1) ),
% 3.88/1.03      inference(instantiation,[status(thm)],[c_5]) ).
% 3.88/1.03  
% 3.88/1.03  cnf(c_8043,plain,
% 3.88/1.03      ( ~ r1_tarski(k1_relat_1(X0),k3_relat_1(sK5))
% 3.88/1.03      | ~ r1_tarski(k2_relat_1(X0),k3_relat_1(sK5))
% 3.88/1.03      | r1_tarski(k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))),k3_relat_1(sK5)) ),
% 3.88/1.03      inference(instantiation,[status(thm)],[c_5868]) ).
% 3.88/1.03  
% 3.88/1.03  cnf(c_8057,plain,
% 3.88/1.03      ( r1_tarski(k1_relat_1(X0),k3_relat_1(sK5)) != iProver_top
% 3.88/1.03      | r1_tarski(k2_relat_1(X0),k3_relat_1(sK5)) != iProver_top
% 3.88/1.03      | r1_tarski(k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))),k3_relat_1(sK5)) = iProver_top ),
% 3.88/1.03      inference(predicate_to_equality,[status(thm)],[c_8043]) ).
% 3.88/1.03  
% 3.88/1.03  cnf(c_8059,plain,
% 3.88/1.03      ( r1_tarski(k1_relat_1(sK4),k3_relat_1(sK5)) != iProver_top
% 3.88/1.03      | r1_tarski(k2_relat_1(sK4),k3_relat_1(sK5)) != iProver_top
% 3.88/1.03      | r1_tarski(k3_tarski(k2_tarski(k1_relat_1(sK4),k2_relat_1(sK4))),k3_relat_1(sK5)) = iProver_top ),
% 3.88/1.03      inference(instantiation,[status(thm)],[c_8057]) ).
% 3.88/1.03  
% 3.88/1.03  cnf(c_16,plain,
% 3.88/1.03      ( r2_hidden(X0,k3_relat_1(X1))
% 3.88/1.03      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 3.88/1.03      | ~ v1_relat_1(X1) ),
% 3.88/1.03      inference(cnf_transformation,[],[f59]) ).
% 3.88/1.03  
% 3.88/1.03  cnf(c_2,plain,
% 3.88/1.03      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.88/1.03      inference(cnf_transformation,[],[f41]) ).
% 3.88/1.03  
% 3.88/1.03  cnf(c_19,negated_conjecture,
% 3.88/1.03      ( r1_tarski(sK4,sK5) ),
% 3.88/1.03      inference(cnf_transformation,[],[f62]) ).
% 3.88/1.03  
% 3.88/1.03  cnf(c_1107,plain,
% 3.88/1.03      ( r2_hidden(X0,sK5) | ~ r2_hidden(X0,sK4) ),
% 3.88/1.03      inference(resolution,[status(thm)],[c_2,c_19]) ).
% 3.88/1.03  
% 3.88/1.03  cnf(c_2383,plain,
% 3.88/1.03      ( r2_hidden(X0,k3_relat_1(sK5))
% 3.88/1.03      | ~ r2_hidden(k4_tarski(X1,X0),sK4)
% 3.88/1.03      | ~ v1_relat_1(sK5) ),
% 3.88/1.03      inference(resolution,[status(thm)],[c_16,c_1107]) ).
% 3.88/1.03  
% 3.88/1.03  cnf(c_2398,plain,
% 3.88/1.03      ( ~ r2_hidden(k4_tarski(X1,X0),sK4)
% 3.88/1.03      | r2_hidden(X0,k3_relat_1(sK5)) ),
% 3.88/1.03      inference(global_propositional_subsumption,
% 3.88/1.03                [status(thm)],
% 3.88/1.03                [c_2383,c_20]) ).
% 3.88/1.03  
% 3.88/1.03  cnf(c_2399,plain,
% 3.88/1.03      ( r2_hidden(X0,k3_relat_1(sK5))
% 3.88/1.03      | ~ r2_hidden(k4_tarski(X1,X0),sK4) ),
% 3.88/1.03      inference(renaming,[status(thm)],[c_2398]) ).
% 3.88/1.03  
% 3.88/1.03  cnf(c_12,plain,
% 3.88/1.03      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 3.88/1.03      | r2_hidden(k4_tarski(sK3(X1,X0),X0),X1) ),
% 3.88/1.03      inference(cnf_transformation,[],[f68]) ).
% 3.88/1.03  
% 3.88/1.03  cnf(c_2537,plain,
% 3.88/1.03      ( r2_hidden(X0,k3_relat_1(sK5)) | ~ r2_hidden(X0,k2_relat_1(sK4)) ),
% 3.88/1.03      inference(resolution,[status(thm)],[c_2399,c_12]) ).
% 3.88/1.03  
% 3.88/1.03  cnf(c_0,plain,
% 3.88/1.03      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.88/1.03      inference(cnf_transformation,[],[f43]) ).
% 3.88/1.03  
% 3.88/1.03  cnf(c_2569,plain,
% 3.88/1.03      ( ~ r2_hidden(sK0(X0,k3_relat_1(sK5)),k2_relat_1(sK4))
% 3.88/1.03      | r1_tarski(X0,k3_relat_1(sK5)) ),
% 3.88/1.03      inference(resolution,[status(thm)],[c_2537,c_0]) ).
% 3.88/1.03  
% 3.88/1.03  cnf(c_1,plain,
% 3.88/1.03      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.88/1.03      inference(cnf_transformation,[],[f42]) ).
% 3.88/1.03  
% 3.88/1.03  cnf(c_2806,plain,
% 3.88/1.03      ( r1_tarski(k2_relat_1(sK4),k3_relat_1(sK5)) ),
% 3.88/1.03      inference(resolution,[status(thm)],[c_2569,c_1]) ).
% 3.88/1.03  
% 3.88/1.03  cnf(c_2807,plain,
% 3.88/1.03      ( r1_tarski(k2_relat_1(sK4),k3_relat_1(sK5)) = iProver_top ),
% 3.88/1.03      inference(predicate_to_equality,[status(thm)],[c_2806]) ).
% 3.88/1.03  
% 3.88/1.03  cnf(c_255,plain,
% 3.88/1.03      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.88/1.03      theory(equality) ).
% 3.88/1.03  
% 3.88/1.03  cnf(c_974,plain,
% 3.88/1.03      ( ~ r1_tarski(X0,X1)
% 3.88/1.03      | r1_tarski(k3_relat_1(sK4),k3_relat_1(sK5))
% 3.88/1.03      | k3_relat_1(sK5) != X1
% 3.88/1.03      | k3_relat_1(sK4) != X0 ),
% 3.88/1.03      inference(instantiation,[status(thm)],[c_255]) ).
% 3.88/1.03  
% 3.88/1.03  cnf(c_1962,plain,
% 3.88/1.03      ( r1_tarski(k3_relat_1(sK4),k3_relat_1(sK5))
% 3.88/1.03      | ~ r1_tarski(k3_tarski(k2_tarski(k1_relat_1(sK4),k2_relat_1(sK4))),X0)
% 3.88/1.03      | k3_relat_1(sK5) != X0
% 3.88/1.03      | k3_relat_1(sK4) != k3_tarski(k2_tarski(k1_relat_1(sK4),k2_relat_1(sK4))) ),
% 3.88/1.03      inference(instantiation,[status(thm)],[c_974]) ).
% 3.88/1.03  
% 3.88/1.03  cnf(c_2612,plain,
% 3.88/1.03      ( r1_tarski(k3_relat_1(sK4),k3_relat_1(sK5))
% 3.88/1.03      | ~ r1_tarski(k3_tarski(k2_tarski(k1_relat_1(sK4),k2_relat_1(sK4))),k3_relat_1(sK5))
% 3.88/1.03      | k3_relat_1(sK5) != k3_relat_1(sK5)
% 3.88/1.03      | k3_relat_1(sK4) != k3_tarski(k2_tarski(k1_relat_1(sK4),k2_relat_1(sK4))) ),
% 3.88/1.03      inference(instantiation,[status(thm)],[c_1962]) ).
% 3.88/1.03  
% 3.88/1.03  cnf(c_2613,plain,
% 3.88/1.03      ( k3_relat_1(sK5) != k3_relat_1(sK5)
% 3.88/1.03      | k3_relat_1(sK4) != k3_tarski(k2_tarski(k1_relat_1(sK4),k2_relat_1(sK4)))
% 3.88/1.03      | r1_tarski(k3_relat_1(sK4),k3_relat_1(sK5)) = iProver_top
% 3.88/1.03      | r1_tarski(k3_tarski(k2_tarski(k1_relat_1(sK4),k2_relat_1(sK4))),k3_relat_1(sK5)) != iProver_top ),
% 3.88/1.03      inference(predicate_to_equality,[status(thm)],[c_2612]) ).
% 3.88/1.03  
% 3.88/1.03  cnf(c_254,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.88/1.03  
% 3.88/1.03  cnf(c_1053,plain,
% 3.88/1.03      ( X0 != X1 | k3_relat_1(sK4) != X1 | k3_relat_1(sK4) = X0 ),
% 3.88/1.03      inference(instantiation,[status(thm)],[c_254]) ).
% 3.88/1.03  
% 3.88/1.03  cnf(c_1274,plain,
% 3.88/1.03      ( X0 != k3_relat_1(sK4)
% 3.88/1.03      | k3_relat_1(sK4) = X0
% 3.88/1.03      | k3_relat_1(sK4) != k3_relat_1(sK4) ),
% 3.88/1.03      inference(instantiation,[status(thm)],[c_1053]) ).
% 3.88/1.03  
% 3.88/1.03  cnf(c_1645,plain,
% 3.88/1.03      ( k3_relat_1(sK4) != k3_relat_1(sK4)
% 3.88/1.03      | k3_relat_1(sK4) = k3_tarski(k2_tarski(k1_relat_1(sK4),k2_relat_1(sK4)))
% 3.88/1.03      | k3_tarski(k2_tarski(k1_relat_1(sK4),k2_relat_1(sK4))) != k3_relat_1(sK4) ),
% 3.88/1.03      inference(instantiation,[status(thm)],[c_1274]) ).
% 3.88/1.03  
% 3.88/1.03  cnf(c_253,plain,( X0 = X0 ),theory(equality) ).
% 3.88/1.03  
% 3.88/1.03  cnf(c_1278,plain,
% 3.88/1.03      ( k3_relat_1(sK5) = k3_relat_1(sK5) ),
% 3.88/1.03      inference(instantiation,[status(thm)],[c_253]) ).
% 3.88/1.03  
% 3.88/1.03  cnf(c_272,plain,
% 3.88/1.03      ( sK4 = sK4 ),
% 3.88/1.03      inference(instantiation,[status(thm)],[c_253]) ).
% 3.88/1.03  
% 3.88/1.03  cnf(c_262,plain,
% 3.88/1.03      ( X0 != X1 | k3_relat_1(X0) = k3_relat_1(X1) ),
% 3.88/1.03      theory(equality) ).
% 3.88/1.03  
% 3.88/1.03  cnf(c_270,plain,
% 3.88/1.03      ( k3_relat_1(sK4) = k3_relat_1(sK4) | sK4 != sK4 ),
% 3.88/1.03      inference(instantiation,[status(thm)],[c_262]) ).
% 3.88/1.03  
% 3.88/1.03  cnf(c_37,plain,
% 3.88/1.03      ( ~ v1_relat_1(sK4)
% 3.88/1.03      | k3_tarski(k2_tarski(k1_relat_1(sK4),k2_relat_1(sK4))) = k3_relat_1(sK4) ),
% 3.88/1.03      inference(instantiation,[status(thm)],[c_13]) ).
% 3.88/1.03  
% 3.88/1.03  cnf(c_18,negated_conjecture,
% 3.88/1.03      ( ~ r1_tarski(k3_relat_1(sK4),k3_relat_1(sK5)) ),
% 3.88/1.03      inference(cnf_transformation,[],[f63]) ).
% 3.88/1.03  
% 3.88/1.03  cnf(c_25,plain,
% 3.88/1.03      ( r1_tarski(k3_relat_1(sK4),k3_relat_1(sK5)) != iProver_top ),
% 3.88/1.03      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.88/1.03  
% 3.88/1.03  cnf(c_24,plain,
% 3.88/1.03      ( r1_tarski(sK4,sK5) = iProver_top ),
% 3.88/1.03      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.88/1.03  
% 3.88/1.03  cnf(c_23,plain,
% 3.88/1.03      ( v1_relat_1(sK5) = iProver_top ),
% 3.88/1.03      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.88/1.03  
% 3.88/1.03  cnf(c_21,negated_conjecture,
% 3.88/1.03      ( v1_relat_1(sK4) ),
% 3.88/1.03      inference(cnf_transformation,[],[f60]) ).
% 3.88/1.03  
% 3.88/1.03  cnf(contradiction,plain,
% 3.88/1.03      ( $false ),
% 3.88/1.03      inference(minisat,
% 3.88/1.03                [status(thm)],
% 3.88/1.03                [c_12827,c_8059,c_2807,c_2613,c_1645,c_1278,c_272,c_270,
% 3.88/1.03                 c_37,c_25,c_24,c_23,c_21]) ).
% 3.88/1.03  
% 3.88/1.03  
% 3.88/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 3.88/1.03  
% 3.88/1.03  ------                               Statistics
% 3.88/1.03  
% 3.88/1.03  ------ Selected
% 3.88/1.03  
% 3.88/1.03  total_time:                             0.505
% 3.88/1.03  
%------------------------------------------------------------------------------
