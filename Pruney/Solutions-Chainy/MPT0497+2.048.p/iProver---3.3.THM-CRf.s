%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:44:55 EST 2020

% Result     : Theorem 3.93s
% Output     : CNFRefutation 3.93s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 701 expanded)
%              Number of clauses        :   73 ( 264 expanded)
%              Number of leaves         :   15 ( 123 expanded)
%              Depth                    :   28
%              Number of atoms          :  342 (2228 expanded)
%              Number of equality atoms :  168 ( 926 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f26])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k7_relat_1(X1,X0)
        <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <~> r1_xboole_0(k1_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f32,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k7_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k7_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f33,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k7_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k7_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f34,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 = k7_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k1_relat_1(sK2),sK1)
        | k1_xboole_0 != k7_relat_1(sK2,sK1) )
      & ( r1_xboole_0(k1_relat_1(sK2),sK1)
        | k1_xboole_0 = k7_relat_1(sK2,sK1) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ( ~ r1_xboole_0(k1_relat_1(sK2),sK1)
      | k1_xboole_0 != k7_relat_1(sK2,sK1) )
    & ( r1_xboole_0(k1_relat_1(sK2),sK1)
      | k1_xboole_0 = k7_relat_1(sK2,sK1) )
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f33,f34])).

fof(f56,plain,
    ( r1_xboole_0(k1_relat_1(sK2),sK1)
    | k1_xboole_0 = k7_relat_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f55,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f47,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f28])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f59,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f44])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f9,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f57,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK2),sK1)
    | k1_xboole_0 != k7_relat_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1242,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1243,plain,
    ( r2_hidden(sK0(X0,X1),X1) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_17,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1234,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_18,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1233,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_20,negated_conjecture,
    ( r1_xboole_0(k1_relat_1(sK2),sK1)
    | k1_xboole_0 = k7_relat_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1231,plain,
    ( k1_xboole_0 = k7_relat_1(sK2,sK1)
    | r1_xboole_0(k1_relat_1(sK2),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_0,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1245,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1495,plain,
    ( k7_relat_1(sK2,sK1) = k1_xboole_0
    | r1_xboole_0(sK1,k1_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1231,c_1245])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | ~ r1_xboole_0(X2,X1)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1240,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_xboole_0(X2,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1712,plain,
    ( k7_relat_1(sK2,sK1) = k1_xboole_0
    | k1_xboole_0 = X0
    | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1495,c_1240])).

cnf(c_1792,plain,
    ( k7_relat_1(sK2,sK1) = k1_xboole_0
    | k1_relat_1(k7_relat_1(sK2,X0)) = k1_xboole_0
    | r1_tarski(k1_relat_1(k7_relat_1(sK2,X0)),sK1) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1233,c_1712])).

cnf(c_21,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_22,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1822,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK2,X0)),sK1) != iProver_top
    | k1_relat_1(k7_relat_1(sK2,X0)) = k1_xboole_0
    | k7_relat_1(sK2,sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1792,c_22])).

cnf(c_1823,plain,
    ( k7_relat_1(sK2,sK1) = k1_xboole_0
    | k1_relat_1(k7_relat_1(sK2,X0)) = k1_xboole_0
    | r1_tarski(k1_relat_1(k7_relat_1(sK2,X0)),sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_1822])).

cnf(c_1831,plain,
    ( k7_relat_1(sK2,sK1) = k1_xboole_0
    | k1_relat_1(k7_relat_1(sK2,sK1)) = k1_xboole_0
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1234,c_1823])).

cnf(c_1832,plain,
    ( ~ v1_relat_1(sK2)
    | k7_relat_1(sK2,sK1) = k1_xboole_0
    | k1_relat_1(k7_relat_1(sK2,sK1)) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1831])).

cnf(c_1908,plain,
    ( k1_relat_1(k7_relat_1(sK2,sK1)) = k1_xboole_0
    | k7_relat_1(sK2,sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1831,c_21,c_1832])).

cnf(c_1909,plain,
    ( k7_relat_1(sK2,sK1) = k1_xboole_0
    | k1_relat_1(k7_relat_1(sK2,sK1)) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_1908])).

cnf(c_1230,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1239,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1238,plain,
    ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1584,plain,
    ( k3_xboole_0(k7_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(k7_relat_1(X0,X1)),k2_relat_1(k7_relat_1(X0,X1)))) = k7_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1239,c_1238])).

cnf(c_2346,plain,
    ( k3_xboole_0(k7_relat_1(sK2,X0),k2_zfmisc_1(k1_relat_1(k7_relat_1(sK2,X0)),k2_relat_1(k7_relat_1(sK2,X0)))) = k7_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_1230,c_1584])).

cnf(c_2386,plain,
    ( k7_relat_1(sK2,sK1) = k1_xboole_0
    | k3_xboole_0(k7_relat_1(sK2,sK1),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k7_relat_1(sK2,sK1)))) = k7_relat_1(sK2,sK1) ),
    inference(superposition,[status(thm)],[c_1909,c_2346])).

cnf(c_4,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_8,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2387,plain,
    ( k7_relat_1(sK2,sK1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2386,c_4,c_8])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(X2))
    | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1237,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_relat_1(X2)) != iProver_top
    | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) = iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2398,plain,
    ( r2_hidden(X0,k1_relat_1(sK2)) != iProver_top
    | r2_hidden(X0,k1_relat_1(k1_xboole_0)) = iProver_top
    | r2_hidden(X0,sK1) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2387,c_1237])).

cnf(c_13,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2438,plain,
    ( r2_hidden(X0,k1_relat_1(sK2)) != iProver_top
    | r2_hidden(X0,sK1) != iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2398,c_13])).

cnf(c_2396,plain,
    ( v1_relat_1(sK2) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2387,c_1239])).

cnf(c_15,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1236,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
    | r2_hidden(X0,k1_relat_1(k7_relat_1(X1,X2))) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2400,plain,
    ( r2_hidden(X0,k1_relat_1(sK2)) = iProver_top
    | r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2387,c_1236])).

cnf(c_2423,plain,
    ( r2_hidden(X0,k1_relat_1(sK2)) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2400,c_13])).

cnf(c_2986,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2423,c_22])).

cnf(c_2987,plain,
    ( r2_hidden(X0,k1_relat_1(sK2)) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2986])).

cnf(c_5,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1241,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1494,plain,
    ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1241,c_1245])).

cnf(c_1,negated_conjecture,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1244,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r1_xboole_0(X2,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1843,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X0,k1_relat_1(X3)) != iProver_top
    | r1_xboole_0(X2,k1_relat_1(k7_relat_1(X3,X1))) != iProver_top
    | v1_relat_1(X3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1237,c_1244])).

cnf(c_2014,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_relat_1(X2)) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1494,c_1843])).

cnf(c_2048,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_2014])).

cnf(c_2994,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2987,c_2048])).

cnf(c_3617,plain,
    ( r2_hidden(X0,k1_relat_1(sK2)) != iProver_top
    | r2_hidden(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2438,c_22,c_2396,c_2994])).

cnf(c_3625,plain,
    ( r2_hidden(sK0(X0,k1_relat_1(sK2)),sK1) != iProver_top
    | r1_xboole_0(X0,k1_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1243,c_3617])).

cnf(c_4502,plain,
    ( r1_xboole_0(sK1,k1_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1242,c_3625])).

cnf(c_19,negated_conjecture,
    ( ~ r1_xboole_0(k1_relat_1(sK2),sK1)
    | k1_xboole_0 != k7_relat_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1232,plain,
    ( k1_xboole_0 != k7_relat_1(sK2,sK1)
    | r1_xboole_0(k1_relat_1(sK2),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2390,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k1_relat_1(sK2),sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2387,c_1232])).

cnf(c_2391,plain,
    ( r1_xboole_0(k1_relat_1(sK2),sK1) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2390])).

cnf(c_1369,plain,
    ( ~ r2_hidden(sK0(X0,X1),X0)
    | ~ r2_hidden(sK0(X0,X1),X2)
    | ~ r1_xboole_0(X2,X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1448,plain,
    ( ~ r2_hidden(sK0(k1_relat_1(sK2),sK1),X0)
    | ~ r2_hidden(sK0(k1_relat_1(sK2),sK1),k1_relat_1(sK2))
    | ~ r1_xboole_0(X0,k1_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_1369])).

cnf(c_1770,plain,
    ( ~ r2_hidden(sK0(k1_relat_1(sK2),sK1),k1_relat_1(sK2))
    | ~ r2_hidden(sK0(k1_relat_1(sK2),sK1),sK1)
    | ~ r1_xboole_0(sK1,k1_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_1448])).

cnf(c_1771,plain,
    ( r2_hidden(sK0(k1_relat_1(sK2),sK1),k1_relat_1(sK2)) != iProver_top
    | r2_hidden(sK0(k1_relat_1(sK2),sK1),sK1) != iProver_top
    | r1_xboole_0(sK1,k1_relat_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1770])).

cnf(c_1375,plain,
    ( r2_hidden(sK0(k1_relat_1(sK2),sK1),sK1)
    | r1_xboole_0(k1_relat_1(sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1379,plain,
    ( r2_hidden(sK0(k1_relat_1(sK2),sK1),sK1) = iProver_top
    | r1_xboole_0(k1_relat_1(sK2),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1375])).

cnf(c_1376,plain,
    ( r2_hidden(sK0(k1_relat_1(sK2),sK1),k1_relat_1(sK2))
    | r1_xboole_0(k1_relat_1(sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1377,plain,
    ( r2_hidden(sK0(k1_relat_1(sK2),sK1),k1_relat_1(sK2)) = iProver_top
    | r1_xboole_0(k1_relat_1(sK2),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1376])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4502,c_2391,c_1771,c_1379,c_1377])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:51:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.19/0.35  % Running in FOF mode
% 3.93/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.93/1.00  
% 3.93/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.93/1.00  
% 3.93/1.00  ------  iProver source info
% 3.93/1.00  
% 3.93/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.93/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.93/1.00  git: non_committed_changes: false
% 3.93/1.00  git: last_make_outside_of_git: false
% 3.93/1.00  
% 3.93/1.00  ------ 
% 3.93/1.00  ------ Parsing...
% 3.93/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.93/1.00  
% 3.93/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.93/1.00  
% 3.93/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.93/1.00  
% 3.93/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.93/1.00  ------ Proving...
% 3.93/1.00  ------ Problem Properties 
% 3.93/1.00  
% 3.93/1.00  
% 3.93/1.00  clauses                                 22
% 3.93/1.00  conjectures                             4
% 3.93/1.00  EPR                                     5
% 3.93/1.00  Horn                                    18
% 3.93/1.00  unary                                   7
% 3.93/1.00  binary                                  9
% 3.93/1.00  lits                                    45
% 3.93/1.00  lits eq                                 12
% 3.93/1.00  fd_pure                                 0
% 3.93/1.00  fd_pseudo                               0
% 3.93/1.00  fd_cond                                 2
% 3.93/1.00  fd_pseudo_cond                          0
% 3.93/1.00  AC symbols                              0
% 3.93/1.00  
% 3.93/1.00  ------ Input Options Time Limit: Unbounded
% 3.93/1.00  
% 3.93/1.00  
% 3.93/1.00  
% 3.93/1.00  
% 3.93/1.00  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.93/1.00  Current options:
% 3.93/1.00  ------ 
% 3.93/1.00  
% 3.93/1.00  
% 3.93/1.00  
% 3.93/1.00  
% 3.93/1.00  ------ Proving...
% 3.93/1.00  
% 3.93/1.00  
% 3.93/1.00  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.93/1.00  
% 3.93/1.00  ------ Proving...
% 3.93/1.00  
% 3.93/1.00  
% 3.93/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.93/1.00  
% 3.93/1.00  ------ Proving...
% 3.93/1.00  
% 3.93/1.00  
% 3.93/1.00  % SZS status Theorem for theBenchmark.p
% 3.93/1.00  
% 3.93/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.93/1.00  
% 3.93/1.00  fof(f2,axiom,(
% 3.93/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.93/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.93/1.00  
% 3.93/1.00  fof(f15,plain,(
% 3.93/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.93/1.00    inference(rectify,[],[f2])).
% 3.93/1.00  
% 3.93/1.00  fof(f17,plain,(
% 3.93/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 3.93/1.00    inference(ennf_transformation,[],[f15])).
% 3.93/1.00  
% 3.93/1.00  fof(f26,plain,(
% 3.93/1.00    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.93/1.00    introduced(choice_axiom,[])).
% 3.93/1.00  
% 3.93/1.00  fof(f27,plain,(
% 3.93/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 3.93/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f26])).
% 3.93/1.00  
% 3.93/1.00  fof(f37,plain,(
% 3.93/1.00    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 3.93/1.00    inference(cnf_transformation,[],[f27])).
% 3.93/1.00  
% 3.93/1.00  fof(f38,plain,(
% 3.93/1.00    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 3.93/1.00    inference(cnf_transformation,[],[f27])).
% 3.93/1.00  
% 3.93/1.00  fof(f11,axiom,(
% 3.93/1.00    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 3.93/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.93/1.00  
% 3.93/1.00  fof(f23,plain,(
% 3.93/1.00    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 3.93/1.00    inference(ennf_transformation,[],[f11])).
% 3.93/1.00  
% 3.93/1.00  fof(f53,plain,(
% 3.93/1.00    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 3.93/1.00    inference(cnf_transformation,[],[f23])).
% 3.93/1.00  
% 3.93/1.00  fof(f12,axiom,(
% 3.93/1.00    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)))),
% 3.93/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.93/1.00  
% 3.93/1.00  fof(f24,plain,(
% 3.93/1.00    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.93/1.00    inference(ennf_transformation,[],[f12])).
% 3.93/1.00  
% 3.93/1.00  fof(f54,plain,(
% 3.93/1.00    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.93/1.00    inference(cnf_transformation,[],[f24])).
% 3.93/1.00  
% 3.93/1.00  fof(f13,conjecture,(
% 3.93/1.00    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 3.93/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.93/1.00  
% 3.93/1.00  fof(f14,negated_conjecture,(
% 3.93/1.00    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 3.93/1.00    inference(negated_conjecture,[],[f13])).
% 3.93/1.00  
% 3.93/1.00  fof(f25,plain,(
% 3.93/1.00    ? [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <~> r1_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 3.93/1.00    inference(ennf_transformation,[],[f14])).
% 3.93/1.00  
% 3.93/1.00  fof(f32,plain,(
% 3.93/1.00    ? [X0,X1] : (((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0))) & v1_relat_1(X1))),
% 3.93/1.00    inference(nnf_transformation,[],[f25])).
% 3.93/1.00  
% 3.93/1.00  fof(f33,plain,(
% 3.93/1.00    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0)) & v1_relat_1(X1))),
% 3.93/1.00    inference(flattening,[],[f32])).
% 3.93/1.00  
% 3.93/1.00  fof(f34,plain,(
% 3.93/1.00    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k1_relat_1(sK2),sK1) | k1_xboole_0 != k7_relat_1(sK2,sK1)) & (r1_xboole_0(k1_relat_1(sK2),sK1) | k1_xboole_0 = k7_relat_1(sK2,sK1)) & v1_relat_1(sK2))),
% 3.93/1.00    introduced(choice_axiom,[])).
% 3.93/1.00  
% 3.93/1.00  fof(f35,plain,(
% 3.93/1.00    (~r1_xboole_0(k1_relat_1(sK2),sK1) | k1_xboole_0 != k7_relat_1(sK2,sK1)) & (r1_xboole_0(k1_relat_1(sK2),sK1) | k1_xboole_0 = k7_relat_1(sK2,sK1)) & v1_relat_1(sK2)),
% 3.93/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f33,f34])).
% 3.93/1.00  
% 3.93/1.00  fof(f56,plain,(
% 3.93/1.00    r1_xboole_0(k1_relat_1(sK2),sK1) | k1_xboole_0 = k7_relat_1(sK2,sK1)),
% 3.93/1.00    inference(cnf_transformation,[],[f35])).
% 3.93/1.00  
% 3.93/1.00  fof(f1,axiom,(
% 3.93/1.00    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 3.93/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.93/1.00  
% 3.93/1.00  fof(f16,plain,(
% 3.93/1.00    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 3.93/1.00    inference(ennf_transformation,[],[f1])).
% 3.93/1.00  
% 3.93/1.00  fof(f36,plain,(
% 3.93/1.00    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 3.93/1.00    inference(cnf_transformation,[],[f16])).
% 3.93/1.00  
% 3.93/1.00  fof(f5,axiom,(
% 3.93/1.00    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k1_xboole_0 = X0)),
% 3.93/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.93/1.00  
% 3.93/1.00  fof(f18,plain,(
% 3.93/1.00    ! [X0,X1,X2] : (k1_xboole_0 = X0 | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 3.93/1.00    inference(ennf_transformation,[],[f5])).
% 3.93/1.00  
% 3.93/1.00  fof(f19,plain,(
% 3.93/1.00    ! [X0,X1,X2] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 3.93/1.00    inference(flattening,[],[f18])).
% 3.93/1.00  
% 3.93/1.00  fof(f42,plain,(
% 3.93/1.00    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 3.93/1.00    inference(cnf_transformation,[],[f19])).
% 3.93/1.00  
% 3.93/1.00  fof(f55,plain,(
% 3.93/1.00    v1_relat_1(sK2)),
% 3.93/1.00    inference(cnf_transformation,[],[f35])).
% 3.93/1.00  
% 3.93/1.00  fof(f7,axiom,(
% 3.93/1.00    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 3.93/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.93/1.00  
% 3.93/1.00  fof(f20,plain,(
% 3.93/1.00    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 3.93/1.00    inference(ennf_transformation,[],[f7])).
% 3.93/1.00  
% 3.93/1.00  fof(f46,plain,(
% 3.93/1.00    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 3.93/1.00    inference(cnf_transformation,[],[f20])).
% 3.93/1.00  
% 3.93/1.00  fof(f8,axiom,(
% 3.93/1.00    ! [X0] : (v1_relat_1(X0) => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0)),
% 3.93/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.93/1.00  
% 3.93/1.00  fof(f21,plain,(
% 3.93/1.00    ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 3.93/1.00    inference(ennf_transformation,[],[f8])).
% 3.93/1.00  
% 3.93/1.00  fof(f47,plain,(
% 3.93/1.00    ( ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 3.93/1.00    inference(cnf_transformation,[],[f21])).
% 3.93/1.00  
% 3.93/1.00  fof(f3,axiom,(
% 3.93/1.00    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 3.93/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.93/1.00  
% 3.93/1.00  fof(f40,plain,(
% 3.93/1.00    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 3.93/1.00    inference(cnf_transformation,[],[f3])).
% 3.93/1.00  
% 3.93/1.00  fof(f6,axiom,(
% 3.93/1.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.93/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.93/1.00  
% 3.93/1.00  fof(f28,plain,(
% 3.93/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.93/1.00    inference(nnf_transformation,[],[f6])).
% 3.93/1.00  
% 3.93/1.00  fof(f29,plain,(
% 3.93/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.93/1.00    inference(flattening,[],[f28])).
% 3.93/1.00  
% 3.93/1.00  fof(f44,plain,(
% 3.93/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.93/1.00    inference(cnf_transformation,[],[f29])).
% 3.93/1.00  
% 3.93/1.00  fof(f59,plain,(
% 3.93/1.00    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.93/1.00    inference(equality_resolution,[],[f44])).
% 3.93/1.00  
% 3.93/1.00  fof(f10,axiom,(
% 3.93/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 3.93/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.93/1.00  
% 3.93/1.00  fof(f22,plain,(
% 3.93/1.00    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 3.93/1.00    inference(ennf_transformation,[],[f10])).
% 3.93/1.00  
% 3.93/1.00  fof(f30,plain,(
% 3.93/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | (~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1))) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 3.93/1.00    inference(nnf_transformation,[],[f22])).
% 3.93/1.00  
% 3.93/1.00  fof(f31,plain,(
% 3.93/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1)) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 3.93/1.00    inference(flattening,[],[f30])).
% 3.93/1.00  
% 3.93/1.00  fof(f52,plain,(
% 3.93/1.00    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1) | ~v1_relat_1(X2)) )),
% 3.93/1.00    inference(cnf_transformation,[],[f31])).
% 3.93/1.00  
% 3.93/1.00  fof(f9,axiom,(
% 3.93/1.00    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.93/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.93/1.00  
% 3.93/1.00  fof(f48,plain,(
% 3.93/1.00    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.93/1.00    inference(cnf_transformation,[],[f9])).
% 3.93/1.00  
% 3.93/1.00  fof(f51,plain,(
% 3.93/1.00    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~v1_relat_1(X2)) )),
% 3.93/1.00    inference(cnf_transformation,[],[f31])).
% 3.93/1.00  
% 3.93/1.00  fof(f4,axiom,(
% 3.93/1.00    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 3.93/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.93/1.00  
% 3.93/1.00  fof(f41,plain,(
% 3.93/1.00    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 3.93/1.00    inference(cnf_transformation,[],[f4])).
% 3.93/1.00  
% 3.93/1.00  fof(f39,plain,(
% 3.93/1.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 3.93/1.00    inference(cnf_transformation,[],[f27])).
% 3.93/1.00  
% 3.93/1.00  fof(f57,plain,(
% 3.93/1.00    ~r1_xboole_0(k1_relat_1(sK2),sK1) | k1_xboole_0 != k7_relat_1(sK2,sK1)),
% 3.93/1.00    inference(cnf_transformation,[],[f35])).
% 3.93/1.00  
% 3.93/1.00  cnf(c_3,plain,
% 3.93/1.00      ( r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1) ),
% 3.93/1.00      inference(cnf_transformation,[],[f37]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1242,plain,
% 3.93/1.00      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.93/1.00      | r1_xboole_0(X0,X1) = iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_2,plain,
% 3.93/1.00      ( r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1) ),
% 3.93/1.00      inference(cnf_transformation,[],[f38]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1243,plain,
% 3.93/1.00      ( r2_hidden(sK0(X0,X1),X1) = iProver_top
% 3.93/1.00      | r1_xboole_0(X0,X1) = iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_17,plain,
% 3.93/1.00      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 3.93/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1234,plain,
% 3.93/1.00      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
% 3.93/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_18,plain,
% 3.93/1.00      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),k1_relat_1(X0))
% 3.93/1.00      | ~ v1_relat_1(X0) ),
% 3.93/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1233,plain,
% 3.93/1.00      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),k1_relat_1(X0)) = iProver_top
% 3.93/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_20,negated_conjecture,
% 3.93/1.00      ( r1_xboole_0(k1_relat_1(sK2),sK1)
% 3.93/1.00      | k1_xboole_0 = k7_relat_1(sK2,sK1) ),
% 3.93/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1231,plain,
% 3.93/1.00      ( k1_xboole_0 = k7_relat_1(sK2,sK1)
% 3.93/1.00      | r1_xboole_0(k1_relat_1(sK2),sK1) = iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_0,plain,
% 3.93/1.00      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 3.93/1.00      inference(cnf_transformation,[],[f36]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1245,plain,
% 3.93/1.00      ( r1_xboole_0(X0,X1) != iProver_top
% 3.93/1.00      | r1_xboole_0(X1,X0) = iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1495,plain,
% 3.93/1.00      ( k7_relat_1(sK2,sK1) = k1_xboole_0
% 3.93/1.00      | r1_xboole_0(sK1,k1_relat_1(sK2)) = iProver_top ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_1231,c_1245]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_6,plain,
% 3.93/1.00      ( ~ r1_tarski(X0,X1)
% 3.93/1.00      | ~ r1_tarski(X0,X2)
% 3.93/1.00      | ~ r1_xboole_0(X2,X1)
% 3.93/1.00      | k1_xboole_0 = X0 ),
% 3.93/1.00      inference(cnf_transformation,[],[f42]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1240,plain,
% 3.93/1.00      ( k1_xboole_0 = X0
% 3.93/1.00      | r1_tarski(X0,X1) != iProver_top
% 3.93/1.00      | r1_tarski(X0,X2) != iProver_top
% 3.93/1.00      | r1_xboole_0(X2,X1) != iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1712,plain,
% 3.93/1.00      ( k7_relat_1(sK2,sK1) = k1_xboole_0
% 3.93/1.00      | k1_xboole_0 = X0
% 3.93/1.00      | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top
% 3.93/1.00      | r1_tarski(X0,sK1) != iProver_top ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_1495,c_1240]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1792,plain,
% 3.93/1.00      ( k7_relat_1(sK2,sK1) = k1_xboole_0
% 3.93/1.00      | k1_relat_1(k7_relat_1(sK2,X0)) = k1_xboole_0
% 3.93/1.00      | r1_tarski(k1_relat_1(k7_relat_1(sK2,X0)),sK1) != iProver_top
% 3.93/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_1233,c_1712]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_21,negated_conjecture,
% 3.93/1.00      ( v1_relat_1(sK2) ),
% 3.93/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_22,plain,
% 3.93/1.00      ( v1_relat_1(sK2) = iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1822,plain,
% 3.93/1.00      ( r1_tarski(k1_relat_1(k7_relat_1(sK2,X0)),sK1) != iProver_top
% 3.93/1.00      | k1_relat_1(k7_relat_1(sK2,X0)) = k1_xboole_0
% 3.93/1.00      | k7_relat_1(sK2,sK1) = k1_xboole_0 ),
% 3.93/1.00      inference(global_propositional_subsumption,
% 3.93/1.00                [status(thm)],
% 3.93/1.00                [c_1792,c_22]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1823,plain,
% 3.93/1.00      ( k7_relat_1(sK2,sK1) = k1_xboole_0
% 3.93/1.00      | k1_relat_1(k7_relat_1(sK2,X0)) = k1_xboole_0
% 3.93/1.00      | r1_tarski(k1_relat_1(k7_relat_1(sK2,X0)),sK1) != iProver_top ),
% 3.93/1.00      inference(renaming,[status(thm)],[c_1822]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1831,plain,
% 3.93/1.00      ( k7_relat_1(sK2,sK1) = k1_xboole_0
% 3.93/1.00      | k1_relat_1(k7_relat_1(sK2,sK1)) = k1_xboole_0
% 3.93/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_1234,c_1823]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1832,plain,
% 3.93/1.00      ( ~ v1_relat_1(sK2)
% 3.93/1.00      | k7_relat_1(sK2,sK1) = k1_xboole_0
% 3.93/1.00      | k1_relat_1(k7_relat_1(sK2,sK1)) = k1_xboole_0 ),
% 3.93/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1831]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1908,plain,
% 3.93/1.00      ( k1_relat_1(k7_relat_1(sK2,sK1)) = k1_xboole_0
% 3.93/1.00      | k7_relat_1(sK2,sK1) = k1_xboole_0 ),
% 3.93/1.00      inference(global_propositional_subsumption,
% 3.93/1.00                [status(thm)],
% 3.93/1.00                [c_1831,c_21,c_1832]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1909,plain,
% 3.93/1.00      ( k7_relat_1(sK2,sK1) = k1_xboole_0
% 3.93/1.00      | k1_relat_1(k7_relat_1(sK2,sK1)) = k1_xboole_0 ),
% 3.93/1.00      inference(renaming,[status(thm)],[c_1908]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1230,plain,
% 3.93/1.00      ( v1_relat_1(sK2) = iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_10,plain,
% 3.93/1.00      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 3.93/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1239,plain,
% 3.93/1.00      ( v1_relat_1(X0) != iProver_top
% 3.93/1.00      | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_11,plain,
% 3.93/1.00      ( ~ v1_relat_1(X0)
% 3.93/1.00      | k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ),
% 3.93/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1238,plain,
% 3.93/1.00      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
% 3.93/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1584,plain,
% 3.93/1.00      ( k3_xboole_0(k7_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(k7_relat_1(X0,X1)),k2_relat_1(k7_relat_1(X0,X1)))) = k7_relat_1(X0,X1)
% 3.93/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_1239,c_1238]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_2346,plain,
% 3.93/1.00      ( k3_xboole_0(k7_relat_1(sK2,X0),k2_zfmisc_1(k1_relat_1(k7_relat_1(sK2,X0)),k2_relat_1(k7_relat_1(sK2,X0)))) = k7_relat_1(sK2,X0) ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_1230,c_1584]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_2386,plain,
% 3.93/1.00      ( k7_relat_1(sK2,sK1) = k1_xboole_0
% 3.93/1.00      | k3_xboole_0(k7_relat_1(sK2,sK1),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k7_relat_1(sK2,sK1)))) = k7_relat_1(sK2,sK1) ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_1909,c_2346]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_4,plain,
% 3.93/1.00      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.93/1.00      inference(cnf_transformation,[],[f40]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_8,plain,
% 3.93/1.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.93/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_2387,plain,
% 3.93/1.00      ( k7_relat_1(sK2,sK1) = k1_xboole_0 ),
% 3.93/1.00      inference(demodulation,[status(thm)],[c_2386,c_4,c_8]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_14,plain,
% 3.93/1.00      ( ~ r2_hidden(X0,X1)
% 3.93/1.00      | ~ r2_hidden(X0,k1_relat_1(X2))
% 3.93/1.00      | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
% 3.93/1.00      | ~ v1_relat_1(X2) ),
% 3.93/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1237,plain,
% 3.93/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.93/1.00      | r2_hidden(X0,k1_relat_1(X2)) != iProver_top
% 3.93/1.00      | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) = iProver_top
% 3.93/1.00      | v1_relat_1(X2) != iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_2398,plain,
% 3.93/1.00      ( r2_hidden(X0,k1_relat_1(sK2)) != iProver_top
% 3.93/1.00      | r2_hidden(X0,k1_relat_1(k1_xboole_0)) = iProver_top
% 3.93/1.00      | r2_hidden(X0,sK1) != iProver_top
% 3.93/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_2387,c_1237]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_13,plain,
% 3.93/1.00      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.93/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_2438,plain,
% 3.93/1.00      ( r2_hidden(X0,k1_relat_1(sK2)) != iProver_top
% 3.93/1.00      | r2_hidden(X0,sK1) != iProver_top
% 3.93/1.00      | r2_hidden(X0,k1_xboole_0) = iProver_top
% 3.93/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.93/1.00      inference(light_normalisation,[status(thm)],[c_2398,c_13]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_2396,plain,
% 3.93/1.00      ( v1_relat_1(sK2) != iProver_top
% 3.93/1.00      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_2387,c_1239]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_15,plain,
% 3.93/1.00      ( r2_hidden(X0,k1_relat_1(X1))
% 3.93/1.00      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X1,X2)))
% 3.93/1.00      | ~ v1_relat_1(X1) ),
% 3.93/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1236,plain,
% 3.93/1.00      ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
% 3.93/1.00      | r2_hidden(X0,k1_relat_1(k7_relat_1(X1,X2))) != iProver_top
% 3.93/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_2400,plain,
% 3.93/1.00      ( r2_hidden(X0,k1_relat_1(sK2)) = iProver_top
% 3.93/1.00      | r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top
% 3.93/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_2387,c_1236]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_2423,plain,
% 3.93/1.00      ( r2_hidden(X0,k1_relat_1(sK2)) = iProver_top
% 3.93/1.00      | r2_hidden(X0,k1_xboole_0) != iProver_top
% 3.93/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.93/1.00      inference(light_normalisation,[status(thm)],[c_2400,c_13]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_2986,plain,
% 3.93/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 3.93/1.00      | r2_hidden(X0,k1_relat_1(sK2)) = iProver_top ),
% 3.93/1.00      inference(global_propositional_subsumption,
% 3.93/1.00                [status(thm)],
% 3.93/1.00                [c_2423,c_22]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_2987,plain,
% 3.93/1.00      ( r2_hidden(X0,k1_relat_1(sK2)) = iProver_top
% 3.93/1.00      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.93/1.00      inference(renaming,[status(thm)],[c_2986]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_5,plain,
% 3.93/1.00      ( r1_xboole_0(X0,k1_xboole_0) ),
% 3.93/1.00      inference(cnf_transformation,[],[f41]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1241,plain,
% 3.93/1.00      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1494,plain,
% 3.93/1.00      ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_1241,c_1245]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1,negated_conjecture,
% 3.93/1.00      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 3.93/1.00      inference(cnf_transformation,[],[f39]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1244,plain,
% 3.93/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.93/1.00      | r2_hidden(X0,X2) != iProver_top
% 3.93/1.00      | r1_xboole_0(X2,X1) != iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1843,plain,
% 3.93/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.93/1.00      | r2_hidden(X0,X2) != iProver_top
% 3.93/1.00      | r2_hidden(X0,k1_relat_1(X3)) != iProver_top
% 3.93/1.00      | r1_xboole_0(X2,k1_relat_1(k7_relat_1(X3,X1))) != iProver_top
% 3.93/1.00      | v1_relat_1(X3) != iProver_top ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_1237,c_1244]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_2014,plain,
% 3.93/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.93/1.00      | r2_hidden(X0,k1_relat_1(X2)) != iProver_top
% 3.93/1.00      | r2_hidden(X0,k1_xboole_0) != iProver_top
% 3.93/1.00      | v1_relat_1(X2) != iProver_top ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_1494,c_1843]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_2048,plain,
% 3.93/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.93/1.00      | r2_hidden(X0,k1_xboole_0) != iProver_top
% 3.93/1.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_13,c_2014]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_2994,plain,
% 3.93/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 3.93/1.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_2987,c_2048]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_3617,plain,
% 3.93/1.00      ( r2_hidden(X0,k1_relat_1(sK2)) != iProver_top
% 3.93/1.00      | r2_hidden(X0,sK1) != iProver_top ),
% 3.93/1.00      inference(global_propositional_subsumption,
% 3.93/1.00                [status(thm)],
% 3.93/1.00                [c_2438,c_22,c_2396,c_2994]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_3625,plain,
% 3.93/1.00      ( r2_hidden(sK0(X0,k1_relat_1(sK2)),sK1) != iProver_top
% 3.93/1.00      | r1_xboole_0(X0,k1_relat_1(sK2)) = iProver_top ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_1243,c_3617]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_4502,plain,
% 3.93/1.00      ( r1_xboole_0(sK1,k1_relat_1(sK2)) = iProver_top ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_1242,c_3625]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_19,negated_conjecture,
% 3.93/1.00      ( ~ r1_xboole_0(k1_relat_1(sK2),sK1)
% 3.93/1.00      | k1_xboole_0 != k7_relat_1(sK2,sK1) ),
% 3.93/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1232,plain,
% 3.93/1.00      ( k1_xboole_0 != k7_relat_1(sK2,sK1)
% 3.93/1.00      | r1_xboole_0(k1_relat_1(sK2),sK1) != iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_2390,plain,
% 3.93/1.00      ( k1_xboole_0 != k1_xboole_0
% 3.93/1.00      | r1_xboole_0(k1_relat_1(sK2),sK1) != iProver_top ),
% 3.93/1.00      inference(demodulation,[status(thm)],[c_2387,c_1232]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_2391,plain,
% 3.93/1.00      ( r1_xboole_0(k1_relat_1(sK2),sK1) != iProver_top ),
% 3.93/1.00      inference(equality_resolution_simp,[status(thm)],[c_2390]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1369,plain,
% 3.93/1.00      ( ~ r2_hidden(sK0(X0,X1),X0)
% 3.93/1.00      | ~ r2_hidden(sK0(X0,X1),X2)
% 3.93/1.00      | ~ r1_xboole_0(X2,X0) ),
% 3.93/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1448,plain,
% 3.93/1.00      ( ~ r2_hidden(sK0(k1_relat_1(sK2),sK1),X0)
% 3.93/1.00      | ~ r2_hidden(sK0(k1_relat_1(sK2),sK1),k1_relat_1(sK2))
% 3.93/1.00      | ~ r1_xboole_0(X0,k1_relat_1(sK2)) ),
% 3.93/1.00      inference(instantiation,[status(thm)],[c_1369]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1770,plain,
% 3.93/1.00      ( ~ r2_hidden(sK0(k1_relat_1(sK2),sK1),k1_relat_1(sK2))
% 3.93/1.00      | ~ r2_hidden(sK0(k1_relat_1(sK2),sK1),sK1)
% 3.93/1.00      | ~ r1_xboole_0(sK1,k1_relat_1(sK2)) ),
% 3.93/1.00      inference(instantiation,[status(thm)],[c_1448]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1771,plain,
% 3.93/1.00      ( r2_hidden(sK0(k1_relat_1(sK2),sK1),k1_relat_1(sK2)) != iProver_top
% 3.93/1.00      | r2_hidden(sK0(k1_relat_1(sK2),sK1),sK1) != iProver_top
% 3.93/1.00      | r1_xboole_0(sK1,k1_relat_1(sK2)) != iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_1770]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1375,plain,
% 3.93/1.00      ( r2_hidden(sK0(k1_relat_1(sK2),sK1),sK1)
% 3.93/1.00      | r1_xboole_0(k1_relat_1(sK2),sK1) ),
% 3.93/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1379,plain,
% 3.93/1.00      ( r2_hidden(sK0(k1_relat_1(sK2),sK1),sK1) = iProver_top
% 3.93/1.00      | r1_xboole_0(k1_relat_1(sK2),sK1) = iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_1375]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1376,plain,
% 3.93/1.00      ( r2_hidden(sK0(k1_relat_1(sK2),sK1),k1_relat_1(sK2))
% 3.93/1.00      | r1_xboole_0(k1_relat_1(sK2),sK1) ),
% 3.93/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1377,plain,
% 3.93/1.00      ( r2_hidden(sK0(k1_relat_1(sK2),sK1),k1_relat_1(sK2)) = iProver_top
% 3.93/1.00      | r1_xboole_0(k1_relat_1(sK2),sK1) = iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_1376]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(contradiction,plain,
% 3.93/1.00      ( $false ),
% 3.93/1.00      inference(minisat,
% 3.93/1.00                [status(thm)],
% 3.93/1.00                [c_4502,c_2391,c_1771,c_1379,c_1377]) ).
% 3.93/1.00  
% 3.93/1.00  
% 3.93/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.93/1.00  
% 3.93/1.00  ------                               Statistics
% 3.93/1.00  
% 3.93/1.00  ------ Selected
% 3.93/1.00  
% 3.93/1.00  total_time:                             0.185
% 3.93/1.00  
%------------------------------------------------------------------------------
