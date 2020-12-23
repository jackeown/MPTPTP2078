%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:48:55 EST 2020

% Result     : Theorem 3.55s
% Output     : CNFRefutation 3.55s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 307 expanded)
%              Number of clauses        :   66 ( 112 expanded)
%              Number of leaves         :   16 (  69 expanded)
%              Depth                    :   15
%              Number of atoms          :  346 (1114 expanded)
%              Number of equality atoms :  113 ( 166 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :    9 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
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
    inference(rectify,[],[f3])).

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

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f32])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f13,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
           => r1_xboole_0(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
             => r1_xboole_0(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(X0,X1)
          & r1_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(X0,X1)
          & r1_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(X0,X1)
          & r1_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
          & v1_relat_1(X1) )
     => ( ~ r1_xboole_0(X0,sK3)
        & r1_xboole_0(k2_relat_1(X0),k2_relat_1(sK3))
        & v1_relat_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_xboole_0(X0,X1)
            & r1_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_xboole_0(sK2,X1)
          & r1_xboole_0(k2_relat_1(sK2),k2_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ~ r1_xboole_0(sK2,sK3)
    & r1_xboole_0(k2_relat_1(sK2),k2_relat_1(sK3))
    & v1_relat_1(sK3)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f30,f40,f39])).

fof(f64,plain,(
    r1_xboole_0(k2_relat_1(sK2),k2_relat_1(sK3)) ),
    inference(cnf_transformation,[],[f41])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k10_relat_1(X1,X0)
          | ~ r1_xboole_0(k2_relat_1(X1),X0) )
        & ( r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 != k10_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k10_relat_1(X1,X0)
      | ~ r1_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f62,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X0,X3),X2)
              & r2_hidden(X3,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X0,X4),X2)
              & r2_hidden(X4,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK1(X0,X1,X2)),X2)
        & r2_hidden(sK1(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ( r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(X0,sK1(X0,X1,X2)),X2)
            & r2_hidden(sK1(X0,X1,X2),k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f36])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK1(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK1(X0,X1,X2),k2_relat_1(X2))
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f63,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f61,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f65,plain,(
    ~ r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_5,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_333,plain,
    ( r2_hidden(sK0(X0_43,X1_43),X0_43)
    | r1_xboole_0(X0_43,X1_43) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_890,plain,
    ( r2_hidden(sK0(X0_43,X1_43),X0_43) = iProver_top
    | r1_xboole_0(X0_43,X1_43) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_333])).

cnf(c_21,negated_conjecture,
    ( r1_xboole_0(k2_relat_1(sK2),k2_relat_1(sK3)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_317,negated_conjecture,
    ( r1_xboole_0(k2_relat_1(sK2),k2_relat_1(sK3)) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_906,plain,
    ( r1_xboole_0(k2_relat_1(sK2),k2_relat_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_317])).

cnf(c_15,plain,
    ( ~ r1_xboole_0(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k10_relat_1(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_323,plain,
    ( ~ r1_xboole_0(k2_relat_1(X0_43),X1_43)
    | ~ v1_relat_1(X0_43)
    | k10_relat_1(X0_43,X1_43) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_900,plain,
    ( k10_relat_1(X0_43,X1_43) = k1_xboole_0
    | r1_xboole_0(k2_relat_1(X0_43),X1_43) != iProver_top
    | v1_relat_1(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_323])).

cnf(c_2076,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK3)) = k1_xboole_0
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_906,c_900])).

cnf(c_23,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_24,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2225,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK3)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2076,c_24])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK1(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_326,plain,
    ( ~ r2_hidden(X0_44,k10_relat_1(X0_43,X1_43))
    | r2_hidden(sK1(X0_44,X1_43,X0_43),X1_43)
    | ~ v1_relat_1(X0_43) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_897,plain,
    ( r2_hidden(X0_44,k10_relat_1(X0_43,X1_43)) != iProver_top
    | r2_hidden(sK1(X0_44,X1_43,X0_43),X1_43) = iProver_top
    | v1_relat_1(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_326])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_335,plain,
    ( ~ r2_hidden(X0_44,X0_43)
    | ~ r2_hidden(X0_44,X1_43)
    | ~ r1_xboole_0(X0_43,X1_43) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_888,plain,
    ( r2_hidden(X0_44,X0_43) != iProver_top
    | r2_hidden(X0_44,X1_43) != iProver_top
    | r1_xboole_0(X1_43,X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_335])).

cnf(c_2754,plain,
    ( r2_hidden(X0_44,k10_relat_1(X0_43,X1_43)) != iProver_top
    | r2_hidden(sK1(X0_44,X1_43,X0_43),X2_43) != iProver_top
    | r1_xboole_0(X1_43,X2_43) != iProver_top
    | v1_relat_1(X0_43) != iProver_top ),
    inference(superposition,[status(thm)],[c_897,c_888])).

cnf(c_6623,plain,
    ( r2_hidden(X0_44,k10_relat_1(X0_43,X1_43)) != iProver_top
    | r1_xboole_0(X1_43,X1_43) != iProver_top
    | v1_relat_1(X0_43) != iProver_top ),
    inference(superposition,[status(thm)],[c_897,c_2754])).

cnf(c_6633,plain,
    ( r2_hidden(X0_44,k1_xboole_0) != iProver_top
    | r1_xboole_0(k2_relat_1(sK3),k2_relat_1(sK3)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2225,c_6623])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_336,plain,
    ( ~ r1_xboole_0(X0_43,X1_43)
    | r1_xboole_0(X1_43,X0_43) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_887,plain,
    ( r1_xboole_0(X0_43,X1_43) != iProver_top
    | r1_xboole_0(X1_43,X0_43) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_336])).

cnf(c_1292,plain,
    ( r1_xboole_0(k2_relat_1(sK3),k2_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_906,c_887])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK1(X0,X2,X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_324,plain,
    ( ~ r2_hidden(X0_44,k10_relat_1(X0_43,X1_43))
    | r2_hidden(sK1(X0_44,X1_43,X0_43),k2_relat_1(X0_43))
    | ~ v1_relat_1(X0_43) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_899,plain,
    ( r2_hidden(X0_44,k10_relat_1(X0_43,X1_43)) != iProver_top
    | r2_hidden(sK1(X0_44,X1_43,X0_43),k2_relat_1(X0_43)) = iProver_top
    | v1_relat_1(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_324])).

cnf(c_6622,plain,
    ( r2_hidden(X0_44,k10_relat_1(X0_43,X1_43)) != iProver_top
    | r1_xboole_0(X1_43,k2_relat_1(X0_43)) != iProver_top
    | v1_relat_1(X0_43) != iProver_top ),
    inference(superposition,[status(thm)],[c_899,c_2754])).

cnf(c_7028,plain,
    ( r2_hidden(X0_44,k1_xboole_0) != iProver_top
    | r1_xboole_0(k2_relat_1(sK3),k2_relat_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2225,c_6622])).

cnf(c_7049,plain,
    ( r2_hidden(X0_44,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6633,c_24,c_1292,c_7028])).

cnf(c_7057,plain,
    ( r1_xboole_0(k1_xboole_0,X0_43) = iProver_top ),
    inference(superposition,[status(thm)],[c_890,c_7049])).

cnf(c_7064,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_7057])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_337,plain,
    ( ~ r1_xboole_0(X0_43,X1_43)
    | k3_xboole_0(X0_43,X1_43) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_886,plain,
    ( k3_xboole_0(X0_43,X1_43) = k1_xboole_0
    | r1_xboole_0(X0_43,X1_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_337])).

cnf(c_1189,plain,
    ( k3_xboole_0(k2_relat_1(sK2),k2_relat_1(sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_906,c_886])).

cnf(c_17,plain,
    ( r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_321,plain,
    ( r1_tarski(k2_relat_1(k3_xboole_0(X0_43,X1_43)),k3_xboole_0(k2_relat_1(X0_43),k2_relat_1(X1_43)))
    | ~ v1_relat_1(X0_43)
    | ~ v1_relat_1(X1_43) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_902,plain,
    ( r1_tarski(k2_relat_1(k3_xboole_0(X0_43,X1_43)),k3_xboole_0(k2_relat_1(X0_43),k2_relat_1(X1_43))) = iProver_top
    | v1_relat_1(X0_43) != iProver_top
    | v1_relat_1(X1_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_321])).

cnf(c_2890,plain,
    ( r1_tarski(k2_relat_1(k3_xboole_0(sK2,sK3)),k1_xboole_0) = iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1189,c_902])).

cnf(c_22,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_25,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3026,plain,
    ( r1_tarski(k2_relat_1(k3_xboole_0(sK2,sK3)),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2890,c_24,c_25])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | ~ r1_xboole_0(X2,X1)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_332,plain,
    ( ~ r1_tarski(X0_43,X1_43)
    | ~ r1_tarski(X0_43,X2_43)
    | ~ r1_xboole_0(X2_43,X1_43)
    | k1_xboole_0 = X0_43 ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_891,plain,
    ( k1_xboole_0 = X0_43
    | r1_tarski(X0_43,X1_43) != iProver_top
    | r1_tarski(X0_43,X2_43) != iProver_top
    | r1_xboole_0(X2_43,X1_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_332])).

cnf(c_3030,plain,
    ( k2_relat_1(k3_xboole_0(sK2,sK3)) = k1_xboole_0
    | r1_tarski(k2_relat_1(k3_xboole_0(sK2,sK3)),X0_43) != iProver_top
    | r1_xboole_0(X0_43,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3026,c_891])).

cnf(c_3032,plain,
    ( k2_relat_1(k3_xboole_0(sK2,sK3)) = k1_xboole_0
    | r1_tarski(k2_relat_1(k3_xboole_0(sK2,sK3)),k1_xboole_0) != iProver_top
    | r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3030])).

cnf(c_340,plain,
    ( X0_43 = X0_43 ),
    theory(equality)).

cnf(c_1313,plain,
    ( k3_xboole_0(sK2,sK3) = k3_xboole_0(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_340])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_331,plain,
    ( ~ v1_relat_1(X0_43)
    | v1_relat_1(k3_xboole_0(X0_43,X1_43)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1298,plain,
    ( v1_relat_1(k3_xboole_0(sK2,sK3))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_331])).

cnf(c_18,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_320,plain,
    ( ~ v1_relat_1(X0_43)
    | k2_relat_1(X0_43) != k1_xboole_0
    | k1_xboole_0 = X0_43 ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1088,plain,
    ( ~ v1_relat_1(k3_xboole_0(sK2,sK3))
    | k2_relat_1(k3_xboole_0(sK2,sK3)) != k1_xboole_0
    | k1_xboole_0 = k3_xboole_0(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_320])).

cnf(c_342,plain,
    ( X0_43 != X1_43
    | X2_43 != X1_43
    | X2_43 = X0_43 ),
    theory(equality)).

cnf(c_954,plain,
    ( k3_xboole_0(sK2,sK3) != X0_43
    | k3_xboole_0(sK2,sK3) = k1_xboole_0
    | k1_xboole_0 != X0_43 ),
    inference(instantiation,[status(thm)],[c_342])).

cnf(c_1009,plain,
    ( k3_xboole_0(sK2,sK3) != k3_xboole_0(sK2,sK3)
    | k3_xboole_0(sK2,sK3) = k1_xboole_0
    | k1_xboole_0 != k3_xboole_0(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_954])).

cnf(c_0,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_338,plain,
    ( r1_xboole_0(X0_43,X1_43)
    | k3_xboole_0(X0_43,X1_43) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_942,plain,
    ( r1_xboole_0(sK2,sK3)
    | k3_xboole_0(sK2,sK3) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_338])).

cnf(c_20,negated_conjecture,
    ( ~ r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f65])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7064,c_3032,c_2890,c_1313,c_1298,c_1088,c_1009,c_942,c_20,c_25,c_24,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:42:37 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  % Running in FOF mode
% 3.55/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.55/0.99  
% 3.55/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.55/0.99  
% 3.55/0.99  ------  iProver source info
% 3.55/0.99  
% 3.55/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.55/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.55/0.99  git: non_committed_changes: false
% 3.55/0.99  git: last_make_outside_of_git: false
% 3.55/0.99  
% 3.55/0.99  ------ 
% 3.55/0.99  
% 3.55/0.99  ------ Input Options
% 3.55/0.99  
% 3.55/0.99  --out_options                           all
% 3.55/0.99  --tptp_safe_out                         true
% 3.55/0.99  --problem_path                          ""
% 3.55/0.99  --include_path                          ""
% 3.55/0.99  --clausifier                            res/vclausify_rel
% 3.55/0.99  --clausifier_options                    ""
% 3.55/0.99  --stdin                                 false
% 3.55/0.99  --stats_out                             all
% 3.55/0.99  
% 3.55/0.99  ------ General Options
% 3.55/0.99  
% 3.55/0.99  --fof                                   false
% 3.55/0.99  --time_out_real                         305.
% 3.55/0.99  --time_out_virtual                      -1.
% 3.55/0.99  --symbol_type_check                     false
% 3.55/0.99  --clausify_out                          false
% 3.55/0.99  --sig_cnt_out                           false
% 3.55/0.99  --trig_cnt_out                          false
% 3.55/0.99  --trig_cnt_out_tolerance                1.
% 3.55/0.99  --trig_cnt_out_sk_spl                   false
% 3.55/0.99  --abstr_cl_out                          false
% 3.55/0.99  
% 3.55/0.99  ------ Global Options
% 3.55/0.99  
% 3.55/0.99  --schedule                              default
% 3.55/0.99  --add_important_lit                     false
% 3.55/0.99  --prop_solver_per_cl                    1000
% 3.55/0.99  --min_unsat_core                        false
% 3.55/0.99  --soft_assumptions                      false
% 3.55/0.99  --soft_lemma_size                       3
% 3.55/0.99  --prop_impl_unit_size                   0
% 3.55/0.99  --prop_impl_unit                        []
% 3.55/0.99  --share_sel_clauses                     true
% 3.55/0.99  --reset_solvers                         false
% 3.55/0.99  --bc_imp_inh                            [conj_cone]
% 3.55/0.99  --conj_cone_tolerance                   3.
% 3.55/0.99  --extra_neg_conj                        none
% 3.55/0.99  --large_theory_mode                     true
% 3.55/0.99  --prolific_symb_bound                   200
% 3.55/0.99  --lt_threshold                          2000
% 3.55/0.99  --clause_weak_htbl                      true
% 3.55/0.99  --gc_record_bc_elim                     false
% 3.55/0.99  
% 3.55/0.99  ------ Preprocessing Options
% 3.55/0.99  
% 3.55/0.99  --preprocessing_flag                    true
% 3.55/0.99  --time_out_prep_mult                    0.1
% 3.55/0.99  --splitting_mode                        input
% 3.55/0.99  --splitting_grd                         true
% 3.55/0.99  --splitting_cvd                         false
% 3.55/0.99  --splitting_cvd_svl                     false
% 3.55/0.99  --splitting_nvd                         32
% 3.55/0.99  --sub_typing                            true
% 3.55/0.99  --prep_gs_sim                           true
% 3.55/0.99  --prep_unflatten                        true
% 3.55/0.99  --prep_res_sim                          true
% 3.55/0.99  --prep_upred                            true
% 3.55/0.99  --prep_sem_filter                       exhaustive
% 3.55/0.99  --prep_sem_filter_out                   false
% 3.55/0.99  --pred_elim                             true
% 3.55/0.99  --res_sim_input                         true
% 3.55/0.99  --eq_ax_congr_red                       true
% 3.55/0.99  --pure_diseq_elim                       true
% 3.55/0.99  --brand_transform                       false
% 3.55/0.99  --non_eq_to_eq                          false
% 3.55/0.99  --prep_def_merge                        true
% 3.55/0.99  --prep_def_merge_prop_impl              false
% 3.55/0.99  --prep_def_merge_mbd                    true
% 3.55/0.99  --prep_def_merge_tr_red                 false
% 3.55/0.99  --prep_def_merge_tr_cl                  false
% 3.55/0.99  --smt_preprocessing                     true
% 3.55/0.99  --smt_ac_axioms                         fast
% 3.55/0.99  --preprocessed_out                      false
% 3.55/0.99  --preprocessed_stats                    false
% 3.55/0.99  
% 3.55/0.99  ------ Abstraction refinement Options
% 3.55/0.99  
% 3.55/0.99  --abstr_ref                             []
% 3.55/0.99  --abstr_ref_prep                        false
% 3.55/0.99  --abstr_ref_until_sat                   false
% 3.55/0.99  --abstr_ref_sig_restrict                funpre
% 3.55/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.55/0.99  --abstr_ref_under                       []
% 3.55/0.99  
% 3.55/0.99  ------ SAT Options
% 3.55/0.99  
% 3.55/0.99  --sat_mode                              false
% 3.55/0.99  --sat_fm_restart_options                ""
% 3.55/0.99  --sat_gr_def                            false
% 3.55/0.99  --sat_epr_types                         true
% 3.55/0.99  --sat_non_cyclic_types                  false
% 3.55/0.99  --sat_finite_models                     false
% 3.55/0.99  --sat_fm_lemmas                         false
% 3.55/0.99  --sat_fm_prep                           false
% 3.55/0.99  --sat_fm_uc_incr                        true
% 3.55/0.99  --sat_out_model                         small
% 3.55/0.99  --sat_out_clauses                       false
% 3.55/0.99  
% 3.55/0.99  ------ QBF Options
% 3.55/0.99  
% 3.55/0.99  --qbf_mode                              false
% 3.55/0.99  --qbf_elim_univ                         false
% 3.55/0.99  --qbf_dom_inst                          none
% 3.55/0.99  --qbf_dom_pre_inst                      false
% 3.55/0.99  --qbf_sk_in                             false
% 3.55/0.99  --qbf_pred_elim                         true
% 3.55/0.99  --qbf_split                             512
% 3.55/0.99  
% 3.55/0.99  ------ BMC1 Options
% 3.55/0.99  
% 3.55/0.99  --bmc1_incremental                      false
% 3.55/0.99  --bmc1_axioms                           reachable_all
% 3.55/0.99  --bmc1_min_bound                        0
% 3.55/0.99  --bmc1_max_bound                        -1
% 3.55/0.99  --bmc1_max_bound_default                -1
% 3.55/0.99  --bmc1_symbol_reachability              true
% 3.55/0.99  --bmc1_property_lemmas                  false
% 3.55/0.99  --bmc1_k_induction                      false
% 3.55/0.99  --bmc1_non_equiv_states                 false
% 3.55/0.99  --bmc1_deadlock                         false
% 3.55/0.99  --bmc1_ucm                              false
% 3.55/0.99  --bmc1_add_unsat_core                   none
% 3.55/0.99  --bmc1_unsat_core_children              false
% 3.55/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.55/0.99  --bmc1_out_stat                         full
% 3.55/0.99  --bmc1_ground_init                      false
% 3.55/0.99  --bmc1_pre_inst_next_state              false
% 3.55/0.99  --bmc1_pre_inst_state                   false
% 3.55/0.99  --bmc1_pre_inst_reach_state             false
% 3.55/0.99  --bmc1_out_unsat_core                   false
% 3.55/0.99  --bmc1_aig_witness_out                  false
% 3.55/0.99  --bmc1_verbose                          false
% 3.55/0.99  --bmc1_dump_clauses_tptp                false
% 3.55/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.55/0.99  --bmc1_dump_file                        -
% 3.55/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.55/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.55/0.99  --bmc1_ucm_extend_mode                  1
% 3.55/0.99  --bmc1_ucm_init_mode                    2
% 3.55/0.99  --bmc1_ucm_cone_mode                    none
% 3.55/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.55/0.99  --bmc1_ucm_relax_model                  4
% 3.55/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.55/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.55/0.99  --bmc1_ucm_layered_model                none
% 3.55/0.99  --bmc1_ucm_max_lemma_size               10
% 3.55/0.99  
% 3.55/0.99  ------ AIG Options
% 3.55/0.99  
% 3.55/0.99  --aig_mode                              false
% 3.55/0.99  
% 3.55/0.99  ------ Instantiation Options
% 3.55/0.99  
% 3.55/0.99  --instantiation_flag                    true
% 3.55/0.99  --inst_sos_flag                         true
% 3.55/0.99  --inst_sos_phase                        true
% 3.55/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.55/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.55/0.99  --inst_lit_sel_side                     num_symb
% 3.55/0.99  --inst_solver_per_active                1400
% 3.55/0.99  --inst_solver_calls_frac                1.
% 3.55/0.99  --inst_passive_queue_type               priority_queues
% 3.55/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.55/0.99  --inst_passive_queues_freq              [25;2]
% 3.55/0.99  --inst_dismatching                      true
% 3.55/0.99  --inst_eager_unprocessed_to_passive     true
% 3.55/0.99  --inst_prop_sim_given                   true
% 3.55/0.99  --inst_prop_sim_new                     false
% 3.55/0.99  --inst_subs_new                         false
% 3.55/0.99  --inst_eq_res_simp                      false
% 3.55/0.99  --inst_subs_given                       false
% 3.55/0.99  --inst_orphan_elimination               true
% 3.55/0.99  --inst_learning_loop_flag               true
% 3.55/0.99  --inst_learning_start                   3000
% 3.55/0.99  --inst_learning_factor                  2
% 3.55/0.99  --inst_start_prop_sim_after_learn       3
% 3.55/0.99  --inst_sel_renew                        solver
% 3.55/0.99  --inst_lit_activity_flag                true
% 3.55/0.99  --inst_restr_to_given                   false
% 3.55/0.99  --inst_activity_threshold               500
% 3.55/0.99  --inst_out_proof                        true
% 3.55/0.99  
% 3.55/0.99  ------ Resolution Options
% 3.55/0.99  
% 3.55/0.99  --resolution_flag                       true
% 3.55/0.99  --res_lit_sel                           adaptive
% 3.55/0.99  --res_lit_sel_side                      none
% 3.55/0.99  --res_ordering                          kbo
% 3.55/0.99  --res_to_prop_solver                    active
% 3.55/0.99  --res_prop_simpl_new                    false
% 3.55/0.99  --res_prop_simpl_given                  true
% 3.55/0.99  --res_passive_queue_type                priority_queues
% 3.55/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.55/0.99  --res_passive_queues_freq               [15;5]
% 3.55/0.99  --res_forward_subs                      full
% 3.55/0.99  --res_backward_subs                     full
% 3.55/0.99  --res_forward_subs_resolution           true
% 3.55/0.99  --res_backward_subs_resolution          true
% 3.55/0.99  --res_orphan_elimination                true
% 3.55/0.99  --res_time_limit                        2.
% 3.55/0.99  --res_out_proof                         true
% 3.55/0.99  
% 3.55/0.99  ------ Superposition Options
% 3.55/0.99  
% 3.55/0.99  --superposition_flag                    true
% 3.55/0.99  --sup_passive_queue_type                priority_queues
% 3.55/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.55/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.55/0.99  --demod_completeness_check              fast
% 3.55/0.99  --demod_use_ground                      true
% 3.55/0.99  --sup_to_prop_solver                    passive
% 3.55/0.99  --sup_prop_simpl_new                    true
% 3.55/0.99  --sup_prop_simpl_given                  true
% 3.55/0.99  --sup_fun_splitting                     true
% 3.55/0.99  --sup_smt_interval                      50000
% 3.55/0.99  
% 3.55/0.99  ------ Superposition Simplification Setup
% 3.55/0.99  
% 3.55/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.55/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.55/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.55/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.55/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.55/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.55/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.55/0.99  --sup_immed_triv                        [TrivRules]
% 3.55/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.55/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.55/0.99  --sup_immed_bw_main                     []
% 3.55/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.55/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.55/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.55/0.99  --sup_input_bw                          []
% 3.55/0.99  
% 3.55/0.99  ------ Combination Options
% 3.55/0.99  
% 3.55/0.99  --comb_res_mult                         3
% 3.55/0.99  --comb_sup_mult                         2
% 3.55/0.99  --comb_inst_mult                        10
% 3.55/0.99  
% 3.55/0.99  ------ Debug Options
% 3.55/0.99  
% 3.55/0.99  --dbg_backtrace                         false
% 3.55/0.99  --dbg_dump_prop_clauses                 false
% 3.55/0.99  --dbg_dump_prop_clauses_file            -
% 3.55/0.99  --dbg_out_stat                          false
% 3.55/0.99  ------ Parsing...
% 3.55/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.55/0.99  
% 3.55/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.55/0.99  
% 3.55/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.55/0.99  
% 3.55/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.55/0.99  ------ Proving...
% 3.55/0.99  ------ Problem Properties 
% 3.55/0.99  
% 3.55/0.99  
% 3.55/0.99  clauses                                 24
% 3.55/0.99  conjectures                             4
% 3.55/0.99  EPR                                     6
% 3.55/0.99  Horn                                    22
% 3.55/0.99  unary                                   4
% 3.55/0.99  binary                                  9
% 3.55/0.99  lits                                    58
% 3.55/0.99  lits eq                                 10
% 3.55/0.99  fd_pure                                 0
% 3.55/0.99  fd_pseudo                               0
% 3.55/0.99  fd_cond                                 3
% 3.55/0.99  fd_pseudo_cond                          0
% 3.55/0.99  AC symbols                              0
% 3.55/0.99  
% 3.55/0.99  ------ Schedule dynamic 5 is on 
% 3.55/0.99  
% 3.55/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.55/0.99  
% 3.55/0.99  
% 3.55/0.99  ------ 
% 3.55/0.99  Current options:
% 3.55/0.99  ------ 
% 3.55/0.99  
% 3.55/0.99  ------ Input Options
% 3.55/0.99  
% 3.55/0.99  --out_options                           all
% 3.55/0.99  --tptp_safe_out                         true
% 3.55/0.99  --problem_path                          ""
% 3.55/0.99  --include_path                          ""
% 3.55/0.99  --clausifier                            res/vclausify_rel
% 3.55/0.99  --clausifier_options                    ""
% 3.55/0.99  --stdin                                 false
% 3.55/0.99  --stats_out                             all
% 3.55/0.99  
% 3.55/0.99  ------ General Options
% 3.55/0.99  
% 3.55/0.99  --fof                                   false
% 3.55/0.99  --time_out_real                         305.
% 3.55/0.99  --time_out_virtual                      -1.
% 3.55/0.99  --symbol_type_check                     false
% 3.55/0.99  --clausify_out                          false
% 3.55/0.99  --sig_cnt_out                           false
% 3.55/0.99  --trig_cnt_out                          false
% 3.55/0.99  --trig_cnt_out_tolerance                1.
% 3.55/0.99  --trig_cnt_out_sk_spl                   false
% 3.55/0.99  --abstr_cl_out                          false
% 3.55/0.99  
% 3.55/0.99  ------ Global Options
% 3.55/0.99  
% 3.55/0.99  --schedule                              default
% 3.55/0.99  --add_important_lit                     false
% 3.55/0.99  --prop_solver_per_cl                    1000
% 3.55/0.99  --min_unsat_core                        false
% 3.55/0.99  --soft_assumptions                      false
% 3.55/0.99  --soft_lemma_size                       3
% 3.55/0.99  --prop_impl_unit_size                   0
% 3.55/0.99  --prop_impl_unit                        []
% 3.55/0.99  --share_sel_clauses                     true
% 3.55/0.99  --reset_solvers                         false
% 3.55/0.99  --bc_imp_inh                            [conj_cone]
% 3.55/0.99  --conj_cone_tolerance                   3.
% 3.55/0.99  --extra_neg_conj                        none
% 3.55/0.99  --large_theory_mode                     true
% 3.55/0.99  --prolific_symb_bound                   200
% 3.55/0.99  --lt_threshold                          2000
% 3.55/0.99  --clause_weak_htbl                      true
% 3.55/0.99  --gc_record_bc_elim                     false
% 3.55/0.99  
% 3.55/0.99  ------ Preprocessing Options
% 3.55/0.99  
% 3.55/0.99  --preprocessing_flag                    true
% 3.55/0.99  --time_out_prep_mult                    0.1
% 3.55/0.99  --splitting_mode                        input
% 3.55/0.99  --splitting_grd                         true
% 3.55/0.99  --splitting_cvd                         false
% 3.55/0.99  --splitting_cvd_svl                     false
% 3.55/0.99  --splitting_nvd                         32
% 3.55/0.99  --sub_typing                            true
% 3.55/0.99  --prep_gs_sim                           true
% 3.55/0.99  --prep_unflatten                        true
% 3.55/0.99  --prep_res_sim                          true
% 3.55/0.99  --prep_upred                            true
% 3.55/0.99  --prep_sem_filter                       exhaustive
% 3.55/0.99  --prep_sem_filter_out                   false
% 3.55/0.99  --pred_elim                             true
% 3.55/0.99  --res_sim_input                         true
% 3.55/0.99  --eq_ax_congr_red                       true
% 3.55/0.99  --pure_diseq_elim                       true
% 3.55/0.99  --brand_transform                       false
% 3.55/0.99  --non_eq_to_eq                          false
% 3.55/0.99  --prep_def_merge                        true
% 3.55/0.99  --prep_def_merge_prop_impl              false
% 3.55/0.99  --prep_def_merge_mbd                    true
% 3.55/0.99  --prep_def_merge_tr_red                 false
% 3.55/0.99  --prep_def_merge_tr_cl                  false
% 3.55/0.99  --smt_preprocessing                     true
% 3.55/0.99  --smt_ac_axioms                         fast
% 3.55/0.99  --preprocessed_out                      false
% 3.55/0.99  --preprocessed_stats                    false
% 3.55/0.99  
% 3.55/0.99  ------ Abstraction refinement Options
% 3.55/0.99  
% 3.55/0.99  --abstr_ref                             []
% 3.55/0.99  --abstr_ref_prep                        false
% 3.55/0.99  --abstr_ref_until_sat                   false
% 3.55/0.99  --abstr_ref_sig_restrict                funpre
% 3.55/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.55/0.99  --abstr_ref_under                       []
% 3.55/0.99  
% 3.55/0.99  ------ SAT Options
% 3.55/0.99  
% 3.55/0.99  --sat_mode                              false
% 3.55/0.99  --sat_fm_restart_options                ""
% 3.55/0.99  --sat_gr_def                            false
% 3.55/0.99  --sat_epr_types                         true
% 3.55/0.99  --sat_non_cyclic_types                  false
% 3.55/0.99  --sat_finite_models                     false
% 3.55/0.99  --sat_fm_lemmas                         false
% 3.55/0.99  --sat_fm_prep                           false
% 3.55/0.99  --sat_fm_uc_incr                        true
% 3.55/0.99  --sat_out_model                         small
% 3.55/0.99  --sat_out_clauses                       false
% 3.55/0.99  
% 3.55/0.99  ------ QBF Options
% 3.55/0.99  
% 3.55/0.99  --qbf_mode                              false
% 3.55/0.99  --qbf_elim_univ                         false
% 3.55/0.99  --qbf_dom_inst                          none
% 3.55/0.99  --qbf_dom_pre_inst                      false
% 3.55/0.99  --qbf_sk_in                             false
% 3.55/0.99  --qbf_pred_elim                         true
% 3.55/0.99  --qbf_split                             512
% 3.55/0.99  
% 3.55/0.99  ------ BMC1 Options
% 3.55/0.99  
% 3.55/0.99  --bmc1_incremental                      false
% 3.55/0.99  --bmc1_axioms                           reachable_all
% 3.55/0.99  --bmc1_min_bound                        0
% 3.55/0.99  --bmc1_max_bound                        -1
% 3.55/0.99  --bmc1_max_bound_default                -1
% 3.55/0.99  --bmc1_symbol_reachability              true
% 3.55/0.99  --bmc1_property_lemmas                  false
% 3.55/0.99  --bmc1_k_induction                      false
% 3.55/0.99  --bmc1_non_equiv_states                 false
% 3.55/0.99  --bmc1_deadlock                         false
% 3.55/0.99  --bmc1_ucm                              false
% 3.55/0.99  --bmc1_add_unsat_core                   none
% 3.55/0.99  --bmc1_unsat_core_children              false
% 3.55/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.55/0.99  --bmc1_out_stat                         full
% 3.55/0.99  --bmc1_ground_init                      false
% 3.55/0.99  --bmc1_pre_inst_next_state              false
% 3.55/0.99  --bmc1_pre_inst_state                   false
% 3.55/0.99  --bmc1_pre_inst_reach_state             false
% 3.55/0.99  --bmc1_out_unsat_core                   false
% 3.55/0.99  --bmc1_aig_witness_out                  false
% 3.55/0.99  --bmc1_verbose                          false
% 3.55/0.99  --bmc1_dump_clauses_tptp                false
% 3.55/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.55/0.99  --bmc1_dump_file                        -
% 3.55/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.55/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.55/0.99  --bmc1_ucm_extend_mode                  1
% 3.55/0.99  --bmc1_ucm_init_mode                    2
% 3.55/0.99  --bmc1_ucm_cone_mode                    none
% 3.55/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.55/0.99  --bmc1_ucm_relax_model                  4
% 3.55/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.55/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.55/0.99  --bmc1_ucm_layered_model                none
% 3.55/0.99  --bmc1_ucm_max_lemma_size               10
% 3.55/0.99  
% 3.55/0.99  ------ AIG Options
% 3.55/0.99  
% 3.55/0.99  --aig_mode                              false
% 3.55/0.99  
% 3.55/0.99  ------ Instantiation Options
% 3.55/0.99  
% 3.55/0.99  --instantiation_flag                    true
% 3.55/0.99  --inst_sos_flag                         true
% 3.55/0.99  --inst_sos_phase                        true
% 3.55/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.55/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.55/0.99  --inst_lit_sel_side                     none
% 3.55/0.99  --inst_solver_per_active                1400
% 3.55/0.99  --inst_solver_calls_frac                1.
% 3.55/0.99  --inst_passive_queue_type               priority_queues
% 3.55/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.55/0.99  --inst_passive_queues_freq              [25;2]
% 3.55/0.99  --inst_dismatching                      true
% 3.55/0.99  --inst_eager_unprocessed_to_passive     true
% 3.55/0.99  --inst_prop_sim_given                   true
% 3.55/0.99  --inst_prop_sim_new                     false
% 3.55/0.99  --inst_subs_new                         false
% 3.55/0.99  --inst_eq_res_simp                      false
% 3.55/0.99  --inst_subs_given                       false
% 3.55/0.99  --inst_orphan_elimination               true
% 3.55/0.99  --inst_learning_loop_flag               true
% 3.55/0.99  --inst_learning_start                   3000
% 3.55/0.99  --inst_learning_factor                  2
% 3.55/0.99  --inst_start_prop_sim_after_learn       3
% 3.55/0.99  --inst_sel_renew                        solver
% 3.55/0.99  --inst_lit_activity_flag                true
% 3.55/0.99  --inst_restr_to_given                   false
% 3.55/0.99  --inst_activity_threshold               500
% 3.55/0.99  --inst_out_proof                        true
% 3.55/0.99  
% 3.55/0.99  ------ Resolution Options
% 3.55/0.99  
% 3.55/0.99  --resolution_flag                       false
% 3.55/0.99  --res_lit_sel                           adaptive
% 3.55/0.99  --res_lit_sel_side                      none
% 3.55/0.99  --res_ordering                          kbo
% 3.55/0.99  --res_to_prop_solver                    active
% 3.55/0.99  --res_prop_simpl_new                    false
% 3.55/0.99  --res_prop_simpl_given                  true
% 3.55/0.99  --res_passive_queue_type                priority_queues
% 3.55/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.55/0.99  --res_passive_queues_freq               [15;5]
% 3.55/0.99  --res_forward_subs                      full
% 3.55/0.99  --res_backward_subs                     full
% 3.55/0.99  --res_forward_subs_resolution           true
% 3.55/0.99  --res_backward_subs_resolution          true
% 3.55/0.99  --res_orphan_elimination                true
% 3.55/0.99  --res_time_limit                        2.
% 3.55/0.99  --res_out_proof                         true
% 3.55/0.99  
% 3.55/0.99  ------ Superposition Options
% 3.55/0.99  
% 3.55/0.99  --superposition_flag                    true
% 3.55/0.99  --sup_passive_queue_type                priority_queues
% 3.55/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.55/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.55/0.99  --demod_completeness_check              fast
% 3.55/0.99  --demod_use_ground                      true
% 3.55/0.99  --sup_to_prop_solver                    passive
% 3.55/0.99  --sup_prop_simpl_new                    true
% 3.55/0.99  --sup_prop_simpl_given                  true
% 3.55/0.99  --sup_fun_splitting                     true
% 3.55/0.99  --sup_smt_interval                      50000
% 3.55/0.99  
% 3.55/0.99  ------ Superposition Simplification Setup
% 3.55/0.99  
% 3.55/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.55/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.55/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.55/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.55/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.55/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.55/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.55/0.99  --sup_immed_triv                        [TrivRules]
% 3.55/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.55/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.55/0.99  --sup_immed_bw_main                     []
% 3.55/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.55/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.55/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.55/0.99  --sup_input_bw                          []
% 3.55/0.99  
% 3.55/0.99  ------ Combination Options
% 3.55/0.99  
% 3.55/0.99  --comb_res_mult                         3
% 3.55/0.99  --comb_sup_mult                         2
% 3.55/0.99  --comb_inst_mult                        10
% 3.55/0.99  
% 3.55/0.99  ------ Debug Options
% 3.55/0.99  
% 3.55/0.99  --dbg_backtrace                         false
% 3.55/0.99  --dbg_dump_prop_clauses                 false
% 3.55/0.99  --dbg_dump_prop_clauses_file            -
% 3.55/0.99  --dbg_out_stat                          false
% 3.55/0.99  
% 3.55/0.99  
% 3.55/0.99  
% 3.55/0.99  
% 3.55/0.99  ------ Proving...
% 3.55/0.99  
% 3.55/0.99  
% 3.55/0.99  % SZS status Theorem for theBenchmark.p
% 3.55/0.99  
% 3.55/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.55/0.99  
% 3.55/0.99  fof(f3,axiom,(
% 3.55/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.55/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/0.99  
% 3.55/0.99  fof(f15,plain,(
% 3.55/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.55/0.99    inference(rectify,[],[f3])).
% 3.55/0.99  
% 3.55/0.99  fof(f17,plain,(
% 3.55/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 3.55/0.99    inference(ennf_transformation,[],[f15])).
% 3.55/0.99  
% 3.55/0.99  fof(f32,plain,(
% 3.55/0.99    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.55/0.99    introduced(choice_axiom,[])).
% 3.55/0.99  
% 3.55/0.99  fof(f33,plain,(
% 3.55/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 3.55/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f32])).
% 3.55/0.99  
% 3.55/0.99  fof(f45,plain,(
% 3.55/0.99    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 3.55/0.99    inference(cnf_transformation,[],[f33])).
% 3.55/0.99  
% 3.55/0.99  fof(f13,conjecture,(
% 3.55/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) => r1_xboole_0(X0,X1))))),
% 3.55/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/0.99  
% 3.55/0.99  fof(f14,negated_conjecture,(
% 3.55/0.99    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) => r1_xboole_0(X0,X1))))),
% 3.55/0.99    inference(negated_conjecture,[],[f13])).
% 3.55/0.99  
% 3.55/0.99  fof(f29,plain,(
% 3.55/0.99    ? [X0] : (? [X1] : ((~r1_xboole_0(X0,X1) & r1_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 3.55/0.99    inference(ennf_transformation,[],[f14])).
% 3.55/0.99  
% 3.55/0.99  fof(f30,plain,(
% 3.55/0.99    ? [X0] : (? [X1] : (~r1_xboole_0(X0,X1) & r1_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 3.55/0.99    inference(flattening,[],[f29])).
% 3.55/0.99  
% 3.55/0.99  fof(f40,plain,(
% 3.55/0.99    ( ! [X0] : (? [X1] : (~r1_xboole_0(X0,X1) & r1_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) & v1_relat_1(X1)) => (~r1_xboole_0(X0,sK3) & r1_xboole_0(k2_relat_1(X0),k2_relat_1(sK3)) & v1_relat_1(sK3))) )),
% 3.55/0.99    introduced(choice_axiom,[])).
% 3.55/0.99  
% 3.55/0.99  fof(f39,plain,(
% 3.55/0.99    ? [X0] : (? [X1] : (~r1_xboole_0(X0,X1) & r1_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_xboole_0(sK2,X1) & r1_xboole_0(k2_relat_1(sK2),k2_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(sK2))),
% 3.55/0.99    introduced(choice_axiom,[])).
% 3.55/0.99  
% 3.55/0.99  fof(f41,plain,(
% 3.55/0.99    (~r1_xboole_0(sK2,sK3) & r1_xboole_0(k2_relat_1(sK2),k2_relat_1(sK3)) & v1_relat_1(sK3)) & v1_relat_1(sK2)),
% 3.55/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f30,f40,f39])).
% 3.55/0.99  
% 3.55/0.99  fof(f64,plain,(
% 3.55/0.99    r1_xboole_0(k2_relat_1(sK2),k2_relat_1(sK3))),
% 3.55/0.99    inference(cnf_transformation,[],[f41])).
% 3.55/0.99  
% 3.55/0.99  fof(f10,axiom,(
% 3.55/0.99    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 3.55/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/0.99  
% 3.55/0.99  fof(f25,plain,(
% 3.55/0.99    ! [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.55/0.99    inference(ennf_transformation,[],[f10])).
% 3.55/0.99  
% 3.55/0.99  fof(f38,plain,(
% 3.55/0.99    ! [X0,X1] : (((k1_xboole_0 = k10_relat_1(X1,X0) | ~r1_xboole_0(k2_relat_1(X1),X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.55/0.99    inference(nnf_transformation,[],[f25])).
% 3.55/0.99  
% 3.55/0.99  fof(f58,plain,(
% 3.55/0.99    ( ! [X0,X1] : (k1_xboole_0 = k10_relat_1(X1,X0) | ~r1_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.55/0.99    inference(cnf_transformation,[],[f38])).
% 3.55/0.99  
% 3.55/0.99  fof(f62,plain,(
% 3.55/0.99    v1_relat_1(sK2)),
% 3.55/0.99    inference(cnf_transformation,[],[f41])).
% 3.55/0.99  
% 3.55/0.99  fof(f9,axiom,(
% 3.55/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 3.55/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/0.99  
% 3.55/0.99  fof(f24,plain,(
% 3.55/0.99    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 3.55/0.99    inference(ennf_transformation,[],[f9])).
% 3.55/0.99  
% 3.55/0.99  fof(f34,plain,(
% 3.55/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.55/0.99    inference(nnf_transformation,[],[f24])).
% 3.55/0.99  
% 3.55/0.99  fof(f35,plain,(
% 3.55/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.55/0.99    inference(rectify,[],[f34])).
% 3.55/0.99  
% 3.55/0.99  fof(f36,plain,(
% 3.55/0.99    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK1(X0,X1,X2)),X2) & r2_hidden(sK1(X0,X1,X2),k2_relat_1(X2))))),
% 3.55/0.99    introduced(choice_axiom,[])).
% 3.55/0.99  
% 3.55/0.99  fof(f37,plain,(
% 3.55/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK1(X0,X1,X2)),X2) & r2_hidden(sK1(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.55/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f36])).
% 3.55/0.99  
% 3.55/0.99  fof(f55,plain,(
% 3.55/0.99    ( ! [X2,X0,X1] : (r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.55/0.99    inference(cnf_transformation,[],[f37])).
% 3.55/0.99  
% 3.55/0.99  fof(f47,plain,(
% 3.55/0.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 3.55/0.99    inference(cnf_transformation,[],[f33])).
% 3.55/0.99  
% 3.55/0.99  fof(f2,axiom,(
% 3.55/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 3.55/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/0.99  
% 3.55/0.99  fof(f16,plain,(
% 3.55/0.99    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 3.55/0.99    inference(ennf_transformation,[],[f2])).
% 3.55/0.99  
% 3.55/0.99  fof(f44,plain,(
% 3.55/0.99    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 3.55/0.99    inference(cnf_transformation,[],[f16])).
% 3.55/0.99  
% 3.55/0.99  fof(f53,plain,(
% 3.55/0.99    ( ! [X2,X0,X1] : (r2_hidden(sK1(X0,X1,X2),k2_relat_1(X2)) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.55/0.99    inference(cnf_transformation,[],[f37])).
% 3.55/0.99  
% 3.55/0.99  fof(f1,axiom,(
% 3.55/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 3.55/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/0.99  
% 3.55/0.99  fof(f31,plain,(
% 3.55/0.99    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 3.55/0.99    inference(nnf_transformation,[],[f1])).
% 3.55/0.99  
% 3.55/0.99  fof(f42,plain,(
% 3.55/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 3.55/0.99    inference(cnf_transformation,[],[f31])).
% 3.55/0.99  
% 3.55/0.99  fof(f11,axiom,(
% 3.55/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))))),
% 3.55/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/0.99  
% 3.55/0.99  fof(f26,plain,(
% 3.55/0.99    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.55/0.99    inference(ennf_transformation,[],[f11])).
% 3.55/0.99  
% 3.55/0.99  fof(f59,plain,(
% 3.55/0.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.55/0.99    inference(cnf_transformation,[],[f26])).
% 3.55/0.99  
% 3.55/0.99  fof(f63,plain,(
% 3.55/0.99    v1_relat_1(sK3)),
% 3.55/0.99    inference(cnf_transformation,[],[f41])).
% 3.55/0.99  
% 3.55/0.99  fof(f4,axiom,(
% 3.55/0.99    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k1_xboole_0 = X0)),
% 3.55/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/0.99  
% 3.55/0.99  fof(f18,plain,(
% 3.55/0.99    ! [X0,X1,X2] : (k1_xboole_0 = X0 | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 3.55/0.99    inference(ennf_transformation,[],[f4])).
% 3.55/0.99  
% 3.55/0.99  fof(f19,plain,(
% 3.55/0.99    ! [X0,X1,X2] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 3.55/0.99    inference(flattening,[],[f18])).
% 3.55/0.99  
% 3.55/0.99  fof(f48,plain,(
% 3.55/0.99    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 3.55/0.99    inference(cnf_transformation,[],[f19])).
% 3.55/0.99  
% 3.55/0.99  fof(f5,axiom,(
% 3.55/0.99    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 3.55/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/0.99  
% 3.55/0.99  fof(f20,plain,(
% 3.55/0.99    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 3.55/0.99    inference(ennf_transformation,[],[f5])).
% 3.55/0.99  
% 3.55/0.99  fof(f49,plain,(
% 3.55/0.99    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 3.55/0.99    inference(cnf_transformation,[],[f20])).
% 3.55/0.99  
% 3.55/0.99  fof(f12,axiom,(
% 3.55/0.99    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 3.55/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/0.99  
% 3.55/0.99  fof(f27,plain,(
% 3.55/0.99    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.55/0.99    inference(ennf_transformation,[],[f12])).
% 3.55/0.99  
% 3.55/0.99  fof(f28,plain,(
% 3.55/0.99    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.55/0.99    inference(flattening,[],[f27])).
% 3.55/0.99  
% 3.55/0.99  fof(f61,plain,(
% 3.55/0.99    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.55/0.99    inference(cnf_transformation,[],[f28])).
% 3.55/0.99  
% 3.55/0.99  fof(f43,plain,(
% 3.55/0.99    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 3.55/0.99    inference(cnf_transformation,[],[f31])).
% 3.55/0.99  
% 3.55/0.99  fof(f65,plain,(
% 3.55/0.99    ~r1_xboole_0(sK2,sK3)),
% 3.55/0.99    inference(cnf_transformation,[],[f41])).
% 3.55/0.99  
% 3.55/0.99  cnf(c_5,plain,
% 3.55/0.99      ( r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1) ),
% 3.55/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_333,plain,
% 3.55/0.99      ( r2_hidden(sK0(X0_43,X1_43),X0_43) | r1_xboole_0(X0_43,X1_43) ),
% 3.55/0.99      inference(subtyping,[status(esa)],[c_5]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_890,plain,
% 3.55/0.99      ( r2_hidden(sK0(X0_43,X1_43),X0_43) = iProver_top
% 3.55/0.99      | r1_xboole_0(X0_43,X1_43) = iProver_top ),
% 3.55/0.99      inference(predicate_to_equality,[status(thm)],[c_333]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_21,negated_conjecture,
% 3.55/0.99      ( r1_xboole_0(k2_relat_1(sK2),k2_relat_1(sK3)) ),
% 3.55/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_317,negated_conjecture,
% 3.55/0.99      ( r1_xboole_0(k2_relat_1(sK2),k2_relat_1(sK3)) ),
% 3.55/0.99      inference(subtyping,[status(esa)],[c_21]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_906,plain,
% 3.55/0.99      ( r1_xboole_0(k2_relat_1(sK2),k2_relat_1(sK3)) = iProver_top ),
% 3.55/0.99      inference(predicate_to_equality,[status(thm)],[c_317]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_15,plain,
% 3.55/0.99      ( ~ r1_xboole_0(k2_relat_1(X0),X1)
% 3.55/0.99      | ~ v1_relat_1(X0)
% 3.55/0.99      | k10_relat_1(X0,X1) = k1_xboole_0 ),
% 3.55/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_323,plain,
% 3.55/0.99      ( ~ r1_xboole_0(k2_relat_1(X0_43),X1_43)
% 3.55/0.99      | ~ v1_relat_1(X0_43)
% 3.55/0.99      | k10_relat_1(X0_43,X1_43) = k1_xboole_0 ),
% 3.55/0.99      inference(subtyping,[status(esa)],[c_15]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_900,plain,
% 3.55/0.99      ( k10_relat_1(X0_43,X1_43) = k1_xboole_0
% 3.55/0.99      | r1_xboole_0(k2_relat_1(X0_43),X1_43) != iProver_top
% 3.55/0.99      | v1_relat_1(X0_43) != iProver_top ),
% 3.55/0.99      inference(predicate_to_equality,[status(thm)],[c_323]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_2076,plain,
% 3.55/0.99      ( k10_relat_1(sK2,k2_relat_1(sK3)) = k1_xboole_0
% 3.55/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.55/0.99      inference(superposition,[status(thm)],[c_906,c_900]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_23,negated_conjecture,
% 3.55/0.99      ( v1_relat_1(sK2) ),
% 3.55/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_24,plain,
% 3.55/0.99      ( v1_relat_1(sK2) = iProver_top ),
% 3.55/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_2225,plain,
% 3.55/0.99      ( k10_relat_1(sK2,k2_relat_1(sK3)) = k1_xboole_0 ),
% 3.55/0.99      inference(global_propositional_subsumption,
% 3.55/0.99                [status(thm)],
% 3.55/0.99                [c_2076,c_24]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_12,plain,
% 3.55/0.99      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 3.55/0.99      | r2_hidden(sK1(X0,X2,X1),X2)
% 3.55/0.99      | ~ v1_relat_1(X1) ),
% 3.55/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_326,plain,
% 3.55/0.99      ( ~ r2_hidden(X0_44,k10_relat_1(X0_43,X1_43))
% 3.55/0.99      | r2_hidden(sK1(X0_44,X1_43,X0_43),X1_43)
% 3.55/0.99      | ~ v1_relat_1(X0_43) ),
% 3.55/0.99      inference(subtyping,[status(esa)],[c_12]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_897,plain,
% 3.55/0.99      ( r2_hidden(X0_44,k10_relat_1(X0_43,X1_43)) != iProver_top
% 3.55/0.99      | r2_hidden(sK1(X0_44,X1_43,X0_43),X1_43) = iProver_top
% 3.55/0.99      | v1_relat_1(X0_43) != iProver_top ),
% 3.55/0.99      inference(predicate_to_equality,[status(thm)],[c_326]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_3,plain,
% 3.55/0.99      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 3.55/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_335,plain,
% 3.55/0.99      ( ~ r2_hidden(X0_44,X0_43)
% 3.55/0.99      | ~ r2_hidden(X0_44,X1_43)
% 3.55/0.99      | ~ r1_xboole_0(X0_43,X1_43) ),
% 3.55/0.99      inference(subtyping,[status(esa)],[c_3]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_888,plain,
% 3.55/0.99      ( r2_hidden(X0_44,X0_43) != iProver_top
% 3.55/0.99      | r2_hidden(X0_44,X1_43) != iProver_top
% 3.55/0.99      | r1_xboole_0(X1_43,X0_43) != iProver_top ),
% 3.55/0.99      inference(predicate_to_equality,[status(thm)],[c_335]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_2754,plain,
% 3.55/0.99      ( r2_hidden(X0_44,k10_relat_1(X0_43,X1_43)) != iProver_top
% 3.55/0.99      | r2_hidden(sK1(X0_44,X1_43,X0_43),X2_43) != iProver_top
% 3.55/0.99      | r1_xboole_0(X1_43,X2_43) != iProver_top
% 3.55/0.99      | v1_relat_1(X0_43) != iProver_top ),
% 3.55/0.99      inference(superposition,[status(thm)],[c_897,c_888]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_6623,plain,
% 3.55/0.99      ( r2_hidden(X0_44,k10_relat_1(X0_43,X1_43)) != iProver_top
% 3.55/0.99      | r1_xboole_0(X1_43,X1_43) != iProver_top
% 3.55/0.99      | v1_relat_1(X0_43) != iProver_top ),
% 3.55/0.99      inference(superposition,[status(thm)],[c_897,c_2754]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_6633,plain,
% 3.55/0.99      ( r2_hidden(X0_44,k1_xboole_0) != iProver_top
% 3.55/0.99      | r1_xboole_0(k2_relat_1(sK3),k2_relat_1(sK3)) != iProver_top
% 3.55/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.55/0.99      inference(superposition,[status(thm)],[c_2225,c_6623]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_2,plain,
% 3.55/0.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 3.55/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_336,plain,
% 3.55/0.99      ( ~ r1_xboole_0(X0_43,X1_43) | r1_xboole_0(X1_43,X0_43) ),
% 3.55/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_887,plain,
% 3.55/0.99      ( r1_xboole_0(X0_43,X1_43) != iProver_top
% 3.55/0.99      | r1_xboole_0(X1_43,X0_43) = iProver_top ),
% 3.55/0.99      inference(predicate_to_equality,[status(thm)],[c_336]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_1292,plain,
% 3.55/0.99      ( r1_xboole_0(k2_relat_1(sK3),k2_relat_1(sK2)) = iProver_top ),
% 3.55/0.99      inference(superposition,[status(thm)],[c_906,c_887]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_14,plain,
% 3.55/0.99      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 3.55/0.99      | r2_hidden(sK1(X0,X2,X1),k2_relat_1(X1))
% 3.55/0.99      | ~ v1_relat_1(X1) ),
% 3.55/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_324,plain,
% 3.55/0.99      ( ~ r2_hidden(X0_44,k10_relat_1(X0_43,X1_43))
% 3.55/0.99      | r2_hidden(sK1(X0_44,X1_43,X0_43),k2_relat_1(X0_43))
% 3.55/0.99      | ~ v1_relat_1(X0_43) ),
% 3.55/0.99      inference(subtyping,[status(esa)],[c_14]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_899,plain,
% 3.55/0.99      ( r2_hidden(X0_44,k10_relat_1(X0_43,X1_43)) != iProver_top
% 3.55/0.99      | r2_hidden(sK1(X0_44,X1_43,X0_43),k2_relat_1(X0_43)) = iProver_top
% 3.55/0.99      | v1_relat_1(X0_43) != iProver_top ),
% 3.55/0.99      inference(predicate_to_equality,[status(thm)],[c_324]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_6622,plain,
% 3.55/0.99      ( r2_hidden(X0_44,k10_relat_1(X0_43,X1_43)) != iProver_top
% 3.55/0.99      | r1_xboole_0(X1_43,k2_relat_1(X0_43)) != iProver_top
% 3.55/0.99      | v1_relat_1(X0_43) != iProver_top ),
% 3.55/0.99      inference(superposition,[status(thm)],[c_899,c_2754]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_7028,plain,
% 3.55/0.99      ( r2_hidden(X0_44,k1_xboole_0) != iProver_top
% 3.55/0.99      | r1_xboole_0(k2_relat_1(sK3),k2_relat_1(sK2)) != iProver_top
% 3.55/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.55/0.99      inference(superposition,[status(thm)],[c_2225,c_6622]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_7049,plain,
% 3.55/0.99      ( r2_hidden(X0_44,k1_xboole_0) != iProver_top ),
% 3.55/0.99      inference(global_propositional_subsumption,
% 3.55/0.99                [status(thm)],
% 3.55/0.99                [c_6633,c_24,c_1292,c_7028]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_7057,plain,
% 3.55/0.99      ( r1_xboole_0(k1_xboole_0,X0_43) = iProver_top ),
% 3.55/0.99      inference(superposition,[status(thm)],[c_890,c_7049]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_7064,plain,
% 3.55/0.99      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.55/0.99      inference(instantiation,[status(thm)],[c_7057]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_1,plain,
% 3.55/0.99      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 3.55/0.99      inference(cnf_transformation,[],[f42]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_337,plain,
% 3.55/0.99      ( ~ r1_xboole_0(X0_43,X1_43)
% 3.55/0.99      | k3_xboole_0(X0_43,X1_43) = k1_xboole_0 ),
% 3.55/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_886,plain,
% 3.55/0.99      ( k3_xboole_0(X0_43,X1_43) = k1_xboole_0
% 3.55/0.99      | r1_xboole_0(X0_43,X1_43) != iProver_top ),
% 3.55/0.99      inference(predicate_to_equality,[status(thm)],[c_337]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_1189,plain,
% 3.55/0.99      ( k3_xboole_0(k2_relat_1(sK2),k2_relat_1(sK3)) = k1_xboole_0 ),
% 3.55/0.99      inference(superposition,[status(thm)],[c_906,c_886]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_17,plain,
% 3.55/0.99      ( r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))
% 3.55/0.99      | ~ v1_relat_1(X0)
% 3.55/0.99      | ~ v1_relat_1(X1) ),
% 3.55/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_321,plain,
% 3.55/0.99      ( r1_tarski(k2_relat_1(k3_xboole_0(X0_43,X1_43)),k3_xboole_0(k2_relat_1(X0_43),k2_relat_1(X1_43)))
% 3.55/0.99      | ~ v1_relat_1(X0_43)
% 3.55/0.99      | ~ v1_relat_1(X1_43) ),
% 3.55/0.99      inference(subtyping,[status(esa)],[c_17]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_902,plain,
% 3.55/0.99      ( r1_tarski(k2_relat_1(k3_xboole_0(X0_43,X1_43)),k3_xboole_0(k2_relat_1(X0_43),k2_relat_1(X1_43))) = iProver_top
% 3.55/0.99      | v1_relat_1(X0_43) != iProver_top
% 3.55/0.99      | v1_relat_1(X1_43) != iProver_top ),
% 3.55/0.99      inference(predicate_to_equality,[status(thm)],[c_321]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_2890,plain,
% 3.55/0.99      ( r1_tarski(k2_relat_1(k3_xboole_0(sK2,sK3)),k1_xboole_0) = iProver_top
% 3.55/0.99      | v1_relat_1(sK3) != iProver_top
% 3.55/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.55/0.99      inference(superposition,[status(thm)],[c_1189,c_902]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_22,negated_conjecture,
% 3.55/0.99      ( v1_relat_1(sK3) ),
% 3.55/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_25,plain,
% 3.55/0.99      ( v1_relat_1(sK3) = iProver_top ),
% 3.55/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_3026,plain,
% 3.55/0.99      ( r1_tarski(k2_relat_1(k3_xboole_0(sK2,sK3)),k1_xboole_0) = iProver_top ),
% 3.55/0.99      inference(global_propositional_subsumption,
% 3.55/0.99                [status(thm)],
% 3.55/0.99                [c_2890,c_24,c_25]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_6,plain,
% 3.55/0.99      ( ~ r1_tarski(X0,X1)
% 3.55/0.99      | ~ r1_tarski(X0,X2)
% 3.55/0.99      | ~ r1_xboole_0(X2,X1)
% 3.55/0.99      | k1_xboole_0 = X0 ),
% 3.55/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_332,plain,
% 3.55/0.99      ( ~ r1_tarski(X0_43,X1_43)
% 3.55/0.99      | ~ r1_tarski(X0_43,X2_43)
% 3.55/0.99      | ~ r1_xboole_0(X2_43,X1_43)
% 3.55/0.99      | k1_xboole_0 = X0_43 ),
% 3.55/0.99      inference(subtyping,[status(esa)],[c_6]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_891,plain,
% 3.55/0.99      ( k1_xboole_0 = X0_43
% 3.55/0.99      | r1_tarski(X0_43,X1_43) != iProver_top
% 3.55/0.99      | r1_tarski(X0_43,X2_43) != iProver_top
% 3.55/0.99      | r1_xboole_0(X2_43,X1_43) != iProver_top ),
% 3.55/0.99      inference(predicate_to_equality,[status(thm)],[c_332]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_3030,plain,
% 3.55/0.99      ( k2_relat_1(k3_xboole_0(sK2,sK3)) = k1_xboole_0
% 3.55/0.99      | r1_tarski(k2_relat_1(k3_xboole_0(sK2,sK3)),X0_43) != iProver_top
% 3.55/0.99      | r1_xboole_0(X0_43,k1_xboole_0) != iProver_top ),
% 3.55/0.99      inference(superposition,[status(thm)],[c_3026,c_891]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_3032,plain,
% 3.55/0.99      ( k2_relat_1(k3_xboole_0(sK2,sK3)) = k1_xboole_0
% 3.55/0.99      | r1_tarski(k2_relat_1(k3_xboole_0(sK2,sK3)),k1_xboole_0) != iProver_top
% 3.55/0.99      | r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.55/0.99      inference(instantiation,[status(thm)],[c_3030]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_340,plain,( X0_43 = X0_43 ),theory(equality) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_1313,plain,
% 3.55/0.99      ( k3_xboole_0(sK2,sK3) = k3_xboole_0(sK2,sK3) ),
% 3.55/0.99      inference(instantiation,[status(thm)],[c_340]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_7,plain,
% 3.55/0.99      ( ~ v1_relat_1(X0) | v1_relat_1(k3_xboole_0(X0,X1)) ),
% 3.55/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_331,plain,
% 3.55/0.99      ( ~ v1_relat_1(X0_43) | v1_relat_1(k3_xboole_0(X0_43,X1_43)) ),
% 3.55/0.99      inference(subtyping,[status(esa)],[c_7]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_1298,plain,
% 3.55/0.99      ( v1_relat_1(k3_xboole_0(sK2,sK3)) | ~ v1_relat_1(sK2) ),
% 3.55/0.99      inference(instantiation,[status(thm)],[c_331]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_18,plain,
% 3.55/0.99      ( ~ v1_relat_1(X0)
% 3.55/0.99      | k2_relat_1(X0) != k1_xboole_0
% 3.55/0.99      | k1_xboole_0 = X0 ),
% 3.55/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_320,plain,
% 3.55/0.99      ( ~ v1_relat_1(X0_43)
% 3.55/0.99      | k2_relat_1(X0_43) != k1_xboole_0
% 3.55/0.99      | k1_xboole_0 = X0_43 ),
% 3.55/0.99      inference(subtyping,[status(esa)],[c_18]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_1088,plain,
% 3.55/0.99      ( ~ v1_relat_1(k3_xboole_0(sK2,sK3))
% 3.55/0.99      | k2_relat_1(k3_xboole_0(sK2,sK3)) != k1_xboole_0
% 3.55/0.99      | k1_xboole_0 = k3_xboole_0(sK2,sK3) ),
% 3.55/0.99      inference(instantiation,[status(thm)],[c_320]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_342,plain,
% 3.55/0.99      ( X0_43 != X1_43 | X2_43 != X1_43 | X2_43 = X0_43 ),
% 3.55/0.99      theory(equality) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_954,plain,
% 3.55/0.99      ( k3_xboole_0(sK2,sK3) != X0_43
% 3.55/0.99      | k3_xboole_0(sK2,sK3) = k1_xboole_0
% 3.55/0.99      | k1_xboole_0 != X0_43 ),
% 3.55/0.99      inference(instantiation,[status(thm)],[c_342]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_1009,plain,
% 3.55/0.99      ( k3_xboole_0(sK2,sK3) != k3_xboole_0(sK2,sK3)
% 3.55/0.99      | k3_xboole_0(sK2,sK3) = k1_xboole_0
% 3.55/0.99      | k1_xboole_0 != k3_xboole_0(sK2,sK3) ),
% 3.55/0.99      inference(instantiation,[status(thm)],[c_954]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_0,plain,
% 3.55/0.99      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 3.55/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_338,plain,
% 3.55/0.99      ( r1_xboole_0(X0_43,X1_43)
% 3.55/0.99      | k3_xboole_0(X0_43,X1_43) != k1_xboole_0 ),
% 3.55/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_942,plain,
% 3.55/0.99      ( r1_xboole_0(sK2,sK3) | k3_xboole_0(sK2,sK3) != k1_xboole_0 ),
% 3.55/0.99      inference(instantiation,[status(thm)],[c_338]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_20,negated_conjecture,
% 3.55/0.99      ( ~ r1_xboole_0(sK2,sK3) ),
% 3.55/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(contradiction,plain,
% 3.55/0.99      ( $false ),
% 3.55/0.99      inference(minisat,
% 3.55/0.99                [status(thm)],
% 3.55/0.99                [c_7064,c_3032,c_2890,c_1313,c_1298,c_1088,c_1009,c_942,
% 3.55/0.99                 c_20,c_25,c_24,c_23]) ).
% 3.55/0.99  
% 3.55/0.99  
% 3.55/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.55/0.99  
% 3.55/0.99  ------                               Statistics
% 3.55/0.99  
% 3.55/0.99  ------ General
% 3.55/0.99  
% 3.55/0.99  abstr_ref_over_cycles:                  0
% 3.55/0.99  abstr_ref_under_cycles:                 0
% 3.55/0.99  gc_basic_clause_elim:                   0
% 3.55/0.99  forced_gc_time:                         0
% 3.55/0.99  parsing_time:                           0.01
% 3.55/0.99  unif_index_cands_time:                  0.
% 3.55/0.99  unif_index_add_time:                    0.
% 3.55/0.99  orderings_time:                         0.
% 3.55/0.99  out_proof_time:                         0.011
% 3.55/0.99  total_time:                             0.262
% 3.55/0.99  num_of_symbols:                         51
% 3.55/0.99  num_of_terms:                           12071
% 3.55/0.99  
% 3.55/0.99  ------ Preprocessing
% 3.55/0.99  
% 3.55/0.99  num_of_splits:                          0
% 3.55/0.99  num_of_split_atoms:                     0
% 3.55/0.99  num_of_reused_defs:                     0
% 3.55/0.99  num_eq_ax_congr_red:                    22
% 3.55/0.99  num_of_sem_filtered_clauses:            1
% 3.55/0.99  num_of_subtypes:                        2
% 3.55/0.99  monotx_restored_types:                  0
% 3.55/0.99  sat_num_of_epr_types:                   0
% 3.55/0.99  sat_num_of_non_cyclic_types:            0
% 3.55/0.99  sat_guarded_non_collapsed_types:        1
% 3.55/0.99  num_pure_diseq_elim:                    0
% 3.55/0.99  simp_replaced_by:                       0
% 3.55/0.99  res_preprocessed:                       93
% 3.55/0.99  prep_upred:                             0
% 3.55/0.99  prep_unflattend:                        0
% 3.55/0.99  smt_new_axioms:                         0
% 3.55/0.99  pred_elim_cands:                        4
% 3.55/0.99  pred_elim:                              0
% 3.55/0.99  pred_elim_cl:                           0
% 3.55/0.99  pred_elim_cycles:                       1
% 3.55/0.99  merged_defs:                            6
% 3.55/0.99  merged_defs_ncl:                        0
% 3.55/0.99  bin_hyper_res:                          6
% 3.55/0.99  prep_cycles:                            3
% 3.55/0.99  pred_elim_time:                         0.
% 3.55/0.99  splitting_time:                         0.
% 3.55/0.99  sem_filter_time:                        0.
% 3.55/0.99  monotx_time:                            0.
% 3.55/0.99  subtype_inf_time:                       0.
% 3.55/0.99  
% 3.55/0.99  ------ Problem properties
% 3.55/0.99  
% 3.55/0.99  clauses:                                24
% 3.55/0.99  conjectures:                            4
% 3.55/0.99  epr:                                    6
% 3.55/0.99  horn:                                   22
% 3.55/0.99  ground:                                 4
% 3.55/0.99  unary:                                  4
% 3.55/0.99  binary:                                 9
% 3.55/0.99  lits:                                   58
% 3.55/0.99  lits_eq:                                10
% 3.55/0.99  fd_pure:                                0
% 3.55/0.99  fd_pseudo:                              0
% 3.55/0.99  fd_cond:                                3
% 3.55/0.99  fd_pseudo_cond:                         0
% 3.55/0.99  ac_symbols:                             0
% 3.55/0.99  
% 3.55/0.99  ------ Propositional Solver
% 3.55/0.99  
% 3.55/0.99  prop_solver_calls:                      29
% 3.55/0.99  prop_fast_solver_calls:                 712
% 3.55/0.99  smt_solver_calls:                       0
% 3.55/0.99  smt_fast_solver_calls:                  0
% 3.55/0.99  prop_num_of_clauses:                    3747
% 3.55/0.99  prop_preprocess_simplified:             7442
% 3.55/0.99  prop_fo_subsumed:                       16
% 3.55/0.99  prop_solver_time:                       0.
% 3.55/0.99  smt_solver_time:                        0.
% 3.55/0.99  smt_fast_solver_time:                   0.
% 3.55/0.99  prop_fast_solver_time:                  0.
% 3.55/0.99  prop_unsat_core_time:                   0.
% 3.55/0.99  
% 3.55/0.99  ------ QBF
% 3.55/0.99  
% 3.55/0.99  qbf_q_res:                              0
% 3.55/0.99  qbf_num_tautologies:                    0
% 3.55/0.99  qbf_prep_cycles:                        0
% 3.55/0.99  
% 3.55/0.99  ------ BMC1
% 3.55/0.99  
% 3.55/0.99  bmc1_current_bound:                     -1
% 3.55/0.99  bmc1_last_solved_bound:                 -1
% 3.55/0.99  bmc1_unsat_core_size:                   -1
% 3.55/0.99  bmc1_unsat_core_parents_size:           -1
% 3.55/0.99  bmc1_merge_next_fun:                    0
% 3.55/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.55/0.99  
% 3.55/0.99  ------ Instantiation
% 3.55/0.99  
% 3.55/0.99  inst_num_of_clauses:                    979
% 3.55/0.99  inst_num_in_passive:                    419
% 3.55/0.99  inst_num_in_active:                     468
% 3.55/0.99  inst_num_in_unprocessed:                92
% 3.55/0.99  inst_num_of_loops:                      500
% 3.55/0.99  inst_num_of_learning_restarts:          0
% 3.55/0.99  inst_num_moves_active_passive:          28
% 3.55/0.99  inst_lit_activity:                      0
% 3.55/0.99  inst_lit_activity_moves:                0
% 3.55/0.99  inst_num_tautologies:                   0
% 3.55/0.99  inst_num_prop_implied:                  0
% 3.55/0.99  inst_num_existing_simplified:           0
% 3.55/0.99  inst_num_eq_res_simplified:             0
% 3.55/0.99  inst_num_child_elim:                    0
% 3.55/0.99  inst_num_of_dismatching_blockings:      541
% 3.55/0.99  inst_num_of_non_proper_insts:           949
% 3.55/0.99  inst_num_of_duplicates:                 0
% 3.55/0.99  inst_inst_num_from_inst_to_res:         0
% 3.55/0.99  inst_dismatching_checking_time:         0.
% 3.55/0.99  
% 3.55/0.99  ------ Resolution
% 3.55/0.99  
% 3.55/0.99  res_num_of_clauses:                     0
% 3.55/0.99  res_num_in_passive:                     0
% 3.55/0.99  res_num_in_active:                      0
% 3.55/0.99  res_num_of_loops:                       96
% 3.55/0.99  res_forward_subset_subsumed:            70
% 3.55/0.99  res_backward_subset_subsumed:           0
% 3.55/0.99  res_forward_subsumed:                   0
% 3.55/0.99  res_backward_subsumed:                  0
% 3.55/0.99  res_forward_subsumption_resolution:     0
% 3.55/0.99  res_backward_subsumption_resolution:    0
% 3.55/0.99  res_clause_to_clause_subsumption:       492
% 3.55/0.99  res_orphan_elimination:                 0
% 3.55/0.99  res_tautology_del:                      79
% 3.55/0.99  res_num_eq_res_simplified:              0
% 3.55/0.99  res_num_sel_changes:                    0
% 3.55/0.99  res_moves_from_active_to_pass:          0
% 3.55/0.99  
% 3.55/0.99  ------ Superposition
% 3.55/0.99  
% 3.55/0.99  sup_time_total:                         0.
% 3.55/0.99  sup_time_generating:                    0.
% 3.55/0.99  sup_time_sim_full:                      0.
% 3.55/0.99  sup_time_sim_immed:                     0.
% 3.55/0.99  
% 3.55/0.99  sup_num_of_clauses:                     182
% 3.55/0.99  sup_num_in_active:                      100
% 3.55/0.99  sup_num_in_passive:                     82
% 3.55/0.99  sup_num_of_loops:                       99
% 3.55/0.99  sup_fw_superposition:                   122
% 3.55/0.99  sup_bw_superposition:                   80
% 3.55/0.99  sup_immediate_simplified:               22
% 3.55/0.99  sup_given_eliminated:                   0
% 3.55/0.99  comparisons_done:                       0
% 3.55/0.99  comparisons_avoided:                    0
% 3.55/0.99  
% 3.55/0.99  ------ Simplifications
% 3.55/0.99  
% 3.55/0.99  
% 3.55/0.99  sim_fw_subset_subsumed:                 15
% 3.55/0.99  sim_bw_subset_subsumed:                 7
% 3.55/0.99  sim_fw_subsumed:                        0
% 3.55/0.99  sim_bw_subsumed:                        0
% 3.55/0.99  sim_fw_subsumption_res:                 0
% 3.55/0.99  sim_bw_subsumption_res:                 0
% 3.55/0.99  sim_tautology_del:                      1
% 3.55/0.99  sim_eq_tautology_del:                   2
% 3.55/0.99  sim_eq_res_simp:                        0
% 3.55/0.99  sim_fw_demodulated:                     0
% 3.55/0.99  sim_bw_demodulated:                     0
% 3.55/0.99  sim_light_normalised:                   6
% 3.55/0.99  sim_joinable_taut:                      0
% 3.55/0.99  sim_joinable_simp:                      0
% 3.55/0.99  sim_ac_normalised:                      0
% 3.55/0.99  sim_smt_subsumption:                    0
% 3.55/0.99  
%------------------------------------------------------------------------------
