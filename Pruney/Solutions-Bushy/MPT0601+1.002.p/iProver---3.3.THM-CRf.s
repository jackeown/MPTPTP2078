%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0601+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:41 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 149 expanded)
%              Number of clauses        :   49 (  54 expanded)
%              Number of leaves         :   16 (  33 expanded)
%              Depth                    :   14
%              Number of atoms          :  245 ( 492 expanded)
%              Number of equality atoms :   69 ( 149 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | ~ r2_hidden(X1,k11_relat_1(X2,X0)) )
        & ( r2_hidden(X1,k11_relat_1(X2,X0))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k11_relat_1(X1,X0) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k1_relat_1(X1))
        <=> k11_relat_1(X1,X0) != k1_xboole_0 ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <~> k11_relat_1(X1,X0) != k1_xboole_0 )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ( k11_relat_1(X1,X0) = k1_xboole_0
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
      & ( k11_relat_1(X1,X0) != k1_xboole_0
        | r2_hidden(X0,k1_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ( k11_relat_1(X1,X0) = k1_xboole_0
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
      & ( k11_relat_1(X1,X0) != k1_xboole_0
        | r2_hidden(X0,k1_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f27,plain,
    ( ? [X0,X1] :
        ( ( k11_relat_1(X1,X0) = k1_xboole_0
          | ~ r2_hidden(X0,k1_relat_1(X1)) )
        & ( k11_relat_1(X1,X0) != k1_xboole_0
          | r2_hidden(X0,k1_relat_1(X1)) )
        & v1_relat_1(X1) )
   => ( ( k11_relat_1(sK5,sK4) = k1_xboole_0
        | ~ r2_hidden(sK4,k1_relat_1(sK5)) )
      & ( k11_relat_1(sK5,sK4) != k1_xboole_0
        | r2_hidden(sK4,k1_relat_1(sK5)) )
      & v1_relat_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ( k11_relat_1(sK5,sK4) = k1_xboole_0
      | ~ r2_hidden(sK4,k1_relat_1(sK5)) )
    & ( k11_relat_1(sK5,sK4) != k1_xboole_0
      | r2_hidden(sK4,k1_relat_1(sK5)) )
    & v1_relat_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f26,f27])).

fof(f40,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f28])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f17,plain,(
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
    inference(rectify,[],[f16])).

fof(f20,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK1(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK0(X0,X1),X3),X0)
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK0(X0,X1),X4),X0)
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK0(X0,X1),X3),X0)
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0)
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f20,f19,f18])).

fof(f30,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f43,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f30])).

fof(f29,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f44,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f29])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f38,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f42,plain,
    ( k11_relat_1(sK5,sK4) = k1_xboole_0
    | ~ r2_hidden(sK4,k1_relat_1(sK5)) ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f3,f22])).

fof(f34,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f41,plain,
    ( k11_relat_1(sK5,sK4) != k1_xboole_0
    | r2_hidden(sK4,k1_relat_1(sK5)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_2192,plain,
    ( ~ r2_hidden(sK2(sK5,sK4),k11_relat_1(sK5,sK4))
    | ~ v1_xboole_0(k11_relat_1(sK5,sK4)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_7,plain,
    ( r2_hidden(X0,k11_relat_1(X1,X2))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_13,negated_conjecture,
    ( v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_211,plain,
    ( r2_hidden(X0,k11_relat_1(X1,X2))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_13])).

cnf(c_212,plain,
    ( r2_hidden(X0,k11_relat_1(sK5,X1))
    | ~ r2_hidden(k4_tarski(X1,X0),sK5) ),
    inference(unflattening,[status(thm)],[c_211])).

cnf(c_335,plain,
    ( ~ r2_hidden(k4_tarski(X1,X0),sK5)
    | r2_hidden(X0,k11_relat_1(sK5,X1)) ),
    inference(prop_impl,[status(thm)],[c_212])).

cnf(c_336,plain,
    ( r2_hidden(X0,k11_relat_1(sK5,X1))
    | ~ r2_hidden(k4_tarski(X1,X0),sK5) ),
    inference(renaming,[status(thm)],[c_335])).

cnf(c_1658,plain,
    ( r2_hidden(sK2(sK5,sK4),k11_relat_1(sK5,sK4))
    | ~ r2_hidden(k4_tarski(sK4,sK2(sK5,sK4)),sK5) ),
    inference(instantiation,[status(thm)],[c_336])).

cnf(c_2,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1391,plain,
    ( ~ r2_hidden(k4_tarski(sK4,sK3(k11_relat_1(sK5,sK4))),sK5)
    | r2_hidden(sK4,k1_relat_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1392,plain,
    ( r2_hidden(k4_tarski(sK4,sK3(k11_relat_1(sK5,sK4))),sK5) != iProver_top
    | r2_hidden(sK4,k1_relat_1(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1391])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,sK2(X1,X0)),X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1088,plain,
    ( r2_hidden(k4_tarski(sK4,sK2(sK5,sK4)),sK5)
    | ~ r2_hidden(sK4,k1_relat_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_452,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_905,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k11_relat_1(sK5,sK4))
    | k11_relat_1(sK5,sK4) != X0 ),
    inference(instantiation,[status(thm)],[c_452])).

cnf(c_992,plain,
    ( v1_xboole_0(k11_relat_1(sK5,sK4))
    | ~ v1_xboole_0(o_0_0_xboole_0)
    | k11_relat_1(sK5,sK4) != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_905])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k11_relat_1(X1,X2))
    | r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_223,plain,
    ( ~ r2_hidden(X0,k11_relat_1(X1,X2))
    | r2_hidden(k4_tarski(X2,X0),X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_13])).

cnf(c_224,plain,
    ( ~ r2_hidden(X0,k11_relat_1(sK5,X1))
    | r2_hidden(k4_tarski(X1,X0),sK5) ),
    inference(unflattening,[status(thm)],[c_223])).

cnf(c_333,plain,
    ( r2_hidden(k4_tarski(X1,X0),sK5)
    | ~ r2_hidden(X0,k11_relat_1(sK5,X1)) ),
    inference(prop_impl,[status(thm)],[c_224])).

cnf(c_334,plain,
    ( ~ r2_hidden(X0,k11_relat_1(sK5,X1))
    | r2_hidden(k4_tarski(X1,X0),sK5) ),
    inference(renaming,[status(thm)],[c_333])).

cnf(c_989,plain,
    ( r2_hidden(k4_tarski(sK4,sK3(k11_relat_1(sK5,sK4))),sK5)
    | ~ r2_hidden(sK3(k11_relat_1(sK5,sK4)),k11_relat_1(sK5,sK4)) ),
    inference(instantiation,[status(thm)],[c_334])).

cnf(c_990,plain,
    ( r2_hidden(k4_tarski(sK4,sK3(k11_relat_1(sK5,sK4))),sK5) = iProver_top
    | r2_hidden(sK3(k11_relat_1(sK5,sK4)),k11_relat_1(sK5,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_989])).

cnf(c_4,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_779,plain,
    ( v1_xboole_0(o_0_0_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_9,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_778,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_873,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_779,c_778])).

cnf(c_11,negated_conjecture,
    ( ~ r2_hidden(sK4,k1_relat_1(sK5))
    | k11_relat_1(sK5,sK4) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_776,plain,
    ( k11_relat_1(sK5,sK4) = k1_xboole_0
    | r2_hidden(sK4,k1_relat_1(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_915,plain,
    ( k11_relat_1(sK5,sK4) = o_0_0_xboole_0
    | r2_hidden(sK4,k1_relat_1(sK5)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_873,c_776])).

cnf(c_5,plain,
    ( m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_196,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | X1 != X2
    | sK3(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_8])).

cnf(c_197,plain,
    ( r2_hidden(sK3(X0),X0)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_196])).

cnf(c_910,plain,
    ( r2_hidden(sK3(k11_relat_1(sK5,sK4)),k11_relat_1(sK5,sK4))
    | v1_xboole_0(k11_relat_1(sK5,sK4)) ),
    inference(instantiation,[status(thm)],[c_197])).

cnf(c_911,plain,
    ( r2_hidden(sK3(k11_relat_1(sK5,sK4)),k11_relat_1(sK5,sK4)) = iProver_top
    | v1_xboole_0(k11_relat_1(sK5,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_910])).

cnf(c_881,plain,
    ( ~ v1_xboole_0(k11_relat_1(sK5,sK4))
    | k1_xboole_0 = k11_relat_1(sK5,sK4) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_882,plain,
    ( k1_xboole_0 = k11_relat_1(sK5,sK4)
    | v1_xboole_0(k11_relat_1(sK5,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_881])).

cnf(c_447,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_875,plain,
    ( k11_relat_1(sK5,sK4) = k11_relat_1(sK5,sK4) ),
    inference(instantiation,[status(thm)],[c_447])).

cnf(c_448,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_866,plain,
    ( k11_relat_1(sK5,sK4) != X0
    | k11_relat_1(sK5,sK4) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_448])).

cnf(c_874,plain,
    ( k11_relat_1(sK5,sK4) != k11_relat_1(sK5,sK4)
    | k11_relat_1(sK5,sK4) = k1_xboole_0
    | k1_xboole_0 != k11_relat_1(sK5,sK4) ),
    inference(instantiation,[status(thm)],[c_866])).

cnf(c_16,plain,
    ( k11_relat_1(sK5,sK4) = k1_xboole_0
    | r2_hidden(sK4,k1_relat_1(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_12,negated_conjecture,
    ( r2_hidden(sK4,k1_relat_1(sK5))
    | k11_relat_1(sK5,sK4) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_15,plain,
    ( k11_relat_1(sK5,sK4) != k1_xboole_0
    | r2_hidden(sK4,k1_relat_1(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2192,c_1658,c_1392,c_1088,c_992,c_990,c_915,c_911,c_882,c_875,c_874,c_4,c_16,c_15,c_12])).


%------------------------------------------------------------------------------
