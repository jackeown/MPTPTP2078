%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0004+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:13 EST 2020

% Result     : Theorem 0.47s
% Output     : CNFRefutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   68 (  92 expanded)
%              Number of clauses        :   43 (  48 expanded)
%              Number of leaves         :   11 (  19 expanded)
%              Depth                    :   12
%              Number of atoms          :  161 ( 228 expanded)
%              Number of equality atoms :   60 (  69 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f11,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f10])).

fof(f12,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f12])).

fof(f18,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ~ ( r1_xboole_0(X0,X1)
            & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
        & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
            & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f7,plain,(
    ~ ! [X0,X1] :
        ( ~ ( r1_xboole_0(X0,X1)
            & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
        & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
            & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f6])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      | ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
        & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))
     => r2_hidden(sK3,k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X0,X1] :
        ( ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
        | ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) )
   => ( ( r1_xboole_0(sK1,sK2)
        & ? [X2] : r2_hidden(X2,k3_xboole_0(sK1,sK2)) )
      | ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(sK1,sK2))
        & ~ r1_xboole_0(sK1,sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ( r1_xboole_0(sK1,sK2)
      & r2_hidden(sK3,k3_xboole_0(sK1,sK2)) )
    | ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(sK1,sK2))
      & ~ r1_xboole_0(sK1,sK2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f9,f16,f15])).

fof(f27,plain,(
    ! [X3] :
      ( r1_xboole_0(sK1,sK2)
      | ~ r2_hidden(X3,k3_xboole_0(sK1,sK2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f19,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f24,plain,
    ( r2_hidden(sK3,k3_xboole_0(sK1,sK2))
    | ~ r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_4,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_303,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_461,plain,
    ( v1_xboole_0(o_0_0_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_303])).

cnf(c_5,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_302,plain,
    ( ~ v1_xboole_0(X0_39)
    | k1_xboole_0 = X0_39 ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_462,plain,
    ( k1_xboole_0 = X0_39
    | v1_xboole_0(X0_39) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_302])).

cnf(c_581,plain,
    ( o_0_0_xboole_0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_461,c_462])).

cnf(c_583,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_581,c_461])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_304,plain,
    ( ~ r2_hidden(X0_38,X0_39)
    | ~ v1_xboole_0(X0_39) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_567,plain,
    ( ~ r2_hidden(sK3,k3_xboole_0(sK1,sK2))
    | ~ v1_xboole_0(k3_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_304])).

cnf(c_568,plain,
    ( r2_hidden(sK3,k3_xboole_0(sK1,sK2)) != iProver_top
    | v1_xboole_0(k3_xboole_0(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_567])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_82,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_3])).

cnf(c_6,negated_conjecture,
    ( r1_xboole_0(sK1,sK2)
    | ~ r2_hidden(X0,k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_190,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(sK1,sK2))
    | k3_xboole_0(X1,X2) = k1_xboole_0
    | sK2 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_82,c_6])).

cnf(c_191,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(sK1,sK2))
    | k3_xboole_0(sK1,sK2) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_190])).

cnf(c_299,plain,
    ( ~ r2_hidden(X0_38,k3_xboole_0(sK1,sK2))
    | k3_xboole_0(sK1,sK2) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_191])).

cnf(c_548,plain,
    ( ~ r2_hidden(sK0(k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2))
    | k3_xboole_0(sK1,sK2) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_299])).

cnf(c_552,plain,
    ( k3_xboole_0(sK1,sK2) = k1_xboole_0
    | r2_hidden(sK0(k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_548])).

cnf(c_310,plain,
    ( ~ v1_xboole_0(X0_39)
    | v1_xboole_0(X1_39)
    | X1_39 != X0_39 ),
    theory(equality)).

cnf(c_531,plain,
    ( ~ v1_xboole_0(X0_39)
    | v1_xboole_0(k3_xboole_0(sK1,sK2))
    | k3_xboole_0(sK1,sK2) != X0_39 ),
    inference(instantiation,[status(thm)],[c_310])).

cnf(c_532,plain,
    ( k3_xboole_0(sK1,sK2) != X0_39
    | v1_xboole_0(X0_39) != iProver_top
    | v1_xboole_0(k3_xboole_0(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_531])).

cnf(c_534,plain,
    ( k3_xboole_0(sK1,sK2) != k1_xboole_0
    | v1_xboole_0(k3_xboole_0(sK1,sK2)) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_532])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_305,plain,
    ( r2_hidden(sK0(X0_39),X0_39)
    | v1_xboole_0(X0_39) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_528,plain,
    ( r2_hidden(sK0(k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2))
    | v1_xboole_0(k3_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_305])).

cnf(c_529,plain,
    ( r2_hidden(sK0(k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2)) = iProver_top
    | v1_xboole_0(k3_xboole_0(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_528])).

cnf(c_518,plain,
    ( ~ v1_xboole_0(k3_xboole_0(sK1,sK2))
    | k1_xboole_0 = k3_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_302])).

cnf(c_519,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,sK2)
    | v1_xboole_0(k3_xboole_0(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_518])).

cnf(c_308,plain,
    ( X0_39 = X0_39 ),
    theory(equality)).

cnf(c_516,plain,
    ( k3_xboole_0(sK1,sK2) = k3_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_308])).

cnf(c_309,plain,
    ( X0_39 != X1_39
    | X2_39 != X1_39
    | X2_39 = X0_39 ),
    theory(equality)).

cnf(c_514,plain,
    ( k3_xboole_0(sK1,sK2) != X0_39
    | k3_xboole_0(sK1,sK2) = k1_xboole_0
    | k1_xboole_0 != X0_39 ),
    inference(instantiation,[status(thm)],[c_309])).

cnf(c_515,plain,
    ( k3_xboole_0(sK1,sK2) != k3_xboole_0(sK1,sK2)
    | k3_xboole_0(sK1,sK2) = k1_xboole_0
    | k1_xboole_0 != k3_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_514])).

cnf(c_2,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_80,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_2])).

cnf(c_9,negated_conjecture,
    ( ~ r1_xboole_0(sK1,sK2)
    | r2_hidden(sK3,k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_180,plain,
    ( r2_hidden(sK3,k3_xboole_0(sK1,sK2))
    | k3_xboole_0(X0,X1) != k1_xboole_0
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_80,c_9])).

cnf(c_181,plain,
    ( r2_hidden(sK3,k3_xboole_0(sK1,sK2))
    | k3_xboole_0(sK1,sK2) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_180])).

cnf(c_300,plain,
    ( r2_hidden(sK3,k3_xboole_0(sK1,sK2))
    | k3_xboole_0(sK1,sK2) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_181])).

cnf(c_326,plain,
    ( k3_xboole_0(sK1,sK2) != k1_xboole_0
    | r2_hidden(sK3,k3_xboole_0(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_300])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_583,c_568,c_552,c_534,c_529,c_519,c_516,c_515,c_326])).


%------------------------------------------------------------------------------
