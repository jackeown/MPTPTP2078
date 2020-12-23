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
% DateTime   : Thu Dec  3 11:47:15 EST 2020

% Result     : Theorem 2.44s
% Output     : CNFRefutation 2.44s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 367 expanded)
%              Number of clauses        :   55 ( 137 expanded)
%              Number of leaves         :   21 (  68 expanded)
%              Depth                    :   22
%              Number of atoms          :  305 ( 966 expanded)
%              Number of equality atoms :  156 ( 562 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) )
     => v1_relat_1(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f14])).

fof(f26,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK2(X0)
        & r2_hidden(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ( ! [X2,X3] : k4_tarski(X2,X3) != sK2(X0)
        & r2_hidden(sK2(X0),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f41])).

fof(f67,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | r2_hidden(sK2(X0),X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f8,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tarski(X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f65,f57])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_xboole_0(k2_tarski(X0,X2),X1)
        & ~ r2_hidden(X2,X1)
        & ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) )
     => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ( ~ r1_xboole_0(X2,X3)
        & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f38])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f87,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f60])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f86,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f61])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f18,conjecture,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f18])).

fof(f29,plain,(
    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f19])).

fof(f43,plain,
    ( ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)
   => k1_xboole_0 != k10_relat_1(k1_xboole_0,sK3) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f43])).

fof(f73,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK1(X0,X1) != X0
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( sK1(X0,X1) = X0
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK1(X0,X1) != X0
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( sK1(X0,X1) = X0
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f36])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f78,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f52,f57])).

fof(f85,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_tarski(X0,X0)) ) ),
    inference(equality_resolution,[],[f78])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ~ ( r1_xboole_0(X0,X1)
          & r1_tarski(X2,X1)
          & r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X2,X0)
      | v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X2,X0)
      | v1_xboole_0(X2) ) ),
    inference(flattening,[],[f22])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X2,X0)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f9,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f79,plain,(
    ! [X0] : ~ v1_xboole_0(k2_tarski(X0,X0)) ),
    inference(definition_unfolding,[],[f58,f57])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k4_xboole_0(k2_relat_1(X1),k4_xboole_0(k2_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f69,f49])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f17,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f17])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = k10_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f70,plain,(
    ! [X0] :
      ( k1_xboole_0 = k10_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_21,plain,
    ( r2_hidden(sK2(X0),X0)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_856,plain,
    ( r2_hidden(sK2(X0),X0) = iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k2_tarski(X0,X0),X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_860,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(k2_tarski(X0,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_19,plain,
    ( r1_xboole_0(k2_tarski(X0,X1),X2)
    | r2_hidden(X0,X2)
    | r2_hidden(X1,X2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_858,plain,
    ( r1_xboole_0(k2_tarski(X0,X1),X2) = iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X1,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_15,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_862,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_13,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1826,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(k1_xboole_0,k2_zfmisc_1(X2,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_862])).

cnf(c_1854,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(k1_xboole_0,k2_zfmisc_1(X2,k2_zfmisc_1(X3,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_862,c_1826])).

cnf(c_2391,plain,
    ( r1_xboole_0(k1_xboole_0,k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))) = iProver_top
    | r2_hidden(X3,X2) = iProver_top
    | r2_hidden(X4,X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_858,c_1854])).

cnf(c_12,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_16,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_861,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1372,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(k2_zfmisc_1(X0,X2),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_12,c_861])).

cnf(c_4615,plain,
    ( r1_xboole_0(k2_zfmisc_1(k1_xboole_0,X0),k1_xboole_0) = iProver_top
    | r2_hidden(X1,X2) = iProver_top
    | r2_hidden(X3,X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2391,c_1372])).

cnf(c_4627,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4615,c_13])).

cnf(c_26,negated_conjecture,
    ( k1_xboole_0 != k10_relat_1(k1_xboole_0,sK3) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k2_tarski(X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1020,plain,
    ( ~ r2_hidden(k1_xboole_0,k2_tarski(k10_relat_1(k1_xboole_0,sK3),k10_relat_1(k1_xboole_0,sK3)))
    | k1_xboole_0 = k10_relat_1(k1_xboole_0,sK3) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1021,plain,
    ( k1_xboole_0 = k10_relat_1(k1_xboole_0,sK3)
    | r2_hidden(k1_xboole_0,k2_tarski(k10_relat_1(k1_xboole_0,sK3),k10_relat_1(k1_xboole_0,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1020])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1124,plain,
    ( ~ r2_hidden(k1_xboole_0,X0)
    | r2_hidden(k1_xboole_0,k2_tarski(k10_relat_1(k1_xboole_0,sK3),k10_relat_1(k1_xboole_0,sK3)))
    | ~ r1_tarski(X0,k2_tarski(k10_relat_1(k1_xboole_0,sK3),k10_relat_1(k1_xboole_0,sK3))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1125,plain,
    ( r2_hidden(k1_xboole_0,X0) != iProver_top
    | r2_hidden(k1_xboole_0,k2_tarski(k10_relat_1(k1_xboole_0,sK3),k10_relat_1(k1_xboole_0,sK3))) = iProver_top
    | r1_tarski(X0,k2_tarski(k10_relat_1(k1_xboole_0,sK3),k10_relat_1(k1_xboole_0,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1124])).

cnf(c_1127,plain,
    ( r2_hidden(k1_xboole_0,k2_tarski(k10_relat_1(k1_xboole_0,sK3),k10_relat_1(k1_xboole_0,sK3))) = iProver_top
    | r2_hidden(k1_xboole_0,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,k2_tarski(k10_relat_1(k1_xboole_0,sK3),k10_relat_1(k1_xboole_0,sK3))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1125])).

cnf(c_4,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1195,plain,
    ( r1_tarski(k1_xboole_0,k2_tarski(k10_relat_1(k1_xboole_0,sK3),k10_relat_1(k1_xboole_0,sK3))) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1198,plain,
    ( r1_tarski(k1_xboole_0,k2_tarski(k10_relat_1(k1_xboole_0,sK3),k10_relat_1(k1_xboole_0,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1195])).

cnf(c_4773,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top
    | r2_hidden(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4627])).

cnf(c_5118,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4627,c_26,c_1021,c_1127,c_1198,c_4773])).

cnf(c_6,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X2,X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_868,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | v1_xboole_0(X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5131,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5118,c_868])).

cnf(c_5222,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | v1_xboole_0(k2_tarski(X0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_860,c_5131])).

cnf(c_11,plain,
    ( ~ v1_xboole_0(k2_tarski(X0,X0)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_54,plain,
    ( v1_xboole_0(k2_tarski(X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_5730,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5222,c_54])).

cnf(c_5740,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_856,c_5730])).

cnf(c_22,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k4_xboole_0(k2_relat_1(X0),k4_xboole_0(k2_relat_1(X0),X1))) = k10_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_855,plain,
    ( k10_relat_1(X0,k4_xboole_0(k2_relat_1(X0),k4_xboole_0(k2_relat_1(X0),X1))) = k10_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_5754,plain,
    ( k10_relat_1(k1_xboole_0,k4_xboole_0(k2_relat_1(k1_xboole_0),k4_xboole_0(k2_relat_1(k1_xboole_0),X0))) = k10_relat_1(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_5740,c_855])).

cnf(c_5,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_24,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_5759,plain,
    ( k10_relat_1(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) = k10_relat_1(k1_xboole_0,X0) ),
    inference(light_normalisation,[status(thm)],[c_5754,c_5,c_24])).

cnf(c_5760,plain,
    ( k10_relat_1(k1_xboole_0,X0) = k10_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_5759,c_5])).

cnf(c_23,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_854,plain,
    ( k10_relat_1(X0,k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_5755,plain,
    ( k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5740,c_854])).

cnf(c_6186,plain,
    ( k10_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5760,c_5755])).

cnf(c_6188,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6186,c_26])).

cnf(c_53,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_14,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_52,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6188,c_53,c_52])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:51:56 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.44/0.96  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.44/0.96  
% 2.44/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.44/0.96  
% 2.44/0.96  ------  iProver source info
% 2.44/0.96  
% 2.44/0.96  git: date: 2020-06-30 10:37:57 +0100
% 2.44/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.44/0.96  git: non_committed_changes: false
% 2.44/0.96  git: last_make_outside_of_git: false
% 2.44/0.96  
% 2.44/0.96  ------ 
% 2.44/0.96  
% 2.44/0.96  ------ Input Options
% 2.44/0.96  
% 2.44/0.96  --out_options                           all
% 2.44/0.96  --tptp_safe_out                         true
% 2.44/0.96  --problem_path                          ""
% 2.44/0.96  --include_path                          ""
% 2.44/0.96  --clausifier                            res/vclausify_rel
% 2.44/0.96  --clausifier_options                    --mode clausify
% 2.44/0.96  --stdin                                 false
% 2.44/0.96  --stats_out                             all
% 2.44/0.96  
% 2.44/0.96  ------ General Options
% 2.44/0.96  
% 2.44/0.96  --fof                                   false
% 2.44/0.96  --time_out_real                         305.
% 2.44/0.96  --time_out_virtual                      -1.
% 2.44/0.96  --symbol_type_check                     false
% 2.44/0.96  --clausify_out                          false
% 2.44/0.96  --sig_cnt_out                           false
% 2.44/0.96  --trig_cnt_out                          false
% 2.44/0.96  --trig_cnt_out_tolerance                1.
% 2.44/0.96  --trig_cnt_out_sk_spl                   false
% 2.44/0.96  --abstr_cl_out                          false
% 2.44/0.96  
% 2.44/0.96  ------ Global Options
% 2.44/0.96  
% 2.44/0.96  --schedule                              default
% 2.44/0.96  --add_important_lit                     false
% 2.44/0.96  --prop_solver_per_cl                    1000
% 2.44/0.96  --min_unsat_core                        false
% 2.44/0.96  --soft_assumptions                      false
% 2.44/0.96  --soft_lemma_size                       3
% 2.44/0.96  --prop_impl_unit_size                   0
% 2.44/0.96  --prop_impl_unit                        []
% 2.44/0.96  --share_sel_clauses                     true
% 2.44/0.96  --reset_solvers                         false
% 2.44/0.96  --bc_imp_inh                            [conj_cone]
% 2.44/0.96  --conj_cone_tolerance                   3.
% 2.44/0.96  --extra_neg_conj                        none
% 2.44/0.96  --large_theory_mode                     true
% 2.44/0.96  --prolific_symb_bound                   200
% 2.44/0.96  --lt_threshold                          2000
% 2.44/0.96  --clause_weak_htbl                      true
% 2.44/0.96  --gc_record_bc_elim                     false
% 2.44/0.96  
% 2.44/0.96  ------ Preprocessing Options
% 2.44/0.96  
% 2.44/0.96  --preprocessing_flag                    true
% 2.44/0.96  --time_out_prep_mult                    0.1
% 2.44/0.96  --splitting_mode                        input
% 2.44/0.96  --splitting_grd                         true
% 2.44/0.96  --splitting_cvd                         false
% 2.44/0.96  --splitting_cvd_svl                     false
% 2.44/0.96  --splitting_nvd                         32
% 2.44/0.96  --sub_typing                            true
% 2.44/0.96  --prep_gs_sim                           true
% 2.44/0.96  --prep_unflatten                        true
% 2.44/0.96  --prep_res_sim                          true
% 2.44/0.96  --prep_upred                            true
% 2.44/0.96  --prep_sem_filter                       exhaustive
% 2.44/0.96  --prep_sem_filter_out                   false
% 2.44/0.96  --pred_elim                             true
% 2.44/0.96  --res_sim_input                         true
% 2.44/0.96  --eq_ax_congr_red                       true
% 2.44/0.96  --pure_diseq_elim                       true
% 2.44/0.96  --brand_transform                       false
% 2.44/0.96  --non_eq_to_eq                          false
% 2.44/0.96  --prep_def_merge                        true
% 2.44/0.96  --prep_def_merge_prop_impl              false
% 2.44/0.96  --prep_def_merge_mbd                    true
% 2.44/0.96  --prep_def_merge_tr_red                 false
% 2.44/0.96  --prep_def_merge_tr_cl                  false
% 2.44/0.96  --smt_preprocessing                     true
% 2.44/0.96  --smt_ac_axioms                         fast
% 2.44/0.96  --preprocessed_out                      false
% 2.44/0.96  --preprocessed_stats                    false
% 2.44/0.96  
% 2.44/0.96  ------ Abstraction refinement Options
% 2.44/0.96  
% 2.44/0.96  --abstr_ref                             []
% 2.44/0.96  --abstr_ref_prep                        false
% 2.44/0.96  --abstr_ref_until_sat                   false
% 2.44/0.96  --abstr_ref_sig_restrict                funpre
% 2.44/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 2.44/0.96  --abstr_ref_under                       []
% 2.44/0.96  
% 2.44/0.96  ------ SAT Options
% 2.44/0.96  
% 2.44/0.96  --sat_mode                              false
% 2.44/0.96  --sat_fm_restart_options                ""
% 2.44/0.96  --sat_gr_def                            false
% 2.44/0.96  --sat_epr_types                         true
% 2.44/0.96  --sat_non_cyclic_types                  false
% 2.44/0.96  --sat_finite_models                     false
% 2.44/0.96  --sat_fm_lemmas                         false
% 2.44/0.96  --sat_fm_prep                           false
% 2.44/0.96  --sat_fm_uc_incr                        true
% 2.44/0.96  --sat_out_model                         small
% 2.44/0.96  --sat_out_clauses                       false
% 2.44/0.96  
% 2.44/0.96  ------ QBF Options
% 2.44/0.96  
% 2.44/0.96  --qbf_mode                              false
% 2.44/0.96  --qbf_elim_univ                         false
% 2.44/0.96  --qbf_dom_inst                          none
% 2.44/0.96  --qbf_dom_pre_inst                      false
% 2.44/0.96  --qbf_sk_in                             false
% 2.44/0.96  --qbf_pred_elim                         true
% 2.44/0.96  --qbf_split                             512
% 2.44/0.96  
% 2.44/0.96  ------ BMC1 Options
% 2.44/0.96  
% 2.44/0.96  --bmc1_incremental                      false
% 2.44/0.96  --bmc1_axioms                           reachable_all
% 2.44/0.96  --bmc1_min_bound                        0
% 2.44/0.96  --bmc1_max_bound                        -1
% 2.44/0.96  --bmc1_max_bound_default                -1
% 2.44/0.96  --bmc1_symbol_reachability              true
% 2.44/0.96  --bmc1_property_lemmas                  false
% 2.44/0.96  --bmc1_k_induction                      false
% 2.44/0.96  --bmc1_non_equiv_states                 false
% 2.44/0.96  --bmc1_deadlock                         false
% 2.44/0.96  --bmc1_ucm                              false
% 2.44/0.96  --bmc1_add_unsat_core                   none
% 2.44/0.96  --bmc1_unsat_core_children              false
% 2.44/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 2.44/0.96  --bmc1_out_stat                         full
% 2.44/0.96  --bmc1_ground_init                      false
% 2.44/0.96  --bmc1_pre_inst_next_state              false
% 2.44/0.96  --bmc1_pre_inst_state                   false
% 2.44/0.96  --bmc1_pre_inst_reach_state             false
% 2.44/0.96  --bmc1_out_unsat_core                   false
% 2.44/0.96  --bmc1_aig_witness_out                  false
% 2.44/0.96  --bmc1_verbose                          false
% 2.44/0.96  --bmc1_dump_clauses_tptp                false
% 2.44/0.96  --bmc1_dump_unsat_core_tptp             false
% 2.44/0.96  --bmc1_dump_file                        -
% 2.44/0.96  --bmc1_ucm_expand_uc_limit              128
% 2.44/0.96  --bmc1_ucm_n_expand_iterations          6
% 2.44/0.96  --bmc1_ucm_extend_mode                  1
% 2.44/0.96  --bmc1_ucm_init_mode                    2
% 2.44/0.96  --bmc1_ucm_cone_mode                    none
% 2.44/0.96  --bmc1_ucm_reduced_relation_type        0
% 2.44/0.96  --bmc1_ucm_relax_model                  4
% 2.44/0.96  --bmc1_ucm_full_tr_after_sat            true
% 2.44/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 2.44/0.96  --bmc1_ucm_layered_model                none
% 2.44/0.96  --bmc1_ucm_max_lemma_size               10
% 2.44/0.96  
% 2.44/0.96  ------ AIG Options
% 2.44/0.96  
% 2.44/0.96  --aig_mode                              false
% 2.44/0.96  
% 2.44/0.96  ------ Instantiation Options
% 2.44/0.96  
% 2.44/0.96  --instantiation_flag                    true
% 2.44/0.96  --inst_sos_flag                         false
% 2.44/0.96  --inst_sos_phase                        true
% 2.44/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.44/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.44/0.96  --inst_lit_sel_side                     num_symb
% 2.44/0.96  --inst_solver_per_active                1400
% 2.44/0.96  --inst_solver_calls_frac                1.
% 2.44/0.96  --inst_passive_queue_type               priority_queues
% 2.44/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.44/0.96  --inst_passive_queues_freq              [25;2]
% 2.44/0.96  --inst_dismatching                      true
% 2.44/0.96  --inst_eager_unprocessed_to_passive     true
% 2.44/0.96  --inst_prop_sim_given                   true
% 2.44/0.96  --inst_prop_sim_new                     false
% 2.44/0.96  --inst_subs_new                         false
% 2.44/0.96  --inst_eq_res_simp                      false
% 2.44/0.96  --inst_subs_given                       false
% 2.44/0.96  --inst_orphan_elimination               true
% 2.44/0.96  --inst_learning_loop_flag               true
% 2.44/0.96  --inst_learning_start                   3000
% 2.44/0.96  --inst_learning_factor                  2
% 2.44/0.96  --inst_start_prop_sim_after_learn       3
% 2.44/0.96  --inst_sel_renew                        solver
% 2.44/0.96  --inst_lit_activity_flag                true
% 2.44/0.96  --inst_restr_to_given                   false
% 2.44/0.96  --inst_activity_threshold               500
% 2.44/0.96  --inst_out_proof                        true
% 2.44/0.96  
% 2.44/0.96  ------ Resolution Options
% 2.44/0.96  
% 2.44/0.96  --resolution_flag                       true
% 2.44/0.96  --res_lit_sel                           adaptive
% 2.44/0.96  --res_lit_sel_side                      none
% 2.44/0.96  --res_ordering                          kbo
% 2.44/0.96  --res_to_prop_solver                    active
% 2.44/0.96  --res_prop_simpl_new                    false
% 2.44/0.96  --res_prop_simpl_given                  true
% 2.44/0.96  --res_passive_queue_type                priority_queues
% 2.44/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.44/0.96  --res_passive_queues_freq               [15;5]
% 2.44/0.96  --res_forward_subs                      full
% 2.44/0.96  --res_backward_subs                     full
% 2.44/0.96  --res_forward_subs_resolution           true
% 2.44/0.96  --res_backward_subs_resolution          true
% 2.44/0.96  --res_orphan_elimination                true
% 2.44/0.96  --res_time_limit                        2.
% 2.44/0.96  --res_out_proof                         true
% 2.44/0.96  
% 2.44/0.96  ------ Superposition Options
% 2.44/0.96  
% 2.44/0.96  --superposition_flag                    true
% 2.44/0.96  --sup_passive_queue_type                priority_queues
% 2.44/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.44/0.96  --sup_passive_queues_freq               [8;1;4]
% 2.44/0.96  --demod_completeness_check              fast
% 2.44/0.96  --demod_use_ground                      true
% 2.44/0.96  --sup_to_prop_solver                    passive
% 2.44/0.96  --sup_prop_simpl_new                    true
% 2.44/0.96  --sup_prop_simpl_given                  true
% 2.44/0.96  --sup_fun_splitting                     false
% 2.44/0.96  --sup_smt_interval                      50000
% 2.44/0.96  
% 2.44/0.96  ------ Superposition Simplification Setup
% 2.44/0.96  
% 2.44/0.96  --sup_indices_passive                   []
% 2.44/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 2.44/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/0.96  --sup_full_bw                           [BwDemod]
% 2.44/0.96  --sup_immed_triv                        [TrivRules]
% 2.44/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.44/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/0.96  --sup_immed_bw_main                     []
% 2.44/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.44/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 2.44/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.44/0.96  
% 2.44/0.96  ------ Combination Options
% 2.44/0.96  
% 2.44/0.96  --comb_res_mult                         3
% 2.44/0.96  --comb_sup_mult                         2
% 2.44/0.96  --comb_inst_mult                        10
% 2.44/0.96  
% 2.44/0.96  ------ Debug Options
% 2.44/0.96  
% 2.44/0.96  --dbg_backtrace                         false
% 2.44/0.96  --dbg_dump_prop_clauses                 false
% 2.44/0.96  --dbg_dump_prop_clauses_file            -
% 2.44/0.96  --dbg_out_stat                          false
% 2.44/0.96  ------ Parsing...
% 2.44/0.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.44/0.96  
% 2.44/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.44/0.96  
% 2.44/0.96  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.44/0.96  
% 2.44/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.44/0.96  ------ Proving...
% 2.44/0.96  ------ Problem Properties 
% 2.44/0.96  
% 2.44/0.96  
% 2.44/0.96  clauses                                 27
% 2.44/0.96  conjectures                             1
% 2.44/0.96  EPR                                     3
% 2.44/0.96  Horn                                    22
% 2.44/0.96  unary                                   10
% 2.44/0.96  binary                                  11
% 2.44/0.96  lits                                    51
% 2.44/0.96  lits eq                                 18
% 2.44/0.96  fd_pure                                 0
% 2.44/0.96  fd_pseudo                               0
% 2.44/0.96  fd_cond                                 1
% 2.44/0.96  fd_pseudo_cond                          2
% 2.44/0.96  AC symbols                              0
% 2.44/0.96  
% 2.44/0.96  ------ Schedule dynamic 5 is on 
% 2.44/0.96  
% 2.44/0.96  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.44/0.96  
% 2.44/0.96  
% 2.44/0.96  ------ 
% 2.44/0.96  Current options:
% 2.44/0.96  ------ 
% 2.44/0.96  
% 2.44/0.96  ------ Input Options
% 2.44/0.96  
% 2.44/0.96  --out_options                           all
% 2.44/0.96  --tptp_safe_out                         true
% 2.44/0.96  --problem_path                          ""
% 2.44/0.96  --include_path                          ""
% 2.44/0.96  --clausifier                            res/vclausify_rel
% 2.44/0.96  --clausifier_options                    --mode clausify
% 2.44/0.96  --stdin                                 false
% 2.44/0.96  --stats_out                             all
% 2.44/0.96  
% 2.44/0.96  ------ General Options
% 2.44/0.96  
% 2.44/0.96  --fof                                   false
% 2.44/0.96  --time_out_real                         305.
% 2.44/0.96  --time_out_virtual                      -1.
% 2.44/0.96  --symbol_type_check                     false
% 2.44/0.96  --clausify_out                          false
% 2.44/0.96  --sig_cnt_out                           false
% 2.44/0.96  --trig_cnt_out                          false
% 2.44/0.96  --trig_cnt_out_tolerance                1.
% 2.44/0.96  --trig_cnt_out_sk_spl                   false
% 2.44/0.96  --abstr_cl_out                          false
% 2.44/0.96  
% 2.44/0.96  ------ Global Options
% 2.44/0.96  
% 2.44/0.96  --schedule                              default
% 2.44/0.96  --add_important_lit                     false
% 2.44/0.96  --prop_solver_per_cl                    1000
% 2.44/0.96  --min_unsat_core                        false
% 2.44/0.96  --soft_assumptions                      false
% 2.44/0.96  --soft_lemma_size                       3
% 2.44/0.96  --prop_impl_unit_size                   0
% 2.44/0.96  --prop_impl_unit                        []
% 2.44/0.96  --share_sel_clauses                     true
% 2.44/0.96  --reset_solvers                         false
% 2.44/0.96  --bc_imp_inh                            [conj_cone]
% 2.44/0.96  --conj_cone_tolerance                   3.
% 2.44/0.96  --extra_neg_conj                        none
% 2.44/0.96  --large_theory_mode                     true
% 2.44/0.96  --prolific_symb_bound                   200
% 2.44/0.96  --lt_threshold                          2000
% 2.44/0.96  --clause_weak_htbl                      true
% 2.44/0.96  --gc_record_bc_elim                     false
% 2.44/0.96  
% 2.44/0.96  ------ Preprocessing Options
% 2.44/0.96  
% 2.44/0.96  --preprocessing_flag                    true
% 2.44/0.96  --time_out_prep_mult                    0.1
% 2.44/0.96  --splitting_mode                        input
% 2.44/0.96  --splitting_grd                         true
% 2.44/0.96  --splitting_cvd                         false
% 2.44/0.96  --splitting_cvd_svl                     false
% 2.44/0.96  --splitting_nvd                         32
% 2.44/0.96  --sub_typing                            true
% 2.44/0.96  --prep_gs_sim                           true
% 2.44/0.96  --prep_unflatten                        true
% 2.44/0.96  --prep_res_sim                          true
% 2.44/0.96  --prep_upred                            true
% 2.44/0.96  --prep_sem_filter                       exhaustive
% 2.44/0.96  --prep_sem_filter_out                   false
% 2.44/0.96  --pred_elim                             true
% 2.44/0.96  --res_sim_input                         true
% 2.44/0.96  --eq_ax_congr_red                       true
% 2.44/0.96  --pure_diseq_elim                       true
% 2.44/0.96  --brand_transform                       false
% 2.44/0.96  --non_eq_to_eq                          false
% 2.44/0.96  --prep_def_merge                        true
% 2.44/0.96  --prep_def_merge_prop_impl              false
% 2.44/0.96  --prep_def_merge_mbd                    true
% 2.44/0.96  --prep_def_merge_tr_red                 false
% 2.44/0.96  --prep_def_merge_tr_cl                  false
% 2.44/0.96  --smt_preprocessing                     true
% 2.44/0.96  --smt_ac_axioms                         fast
% 2.44/0.96  --preprocessed_out                      false
% 2.44/0.96  --preprocessed_stats                    false
% 2.44/0.96  
% 2.44/0.96  ------ Abstraction refinement Options
% 2.44/0.96  
% 2.44/0.96  --abstr_ref                             []
% 2.44/0.96  --abstr_ref_prep                        false
% 2.44/0.96  --abstr_ref_until_sat                   false
% 2.44/0.96  --abstr_ref_sig_restrict                funpre
% 2.44/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 2.44/0.96  --abstr_ref_under                       []
% 2.44/0.96  
% 2.44/0.96  ------ SAT Options
% 2.44/0.96  
% 2.44/0.96  --sat_mode                              false
% 2.44/0.96  --sat_fm_restart_options                ""
% 2.44/0.96  --sat_gr_def                            false
% 2.44/0.96  --sat_epr_types                         true
% 2.44/0.96  --sat_non_cyclic_types                  false
% 2.44/0.96  --sat_finite_models                     false
% 2.44/0.96  --sat_fm_lemmas                         false
% 2.44/0.96  --sat_fm_prep                           false
% 2.44/0.96  --sat_fm_uc_incr                        true
% 2.44/0.96  --sat_out_model                         small
% 2.44/0.96  --sat_out_clauses                       false
% 2.44/0.96  
% 2.44/0.96  ------ QBF Options
% 2.44/0.96  
% 2.44/0.96  --qbf_mode                              false
% 2.44/0.96  --qbf_elim_univ                         false
% 2.44/0.96  --qbf_dom_inst                          none
% 2.44/0.96  --qbf_dom_pre_inst                      false
% 2.44/0.96  --qbf_sk_in                             false
% 2.44/0.96  --qbf_pred_elim                         true
% 2.44/0.96  --qbf_split                             512
% 2.44/0.96  
% 2.44/0.96  ------ BMC1 Options
% 2.44/0.96  
% 2.44/0.96  --bmc1_incremental                      false
% 2.44/0.96  --bmc1_axioms                           reachable_all
% 2.44/0.96  --bmc1_min_bound                        0
% 2.44/0.96  --bmc1_max_bound                        -1
% 2.44/0.96  --bmc1_max_bound_default                -1
% 2.44/0.96  --bmc1_symbol_reachability              true
% 2.44/0.96  --bmc1_property_lemmas                  false
% 2.44/0.96  --bmc1_k_induction                      false
% 2.44/0.96  --bmc1_non_equiv_states                 false
% 2.44/0.96  --bmc1_deadlock                         false
% 2.44/0.96  --bmc1_ucm                              false
% 2.44/0.96  --bmc1_add_unsat_core                   none
% 2.44/0.96  --bmc1_unsat_core_children              false
% 2.44/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 2.44/0.96  --bmc1_out_stat                         full
% 2.44/0.96  --bmc1_ground_init                      false
% 2.44/0.96  --bmc1_pre_inst_next_state              false
% 2.44/0.96  --bmc1_pre_inst_state                   false
% 2.44/0.96  --bmc1_pre_inst_reach_state             false
% 2.44/0.96  --bmc1_out_unsat_core                   false
% 2.44/0.96  --bmc1_aig_witness_out                  false
% 2.44/0.96  --bmc1_verbose                          false
% 2.44/0.96  --bmc1_dump_clauses_tptp                false
% 2.44/0.96  --bmc1_dump_unsat_core_tptp             false
% 2.44/0.96  --bmc1_dump_file                        -
% 2.44/0.96  --bmc1_ucm_expand_uc_limit              128
% 2.44/0.96  --bmc1_ucm_n_expand_iterations          6
% 2.44/0.96  --bmc1_ucm_extend_mode                  1
% 2.44/0.96  --bmc1_ucm_init_mode                    2
% 2.44/0.96  --bmc1_ucm_cone_mode                    none
% 2.44/0.96  --bmc1_ucm_reduced_relation_type        0
% 2.44/0.96  --bmc1_ucm_relax_model                  4
% 2.44/0.96  --bmc1_ucm_full_tr_after_sat            true
% 2.44/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 2.44/0.96  --bmc1_ucm_layered_model                none
% 2.44/0.96  --bmc1_ucm_max_lemma_size               10
% 2.44/0.96  
% 2.44/0.96  ------ AIG Options
% 2.44/0.96  
% 2.44/0.96  --aig_mode                              false
% 2.44/0.96  
% 2.44/0.96  ------ Instantiation Options
% 2.44/0.96  
% 2.44/0.96  --instantiation_flag                    true
% 2.44/0.96  --inst_sos_flag                         false
% 2.44/0.96  --inst_sos_phase                        true
% 2.44/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.44/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.44/0.96  --inst_lit_sel_side                     none
% 2.44/0.96  --inst_solver_per_active                1400
% 2.44/0.96  --inst_solver_calls_frac                1.
% 2.44/0.96  --inst_passive_queue_type               priority_queues
% 2.44/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.44/0.96  --inst_passive_queues_freq              [25;2]
% 2.44/0.96  --inst_dismatching                      true
% 2.44/0.96  --inst_eager_unprocessed_to_passive     true
% 2.44/0.96  --inst_prop_sim_given                   true
% 2.44/0.96  --inst_prop_sim_new                     false
% 2.44/0.96  --inst_subs_new                         false
% 2.44/0.96  --inst_eq_res_simp                      false
% 2.44/0.96  --inst_subs_given                       false
% 2.44/0.96  --inst_orphan_elimination               true
% 2.44/0.96  --inst_learning_loop_flag               true
% 2.44/0.96  --inst_learning_start                   3000
% 2.44/0.96  --inst_learning_factor                  2
% 2.44/0.96  --inst_start_prop_sim_after_learn       3
% 2.44/0.96  --inst_sel_renew                        solver
% 2.44/0.96  --inst_lit_activity_flag                true
% 2.44/0.96  --inst_restr_to_given                   false
% 2.44/0.96  --inst_activity_threshold               500
% 2.44/0.96  --inst_out_proof                        true
% 2.44/0.96  
% 2.44/0.96  ------ Resolution Options
% 2.44/0.96  
% 2.44/0.96  --resolution_flag                       false
% 2.44/0.96  --res_lit_sel                           adaptive
% 2.44/0.96  --res_lit_sel_side                      none
% 2.44/0.96  --res_ordering                          kbo
% 2.44/0.96  --res_to_prop_solver                    active
% 2.44/0.96  --res_prop_simpl_new                    false
% 2.44/0.96  --res_prop_simpl_given                  true
% 2.44/0.96  --res_passive_queue_type                priority_queues
% 2.44/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.44/0.96  --res_passive_queues_freq               [15;5]
% 2.44/0.96  --res_forward_subs                      full
% 2.44/0.96  --res_backward_subs                     full
% 2.44/0.96  --res_forward_subs_resolution           true
% 2.44/0.96  --res_backward_subs_resolution          true
% 2.44/0.96  --res_orphan_elimination                true
% 2.44/0.96  --res_time_limit                        2.
% 2.44/0.96  --res_out_proof                         true
% 2.44/0.96  
% 2.44/0.96  ------ Superposition Options
% 2.44/0.96  
% 2.44/0.96  --superposition_flag                    true
% 2.44/0.96  --sup_passive_queue_type                priority_queues
% 2.44/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.44/0.96  --sup_passive_queues_freq               [8;1;4]
% 2.44/0.96  --demod_completeness_check              fast
% 2.44/0.96  --demod_use_ground                      true
% 2.44/0.96  --sup_to_prop_solver                    passive
% 2.44/0.96  --sup_prop_simpl_new                    true
% 2.44/0.96  --sup_prop_simpl_given                  true
% 2.44/0.96  --sup_fun_splitting                     false
% 2.44/0.96  --sup_smt_interval                      50000
% 2.44/0.96  
% 2.44/0.96  ------ Superposition Simplification Setup
% 2.44/0.96  
% 2.44/0.96  --sup_indices_passive                   []
% 2.44/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 2.44/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/0.96  --sup_full_bw                           [BwDemod]
% 2.44/0.96  --sup_immed_triv                        [TrivRules]
% 2.44/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.44/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/0.96  --sup_immed_bw_main                     []
% 2.44/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.44/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 2.44/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.44/0.96  
% 2.44/0.96  ------ Combination Options
% 2.44/0.96  
% 2.44/0.96  --comb_res_mult                         3
% 2.44/0.96  --comb_sup_mult                         2
% 2.44/0.96  --comb_inst_mult                        10
% 2.44/0.96  
% 2.44/0.96  ------ Debug Options
% 2.44/0.96  
% 2.44/0.96  --dbg_backtrace                         false
% 2.44/0.96  --dbg_dump_prop_clauses                 false
% 2.44/0.96  --dbg_dump_prop_clauses_file            -
% 2.44/0.96  --dbg_out_stat                          false
% 2.44/0.96  
% 2.44/0.96  
% 2.44/0.96  
% 2.44/0.96  
% 2.44/0.96  ------ Proving...
% 2.44/0.96  
% 2.44/0.96  
% 2.44/0.96  % SZS status Theorem for theBenchmark.p
% 2.44/0.96  
% 2.44/0.96  % SZS output start CNFRefutation for theBenchmark.p
% 2.44/0.96  
% 2.44/0.96  fof(f14,axiom,(
% 2.44/0.96    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 2.44/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.44/0.96  
% 2.44/0.96  fof(f20,plain,(
% 2.44/0.96    ! [X0] : (! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => v1_relat_1(X0))),
% 2.44/0.96    inference(unused_predicate_definition_removal,[],[f14])).
% 2.44/0.96  
% 2.44/0.96  fof(f26,plain,(
% 2.44/0.96    ! [X0] : (v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 2.44/0.96    inference(ennf_transformation,[],[f20])).
% 2.44/0.96  
% 2.44/0.96  fof(f41,plain,(
% 2.44/0.96    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK2(X0) & r2_hidden(sK2(X0),X0)))),
% 2.44/0.96    introduced(choice_axiom,[])).
% 2.44/0.96  
% 2.44/0.96  fof(f42,plain,(
% 2.44/0.96    ! [X0] : (v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK2(X0) & r2_hidden(sK2(X0),X0)))),
% 2.44/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f41])).
% 2.44/0.96  
% 2.44/0.96  fof(f67,plain,(
% 2.44/0.96    ( ! [X0] : (v1_relat_1(X0) | r2_hidden(sK2(X0),X0)) )),
% 2.44/0.96    inference(cnf_transformation,[],[f42])).
% 2.44/0.96  
% 2.44/0.96  fof(f12,axiom,(
% 2.44/0.96    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 2.44/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.44/0.96  
% 2.44/0.96  fof(f40,plain,(
% 2.44/0.96    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 2.44/0.96    inference(nnf_transformation,[],[f12])).
% 2.44/0.96  
% 2.44/0.96  fof(f65,plain,(
% 2.44/0.96    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.44/0.96    inference(cnf_transformation,[],[f40])).
% 2.44/0.96  
% 2.44/0.96  fof(f8,axiom,(
% 2.44/0.96    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 2.44/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.44/0.96  
% 2.44/0.96  fof(f57,plain,(
% 2.44/0.96    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 2.44/0.96    inference(cnf_transformation,[],[f8])).
% 2.44/0.96  
% 2.44/0.96  fof(f80,plain,(
% 2.44/0.96    ( ! [X0,X1] : (r1_tarski(k2_tarski(X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.44/0.96    inference(definition_unfolding,[],[f65,f57])).
% 2.44/0.96  
% 2.44/0.96  fof(f13,axiom,(
% 2.44/0.96    ! [X0,X1,X2] : ~(~r1_xboole_0(k2_tarski(X0,X2),X1) & ~r2_hidden(X2,X1) & ~r2_hidden(X0,X1))),
% 2.44/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.44/0.96  
% 2.44/0.96  fof(f25,plain,(
% 2.44/0.96    ! [X0,X1,X2] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1))),
% 2.44/0.96    inference(ennf_transformation,[],[f13])).
% 2.44/0.96  
% 2.44/0.96  fof(f66,plain,(
% 2.44/0.96    ( ! [X2,X0,X1] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1)) )),
% 2.44/0.96    inference(cnf_transformation,[],[f25])).
% 2.44/0.96  
% 2.44/0.96  fof(f11,axiom,(
% 2.44/0.96    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) | r1_xboole_0(X0,X1)) => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 2.44/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.44/0.96  
% 2.44/0.96  fof(f24,plain,(
% 2.44/0.96    ! [X0,X1,X2,X3] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | (~r1_xboole_0(X2,X3) & ~r1_xboole_0(X0,X1)))),
% 2.44/0.96    inference(ennf_transformation,[],[f11])).
% 2.44/0.96  
% 2.44/0.96  fof(f63,plain,(
% 2.44/0.96    ( ! [X2,X0,X3,X1] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_xboole_0(X2,X3)) )),
% 2.44/0.96    inference(cnf_transformation,[],[f24])).
% 2.44/0.96  
% 2.44/0.96  fof(f10,axiom,(
% 2.44/0.96    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.44/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.44/0.96  
% 2.44/0.96  fof(f38,plain,(
% 2.44/0.96    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.44/0.96    inference(nnf_transformation,[],[f10])).
% 2.44/0.96  
% 2.44/0.96  fof(f39,plain,(
% 2.44/0.96    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.44/0.96    inference(flattening,[],[f38])).
% 2.44/0.96  
% 2.44/0.96  fof(f60,plain,(
% 2.44/0.96    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.44/0.96    inference(cnf_transformation,[],[f39])).
% 2.44/0.96  
% 2.44/0.96  fof(f87,plain,(
% 2.44/0.96    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.44/0.96    inference(equality_resolution,[],[f60])).
% 2.44/0.96  
% 2.44/0.96  fof(f61,plain,(
% 2.44/0.96    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 2.44/0.96    inference(cnf_transformation,[],[f39])).
% 2.44/0.96  
% 2.44/0.96  fof(f86,plain,(
% 2.44/0.96    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.44/0.96    inference(equality_resolution,[],[f61])).
% 2.44/0.96  
% 2.44/0.96  fof(f62,plain,(
% 2.44/0.96    ( ! [X2,X0,X3,X1] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_xboole_0(X0,X1)) )),
% 2.44/0.96    inference(cnf_transformation,[],[f24])).
% 2.44/0.96  
% 2.44/0.96  fof(f18,conjecture,(
% 2.44/0.96    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 2.44/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.44/0.96  
% 2.44/0.96  fof(f19,negated_conjecture,(
% 2.44/0.96    ~! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 2.44/0.96    inference(negated_conjecture,[],[f18])).
% 2.44/0.96  
% 2.44/0.96  fof(f29,plain,(
% 2.44/0.96    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)),
% 2.44/0.96    inference(ennf_transformation,[],[f19])).
% 2.44/0.96  
% 2.44/0.96  fof(f43,plain,(
% 2.44/0.96    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) => k1_xboole_0 != k10_relat_1(k1_xboole_0,sK3)),
% 2.44/0.96    introduced(choice_axiom,[])).
% 2.44/0.96  
% 2.44/0.96  fof(f44,plain,(
% 2.44/0.96    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK3)),
% 2.44/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f43])).
% 2.44/0.96  
% 2.44/0.96  fof(f73,plain,(
% 2.44/0.96    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK3)),
% 2.44/0.96    inference(cnf_transformation,[],[f44])).
% 2.44/0.96  
% 2.44/0.96  fof(f6,axiom,(
% 2.44/0.96    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.44/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.44/0.96  
% 2.44/0.96  fof(f34,plain,(
% 2.44/0.96    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 2.44/0.96    inference(nnf_transformation,[],[f6])).
% 2.44/0.96  
% 2.44/0.96  fof(f35,plain,(
% 2.44/0.96    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.44/0.96    inference(rectify,[],[f34])).
% 2.44/0.96  
% 2.44/0.96  fof(f36,plain,(
% 2.44/0.96    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 2.44/0.96    introduced(choice_axiom,[])).
% 2.44/0.96  
% 2.44/0.96  fof(f37,plain,(
% 2.44/0.96    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.44/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f36])).
% 2.44/0.96  
% 2.44/0.96  fof(f52,plain,(
% 2.44/0.96    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 2.44/0.96    inference(cnf_transformation,[],[f37])).
% 2.44/0.96  
% 2.44/0.96  fof(f78,plain,(
% 2.44/0.96    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_tarski(X0,X0) != X1) )),
% 2.44/0.96    inference(definition_unfolding,[],[f52,f57])).
% 2.44/0.96  
% 2.44/0.96  fof(f85,plain,(
% 2.44/0.96    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_tarski(X0,X0))) )),
% 2.44/0.96    inference(equality_resolution,[],[f78])).
% 2.44/0.96  
% 2.44/0.96  fof(f1,axiom,(
% 2.44/0.96    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.44/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.44/0.96  
% 2.44/0.96  fof(f21,plain,(
% 2.44/0.96    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.44/0.96    inference(ennf_transformation,[],[f1])).
% 2.44/0.96  
% 2.44/0.96  fof(f30,plain,(
% 2.44/0.96    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.44/0.96    inference(nnf_transformation,[],[f21])).
% 2.44/0.96  
% 2.44/0.96  fof(f31,plain,(
% 2.44/0.96    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.44/0.96    inference(rectify,[],[f30])).
% 2.44/0.96  
% 2.44/0.96  fof(f32,plain,(
% 2.44/0.96    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.44/0.96    introduced(choice_axiom,[])).
% 2.44/0.96  
% 2.44/0.96  fof(f33,plain,(
% 2.44/0.96    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.44/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).
% 2.44/0.96  
% 2.44/0.96  fof(f45,plain,(
% 2.44/0.96    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.44/0.96    inference(cnf_transformation,[],[f33])).
% 2.44/0.96  
% 2.44/0.96  fof(f2,axiom,(
% 2.44/0.96    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.44/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.44/0.96  
% 2.44/0.96  fof(f48,plain,(
% 2.44/0.96    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.44/0.96    inference(cnf_transformation,[],[f2])).
% 2.44/0.96  
% 2.44/0.96  fof(f5,axiom,(
% 2.44/0.96    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ~(r1_xboole_0(X0,X1) & r1_tarski(X2,X1) & r1_tarski(X2,X0)))),
% 2.44/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.44/0.96  
% 2.44/0.96  fof(f22,plain,(
% 2.44/0.96    ! [X0,X1,X2] : ((~r1_xboole_0(X0,X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X2,X0)) | v1_xboole_0(X2))),
% 2.44/0.96    inference(ennf_transformation,[],[f5])).
% 2.44/0.96  
% 2.44/0.96  fof(f23,plain,(
% 2.44/0.96    ! [X0,X1,X2] : (~r1_xboole_0(X0,X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X2,X0) | v1_xboole_0(X2))),
% 2.44/0.96    inference(flattening,[],[f22])).
% 2.44/0.96  
% 2.44/0.96  fof(f51,plain,(
% 2.44/0.96    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X2,X0) | v1_xboole_0(X2)) )),
% 2.44/0.96    inference(cnf_transformation,[],[f23])).
% 2.44/0.96  
% 2.44/0.96  fof(f9,axiom,(
% 2.44/0.96    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 2.44/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.44/0.96  
% 2.44/0.96  fof(f58,plain,(
% 2.44/0.96    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 2.44/0.96    inference(cnf_transformation,[],[f9])).
% 2.44/0.96  
% 2.44/0.96  fof(f79,plain,(
% 2.44/0.96    ( ! [X0] : (~v1_xboole_0(k2_tarski(X0,X0))) )),
% 2.44/0.96    inference(definition_unfolding,[],[f58,f57])).
% 2.44/0.96  
% 2.44/0.96  fof(f15,axiom,(
% 2.44/0.96    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 2.44/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.44/0.96  
% 2.44/0.96  fof(f27,plain,(
% 2.44/0.96    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.44/0.96    inference(ennf_transformation,[],[f15])).
% 2.44/0.96  
% 2.44/0.96  fof(f69,plain,(
% 2.44/0.96    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 2.44/0.96    inference(cnf_transformation,[],[f27])).
% 2.44/0.96  
% 2.44/0.96  fof(f3,axiom,(
% 2.44/0.96    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 2.44/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.44/0.96  
% 2.44/0.96  fof(f49,plain,(
% 2.44/0.96    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 2.44/0.96    inference(cnf_transformation,[],[f3])).
% 2.44/0.96  
% 2.44/0.96  fof(f82,plain,(
% 2.44/0.96    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k4_xboole_0(k2_relat_1(X1),k4_xboole_0(k2_relat_1(X1),X0))) | ~v1_relat_1(X1)) )),
% 2.44/0.96    inference(definition_unfolding,[],[f69,f49])).
% 2.44/0.96  
% 2.44/0.96  fof(f4,axiom,(
% 2.44/0.96    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 2.44/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.44/0.96  
% 2.44/0.96  fof(f50,plain,(
% 2.44/0.96    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 2.44/0.96    inference(cnf_transformation,[],[f4])).
% 2.44/0.96  
% 2.44/0.96  fof(f17,axiom,(
% 2.44/0.96    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.44/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.44/0.96  
% 2.44/0.96  fof(f72,plain,(
% 2.44/0.96    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 2.44/0.96    inference(cnf_transformation,[],[f17])).
% 2.44/0.96  
% 2.44/0.96  fof(f16,axiom,(
% 2.44/0.96    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0))),
% 2.44/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.44/0.96  
% 2.44/0.96  fof(f28,plain,(
% 2.44/0.96    ! [X0] : (k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 2.44/0.96    inference(ennf_transformation,[],[f16])).
% 2.44/0.96  
% 2.44/0.96  fof(f70,plain,(
% 2.44/0.96    ( ! [X0] : (k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 2.44/0.96    inference(cnf_transformation,[],[f28])).
% 2.44/0.96  
% 2.44/0.96  fof(f59,plain,(
% 2.44/0.96    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 2.44/0.96    inference(cnf_transformation,[],[f39])).
% 2.44/0.96  
% 2.44/0.96  cnf(c_21,plain,
% 2.44/0.96      ( r2_hidden(sK2(X0),X0) | v1_relat_1(X0) ),
% 2.44/0.96      inference(cnf_transformation,[],[f67]) ).
% 2.44/0.96  
% 2.44/0.96  cnf(c_856,plain,
% 2.44/0.96      ( r2_hidden(sK2(X0),X0) = iProver_top
% 2.44/0.96      | v1_relat_1(X0) = iProver_top ),
% 2.44/0.96      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.44/0.96  
% 2.44/0.96  cnf(c_17,plain,
% 2.44/0.96      ( ~ r2_hidden(X0,X1) | r1_tarski(k2_tarski(X0,X0),X1) ),
% 2.44/0.96      inference(cnf_transformation,[],[f80]) ).
% 2.44/0.96  
% 2.44/0.96  cnf(c_860,plain,
% 2.44/0.96      ( r2_hidden(X0,X1) != iProver_top
% 2.44/0.96      | r1_tarski(k2_tarski(X0,X0),X1) = iProver_top ),
% 2.44/0.96      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.44/0.96  
% 2.44/0.96  cnf(c_19,plain,
% 2.44/0.96      ( r1_xboole_0(k2_tarski(X0,X1),X2)
% 2.44/0.96      | r2_hidden(X0,X2)
% 2.44/0.96      | r2_hidden(X1,X2) ),
% 2.44/0.96      inference(cnf_transformation,[],[f66]) ).
% 2.44/0.96  
% 2.44/0.96  cnf(c_858,plain,
% 2.44/0.96      ( r1_xboole_0(k2_tarski(X0,X1),X2) = iProver_top
% 2.44/0.96      | r2_hidden(X0,X2) = iProver_top
% 2.44/0.96      | r2_hidden(X1,X2) = iProver_top ),
% 2.44/0.96      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.44/0.96  
% 2.44/0.96  cnf(c_15,plain,
% 2.44/0.96      ( ~ r1_xboole_0(X0,X1)
% 2.44/0.96      | r1_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 2.44/0.96      inference(cnf_transformation,[],[f63]) ).
% 2.44/0.96  
% 2.44/0.96  cnf(c_862,plain,
% 2.44/0.96      ( r1_xboole_0(X0,X1) != iProver_top
% 2.44/0.96      | r1_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
% 2.44/0.96      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.44/0.96  
% 2.44/0.96  cnf(c_13,plain,
% 2.44/0.96      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.44/0.96      inference(cnf_transformation,[],[f87]) ).
% 2.44/0.96  
% 2.44/0.96  cnf(c_1826,plain,
% 2.44/0.96      ( r1_xboole_0(X0,X1) != iProver_top
% 2.44/0.96      | r1_xboole_0(k1_xboole_0,k2_zfmisc_1(X2,X1)) = iProver_top ),
% 2.44/0.96      inference(superposition,[status(thm)],[c_13,c_862]) ).
% 2.44/0.96  
% 2.44/0.96  cnf(c_1854,plain,
% 2.44/0.96      ( r1_xboole_0(X0,X1) != iProver_top
% 2.44/0.96      | r1_xboole_0(k1_xboole_0,k2_zfmisc_1(X2,k2_zfmisc_1(X3,X1))) = iProver_top ),
% 2.44/0.96      inference(superposition,[status(thm)],[c_862,c_1826]) ).
% 2.44/0.96  
% 2.44/0.96  cnf(c_2391,plain,
% 2.44/0.96      ( r1_xboole_0(k1_xboole_0,k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))) = iProver_top
% 2.44/0.96      | r2_hidden(X3,X2) = iProver_top
% 2.44/0.96      | r2_hidden(X4,X2) = iProver_top ),
% 2.44/0.96      inference(superposition,[status(thm)],[c_858,c_1854]) ).
% 2.44/0.96  
% 2.44/0.96  cnf(c_12,plain,
% 2.44/0.96      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.44/0.96      inference(cnf_transformation,[],[f86]) ).
% 2.44/0.96  
% 2.44/0.96  cnf(c_16,plain,
% 2.44/0.96      ( ~ r1_xboole_0(X0,X1)
% 2.44/0.96      | r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
% 2.44/0.96      inference(cnf_transformation,[],[f62]) ).
% 2.44/0.96  
% 2.44/0.96  cnf(c_861,plain,
% 2.44/0.96      ( r1_xboole_0(X0,X1) != iProver_top
% 2.44/0.96      | r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) = iProver_top ),
% 2.44/0.96      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.44/0.96  
% 2.44/0.96  cnf(c_1372,plain,
% 2.44/0.96      ( r1_xboole_0(X0,X1) != iProver_top
% 2.44/0.96      | r1_xboole_0(k2_zfmisc_1(X0,X2),k1_xboole_0) = iProver_top ),
% 2.44/0.96      inference(superposition,[status(thm)],[c_12,c_861]) ).
% 2.44/0.96  
% 2.44/0.96  cnf(c_4615,plain,
% 2.44/0.96      ( r1_xboole_0(k2_zfmisc_1(k1_xboole_0,X0),k1_xboole_0) = iProver_top
% 2.44/0.96      | r2_hidden(X1,X2) = iProver_top
% 2.44/0.96      | r2_hidden(X3,X2) = iProver_top ),
% 2.44/0.96      inference(superposition,[status(thm)],[c_2391,c_1372]) ).
% 2.44/0.96  
% 2.44/0.96  cnf(c_4627,plain,
% 2.44/0.96      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top
% 2.44/0.96      | r2_hidden(X0,X1) = iProver_top
% 2.44/0.96      | r2_hidden(X2,X1) = iProver_top ),
% 2.44/0.96      inference(light_normalisation,[status(thm)],[c_4615,c_13]) ).
% 2.44/0.96  
% 2.44/0.96  cnf(c_26,negated_conjecture,
% 2.44/0.96      ( k1_xboole_0 != k10_relat_1(k1_xboole_0,sK3) ),
% 2.44/0.96      inference(cnf_transformation,[],[f73]) ).
% 2.44/0.96  
% 2.44/0.96  cnf(c_10,plain,
% 2.44/0.96      ( ~ r2_hidden(X0,k2_tarski(X1,X1)) | X0 = X1 ),
% 2.44/0.96      inference(cnf_transformation,[],[f85]) ).
% 2.44/0.96  
% 2.44/0.96  cnf(c_1020,plain,
% 2.44/0.96      ( ~ r2_hidden(k1_xboole_0,k2_tarski(k10_relat_1(k1_xboole_0,sK3),k10_relat_1(k1_xboole_0,sK3)))
% 2.44/0.96      | k1_xboole_0 = k10_relat_1(k1_xboole_0,sK3) ),
% 2.44/0.96      inference(instantiation,[status(thm)],[c_10]) ).
% 2.44/0.96  
% 2.44/0.96  cnf(c_1021,plain,
% 2.44/0.96      ( k1_xboole_0 = k10_relat_1(k1_xboole_0,sK3)
% 2.44/0.96      | r2_hidden(k1_xboole_0,k2_tarski(k10_relat_1(k1_xboole_0,sK3),k10_relat_1(k1_xboole_0,sK3))) != iProver_top ),
% 2.44/0.96      inference(predicate_to_equality,[status(thm)],[c_1020]) ).
% 2.44/0.96  
% 2.44/0.96  cnf(c_3,plain,
% 2.44/0.96      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 2.44/0.96      inference(cnf_transformation,[],[f45]) ).
% 2.44/0.96  
% 2.44/0.96  cnf(c_1124,plain,
% 2.44/0.96      ( ~ r2_hidden(k1_xboole_0,X0)
% 2.44/0.96      | r2_hidden(k1_xboole_0,k2_tarski(k10_relat_1(k1_xboole_0,sK3),k10_relat_1(k1_xboole_0,sK3)))
% 2.44/0.96      | ~ r1_tarski(X0,k2_tarski(k10_relat_1(k1_xboole_0,sK3),k10_relat_1(k1_xboole_0,sK3))) ),
% 2.44/0.96      inference(instantiation,[status(thm)],[c_3]) ).
% 2.44/0.96  
% 2.44/0.96  cnf(c_1125,plain,
% 2.44/0.96      ( r2_hidden(k1_xboole_0,X0) != iProver_top
% 2.44/0.96      | r2_hidden(k1_xboole_0,k2_tarski(k10_relat_1(k1_xboole_0,sK3),k10_relat_1(k1_xboole_0,sK3))) = iProver_top
% 2.44/0.96      | r1_tarski(X0,k2_tarski(k10_relat_1(k1_xboole_0,sK3),k10_relat_1(k1_xboole_0,sK3))) != iProver_top ),
% 2.44/0.96      inference(predicate_to_equality,[status(thm)],[c_1124]) ).
% 2.44/0.96  
% 2.44/0.96  cnf(c_1127,plain,
% 2.44/0.96      ( r2_hidden(k1_xboole_0,k2_tarski(k10_relat_1(k1_xboole_0,sK3),k10_relat_1(k1_xboole_0,sK3))) = iProver_top
% 2.44/0.96      | r2_hidden(k1_xboole_0,k1_xboole_0) != iProver_top
% 2.44/0.96      | r1_tarski(k1_xboole_0,k2_tarski(k10_relat_1(k1_xboole_0,sK3),k10_relat_1(k1_xboole_0,sK3))) != iProver_top ),
% 2.44/0.96      inference(instantiation,[status(thm)],[c_1125]) ).
% 2.44/0.96  
% 2.44/0.96  cnf(c_4,plain,
% 2.44/0.96      ( r1_tarski(k1_xboole_0,X0) ),
% 2.44/0.96      inference(cnf_transformation,[],[f48]) ).
% 2.44/0.96  
% 2.44/0.96  cnf(c_1195,plain,
% 2.44/0.96      ( r1_tarski(k1_xboole_0,k2_tarski(k10_relat_1(k1_xboole_0,sK3),k10_relat_1(k1_xboole_0,sK3))) ),
% 2.44/0.96      inference(instantiation,[status(thm)],[c_4]) ).
% 2.44/0.96  
% 2.44/0.96  cnf(c_1198,plain,
% 2.44/0.96      ( r1_tarski(k1_xboole_0,k2_tarski(k10_relat_1(k1_xboole_0,sK3),k10_relat_1(k1_xboole_0,sK3))) = iProver_top ),
% 2.44/0.96      inference(predicate_to_equality,[status(thm)],[c_1195]) ).
% 2.44/0.96  
% 2.44/0.96  cnf(c_4773,plain,
% 2.44/0.96      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top
% 2.44/0.96      | r2_hidden(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 2.44/0.96      inference(instantiation,[status(thm)],[c_4627]) ).
% 2.44/0.96  
% 2.44/0.96  cnf(c_5118,plain,
% 2.44/0.96      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 2.44/0.96      inference(global_propositional_subsumption,
% 2.44/0.96                [status(thm)],
% 2.44/0.96                [c_4627,c_26,c_1021,c_1127,c_1198,c_4773]) ).
% 2.44/0.96  
% 2.44/0.96  cnf(c_6,plain,
% 2.44/0.96      ( ~ r1_xboole_0(X0,X1)
% 2.44/0.96      | ~ r1_tarski(X2,X1)
% 2.44/0.96      | ~ r1_tarski(X2,X0)
% 2.44/0.96      | v1_xboole_0(X2) ),
% 2.44/0.96      inference(cnf_transformation,[],[f51]) ).
% 2.44/0.96  
% 2.44/0.96  cnf(c_868,plain,
% 2.44/0.96      ( r1_xboole_0(X0,X1) != iProver_top
% 2.44/0.96      | r1_tarski(X2,X1) != iProver_top
% 2.44/0.96      | r1_tarski(X2,X0) != iProver_top
% 2.44/0.96      | v1_xboole_0(X2) = iProver_top ),
% 2.44/0.96      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.44/0.96  
% 2.44/0.96  cnf(c_5131,plain,
% 2.44/0.96      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 2.44/0.96      | v1_xboole_0(X0) = iProver_top ),
% 2.44/0.96      inference(superposition,[status(thm)],[c_5118,c_868]) ).
% 2.44/0.96  
% 2.44/0.96  cnf(c_5222,plain,
% 2.44/0.96      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 2.44/0.96      | v1_xboole_0(k2_tarski(X0,X0)) = iProver_top ),
% 2.44/0.96      inference(superposition,[status(thm)],[c_860,c_5131]) ).
% 2.44/0.96  
% 2.44/0.96  cnf(c_11,plain,
% 2.44/0.96      ( ~ v1_xboole_0(k2_tarski(X0,X0)) ),
% 2.44/0.96      inference(cnf_transformation,[],[f79]) ).
% 2.44/0.96  
% 2.44/0.96  cnf(c_54,plain,
% 2.44/0.96      ( v1_xboole_0(k2_tarski(X0,X0)) != iProver_top ),
% 2.44/0.96      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.44/0.96  
% 2.44/0.96  cnf(c_5730,plain,
% 2.44/0.96      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.44/0.96      inference(global_propositional_subsumption,
% 2.44/0.96                [status(thm)],
% 2.44/0.96                [c_5222,c_54]) ).
% 2.44/0.96  
% 2.44/0.96  cnf(c_5740,plain,
% 2.44/0.96      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 2.44/0.96      inference(superposition,[status(thm)],[c_856,c_5730]) ).
% 2.44/0.96  
% 2.44/0.96  cnf(c_22,plain,
% 2.44/0.96      ( ~ v1_relat_1(X0)
% 2.44/0.96      | k10_relat_1(X0,k4_xboole_0(k2_relat_1(X0),k4_xboole_0(k2_relat_1(X0),X1))) = k10_relat_1(X0,X1) ),
% 2.44/0.96      inference(cnf_transformation,[],[f82]) ).
% 2.44/0.96  
% 2.44/0.96  cnf(c_855,plain,
% 2.44/0.96      ( k10_relat_1(X0,k4_xboole_0(k2_relat_1(X0),k4_xboole_0(k2_relat_1(X0),X1))) = k10_relat_1(X0,X1)
% 2.44/0.96      | v1_relat_1(X0) != iProver_top ),
% 2.44/0.96      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.44/0.96  
% 2.44/0.96  cnf(c_5754,plain,
% 2.44/0.96      ( k10_relat_1(k1_xboole_0,k4_xboole_0(k2_relat_1(k1_xboole_0),k4_xboole_0(k2_relat_1(k1_xboole_0),X0))) = k10_relat_1(k1_xboole_0,X0) ),
% 2.44/0.96      inference(superposition,[status(thm)],[c_5740,c_855]) ).
% 2.44/0.96  
% 2.44/0.96  cnf(c_5,plain,
% 2.44/0.96      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.44/0.96      inference(cnf_transformation,[],[f50]) ).
% 2.44/0.96  
% 2.44/0.96  cnf(c_24,plain,
% 2.44/0.96      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.44/0.96      inference(cnf_transformation,[],[f72]) ).
% 2.44/0.96  
% 2.44/0.96  cnf(c_5759,plain,
% 2.44/0.96      ( k10_relat_1(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) = k10_relat_1(k1_xboole_0,X0) ),
% 2.44/0.96      inference(light_normalisation,[status(thm)],[c_5754,c_5,c_24]) ).
% 2.44/0.97  
% 2.44/0.97  cnf(c_5760,plain,
% 2.44/0.97      ( k10_relat_1(k1_xboole_0,X0) = k10_relat_1(k1_xboole_0,k1_xboole_0) ),
% 2.44/0.97      inference(demodulation,[status(thm)],[c_5759,c_5]) ).
% 2.44/0.97  
% 2.44/0.97  cnf(c_23,plain,
% 2.44/0.97      ( ~ v1_relat_1(X0) | k10_relat_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.44/0.97      inference(cnf_transformation,[],[f70]) ).
% 2.44/0.97  
% 2.44/0.97  cnf(c_854,plain,
% 2.44/0.97      ( k10_relat_1(X0,k1_xboole_0) = k1_xboole_0
% 2.44/0.97      | v1_relat_1(X0) != iProver_top ),
% 2.44/0.97      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.44/0.97  
% 2.44/0.97  cnf(c_5755,plain,
% 2.44/0.97      ( k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 2.44/0.97      inference(superposition,[status(thm)],[c_5740,c_854]) ).
% 2.44/0.97  
% 2.44/0.97  cnf(c_6186,plain,
% 2.44/0.97      ( k10_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.44/0.97      inference(light_normalisation,[status(thm)],[c_5760,c_5755]) ).
% 2.44/0.97  
% 2.44/0.97  cnf(c_6188,plain,
% 2.44/0.97      ( k1_xboole_0 != k1_xboole_0 ),
% 2.44/0.97      inference(demodulation,[status(thm)],[c_6186,c_26]) ).
% 2.44/0.97  
% 2.44/0.97  cnf(c_53,plain,
% 2.44/0.97      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 2.44/0.97      inference(instantiation,[status(thm)],[c_13]) ).
% 2.44/0.97  
% 2.44/0.97  cnf(c_14,plain,
% 2.44/0.97      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 2.44/0.97      | k1_xboole_0 = X1
% 2.44/0.97      | k1_xboole_0 = X0 ),
% 2.44/0.97      inference(cnf_transformation,[],[f59]) ).
% 2.44/0.97  
% 2.44/0.97  cnf(c_52,plain,
% 2.44/0.97      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 2.44/0.97      | k1_xboole_0 = k1_xboole_0 ),
% 2.44/0.97      inference(instantiation,[status(thm)],[c_14]) ).
% 2.44/0.97  
% 2.44/0.97  cnf(contradiction,plain,
% 2.44/0.97      ( $false ),
% 2.44/0.97      inference(minisat,[status(thm)],[c_6188,c_53,c_52]) ).
% 2.44/0.97  
% 2.44/0.97  
% 2.44/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 2.44/0.97  
% 2.44/0.97  ------                               Statistics
% 2.44/0.97  
% 2.44/0.97  ------ General
% 2.44/0.97  
% 2.44/0.97  abstr_ref_over_cycles:                  0
% 2.44/0.97  abstr_ref_under_cycles:                 0
% 2.44/0.97  gc_basic_clause_elim:                   0
% 2.44/0.97  forced_gc_time:                         0
% 2.44/0.97  parsing_time:                           0.007
% 2.44/0.97  unif_index_cands_time:                  0.
% 2.44/0.97  unif_index_add_time:                    0.
% 2.44/0.97  orderings_time:                         0.
% 2.44/0.97  out_proof_time:                         0.009
% 2.44/0.97  total_time:                             0.173
% 2.44/0.97  num_of_symbols:                         49
% 2.44/0.97  num_of_terms:                           6688
% 2.44/0.97  
% 2.44/0.97  ------ Preprocessing
% 2.44/0.97  
% 2.44/0.97  num_of_splits:                          0
% 2.44/0.97  num_of_split_atoms:                     0
% 2.44/0.97  num_of_reused_defs:                     0
% 2.44/0.97  num_eq_ax_congr_red:                    22
% 2.44/0.97  num_of_sem_filtered_clauses:            1
% 2.44/0.97  num_of_subtypes:                        0
% 2.44/0.97  monotx_restored_types:                  0
% 2.44/0.97  sat_num_of_epr_types:                   0
% 2.44/0.97  sat_num_of_non_cyclic_types:            0
% 2.44/0.97  sat_guarded_non_collapsed_types:        0
% 2.44/0.97  num_pure_diseq_elim:                    0
% 2.44/0.97  simp_replaced_by:                       0
% 2.44/0.97  res_preprocessed:                       106
% 2.44/0.97  prep_upred:                             0
% 2.44/0.97  prep_unflattend:                        1
% 2.44/0.97  smt_new_axioms:                         0
% 2.44/0.97  pred_elim_cands:                        5
% 2.44/0.97  pred_elim:                              0
% 2.44/0.97  pred_elim_cl:                           0
% 2.44/0.97  pred_elim_cycles:                       2
% 2.44/0.97  merged_defs:                            6
% 2.44/0.97  merged_defs_ncl:                        0
% 2.44/0.97  bin_hyper_res:                          6
% 2.44/0.97  prep_cycles:                            3
% 2.44/0.97  pred_elim_time:                         0.001
% 2.44/0.97  splitting_time:                         0.
% 2.44/0.97  sem_filter_time:                        0.
% 2.44/0.97  monotx_time:                            0.
% 2.44/0.97  subtype_inf_time:                       0.
% 2.44/0.97  
% 2.44/0.97  ------ Problem properties
% 2.44/0.97  
% 2.44/0.97  clauses:                                27
% 2.44/0.97  conjectures:                            1
% 2.44/0.97  epr:                                    3
% 2.44/0.97  horn:                                   22
% 2.44/0.97  ground:                                 3
% 2.44/0.97  unary:                                  10
% 2.44/0.97  binary:                                 11
% 2.44/0.97  lits:                                   51
% 2.44/0.97  lits_eq:                                18
% 2.44/0.97  fd_pure:                                0
% 2.44/0.97  fd_pseudo:                              0
% 2.44/0.97  fd_cond:                                1
% 2.44/0.97  fd_pseudo_cond:                         2
% 2.44/0.97  ac_symbols:                             0
% 2.44/0.97  
% 2.44/0.97  ------ Propositional Solver
% 2.44/0.97  
% 2.44/0.97  prop_solver_calls:                      25
% 2.44/0.97  prop_fast_solver_calls:                 585
% 2.44/0.97  smt_solver_calls:                       0
% 2.44/0.97  smt_fast_solver_calls:                  0
% 2.44/0.97  prop_num_of_clauses:                    2290
% 2.44/0.97  prop_preprocess_simplified:             7314
% 2.44/0.97  prop_fo_subsumed:                       3
% 2.44/0.97  prop_solver_time:                       0.
% 2.44/0.97  smt_solver_time:                        0.
% 2.44/0.97  smt_fast_solver_time:                   0.
% 2.44/0.97  prop_fast_solver_time:                  0.
% 2.44/0.97  prop_unsat_core_time:                   0.
% 2.44/0.97  
% 2.44/0.97  ------ QBF
% 2.44/0.97  
% 2.44/0.97  qbf_q_res:                              0
% 2.44/0.97  qbf_num_tautologies:                    0
% 2.44/0.97  qbf_prep_cycles:                        0
% 2.44/0.97  
% 2.44/0.97  ------ BMC1
% 2.44/0.97  
% 2.44/0.97  bmc1_current_bound:                     -1
% 2.44/0.97  bmc1_last_solved_bound:                 -1
% 2.44/0.97  bmc1_unsat_core_size:                   -1
% 2.44/0.97  bmc1_unsat_core_parents_size:           -1
% 2.44/0.97  bmc1_merge_next_fun:                    0
% 2.44/0.97  bmc1_unsat_core_clauses_time:           0.
% 2.44/0.97  
% 2.44/0.97  ------ Instantiation
% 2.44/0.97  
% 2.44/0.97  inst_num_of_clauses:                    759
% 2.44/0.97  inst_num_in_passive:                    427
% 2.44/0.97  inst_num_in_active:                     282
% 2.44/0.97  inst_num_in_unprocessed:                50
% 2.44/0.97  inst_num_of_loops:                      340
% 2.44/0.97  inst_num_of_learning_restarts:          0
% 2.44/0.97  inst_num_moves_active_passive:          55
% 2.44/0.97  inst_lit_activity:                      0
% 2.44/0.97  inst_lit_activity_moves:                0
% 2.44/0.97  inst_num_tautologies:                   0
% 2.44/0.97  inst_num_prop_implied:                  0
% 2.44/0.97  inst_num_existing_simplified:           0
% 2.44/0.97  inst_num_eq_res_simplified:             0
% 2.44/0.97  inst_num_child_elim:                    0
% 2.44/0.97  inst_num_of_dismatching_blockings:      249
% 2.44/0.97  inst_num_of_non_proper_insts:           608
% 2.44/0.97  inst_num_of_duplicates:                 0
% 2.44/0.97  inst_inst_num_from_inst_to_res:         0
% 2.44/0.97  inst_dismatching_checking_time:         0.
% 2.44/0.97  
% 2.44/0.97  ------ Resolution
% 2.44/0.97  
% 2.44/0.97  res_num_of_clauses:                     0
% 2.44/0.97  res_num_in_passive:                     0
% 2.44/0.97  res_num_in_active:                      0
% 2.44/0.97  res_num_of_loops:                       109
% 2.44/0.97  res_forward_subset_subsumed:            91
% 2.44/0.97  res_backward_subset_subsumed:           0
% 2.44/0.97  res_forward_subsumed:                   0
% 2.44/0.97  res_backward_subsumed:                  0
% 2.44/0.97  res_forward_subsumption_resolution:     0
% 2.44/0.97  res_backward_subsumption_resolution:    0
% 2.44/0.97  res_clause_to_clause_subsumption:       1552
% 2.44/0.97  res_orphan_elimination:                 0
% 2.44/0.97  res_tautology_del:                      82
% 2.44/0.97  res_num_eq_res_simplified:              0
% 2.44/0.97  res_num_sel_changes:                    0
% 2.44/0.97  res_moves_from_active_to_pass:          0
% 2.44/0.97  
% 2.44/0.97  ------ Superposition
% 2.44/0.97  
% 2.44/0.97  sup_time_total:                         0.
% 2.44/0.97  sup_time_generating:                    0.
% 2.44/0.97  sup_time_sim_full:                      0.
% 2.44/0.97  sup_time_sim_immed:                     0.
% 2.44/0.97  
% 2.44/0.97  sup_num_of_clauses:                     150
% 2.44/0.97  sup_num_in_active:                      64
% 2.44/0.97  sup_num_in_passive:                     86
% 2.44/0.97  sup_num_of_loops:                       66
% 2.44/0.97  sup_fw_superposition:                   96
% 2.44/0.97  sup_bw_superposition:                   87
% 2.44/0.97  sup_immediate_simplified:               51
% 2.44/0.97  sup_given_eliminated:                   0
% 2.44/0.97  comparisons_done:                       0
% 2.44/0.97  comparisons_avoided:                    5
% 2.44/0.97  
% 2.44/0.97  ------ Simplifications
% 2.44/0.97  
% 2.44/0.97  
% 2.44/0.97  sim_fw_subset_subsumed:                 4
% 2.44/0.97  sim_bw_subset_subsumed:                 4
% 2.44/0.97  sim_fw_subsumed:                        3
% 2.44/0.97  sim_bw_subsumed:                        2
% 2.44/0.97  sim_fw_subsumption_res:                 0
% 2.44/0.97  sim_bw_subsumption_res:                 0
% 2.44/0.97  sim_tautology_del:                      1
% 2.44/0.97  sim_eq_tautology_del:                   2
% 2.44/0.97  sim_eq_res_simp:                        1
% 2.44/0.97  sim_fw_demodulated:                     33
% 2.44/0.97  sim_bw_demodulated:                     1
% 2.44/0.97  sim_light_normalised:                   22
% 2.44/0.97  sim_joinable_taut:                      0
% 2.44/0.97  sim_joinable_simp:                      0
% 2.44/0.97  sim_ac_normalised:                      0
% 2.44/0.97  sim_smt_subsumption:                    0
% 2.44/0.97  
%------------------------------------------------------------------------------
