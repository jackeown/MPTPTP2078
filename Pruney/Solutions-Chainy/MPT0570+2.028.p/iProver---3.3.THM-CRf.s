%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:47:39 EST 2020

% Result     : Theorem 1.79s
% Output     : CNFRefutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 147 expanded)
%              Number of clauses        :   45 (  48 expanded)
%              Number of leaves         :   15 (  29 expanded)
%              Depth                    :   17
%              Number of atoms          :  302 ( 506 expanded)
%              Number of equality atoms :   99 ( 213 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :    9 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
     => v1_xboole_0(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f14,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ? [X1] : r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f24])).

fof(f38,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f40,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f49,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k1_xboole_0 = k10_relat_1(X1,X0)
          & r1_tarski(X0,k2_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ~ ( k1_xboole_0 = k10_relat_1(X1,X0)
            & r1_tarski(X0,k2_relat_1(X1))
            & k1_xboole_0 != X0 ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f22,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k10_relat_1(X1,X0)
      & r1_tarski(X0,k2_relat_1(X1))
      & k1_xboole_0 != X0
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f23,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k10_relat_1(X1,X0)
      & r1_tarski(X0,k2_relat_1(X1))
      & k1_xboole_0 != X0
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f36,plain,
    ( ? [X0,X1] :
        ( k1_xboole_0 = k10_relat_1(X1,X0)
        & r1_tarski(X0,k2_relat_1(X1))
        & k1_xboole_0 != X0
        & v1_relat_1(X1) )
   => ( k1_xboole_0 = k10_relat_1(sK4,sK3)
      & r1_tarski(sK3,k2_relat_1(sK4))
      & k1_xboole_0 != sK3
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( k1_xboole_0 = k10_relat_1(sK4,sK3)
    & r1_tarski(sK3,k2_relat_1(sK4))
    & k1_xboole_0 != sK3
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f23,f36])).

fof(f56,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f59,plain,(
    k1_xboole_0 = k10_relat_1(sK4,sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
        & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
            & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f30])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK2(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK2(X0,X1,X2)),X2)
        & r2_hidden(sK2(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ( r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(X0,sK2(X0,X1,X2)),X2)
            & r2_hidden(sK2(X0,X1,X2),k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X0,X3),X2)
      | ~ r2_hidden(X3,k2_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k2_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f26])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f60,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f43])).

fof(f5,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f58,plain,(
    r1_tarski(sK3,k2_relat_1(sK4)) ),
    inference(cnf_transformation,[],[f37])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f61,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f42])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f57,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_2,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_202,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(resolution,[status(thm)],[c_0,c_2])).

cnf(c_752,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_202])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_21,negated_conjecture,
    ( v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_365,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_21])).

cnf(c_366,plain,
    ( k9_relat_1(sK4,k1_relat_1(sK4)) = k2_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_365])).

cnf(c_18,negated_conjecture,
    ( k1_xboole_0 = k10_relat_1(sK4,sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_303,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_21])).

cnf(c_304,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK4,X1))
    | r2_hidden(k4_tarski(sK1(X0,X1,sK4),X0),sK4) ),
    inference(unflattening,[status(thm)],[c_303])).

cnf(c_744,plain,
    ( r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
    | r2_hidden(k4_tarski(sK1(X0,X1,sK4),X0),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_304])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(X0,k2_relat_1(X3))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_327,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(X0,k2_relat_1(X3))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | sK4 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_21])).

cnf(c_328,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(sK4,X1))
    | ~ r2_hidden(X0,k2_relat_1(sK4))
    | ~ r2_hidden(k4_tarski(X2,X0),sK4) ),
    inference(unflattening,[status(thm)],[c_327])).

cnf(c_16,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_243,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_21])).

cnf(c_244,plain,
    ( r2_hidden(X0,k2_relat_1(sK4))
    | ~ r2_hidden(k4_tarski(X1,X0),sK4) ),
    inference(unflattening,[status(thm)],[c_243])).

cnf(c_336,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(sK4,X1))
    | ~ r2_hidden(k4_tarski(X2,X0),sK4) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_328,c_244])).

cnf(c_742,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,k10_relat_1(sK4,X1)) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_336])).

cnf(c_1428,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k9_relat_1(sK4,X2)) != iProver_top
    | r2_hidden(sK1(X0,X2,sK4),k10_relat_1(sK4,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_744,c_742])).

cnf(c_3569,plain,
    ( r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(sK1(X0,X1,sK4),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_18,c_1428])).

cnf(c_3,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_753,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1447,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_753])).

cnf(c_3602,plain,
    ( r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3569,c_1447])).

cnf(c_3609,plain,
    ( r2_hidden(X0,k2_relat_1(sK4)) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_366,c_3602])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_19,negated_conjecture,
    ( r1_tarski(sK3,k2_relat_1(sK4)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_216,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | k2_relat_1(sK4) != X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_19])).

cnf(c_217,plain,
    ( r2_hidden(X0,k2_relat_1(sK4))
    | ~ r2_hidden(X0,sK3) ),
    inference(unflattening,[status(thm)],[c_216])).

cnf(c_218,plain,
    ( r2_hidden(X0,k2_relat_1(sK4)) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_217])).

cnf(c_3654,plain,
    ( r2_hidden(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3609,c_218])).

cnf(c_3661,plain,
    ( sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_752,c_3654])).

cnf(c_505,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_861,plain,
    ( sK3 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_505])).

cnf(c_862,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_861])).

cnf(c_4,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_61,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_5,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_60,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_20,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f57])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3661,c_862,c_61,c_60,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:38:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.79/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.01  
% 1.79/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.79/1.01  
% 1.79/1.01  ------  iProver source info
% 1.79/1.01  
% 1.79/1.01  git: date: 2020-06-30 10:37:57 +0100
% 1.79/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.79/1.01  git: non_committed_changes: false
% 1.79/1.01  git: last_make_outside_of_git: false
% 1.79/1.01  
% 1.79/1.01  ------ 
% 1.79/1.01  
% 1.79/1.01  ------ Input Options
% 1.79/1.01  
% 1.79/1.01  --out_options                           all
% 1.79/1.01  --tptp_safe_out                         true
% 1.79/1.01  --problem_path                          ""
% 1.79/1.01  --include_path                          ""
% 1.79/1.01  --clausifier                            res/vclausify_rel
% 1.79/1.01  --clausifier_options                    --mode clausify
% 1.79/1.01  --stdin                                 false
% 1.79/1.01  --stats_out                             all
% 1.79/1.01  
% 1.79/1.01  ------ General Options
% 1.79/1.01  
% 1.79/1.01  --fof                                   false
% 1.79/1.01  --time_out_real                         305.
% 1.79/1.01  --time_out_virtual                      -1.
% 1.79/1.01  --symbol_type_check                     false
% 1.79/1.01  --clausify_out                          false
% 1.79/1.01  --sig_cnt_out                           false
% 1.79/1.01  --trig_cnt_out                          false
% 1.79/1.01  --trig_cnt_out_tolerance                1.
% 1.79/1.01  --trig_cnt_out_sk_spl                   false
% 1.79/1.01  --abstr_cl_out                          false
% 1.79/1.01  
% 1.79/1.01  ------ Global Options
% 1.79/1.01  
% 1.79/1.01  --schedule                              default
% 1.79/1.01  --add_important_lit                     false
% 1.79/1.01  --prop_solver_per_cl                    1000
% 1.79/1.01  --min_unsat_core                        false
% 1.79/1.01  --soft_assumptions                      false
% 1.79/1.01  --soft_lemma_size                       3
% 1.79/1.01  --prop_impl_unit_size                   0
% 1.79/1.01  --prop_impl_unit                        []
% 1.79/1.01  --share_sel_clauses                     true
% 1.79/1.01  --reset_solvers                         false
% 1.79/1.01  --bc_imp_inh                            [conj_cone]
% 1.79/1.01  --conj_cone_tolerance                   3.
% 1.79/1.01  --extra_neg_conj                        none
% 1.79/1.01  --large_theory_mode                     true
% 1.79/1.01  --prolific_symb_bound                   200
% 1.79/1.01  --lt_threshold                          2000
% 1.79/1.01  --clause_weak_htbl                      true
% 1.79/1.01  --gc_record_bc_elim                     false
% 1.79/1.01  
% 1.79/1.01  ------ Preprocessing Options
% 1.79/1.01  
% 1.79/1.01  --preprocessing_flag                    true
% 1.79/1.01  --time_out_prep_mult                    0.1
% 1.79/1.01  --splitting_mode                        input
% 1.79/1.01  --splitting_grd                         true
% 1.79/1.01  --splitting_cvd                         false
% 1.79/1.01  --splitting_cvd_svl                     false
% 1.79/1.01  --splitting_nvd                         32
% 1.79/1.01  --sub_typing                            true
% 1.79/1.01  --prep_gs_sim                           true
% 1.79/1.01  --prep_unflatten                        true
% 1.79/1.01  --prep_res_sim                          true
% 1.79/1.01  --prep_upred                            true
% 1.79/1.01  --prep_sem_filter                       exhaustive
% 1.79/1.01  --prep_sem_filter_out                   false
% 1.79/1.01  --pred_elim                             true
% 1.79/1.01  --res_sim_input                         true
% 1.79/1.01  --eq_ax_congr_red                       true
% 1.79/1.01  --pure_diseq_elim                       true
% 1.79/1.01  --brand_transform                       false
% 1.79/1.01  --non_eq_to_eq                          false
% 1.79/1.01  --prep_def_merge                        true
% 1.79/1.01  --prep_def_merge_prop_impl              false
% 1.79/1.01  --prep_def_merge_mbd                    true
% 1.79/1.01  --prep_def_merge_tr_red                 false
% 1.79/1.01  --prep_def_merge_tr_cl                  false
% 1.79/1.01  --smt_preprocessing                     true
% 1.79/1.01  --smt_ac_axioms                         fast
% 1.79/1.01  --preprocessed_out                      false
% 1.79/1.01  --preprocessed_stats                    false
% 1.79/1.01  
% 1.79/1.01  ------ Abstraction refinement Options
% 1.79/1.01  
% 1.79/1.01  --abstr_ref                             []
% 1.79/1.01  --abstr_ref_prep                        false
% 1.79/1.01  --abstr_ref_until_sat                   false
% 1.79/1.01  --abstr_ref_sig_restrict                funpre
% 1.79/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 1.79/1.01  --abstr_ref_under                       []
% 1.79/1.01  
% 1.79/1.01  ------ SAT Options
% 1.79/1.01  
% 1.79/1.01  --sat_mode                              false
% 1.79/1.01  --sat_fm_restart_options                ""
% 1.79/1.01  --sat_gr_def                            false
% 1.79/1.01  --sat_epr_types                         true
% 1.79/1.01  --sat_non_cyclic_types                  false
% 1.79/1.01  --sat_finite_models                     false
% 1.79/1.01  --sat_fm_lemmas                         false
% 1.79/1.01  --sat_fm_prep                           false
% 1.79/1.01  --sat_fm_uc_incr                        true
% 1.79/1.01  --sat_out_model                         small
% 1.79/1.01  --sat_out_clauses                       false
% 1.79/1.01  
% 1.79/1.01  ------ QBF Options
% 1.79/1.01  
% 1.79/1.01  --qbf_mode                              false
% 1.79/1.01  --qbf_elim_univ                         false
% 1.79/1.01  --qbf_dom_inst                          none
% 1.79/1.01  --qbf_dom_pre_inst                      false
% 1.79/1.01  --qbf_sk_in                             false
% 1.79/1.01  --qbf_pred_elim                         true
% 1.79/1.01  --qbf_split                             512
% 1.79/1.01  
% 1.79/1.01  ------ BMC1 Options
% 1.79/1.01  
% 1.79/1.01  --bmc1_incremental                      false
% 1.79/1.01  --bmc1_axioms                           reachable_all
% 1.79/1.01  --bmc1_min_bound                        0
% 1.79/1.01  --bmc1_max_bound                        -1
% 1.79/1.01  --bmc1_max_bound_default                -1
% 1.79/1.01  --bmc1_symbol_reachability              true
% 1.79/1.01  --bmc1_property_lemmas                  false
% 1.79/1.01  --bmc1_k_induction                      false
% 1.79/1.01  --bmc1_non_equiv_states                 false
% 1.79/1.01  --bmc1_deadlock                         false
% 1.79/1.01  --bmc1_ucm                              false
% 1.79/1.01  --bmc1_add_unsat_core                   none
% 1.79/1.01  --bmc1_unsat_core_children              false
% 1.79/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 1.79/1.01  --bmc1_out_stat                         full
% 1.79/1.01  --bmc1_ground_init                      false
% 1.79/1.01  --bmc1_pre_inst_next_state              false
% 1.79/1.01  --bmc1_pre_inst_state                   false
% 1.79/1.01  --bmc1_pre_inst_reach_state             false
% 1.79/1.01  --bmc1_out_unsat_core                   false
% 1.79/1.01  --bmc1_aig_witness_out                  false
% 1.79/1.01  --bmc1_verbose                          false
% 1.79/1.01  --bmc1_dump_clauses_tptp                false
% 1.79/1.01  --bmc1_dump_unsat_core_tptp             false
% 1.79/1.01  --bmc1_dump_file                        -
% 1.79/1.01  --bmc1_ucm_expand_uc_limit              128
% 1.79/1.01  --bmc1_ucm_n_expand_iterations          6
% 1.79/1.01  --bmc1_ucm_extend_mode                  1
% 1.79/1.01  --bmc1_ucm_init_mode                    2
% 1.79/1.01  --bmc1_ucm_cone_mode                    none
% 1.79/1.01  --bmc1_ucm_reduced_relation_type        0
% 1.79/1.01  --bmc1_ucm_relax_model                  4
% 1.79/1.01  --bmc1_ucm_full_tr_after_sat            true
% 1.79/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 1.79/1.01  --bmc1_ucm_layered_model                none
% 1.79/1.01  --bmc1_ucm_max_lemma_size               10
% 1.79/1.01  
% 1.79/1.01  ------ AIG Options
% 1.79/1.01  
% 1.79/1.01  --aig_mode                              false
% 1.79/1.01  
% 1.79/1.01  ------ Instantiation Options
% 1.79/1.01  
% 1.79/1.01  --instantiation_flag                    true
% 1.79/1.01  --inst_sos_flag                         false
% 1.79/1.01  --inst_sos_phase                        true
% 1.79/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.79/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.79/1.01  --inst_lit_sel_side                     num_symb
% 1.79/1.01  --inst_solver_per_active                1400
% 1.79/1.01  --inst_solver_calls_frac                1.
% 1.79/1.01  --inst_passive_queue_type               priority_queues
% 1.79/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.79/1.01  --inst_passive_queues_freq              [25;2]
% 1.79/1.01  --inst_dismatching                      true
% 1.79/1.01  --inst_eager_unprocessed_to_passive     true
% 1.79/1.01  --inst_prop_sim_given                   true
% 1.79/1.01  --inst_prop_sim_new                     false
% 1.79/1.01  --inst_subs_new                         false
% 1.79/1.01  --inst_eq_res_simp                      false
% 1.79/1.01  --inst_subs_given                       false
% 1.79/1.01  --inst_orphan_elimination               true
% 1.79/1.01  --inst_learning_loop_flag               true
% 1.79/1.01  --inst_learning_start                   3000
% 1.79/1.01  --inst_learning_factor                  2
% 1.79/1.01  --inst_start_prop_sim_after_learn       3
% 1.79/1.01  --inst_sel_renew                        solver
% 1.79/1.01  --inst_lit_activity_flag                true
% 1.79/1.01  --inst_restr_to_given                   false
% 1.79/1.01  --inst_activity_threshold               500
% 1.79/1.01  --inst_out_proof                        true
% 1.79/1.01  
% 1.79/1.01  ------ Resolution Options
% 1.79/1.01  
% 1.79/1.01  --resolution_flag                       true
% 1.79/1.01  --res_lit_sel                           adaptive
% 1.79/1.01  --res_lit_sel_side                      none
% 1.79/1.01  --res_ordering                          kbo
% 1.79/1.01  --res_to_prop_solver                    active
% 1.79/1.01  --res_prop_simpl_new                    false
% 1.79/1.01  --res_prop_simpl_given                  true
% 1.79/1.01  --res_passive_queue_type                priority_queues
% 1.79/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.79/1.01  --res_passive_queues_freq               [15;5]
% 1.79/1.01  --res_forward_subs                      full
% 1.79/1.01  --res_backward_subs                     full
% 1.79/1.01  --res_forward_subs_resolution           true
% 1.79/1.01  --res_backward_subs_resolution          true
% 1.79/1.01  --res_orphan_elimination                true
% 1.79/1.01  --res_time_limit                        2.
% 1.79/1.01  --res_out_proof                         true
% 1.79/1.01  
% 1.79/1.01  ------ Superposition Options
% 1.79/1.01  
% 1.79/1.01  --superposition_flag                    true
% 1.79/1.01  --sup_passive_queue_type                priority_queues
% 1.79/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.79/1.01  --sup_passive_queues_freq               [8;1;4]
% 1.79/1.01  --demod_completeness_check              fast
% 1.79/1.01  --demod_use_ground                      true
% 1.79/1.01  --sup_to_prop_solver                    passive
% 1.79/1.01  --sup_prop_simpl_new                    true
% 1.79/1.01  --sup_prop_simpl_given                  true
% 1.79/1.01  --sup_fun_splitting                     false
% 1.79/1.01  --sup_smt_interval                      50000
% 1.79/1.01  
% 1.79/1.01  ------ Superposition Simplification Setup
% 1.79/1.01  
% 1.79/1.01  --sup_indices_passive                   []
% 1.79/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.79/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.79/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.79/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 1.79/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.79/1.01  --sup_full_bw                           [BwDemod]
% 1.79/1.01  --sup_immed_triv                        [TrivRules]
% 1.79/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.79/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.79/1.01  --sup_immed_bw_main                     []
% 1.79/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.79/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 1.79/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.79/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.79/1.01  
% 1.79/1.01  ------ Combination Options
% 1.79/1.01  
% 1.79/1.01  --comb_res_mult                         3
% 1.79/1.01  --comb_sup_mult                         2
% 1.79/1.01  --comb_inst_mult                        10
% 1.79/1.01  
% 1.79/1.01  ------ Debug Options
% 1.79/1.01  
% 1.79/1.01  --dbg_backtrace                         false
% 1.79/1.01  --dbg_dump_prop_clauses                 false
% 1.79/1.01  --dbg_dump_prop_clauses_file            -
% 1.79/1.01  --dbg_out_stat                          false
% 1.79/1.01  ------ Parsing...
% 1.79/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.79/1.01  
% 1.79/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 1.79/1.01  
% 1.79/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.79/1.01  
% 1.79/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.79/1.01  ------ Proving...
% 1.79/1.01  ------ Problem Properties 
% 1.79/1.01  
% 1.79/1.01  
% 1.79/1.01  clauses                                 19
% 1.79/1.01  conjectures                             2
% 1.79/1.01  EPR                                     1
% 1.79/1.01  Horn                                    17
% 1.79/1.01  unary                                   6
% 1.79/1.01  binary                                  10
% 1.79/1.01  lits                                    35
% 1.79/1.01  lits eq                                 9
% 1.79/1.01  fd_pure                                 0
% 1.79/1.01  fd_pseudo                               0
% 1.79/1.01  fd_cond                                 2
% 1.79/1.01  fd_pseudo_cond                          0
% 1.79/1.01  AC symbols                              0
% 1.79/1.01  
% 1.79/1.01  ------ Schedule dynamic 5 is on 
% 1.79/1.01  
% 1.79/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.79/1.01  
% 1.79/1.01  
% 1.79/1.01  ------ 
% 1.79/1.01  Current options:
% 1.79/1.01  ------ 
% 1.79/1.01  
% 1.79/1.01  ------ Input Options
% 1.79/1.01  
% 1.79/1.01  --out_options                           all
% 1.79/1.01  --tptp_safe_out                         true
% 1.79/1.01  --problem_path                          ""
% 1.79/1.01  --include_path                          ""
% 1.79/1.01  --clausifier                            res/vclausify_rel
% 1.79/1.01  --clausifier_options                    --mode clausify
% 1.79/1.01  --stdin                                 false
% 1.79/1.01  --stats_out                             all
% 1.79/1.01  
% 1.79/1.01  ------ General Options
% 1.79/1.01  
% 1.79/1.01  --fof                                   false
% 1.79/1.01  --time_out_real                         305.
% 1.79/1.01  --time_out_virtual                      -1.
% 1.79/1.01  --symbol_type_check                     false
% 1.79/1.01  --clausify_out                          false
% 1.79/1.01  --sig_cnt_out                           false
% 1.79/1.01  --trig_cnt_out                          false
% 1.79/1.01  --trig_cnt_out_tolerance                1.
% 1.79/1.01  --trig_cnt_out_sk_spl                   false
% 1.79/1.01  --abstr_cl_out                          false
% 1.79/1.01  
% 1.79/1.01  ------ Global Options
% 1.79/1.01  
% 1.79/1.01  --schedule                              default
% 1.79/1.01  --add_important_lit                     false
% 1.79/1.01  --prop_solver_per_cl                    1000
% 1.79/1.01  --min_unsat_core                        false
% 1.79/1.01  --soft_assumptions                      false
% 1.79/1.01  --soft_lemma_size                       3
% 1.79/1.01  --prop_impl_unit_size                   0
% 1.79/1.01  --prop_impl_unit                        []
% 1.79/1.01  --share_sel_clauses                     true
% 1.79/1.01  --reset_solvers                         false
% 1.79/1.01  --bc_imp_inh                            [conj_cone]
% 1.79/1.01  --conj_cone_tolerance                   3.
% 1.79/1.01  --extra_neg_conj                        none
% 1.79/1.01  --large_theory_mode                     true
% 1.79/1.01  --prolific_symb_bound                   200
% 1.79/1.01  --lt_threshold                          2000
% 1.79/1.01  --clause_weak_htbl                      true
% 1.79/1.01  --gc_record_bc_elim                     false
% 1.79/1.01  
% 1.79/1.01  ------ Preprocessing Options
% 1.79/1.01  
% 1.79/1.01  --preprocessing_flag                    true
% 1.79/1.01  --time_out_prep_mult                    0.1
% 1.79/1.01  --splitting_mode                        input
% 1.79/1.01  --splitting_grd                         true
% 1.79/1.01  --splitting_cvd                         false
% 1.79/1.01  --splitting_cvd_svl                     false
% 1.79/1.01  --splitting_nvd                         32
% 1.79/1.01  --sub_typing                            true
% 1.79/1.01  --prep_gs_sim                           true
% 1.79/1.01  --prep_unflatten                        true
% 1.79/1.01  --prep_res_sim                          true
% 1.79/1.01  --prep_upred                            true
% 1.79/1.01  --prep_sem_filter                       exhaustive
% 1.79/1.01  --prep_sem_filter_out                   false
% 1.79/1.01  --pred_elim                             true
% 1.79/1.01  --res_sim_input                         true
% 1.79/1.01  --eq_ax_congr_red                       true
% 1.79/1.01  --pure_diseq_elim                       true
% 1.79/1.01  --brand_transform                       false
% 1.79/1.01  --non_eq_to_eq                          false
% 1.79/1.01  --prep_def_merge                        true
% 1.79/1.01  --prep_def_merge_prop_impl              false
% 1.79/1.01  --prep_def_merge_mbd                    true
% 1.79/1.01  --prep_def_merge_tr_red                 false
% 1.79/1.01  --prep_def_merge_tr_cl                  false
% 1.79/1.01  --smt_preprocessing                     true
% 1.79/1.01  --smt_ac_axioms                         fast
% 1.79/1.01  --preprocessed_out                      false
% 1.79/1.01  --preprocessed_stats                    false
% 1.79/1.01  
% 1.79/1.01  ------ Abstraction refinement Options
% 1.79/1.01  
% 1.79/1.01  --abstr_ref                             []
% 1.79/1.01  --abstr_ref_prep                        false
% 1.79/1.01  --abstr_ref_until_sat                   false
% 1.79/1.01  --abstr_ref_sig_restrict                funpre
% 1.79/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 1.79/1.01  --abstr_ref_under                       []
% 1.79/1.01  
% 1.79/1.01  ------ SAT Options
% 1.79/1.01  
% 1.79/1.01  --sat_mode                              false
% 1.79/1.01  --sat_fm_restart_options                ""
% 1.79/1.01  --sat_gr_def                            false
% 1.79/1.01  --sat_epr_types                         true
% 1.79/1.01  --sat_non_cyclic_types                  false
% 1.79/1.01  --sat_finite_models                     false
% 1.79/1.01  --sat_fm_lemmas                         false
% 1.79/1.01  --sat_fm_prep                           false
% 1.79/1.01  --sat_fm_uc_incr                        true
% 1.79/1.01  --sat_out_model                         small
% 1.79/1.01  --sat_out_clauses                       false
% 1.79/1.01  
% 1.79/1.01  ------ QBF Options
% 1.79/1.01  
% 1.79/1.01  --qbf_mode                              false
% 1.79/1.01  --qbf_elim_univ                         false
% 1.79/1.01  --qbf_dom_inst                          none
% 1.79/1.01  --qbf_dom_pre_inst                      false
% 1.79/1.01  --qbf_sk_in                             false
% 1.79/1.01  --qbf_pred_elim                         true
% 1.79/1.01  --qbf_split                             512
% 1.79/1.01  
% 1.79/1.01  ------ BMC1 Options
% 1.79/1.01  
% 1.79/1.01  --bmc1_incremental                      false
% 1.79/1.01  --bmc1_axioms                           reachable_all
% 1.79/1.01  --bmc1_min_bound                        0
% 1.79/1.01  --bmc1_max_bound                        -1
% 1.79/1.01  --bmc1_max_bound_default                -1
% 1.79/1.01  --bmc1_symbol_reachability              true
% 1.79/1.01  --bmc1_property_lemmas                  false
% 1.79/1.01  --bmc1_k_induction                      false
% 1.79/1.01  --bmc1_non_equiv_states                 false
% 1.79/1.01  --bmc1_deadlock                         false
% 1.79/1.01  --bmc1_ucm                              false
% 1.79/1.01  --bmc1_add_unsat_core                   none
% 1.79/1.01  --bmc1_unsat_core_children              false
% 1.79/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 1.79/1.01  --bmc1_out_stat                         full
% 1.79/1.01  --bmc1_ground_init                      false
% 1.79/1.01  --bmc1_pre_inst_next_state              false
% 1.79/1.01  --bmc1_pre_inst_state                   false
% 1.79/1.01  --bmc1_pre_inst_reach_state             false
% 1.79/1.01  --bmc1_out_unsat_core                   false
% 1.79/1.01  --bmc1_aig_witness_out                  false
% 1.79/1.01  --bmc1_verbose                          false
% 1.79/1.01  --bmc1_dump_clauses_tptp                false
% 1.79/1.01  --bmc1_dump_unsat_core_tptp             false
% 1.79/1.01  --bmc1_dump_file                        -
% 1.79/1.01  --bmc1_ucm_expand_uc_limit              128
% 1.79/1.01  --bmc1_ucm_n_expand_iterations          6
% 1.79/1.01  --bmc1_ucm_extend_mode                  1
% 1.79/1.01  --bmc1_ucm_init_mode                    2
% 1.79/1.01  --bmc1_ucm_cone_mode                    none
% 1.79/1.01  --bmc1_ucm_reduced_relation_type        0
% 1.79/1.01  --bmc1_ucm_relax_model                  4
% 1.79/1.01  --bmc1_ucm_full_tr_after_sat            true
% 1.79/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 1.79/1.01  --bmc1_ucm_layered_model                none
% 1.79/1.01  --bmc1_ucm_max_lemma_size               10
% 1.79/1.01  
% 1.79/1.01  ------ AIG Options
% 1.79/1.01  
% 1.79/1.01  --aig_mode                              false
% 1.79/1.01  
% 1.79/1.01  ------ Instantiation Options
% 1.79/1.01  
% 1.79/1.01  --instantiation_flag                    true
% 1.79/1.01  --inst_sos_flag                         false
% 1.79/1.01  --inst_sos_phase                        true
% 1.79/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.79/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.79/1.01  --inst_lit_sel_side                     none
% 1.79/1.01  --inst_solver_per_active                1400
% 1.79/1.01  --inst_solver_calls_frac                1.
% 1.79/1.01  --inst_passive_queue_type               priority_queues
% 1.79/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.79/1.02  --inst_passive_queues_freq              [25;2]
% 1.79/1.02  --inst_dismatching                      true
% 1.79/1.02  --inst_eager_unprocessed_to_passive     true
% 1.79/1.02  --inst_prop_sim_given                   true
% 1.79/1.02  --inst_prop_sim_new                     false
% 1.79/1.02  --inst_subs_new                         false
% 1.79/1.02  --inst_eq_res_simp                      false
% 1.79/1.02  --inst_subs_given                       false
% 1.79/1.02  --inst_orphan_elimination               true
% 1.79/1.02  --inst_learning_loop_flag               true
% 1.79/1.02  --inst_learning_start                   3000
% 1.79/1.02  --inst_learning_factor                  2
% 1.79/1.02  --inst_start_prop_sim_after_learn       3
% 1.79/1.02  --inst_sel_renew                        solver
% 1.79/1.02  --inst_lit_activity_flag                true
% 1.79/1.02  --inst_restr_to_given                   false
% 1.79/1.02  --inst_activity_threshold               500
% 1.79/1.02  --inst_out_proof                        true
% 1.79/1.02  
% 1.79/1.02  ------ Resolution Options
% 1.79/1.02  
% 1.79/1.02  --resolution_flag                       false
% 1.79/1.02  --res_lit_sel                           adaptive
% 1.79/1.02  --res_lit_sel_side                      none
% 1.79/1.02  --res_ordering                          kbo
% 1.79/1.02  --res_to_prop_solver                    active
% 1.79/1.02  --res_prop_simpl_new                    false
% 1.79/1.02  --res_prop_simpl_given                  true
% 1.79/1.02  --res_passive_queue_type                priority_queues
% 1.79/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.79/1.02  --res_passive_queues_freq               [15;5]
% 1.79/1.02  --res_forward_subs                      full
% 1.79/1.02  --res_backward_subs                     full
% 1.79/1.02  --res_forward_subs_resolution           true
% 1.79/1.02  --res_backward_subs_resolution          true
% 1.79/1.02  --res_orphan_elimination                true
% 1.79/1.02  --res_time_limit                        2.
% 1.79/1.02  --res_out_proof                         true
% 1.79/1.02  
% 1.79/1.02  ------ Superposition Options
% 1.79/1.02  
% 1.79/1.02  --superposition_flag                    true
% 1.79/1.02  --sup_passive_queue_type                priority_queues
% 1.79/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.79/1.02  --sup_passive_queues_freq               [8;1;4]
% 1.79/1.02  --demod_completeness_check              fast
% 1.79/1.02  --demod_use_ground                      true
% 1.79/1.02  --sup_to_prop_solver                    passive
% 1.79/1.02  --sup_prop_simpl_new                    true
% 1.79/1.02  --sup_prop_simpl_given                  true
% 1.79/1.02  --sup_fun_splitting                     false
% 1.79/1.02  --sup_smt_interval                      50000
% 1.79/1.02  
% 1.79/1.02  ------ Superposition Simplification Setup
% 1.79/1.02  
% 1.79/1.02  --sup_indices_passive                   []
% 1.79/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.79/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.79/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.79/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 1.79/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.79/1.02  --sup_full_bw                           [BwDemod]
% 1.79/1.02  --sup_immed_triv                        [TrivRules]
% 1.79/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.79/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.79/1.02  --sup_immed_bw_main                     []
% 1.79/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.79/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 1.79/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.79/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.79/1.02  
% 1.79/1.02  ------ Combination Options
% 1.79/1.02  
% 1.79/1.02  --comb_res_mult                         3
% 1.79/1.02  --comb_sup_mult                         2
% 1.79/1.02  --comb_inst_mult                        10
% 1.79/1.02  
% 1.79/1.02  ------ Debug Options
% 1.79/1.02  
% 1.79/1.02  --dbg_backtrace                         false
% 1.79/1.02  --dbg_dump_prop_clauses                 false
% 1.79/1.02  --dbg_dump_prop_clauses_file            -
% 1.79/1.02  --dbg_out_stat                          false
% 1.79/1.02  
% 1.79/1.02  
% 1.79/1.02  
% 1.79/1.02  
% 1.79/1.02  ------ Proving...
% 1.79/1.02  
% 1.79/1.02  
% 1.79/1.02  % SZS status Theorem for theBenchmark.p
% 1.79/1.02  
% 1.79/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 1.79/1.02  
% 1.79/1.02  fof(f1,axiom,(
% 1.79/1.02    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.79/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.79/1.02  
% 1.79/1.02  fof(f13,plain,(
% 1.79/1.02    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) => v1_xboole_0(X0))),
% 1.79/1.02    inference(unused_predicate_definition_removal,[],[f1])).
% 1.79/1.02  
% 1.79/1.02  fof(f14,plain,(
% 1.79/1.02    ! [X0] : (v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0))),
% 1.79/1.02    inference(ennf_transformation,[],[f13])).
% 1.79/1.02  
% 1.79/1.02  fof(f24,plain,(
% 1.79/1.02    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 1.79/1.02    introduced(choice_axiom,[])).
% 1.79/1.02  
% 1.79/1.02  fof(f25,plain,(
% 1.79/1.02    ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0))),
% 1.79/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f24])).
% 1.79/1.02  
% 1.79/1.02  fof(f38,plain,(
% 1.79/1.02    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 1.79/1.02    inference(cnf_transformation,[],[f25])).
% 1.79/1.02  
% 1.79/1.02  fof(f3,axiom,(
% 1.79/1.02    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.79/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.79/1.02  
% 1.79/1.02  fof(f16,plain,(
% 1.79/1.02    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.79/1.02    inference(ennf_transformation,[],[f3])).
% 1.79/1.02  
% 1.79/1.02  fof(f40,plain,(
% 1.79/1.02    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 1.79/1.02    inference(cnf_transformation,[],[f16])).
% 1.79/1.02  
% 1.79/1.02  fof(f7,axiom,(
% 1.79/1.02    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 1.79/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.79/1.02  
% 1.79/1.02  fof(f18,plain,(
% 1.79/1.02    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 1.79/1.02    inference(ennf_transformation,[],[f7])).
% 1.79/1.02  
% 1.79/1.02  fof(f49,plain,(
% 1.79/1.02    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.79/1.02    inference(cnf_transformation,[],[f18])).
% 1.79/1.02  
% 1.79/1.02  fof(f10,conjecture,(
% 1.79/1.02    ! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0))),
% 1.79/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.79/1.02  
% 1.79/1.02  fof(f11,negated_conjecture,(
% 1.79/1.02    ~! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0))),
% 1.79/1.02    inference(negated_conjecture,[],[f10])).
% 1.79/1.02  
% 1.79/1.02  fof(f22,plain,(
% 1.79/1.02    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0) & v1_relat_1(X1))),
% 1.79/1.02    inference(ennf_transformation,[],[f11])).
% 1.79/1.02  
% 1.79/1.02  fof(f23,plain,(
% 1.79/1.02    ? [X0,X1] : (k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0 & v1_relat_1(X1))),
% 1.79/1.02    inference(flattening,[],[f22])).
% 1.79/1.02  
% 1.79/1.02  fof(f36,plain,(
% 1.79/1.02    ? [X0,X1] : (k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0 & v1_relat_1(X1)) => (k1_xboole_0 = k10_relat_1(sK4,sK3) & r1_tarski(sK3,k2_relat_1(sK4)) & k1_xboole_0 != sK3 & v1_relat_1(sK4))),
% 1.79/1.02    introduced(choice_axiom,[])).
% 1.79/1.02  
% 1.79/1.02  fof(f37,plain,(
% 1.79/1.02    k1_xboole_0 = k10_relat_1(sK4,sK3) & r1_tarski(sK3,k2_relat_1(sK4)) & k1_xboole_0 != sK3 & v1_relat_1(sK4)),
% 1.79/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f23,f36])).
% 1.79/1.02  
% 1.79/1.02  fof(f56,plain,(
% 1.79/1.02    v1_relat_1(sK4)),
% 1.79/1.02    inference(cnf_transformation,[],[f37])).
% 1.79/1.02  
% 1.79/1.02  fof(f59,plain,(
% 1.79/1.02    k1_xboole_0 = k10_relat_1(sK4,sK3)),
% 1.79/1.02    inference(cnf_transformation,[],[f37])).
% 1.79/1.02  
% 1.79/1.02  fof(f6,axiom,(
% 1.79/1.02    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 1.79/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.79/1.02  
% 1.79/1.02  fof(f17,plain,(
% 1.79/1.02    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 1.79/1.02    inference(ennf_transformation,[],[f6])).
% 1.79/1.02  
% 1.79/1.02  fof(f28,plain,(
% 1.79/1.02    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.79/1.02    inference(nnf_transformation,[],[f17])).
% 1.79/1.02  
% 1.79/1.02  fof(f29,plain,(
% 1.79/1.02    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.79/1.02    inference(rectify,[],[f28])).
% 1.79/1.02  
% 1.79/1.02  fof(f30,plain,(
% 1.79/1.02    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))))),
% 1.79/1.02    introduced(choice_axiom,[])).
% 1.79/1.02  
% 1.79/1.02  fof(f31,plain,(
% 1.79/1.02    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.79/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f30])).
% 1.79/1.02  
% 1.79/1.02  fof(f46,plain,(
% 1.79/1.02    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.79/1.02    inference(cnf_transformation,[],[f31])).
% 1.79/1.02  
% 1.79/1.02  fof(f8,axiom,(
% 1.79/1.02    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 1.79/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.79/1.02  
% 1.79/1.02  fof(f19,plain,(
% 1.79/1.02    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 1.79/1.02    inference(ennf_transformation,[],[f8])).
% 1.79/1.02  
% 1.79/1.02  fof(f32,plain,(
% 1.79/1.02    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.79/1.02    inference(nnf_transformation,[],[f19])).
% 1.79/1.02  
% 1.79/1.02  fof(f33,plain,(
% 1.79/1.02    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.79/1.02    inference(rectify,[],[f32])).
% 1.79/1.02  
% 1.79/1.02  fof(f34,plain,(
% 1.79/1.02    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK2(X0,X1,X2)),X2) & r2_hidden(sK2(X0,X1,X2),k2_relat_1(X2))))),
% 1.79/1.02    introduced(choice_axiom,[])).
% 1.79/1.02  
% 1.79/1.02  fof(f35,plain,(
% 1.79/1.02    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK2(X0,X1,X2)),X2) & r2_hidden(sK2(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.79/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).
% 1.79/1.02  
% 1.79/1.02  fof(f53,plain,(
% 1.79/1.02    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,k10_relat_1(X2,X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 1.79/1.02    inference(cnf_transformation,[],[f35])).
% 1.79/1.02  
% 1.79/1.02  fof(f9,axiom,(
% 1.79/1.02    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 1.79/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.79/1.02  
% 1.79/1.02  fof(f20,plain,(
% 1.79/1.02    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 1.79/1.02    inference(ennf_transformation,[],[f9])).
% 1.79/1.02  
% 1.79/1.02  fof(f21,plain,(
% 1.79/1.02    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 1.79/1.02    inference(flattening,[],[f20])).
% 1.79/1.02  
% 1.79/1.02  fof(f55,plain,(
% 1.79/1.02    ( ! [X2,X0,X1] : (r2_hidden(X1,k2_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 1.79/1.02    inference(cnf_transformation,[],[f21])).
% 1.79/1.02  
% 1.79/1.02  fof(f4,axiom,(
% 1.79/1.02    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.79/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.79/1.02  
% 1.79/1.02  fof(f26,plain,(
% 1.79/1.02    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.79/1.02    inference(nnf_transformation,[],[f4])).
% 1.79/1.02  
% 1.79/1.02  fof(f27,plain,(
% 1.79/1.02    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.79/1.02    inference(flattening,[],[f26])).
% 1.79/1.02  
% 1.79/1.02  fof(f43,plain,(
% 1.79/1.02    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.79/1.02    inference(cnf_transformation,[],[f27])).
% 1.79/1.02  
% 1.79/1.02  fof(f60,plain,(
% 1.79/1.02    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.79/1.02    inference(equality_resolution,[],[f43])).
% 1.79/1.02  
% 1.79/1.02  fof(f5,axiom,(
% 1.79/1.02    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 1.79/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.79/1.02  
% 1.79/1.02  fof(f44,plain,(
% 1.79/1.02    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 1.79/1.02    inference(cnf_transformation,[],[f5])).
% 1.79/1.02  
% 1.79/1.02  fof(f2,axiom,(
% 1.79/1.02    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.79/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.79/1.02  
% 1.79/1.02  fof(f12,plain,(
% 1.79/1.02    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.79/1.02    inference(unused_predicate_definition_removal,[],[f2])).
% 1.79/1.02  
% 1.79/1.02  fof(f15,plain,(
% 1.79/1.02    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 1.79/1.02    inference(ennf_transformation,[],[f12])).
% 1.79/1.02  
% 1.79/1.02  fof(f39,plain,(
% 1.79/1.02    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 1.79/1.02    inference(cnf_transformation,[],[f15])).
% 1.79/1.02  
% 1.79/1.02  fof(f58,plain,(
% 1.79/1.02    r1_tarski(sK3,k2_relat_1(sK4))),
% 1.79/1.02    inference(cnf_transformation,[],[f37])).
% 1.79/1.02  
% 1.79/1.02  fof(f42,plain,(
% 1.79/1.02    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.79/1.02    inference(cnf_transformation,[],[f27])).
% 1.79/1.02  
% 1.79/1.02  fof(f61,plain,(
% 1.79/1.02    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.79/1.02    inference(equality_resolution,[],[f42])).
% 1.79/1.02  
% 1.79/1.02  fof(f41,plain,(
% 1.79/1.02    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 1.79/1.02    inference(cnf_transformation,[],[f27])).
% 1.79/1.02  
% 1.79/1.02  fof(f57,plain,(
% 1.79/1.02    k1_xboole_0 != sK3),
% 1.79/1.02    inference(cnf_transformation,[],[f37])).
% 1.79/1.02  
% 1.79/1.02  cnf(c_0,plain,
% 1.79/1.02      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 1.79/1.02      inference(cnf_transformation,[],[f38]) ).
% 1.79/1.02  
% 1.79/1.02  cnf(c_2,plain,
% 1.79/1.02      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 1.79/1.02      inference(cnf_transformation,[],[f40]) ).
% 1.79/1.02  
% 1.79/1.02  cnf(c_202,plain,
% 1.79/1.02      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 1.79/1.02      inference(resolution,[status(thm)],[c_0,c_2]) ).
% 1.79/1.02  
% 1.79/1.02  cnf(c_752,plain,
% 1.79/1.02      ( k1_xboole_0 = X0 | r2_hidden(sK0(X0),X0) = iProver_top ),
% 1.79/1.02      inference(predicate_to_equality,[status(thm)],[c_202]) ).
% 1.79/1.02  
% 1.79/1.02  cnf(c_11,plain,
% 1.79/1.02      ( ~ v1_relat_1(X0)
% 1.79/1.02      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 1.79/1.02      inference(cnf_transformation,[],[f49]) ).
% 1.79/1.02  
% 1.79/1.02  cnf(c_21,negated_conjecture,
% 1.79/1.02      ( v1_relat_1(sK4) ),
% 1.79/1.02      inference(cnf_transformation,[],[f56]) ).
% 1.79/1.02  
% 1.79/1.02  cnf(c_365,plain,
% 1.79/1.02      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | sK4 != X0 ),
% 1.79/1.02      inference(resolution_lifted,[status(thm)],[c_11,c_21]) ).
% 1.79/1.02  
% 1.79/1.02  cnf(c_366,plain,
% 1.79/1.02      ( k9_relat_1(sK4,k1_relat_1(sK4)) = k2_relat_1(sK4) ),
% 1.79/1.02      inference(unflattening,[status(thm)],[c_365]) ).
% 1.79/1.02  
% 1.79/1.02  cnf(c_18,negated_conjecture,
% 1.79/1.02      ( k1_xboole_0 = k10_relat_1(sK4,sK3) ),
% 1.79/1.02      inference(cnf_transformation,[],[f59]) ).
% 1.79/1.02  
% 1.79/1.02  cnf(c_9,plain,
% 1.79/1.02      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 1.79/1.02      | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
% 1.79/1.02      | ~ v1_relat_1(X1) ),
% 1.79/1.02      inference(cnf_transformation,[],[f46]) ).
% 1.79/1.02  
% 1.79/1.02  cnf(c_303,plain,
% 1.79/1.02      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 1.79/1.02      | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
% 1.79/1.02      | sK4 != X1 ),
% 1.79/1.02      inference(resolution_lifted,[status(thm)],[c_9,c_21]) ).
% 1.79/1.02  
% 1.79/1.02  cnf(c_304,plain,
% 1.79/1.02      ( ~ r2_hidden(X0,k9_relat_1(sK4,X1))
% 1.79/1.02      | r2_hidden(k4_tarski(sK1(X0,X1,sK4),X0),sK4) ),
% 1.79/1.02      inference(unflattening,[status(thm)],[c_303]) ).
% 1.79/1.02  
% 1.79/1.02  cnf(c_744,plain,
% 1.79/1.02      ( r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
% 1.79/1.02      | r2_hidden(k4_tarski(sK1(X0,X1,sK4),X0),sK4) = iProver_top ),
% 1.79/1.02      inference(predicate_to_equality,[status(thm)],[c_304]) ).
% 1.79/1.02  
% 1.79/1.02  cnf(c_12,plain,
% 1.79/1.02      ( ~ r2_hidden(X0,X1)
% 1.79/1.02      | r2_hidden(X2,k10_relat_1(X3,X1))
% 1.79/1.02      | ~ r2_hidden(X0,k2_relat_1(X3))
% 1.79/1.02      | ~ r2_hidden(k4_tarski(X2,X0),X3)
% 1.79/1.02      | ~ v1_relat_1(X3) ),
% 1.79/1.02      inference(cnf_transformation,[],[f53]) ).
% 1.79/1.02  
% 1.79/1.02  cnf(c_327,plain,
% 1.79/1.02      ( ~ r2_hidden(X0,X1)
% 1.79/1.02      | r2_hidden(X2,k10_relat_1(X3,X1))
% 1.79/1.02      | ~ r2_hidden(X0,k2_relat_1(X3))
% 1.79/1.02      | ~ r2_hidden(k4_tarski(X2,X0),X3)
% 1.79/1.02      | sK4 != X3 ),
% 1.79/1.02      inference(resolution_lifted,[status(thm)],[c_12,c_21]) ).
% 1.79/1.02  
% 1.79/1.02  cnf(c_328,plain,
% 1.79/1.02      ( ~ r2_hidden(X0,X1)
% 1.79/1.02      | r2_hidden(X2,k10_relat_1(sK4,X1))
% 1.79/1.02      | ~ r2_hidden(X0,k2_relat_1(sK4))
% 1.79/1.02      | ~ r2_hidden(k4_tarski(X2,X0),sK4) ),
% 1.79/1.02      inference(unflattening,[status(thm)],[c_327]) ).
% 1.79/1.02  
% 1.79/1.02  cnf(c_16,plain,
% 1.79/1.02      ( r2_hidden(X0,k2_relat_1(X1))
% 1.79/1.02      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 1.79/1.02      | ~ v1_relat_1(X1) ),
% 1.79/1.02      inference(cnf_transformation,[],[f55]) ).
% 1.79/1.02  
% 1.79/1.02  cnf(c_243,plain,
% 1.79/1.02      ( r2_hidden(X0,k2_relat_1(X1))
% 1.79/1.02      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 1.79/1.02      | sK4 != X1 ),
% 1.79/1.02      inference(resolution_lifted,[status(thm)],[c_16,c_21]) ).
% 1.79/1.02  
% 1.79/1.02  cnf(c_244,plain,
% 1.79/1.02      ( r2_hidden(X0,k2_relat_1(sK4))
% 1.79/1.02      | ~ r2_hidden(k4_tarski(X1,X0),sK4) ),
% 1.79/1.02      inference(unflattening,[status(thm)],[c_243]) ).
% 1.79/1.02  
% 1.79/1.02  cnf(c_336,plain,
% 1.79/1.02      ( ~ r2_hidden(X0,X1)
% 1.79/1.02      | r2_hidden(X2,k10_relat_1(sK4,X1))
% 1.79/1.02      | ~ r2_hidden(k4_tarski(X2,X0),sK4) ),
% 1.79/1.02      inference(forward_subsumption_resolution,
% 1.79/1.02                [status(thm)],
% 1.79/1.02                [c_328,c_244]) ).
% 1.79/1.02  
% 1.79/1.02  cnf(c_742,plain,
% 1.79/1.02      ( r2_hidden(X0,X1) != iProver_top
% 1.79/1.02      | r2_hidden(X2,k10_relat_1(sK4,X1)) = iProver_top
% 1.79/1.02      | r2_hidden(k4_tarski(X2,X0),sK4) != iProver_top ),
% 1.79/1.02      inference(predicate_to_equality,[status(thm)],[c_336]) ).
% 1.79/1.02  
% 1.79/1.02  cnf(c_1428,plain,
% 1.79/1.02      ( r2_hidden(X0,X1) != iProver_top
% 1.79/1.02      | r2_hidden(X0,k9_relat_1(sK4,X2)) != iProver_top
% 1.79/1.02      | r2_hidden(sK1(X0,X2,sK4),k10_relat_1(sK4,X1)) = iProver_top ),
% 1.79/1.02      inference(superposition,[status(thm)],[c_744,c_742]) ).
% 1.79/1.02  
% 1.79/1.02  cnf(c_3569,plain,
% 1.79/1.02      ( r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
% 1.79/1.02      | r2_hidden(X0,sK3) != iProver_top
% 1.79/1.02      | r2_hidden(sK1(X0,X1,sK4),k1_xboole_0) = iProver_top ),
% 1.79/1.02      inference(superposition,[status(thm)],[c_18,c_1428]) ).
% 1.79/1.02  
% 1.79/1.02  cnf(c_3,plain,
% 1.79/1.02      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 1.79/1.02      inference(cnf_transformation,[],[f60]) ).
% 1.79/1.02  
% 1.79/1.02  cnf(c_6,plain,
% 1.79/1.02      ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
% 1.79/1.02      inference(cnf_transformation,[],[f44]) ).
% 1.79/1.02  
% 1.79/1.02  cnf(c_753,plain,
% 1.79/1.02      ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 1.79/1.02      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 1.79/1.02  
% 1.79/1.02  cnf(c_1447,plain,
% 1.79/1.02      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 1.79/1.02      inference(superposition,[status(thm)],[c_3,c_753]) ).
% 1.79/1.02  
% 1.79/1.02  cnf(c_3602,plain,
% 1.79/1.02      ( r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
% 1.79/1.02      | r2_hidden(X0,sK3) != iProver_top ),
% 1.79/1.02      inference(forward_subsumption_resolution,
% 1.79/1.02                [status(thm)],
% 1.79/1.02                [c_3569,c_1447]) ).
% 1.79/1.02  
% 1.79/1.02  cnf(c_3609,plain,
% 1.79/1.02      ( r2_hidden(X0,k2_relat_1(sK4)) != iProver_top
% 1.79/1.02      | r2_hidden(X0,sK3) != iProver_top ),
% 1.79/1.02      inference(superposition,[status(thm)],[c_366,c_3602]) ).
% 1.79/1.02  
% 1.79/1.02  cnf(c_1,plain,
% 1.79/1.02      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 1.79/1.02      inference(cnf_transformation,[],[f39]) ).
% 1.79/1.02  
% 1.79/1.02  cnf(c_19,negated_conjecture,
% 1.79/1.02      ( r1_tarski(sK3,k2_relat_1(sK4)) ),
% 1.79/1.02      inference(cnf_transformation,[],[f58]) ).
% 1.79/1.02  
% 1.79/1.02  cnf(c_216,plain,
% 1.79/1.02      ( ~ r2_hidden(X0,X1)
% 1.79/1.02      | r2_hidden(X0,X2)
% 1.79/1.02      | k2_relat_1(sK4) != X2
% 1.79/1.02      | sK3 != X1 ),
% 1.79/1.02      inference(resolution_lifted,[status(thm)],[c_1,c_19]) ).
% 1.79/1.02  
% 1.79/1.02  cnf(c_217,plain,
% 1.79/1.02      ( r2_hidden(X0,k2_relat_1(sK4)) | ~ r2_hidden(X0,sK3) ),
% 1.79/1.02      inference(unflattening,[status(thm)],[c_216]) ).
% 1.79/1.02  
% 1.79/1.02  cnf(c_218,plain,
% 1.79/1.02      ( r2_hidden(X0,k2_relat_1(sK4)) = iProver_top
% 1.79/1.02      | r2_hidden(X0,sK3) != iProver_top ),
% 1.79/1.02      inference(predicate_to_equality,[status(thm)],[c_217]) ).
% 1.79/1.02  
% 1.79/1.02  cnf(c_3654,plain,
% 1.79/1.02      ( r2_hidden(X0,sK3) != iProver_top ),
% 1.79/1.02      inference(global_propositional_subsumption,
% 1.79/1.02                [status(thm)],
% 1.79/1.02                [c_3609,c_218]) ).
% 1.79/1.02  
% 1.79/1.02  cnf(c_3661,plain,
% 1.79/1.02      ( sK3 = k1_xboole_0 ),
% 1.79/1.02      inference(superposition,[status(thm)],[c_752,c_3654]) ).
% 1.79/1.02  
% 1.79/1.02  cnf(c_505,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 1.79/1.02  
% 1.79/1.02  cnf(c_861,plain,
% 1.79/1.02      ( sK3 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK3 ),
% 1.79/1.02      inference(instantiation,[status(thm)],[c_505]) ).
% 1.79/1.02  
% 1.79/1.02  cnf(c_862,plain,
% 1.79/1.02      ( sK3 != k1_xboole_0
% 1.79/1.02      | k1_xboole_0 = sK3
% 1.79/1.02      | k1_xboole_0 != k1_xboole_0 ),
% 1.79/1.02      inference(instantiation,[status(thm)],[c_861]) ).
% 1.79/1.02  
% 1.79/1.02  cnf(c_4,plain,
% 1.79/1.02      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 1.79/1.02      inference(cnf_transformation,[],[f61]) ).
% 1.79/1.02  
% 1.79/1.02  cnf(c_61,plain,
% 1.79/1.02      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 1.79/1.02      inference(instantiation,[status(thm)],[c_4]) ).
% 1.79/1.02  
% 1.79/1.02  cnf(c_5,plain,
% 1.79/1.02      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 1.79/1.02      | k1_xboole_0 = X0
% 1.79/1.02      | k1_xboole_0 = X1 ),
% 1.79/1.02      inference(cnf_transformation,[],[f41]) ).
% 1.79/1.02  
% 1.79/1.02  cnf(c_60,plain,
% 1.79/1.02      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 1.79/1.02      | k1_xboole_0 = k1_xboole_0 ),
% 1.79/1.02      inference(instantiation,[status(thm)],[c_5]) ).
% 1.79/1.02  
% 1.79/1.02  cnf(c_20,negated_conjecture,
% 1.79/1.02      ( k1_xboole_0 != sK3 ),
% 1.79/1.02      inference(cnf_transformation,[],[f57]) ).
% 1.79/1.02  
% 1.79/1.02  cnf(contradiction,plain,
% 1.79/1.02      ( $false ),
% 1.79/1.02      inference(minisat,[status(thm)],[c_3661,c_862,c_61,c_60,c_20]) ).
% 1.79/1.02  
% 1.79/1.02  
% 1.79/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 1.79/1.02  
% 1.79/1.02  ------                               Statistics
% 1.79/1.02  
% 1.79/1.02  ------ General
% 1.79/1.02  
% 1.79/1.02  abstr_ref_over_cycles:                  0
% 1.79/1.02  abstr_ref_under_cycles:                 0
% 1.79/1.02  gc_basic_clause_elim:                   0
% 1.79/1.02  forced_gc_time:                         0
% 1.79/1.02  parsing_time:                           0.01
% 1.79/1.02  unif_index_cands_time:                  0.
% 1.79/1.02  unif_index_add_time:                    0.
% 1.79/1.02  orderings_time:                         0.
% 1.79/1.02  out_proof_time:                         0.006
% 1.79/1.02  total_time:                             0.171
% 1.79/1.02  num_of_symbols:                         47
% 1.79/1.02  num_of_terms:                           3212
% 1.79/1.02  
% 1.79/1.02  ------ Preprocessing
% 1.79/1.02  
% 1.79/1.02  num_of_splits:                          0
% 1.79/1.02  num_of_split_atoms:                     0
% 1.79/1.02  num_of_reused_defs:                     0
% 1.79/1.02  num_eq_ax_congr_red:                    20
% 1.79/1.02  num_of_sem_filtered_clauses:            1
% 1.79/1.02  num_of_subtypes:                        0
% 1.79/1.02  monotx_restored_types:                  0
% 1.79/1.02  sat_num_of_epr_types:                   0
% 1.79/1.02  sat_num_of_non_cyclic_types:            0
% 1.79/1.02  sat_guarded_non_collapsed_types:        0
% 1.79/1.02  num_pure_diseq_elim:                    0
% 1.79/1.02  simp_replaced_by:                       0
% 1.79/1.02  res_preprocessed:                       102
% 1.79/1.02  prep_upred:                             0
% 1.79/1.02  prep_unflattend:                        13
% 1.79/1.02  smt_new_axioms:                         0
% 1.79/1.02  pred_elim_cands:                        1
% 1.79/1.02  pred_elim:                              3
% 1.79/1.02  pred_elim_cl:                           3
% 1.79/1.02  pred_elim_cycles:                       5
% 1.79/1.02  merged_defs:                            0
% 1.79/1.02  merged_defs_ncl:                        0
% 1.79/1.02  bin_hyper_res:                          0
% 1.79/1.02  prep_cycles:                            4
% 1.79/1.02  pred_elim_time:                         0.005
% 1.79/1.02  splitting_time:                         0.
% 1.79/1.02  sem_filter_time:                        0.
% 1.79/1.02  monotx_time:                            0.001
% 1.79/1.02  subtype_inf_time:                       0.
% 1.79/1.02  
% 1.79/1.02  ------ Problem properties
% 1.79/1.02  
% 1.79/1.02  clauses:                                19
% 1.79/1.02  conjectures:                            2
% 1.79/1.02  epr:                                    1
% 1.79/1.02  horn:                                   17
% 1.79/1.02  ground:                                 3
% 1.79/1.02  unary:                                  6
% 1.79/1.02  binary:                                 10
% 1.79/1.02  lits:                                   35
% 1.79/1.02  lits_eq:                                9
% 1.79/1.02  fd_pure:                                0
% 1.79/1.02  fd_pseudo:                              0
% 1.79/1.02  fd_cond:                                2
% 1.79/1.02  fd_pseudo_cond:                         0
% 1.79/1.02  ac_symbols:                             0
% 1.79/1.02  
% 1.79/1.02  ------ Propositional Solver
% 1.79/1.02  
% 1.79/1.02  prop_solver_calls:                      29
% 1.79/1.02  prop_fast_solver_calls:                 585
% 1.79/1.02  smt_solver_calls:                       0
% 1.79/1.02  smt_fast_solver_calls:                  0
% 1.79/1.02  prop_num_of_clauses:                    1409
% 1.79/1.02  prop_preprocess_simplified:             4859
% 1.79/1.02  prop_fo_subsumed:                       1
% 1.79/1.02  prop_solver_time:                       0.
% 1.79/1.02  smt_solver_time:                        0.
% 1.79/1.02  smt_fast_solver_time:                   0.
% 1.79/1.02  prop_fast_solver_time:                  0.
% 1.79/1.02  prop_unsat_core_time:                   0.
% 1.79/1.02  
% 1.79/1.02  ------ QBF
% 1.79/1.02  
% 1.79/1.02  qbf_q_res:                              0
% 1.79/1.02  qbf_num_tautologies:                    0
% 1.79/1.02  qbf_prep_cycles:                        0
% 1.79/1.02  
% 1.79/1.02  ------ BMC1
% 1.79/1.02  
% 1.79/1.02  bmc1_current_bound:                     -1
% 1.79/1.02  bmc1_last_solved_bound:                 -1
% 1.79/1.02  bmc1_unsat_core_size:                   -1
% 1.79/1.02  bmc1_unsat_core_parents_size:           -1
% 1.79/1.02  bmc1_merge_next_fun:                    0
% 1.79/1.02  bmc1_unsat_core_clauses_time:           0.
% 1.79/1.02  
% 1.79/1.02  ------ Instantiation
% 1.79/1.02  
% 1.79/1.02  inst_num_of_clauses:                    638
% 1.79/1.02  inst_num_in_passive:                    271
% 1.79/1.02  inst_num_in_active:                     307
% 1.79/1.02  inst_num_in_unprocessed:                60
% 1.79/1.02  inst_num_of_loops:                      330
% 1.79/1.02  inst_num_of_learning_restarts:          0
% 1.79/1.02  inst_num_moves_active_passive:          18
% 1.79/1.02  inst_lit_activity:                      0
% 1.79/1.02  inst_lit_activity_moves:                0
% 1.79/1.02  inst_num_tautologies:                   0
% 1.79/1.02  inst_num_prop_implied:                  0
% 1.79/1.02  inst_num_existing_simplified:           0
% 1.79/1.02  inst_num_eq_res_simplified:             0
% 1.79/1.02  inst_num_child_elim:                    0
% 1.79/1.02  inst_num_of_dismatching_blockings:      65
% 1.79/1.02  inst_num_of_non_proper_insts:           395
% 1.79/1.02  inst_num_of_duplicates:                 0
% 1.79/1.02  inst_inst_num_from_inst_to_res:         0
% 1.79/1.02  inst_dismatching_checking_time:         0.
% 1.79/1.02  
% 1.79/1.02  ------ Resolution
% 1.79/1.02  
% 1.79/1.02  res_num_of_clauses:                     0
% 1.79/1.02  res_num_in_passive:                     0
% 1.79/1.02  res_num_in_active:                      0
% 1.79/1.02  res_num_of_loops:                       106
% 1.79/1.02  res_forward_subset_subsumed:            23
% 1.79/1.02  res_backward_subset_subsumed:           0
% 1.79/1.02  res_forward_subsumed:                   0
% 1.79/1.02  res_backward_subsumed:                  0
% 1.79/1.02  res_forward_subsumption_resolution:     2
% 1.79/1.02  res_backward_subsumption_resolution:    0
% 1.79/1.02  res_clause_to_clause_subsumption:       213
% 1.79/1.02  res_orphan_elimination:                 0
% 1.79/1.02  res_tautology_del:                      41
% 1.79/1.02  res_num_eq_res_simplified:              0
% 1.79/1.02  res_num_sel_changes:                    0
% 1.79/1.02  res_moves_from_active_to_pass:          0
% 1.79/1.02  
% 1.79/1.02  ------ Superposition
% 1.79/1.02  
% 1.79/1.02  sup_time_total:                         0.
% 1.79/1.02  sup_time_generating:                    0.
% 1.79/1.02  sup_time_sim_full:                      0.
% 1.79/1.02  sup_time_sim_immed:                     0.
% 1.79/1.02  
% 1.79/1.02  sup_num_of_clauses:                     74
% 1.79/1.02  sup_num_in_active:                      39
% 1.79/1.02  sup_num_in_passive:                     35
% 1.79/1.02  sup_num_of_loops:                       64
% 1.79/1.02  sup_fw_superposition:                   101
% 1.79/1.02  sup_bw_superposition:                   60
% 1.79/1.02  sup_immediate_simplified:               62
% 1.79/1.02  sup_given_eliminated:                   9
% 1.79/1.02  comparisons_done:                       0
% 1.79/1.02  comparisons_avoided:                    0
% 1.79/1.02  
% 1.79/1.02  ------ Simplifications
% 1.79/1.02  
% 1.79/1.02  
% 1.79/1.02  sim_fw_subset_subsumed:                 31
% 1.79/1.02  sim_bw_subset_subsumed:                 0
% 1.79/1.02  sim_fw_subsumed:                        15
% 1.79/1.02  sim_bw_subsumed:                        1
% 1.79/1.02  sim_fw_subsumption_res:                 1
% 1.79/1.02  sim_bw_subsumption_res:                 0
% 1.79/1.02  sim_tautology_del:                      3
% 1.79/1.02  sim_eq_tautology_del:                   8
% 1.79/1.02  sim_eq_res_simp:                        0
% 1.79/1.02  sim_fw_demodulated:                     2
% 1.79/1.02  sim_bw_demodulated:                     51
% 1.79/1.02  sim_light_normalised:                   36
% 1.79/1.02  sim_joinable_taut:                      0
% 1.79/1.02  sim_joinable_simp:                      0
% 1.79/1.02  sim_ac_normalised:                      0
% 1.79/1.02  sim_smt_subsumption:                    0
% 1.79/1.02  
%------------------------------------------------------------------------------
