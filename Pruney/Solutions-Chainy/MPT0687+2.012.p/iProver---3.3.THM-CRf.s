%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:51:32 EST 2020

% Result     : Theorem 0.38s
% Output     : CNFRefutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 716 expanded)
%              Number of clauses        :   55 (  85 expanded)
%              Number of leaves         :   23 ( 212 expanded)
%              Depth                    :   21
%              Number of atoms          :  266 (1065 expanded)
%              Number of equality atoms :  124 ( 724 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
        | r2_hidden(X0,X1) )
      & ( ~ r2_hidden(X0,X1)
        | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f19,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f69,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f58,f68])).

fof(f70,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f42,f69])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f12])).

fof(f64,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f49,f50])).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f48,f64])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f47,f65])).

fof(f67,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f46,f66])).

fof(f68,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f45,f67])).

fof(f71,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f44,f68])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f53,f70,f71,f71])).

fof(f21,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k2_relat_1(X1))
      <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k2_relat_1(X1))
        <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f28,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k2_relat_1(X1))
      <~> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f33,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0))
        | ~ r2_hidden(X0,k2_relat_1(X1)) )
      & ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))
        | r2_hidden(X0,k2_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f34,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0))
        | ~ r2_hidden(X0,k2_relat_1(X1)) )
      & ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))
        | r2_hidden(X0,k2_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f35,plain,
    ( ? [X0,X1] :
        ( ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0))
          | ~ r2_hidden(X0,k2_relat_1(X1)) )
        & ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))
          | r2_hidden(X0,k2_relat_1(X1)) )
        & v1_relat_1(X1) )
   => ( ( k1_xboole_0 = k10_relat_1(sK2,k1_tarski(sK1))
        | ~ r2_hidden(sK1,k2_relat_1(sK2)) )
      & ( k1_xboole_0 != k10_relat_1(sK2,k1_tarski(sK1))
        | r2_hidden(sK1,k2_relat_1(sK2)) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ( k1_xboole_0 = k10_relat_1(sK2,k1_tarski(sK1))
      | ~ r2_hidden(sK1,k2_relat_1(sK2)) )
    & ( k1_xboole_0 != k10_relat_1(sK2,k1_tarski(sK1))
      | r2_hidden(sK1,k2_relat_1(sK2)) )
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f34,f35])).

fof(f63,plain,
    ( k1_xboole_0 = k10_relat_1(sK2,k1_tarski(sK1))
    | ~ r2_hidden(sK1,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f36])).

fof(f1,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f81,plain,
    ( o_0_0_xboole_0 = k10_relat_1(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | ~ r2_hidden(sK1,k2_relat_1(sK2)) ),
    inference(definition_unfolding,[],[f63,f37,f71])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f51,f71])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ) ),
    inference(definition_unfolding,[],[f52,f70,f71,f71])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k10_relat_1(X1,X0)
          | ~ r1_xboole_0(k2_relat_1(X1),X0) )
        & ( r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 != k10_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k10_relat_1(X1,X0)
      | ~ r1_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f79,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 = k10_relat_1(X1,X0)
      | ~ r1_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f60,f37])).

fof(f61,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_relat_1(X1),X0)
      | k1_xboole_0 != k10_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_relat_1(X1),X0)
      | o_0_0_xboole_0 != k10_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f59,f37])).

fof(f62,plain,
    ( k1_xboole_0 != k10_relat_1(sK2,k1_tarski(sK1))
    | r2_hidden(sK1,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f36])).

fof(f82,plain,
    ( o_0_0_xboole_0 != k10_relat_1(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | r2_hidden(sK1,k2_relat_1(sK2)) ),
    inference(definition_unfolding,[],[f62,f37,f71])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
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

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f29])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f15,axiom,(
    ! [X0,X1] : k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f77,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f54,f69,f71,f68,f71])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f73,plain,(
    ! [X0] : o_0_0_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(definition_unfolding,[],[f43,f37])).

fof(f17,axiom,(
    ! [X0] : v1_xboole_0(k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : v1_xboole_0(k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f16,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f72,plain,(
    ! [X0] : o_0_0_xboole_0 = k1_subset_1(X0) ),
    inference(definition_unfolding,[],[f55,f37])).

fof(f78,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f56,f72])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : ~ v1_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : ~ v1_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_374,plain,
    ( r2_hidden(X0_41,X1_41)
    | k5_xboole_0(k6_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41),k1_setfam_1(k6_enumset1(k6_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41),k6_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41),k6_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41),k6_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41),k6_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41),k6_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41),k6_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41),X1_41))) = k6_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_735,plain,
    ( k5_xboole_0(k6_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41),k1_setfam_1(k6_enumset1(k6_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41),k6_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41),k6_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41),k6_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41),k6_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41),k6_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41),k6_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41),X1_41))) = k6_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41)
    | r2_hidden(X0_41,X1_41) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_374])).

cnf(c_13,negated_conjecture,
    ( ~ r2_hidden(sK1,k2_relat_1(sK2))
    | o_0_0_xboole_0 = k10_relat_1(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_371,negated_conjecture,
    ( ~ r2_hidden(sK1,k2_relat_1(sK2))
    | o_0_0_xboole_0 = k10_relat_1(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_737,plain,
    ( o_0_0_xboole_0 = k10_relat_1(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | r2_hidden(sK1,k2_relat_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_371])).

cnf(c_1072,plain,
    ( k10_relat_1(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = o_0_0_xboole_0
    | k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_setfam_1(k6_enumset1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k2_relat_1(sK2)))) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(superposition,[status(thm)],[c_735,c_737])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_375,plain,
    ( r2_hidden(X0_41,X1_41)
    | r1_xboole_0(k6_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41),X1_41) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_834,plain,
    ( r2_hidden(sK1,k2_relat_1(sK2))
    | r1_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k2_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_375])).

cnf(c_0,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_380,plain,
    ( ~ r1_xboole_0(X0_41,X1_41)
    | r1_xboole_0(X1_41,X0_41) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_849,plain,
    ( ~ r1_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k2_relat_1(sK2))
    | r1_xboole_0(k2_relat_1(sK2),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_380])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_373,plain,
    ( ~ r2_hidden(X0_41,X1_41)
    | k5_xboole_0(k6_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41),k1_setfam_1(k6_enumset1(k6_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41),k6_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41),k6_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41),k6_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41),k6_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41),k6_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41),k6_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41),X1_41))) != k6_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_857,plain,
    ( ~ r2_hidden(sK1,k2_relat_1(sK2))
    | k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_setfam_1(k6_enumset1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k2_relat_1(sK2)))) != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_373])).

cnf(c_11,plain,
    ( ~ r1_xboole_0(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k10_relat_1(X0,X1) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_15,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_222,plain,
    ( ~ r1_xboole_0(k2_relat_1(X0),X1)
    | k10_relat_1(X0,X1) = o_0_0_xboole_0
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_15])).

cnf(c_223,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK2),X0)
    | k10_relat_1(sK2,X0) = o_0_0_xboole_0 ),
    inference(unflattening,[status(thm)],[c_222])).

cnf(c_293,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK2),X0)
    | k10_relat_1(sK2,X0) = o_0_0_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_223])).

cnf(c_367,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK2),X0_41)
    | k10_relat_1(sK2,X0_41) = o_0_0_xboole_0 ),
    inference(subtyping,[status(esa)],[c_293])).

cnf(c_916,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK2),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | k10_relat_1(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_367])).

cnf(c_1085,plain,
    ( k10_relat_1(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1072,c_834,c_849,c_857,c_916])).

cnf(c_12,plain,
    ( r1_xboole_0(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k10_relat_1(X0,X1) != o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_210,plain,
    ( r1_xboole_0(k2_relat_1(X0),X1)
    | k10_relat_1(X0,X1) != o_0_0_xboole_0
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_15])).

cnf(c_211,plain,
    ( r1_xboole_0(k2_relat_1(sK2),X0)
    | k10_relat_1(sK2,X0) != o_0_0_xboole_0 ),
    inference(unflattening,[status(thm)],[c_210])).

cnf(c_291,plain,
    ( r1_xboole_0(k2_relat_1(sK2),X0)
    | k10_relat_1(sK2,X0) != o_0_0_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_211])).

cnf(c_368,plain,
    ( r1_xboole_0(k2_relat_1(sK2),X0_41)
    | k10_relat_1(sK2,X0_41) != o_0_0_xboole_0 ),
    inference(subtyping,[status(esa)],[c_291])).

cnf(c_739,plain,
    ( k10_relat_1(sK2,X0_41) != o_0_0_xboole_0
    | r1_xboole_0(k2_relat_1(sK2),X0_41) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_368])).

cnf(c_1094,plain,
    ( r1_xboole_0(k2_relat_1(sK2),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1085,c_739])).

cnf(c_730,plain,
    ( r1_xboole_0(X0_41,X1_41) != iProver_top
    | r1_xboole_0(X1_41,X0_41) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_380])).

cnf(c_1125,plain,
    ( r1_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k2_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1094,c_730])).

cnf(c_14,negated_conjecture,
    ( r2_hidden(sK1,k2_relat_1(sK2))
    | o_0_0_xboole_0 != k10_relat_1(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_370,negated_conjecture,
    ( r2_hidden(sK1,k2_relat_1(sK2))
    | o_0_0_xboole_0 != k10_relat_1(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_738,plain,
    ( o_0_0_xboole_0 != k10_relat_1(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | r2_hidden(sK1,k2_relat_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_370])).

cnf(c_1088,plain,
    ( o_0_0_xboole_0 != o_0_0_xboole_0
    | r2_hidden(sK1,k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1085,c_738])).

cnf(c_1090,plain,
    ( r2_hidden(sK1,k2_relat_1(sK2)) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_1088])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_379,plain,
    ( ~ r2_hidden(X0_41,X1_41)
    | ~ r2_hidden(X0_41,X2_41)
    | ~ r1_xboole_0(X2_41,X1_41) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_731,plain,
    ( r2_hidden(X0_41,X1_41) != iProver_top
    | r2_hidden(X0_41,X2_41) != iProver_top
    | r1_xboole_0(X2_41,X1_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_379])).

cnf(c_1118,plain,
    ( r2_hidden(sK1,X0_41) != iProver_top
    | r1_xboole_0(X0_41,k2_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1090,c_731])).

cnf(c_1170,plain,
    ( r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1125,c_1118])).

cnf(c_1256,plain,
    ( k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_setfam_1(k6_enumset1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(superposition,[status(thm)],[c_735,c_1170])).

cnf(c_8,plain,
    ( k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_372,plain,
    ( k1_setfam_1(k6_enumset1(k6_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41),k6_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41),k6_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41),k6_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41),k6_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41),k6_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41),k6_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41),k6_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X1_41))) = k6_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_4,plain,
    ( k5_xboole_0(X0,X0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_376,plain,
    ( k5_xboole_0(X0_41,X0_41) = o_0_0_xboole_0 ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1257,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1256,c_372,c_376])).

cnf(c_9,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_10,plain,
    ( ~ v1_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_204,plain,
    ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != o_0_0_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_10])).

cnf(c_369,plain,
    ( k6_enumset1(X0_41,X1_41,X2_41,X3_41,X4_41,X5_41,X6_41,X7_41) != o_0_0_xboole_0 ),
    inference(subtyping,[status(esa)],[c_204])).

cnf(c_413,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_369])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1257,c_413])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:08:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 0.38/1.04  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.38/1.04  
% 0.38/1.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.38/1.04  
% 0.38/1.04  ------  iProver source info
% 0.38/1.04  
% 0.38/1.04  git: date: 2020-06-30 10:37:57 +0100
% 0.38/1.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.38/1.04  git: non_committed_changes: false
% 0.38/1.04  git: last_make_outside_of_git: false
% 0.38/1.04  
% 0.38/1.04  ------ 
% 0.38/1.04  
% 0.38/1.04  ------ Input Options
% 0.38/1.04  
% 0.38/1.04  --out_options                           all
% 0.38/1.04  --tptp_safe_out                         true
% 0.38/1.04  --problem_path                          ""
% 0.38/1.04  --include_path                          ""
% 0.38/1.04  --clausifier                            res/vclausify_rel
% 0.38/1.04  --clausifier_options                    --mode clausify
% 0.38/1.04  --stdin                                 false
% 0.38/1.04  --stats_out                             all
% 0.38/1.04  
% 0.38/1.04  ------ General Options
% 0.38/1.04  
% 0.38/1.04  --fof                                   false
% 0.38/1.04  --time_out_real                         305.
% 0.38/1.04  --time_out_virtual                      -1.
% 0.38/1.04  --symbol_type_check                     false
% 0.38/1.04  --clausify_out                          false
% 0.38/1.04  --sig_cnt_out                           false
% 0.38/1.04  --trig_cnt_out                          false
% 0.38/1.04  --trig_cnt_out_tolerance                1.
% 0.38/1.04  --trig_cnt_out_sk_spl                   false
% 0.38/1.04  --abstr_cl_out                          false
% 0.38/1.04  
% 0.38/1.04  ------ Global Options
% 0.38/1.04  
% 0.38/1.04  --schedule                              default
% 0.38/1.04  --add_important_lit                     false
% 0.38/1.04  --prop_solver_per_cl                    1000
% 0.38/1.04  --min_unsat_core                        false
% 0.38/1.04  --soft_assumptions                      false
% 0.38/1.04  --soft_lemma_size                       3
% 0.38/1.04  --prop_impl_unit_size                   0
% 0.38/1.04  --prop_impl_unit                        []
% 0.38/1.04  --share_sel_clauses                     true
% 0.38/1.04  --reset_solvers                         false
% 0.38/1.04  --bc_imp_inh                            [conj_cone]
% 0.38/1.04  --conj_cone_tolerance                   3.
% 0.38/1.04  --extra_neg_conj                        none
% 0.38/1.04  --large_theory_mode                     true
% 0.38/1.04  --prolific_symb_bound                   200
% 0.38/1.04  --lt_threshold                          2000
% 0.38/1.04  --clause_weak_htbl                      true
% 0.38/1.04  --gc_record_bc_elim                     false
% 0.38/1.04  
% 0.38/1.04  ------ Preprocessing Options
% 0.38/1.04  
% 0.38/1.04  --preprocessing_flag                    true
% 0.38/1.04  --time_out_prep_mult                    0.1
% 0.38/1.04  --splitting_mode                        input
% 0.38/1.04  --splitting_grd                         true
% 0.38/1.04  --splitting_cvd                         false
% 0.38/1.04  --splitting_cvd_svl                     false
% 0.38/1.04  --splitting_nvd                         32
% 0.38/1.04  --sub_typing                            true
% 0.38/1.04  --prep_gs_sim                           true
% 0.38/1.04  --prep_unflatten                        true
% 0.38/1.04  --prep_res_sim                          true
% 0.38/1.04  --prep_upred                            true
% 0.38/1.04  --prep_sem_filter                       exhaustive
% 0.38/1.04  --prep_sem_filter_out                   false
% 0.38/1.04  --pred_elim                             true
% 0.38/1.04  --res_sim_input                         true
% 0.38/1.04  --eq_ax_congr_red                       true
% 0.38/1.04  --pure_diseq_elim                       true
% 0.38/1.04  --brand_transform                       false
% 0.38/1.04  --non_eq_to_eq                          false
% 0.38/1.04  --prep_def_merge                        true
% 0.38/1.04  --prep_def_merge_prop_impl              false
% 0.38/1.04  --prep_def_merge_mbd                    true
% 0.38/1.04  --prep_def_merge_tr_red                 false
% 0.38/1.04  --prep_def_merge_tr_cl                  false
% 0.38/1.04  --smt_preprocessing                     true
% 0.38/1.04  --smt_ac_axioms                         fast
% 0.38/1.04  --preprocessed_out                      false
% 0.38/1.04  --preprocessed_stats                    false
% 0.38/1.04  
% 0.38/1.04  ------ Abstraction refinement Options
% 0.38/1.04  
% 0.38/1.04  --abstr_ref                             []
% 0.38/1.04  --abstr_ref_prep                        false
% 0.38/1.04  --abstr_ref_until_sat                   false
% 0.38/1.04  --abstr_ref_sig_restrict                funpre
% 0.38/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 0.38/1.04  --abstr_ref_under                       []
% 0.38/1.04  
% 0.38/1.04  ------ SAT Options
% 0.38/1.04  
% 0.38/1.04  --sat_mode                              false
% 0.38/1.04  --sat_fm_restart_options                ""
% 0.38/1.04  --sat_gr_def                            false
% 0.38/1.04  --sat_epr_types                         true
% 0.38/1.04  --sat_non_cyclic_types                  false
% 0.38/1.04  --sat_finite_models                     false
% 0.38/1.04  --sat_fm_lemmas                         false
% 0.38/1.04  --sat_fm_prep                           false
% 0.38/1.04  --sat_fm_uc_incr                        true
% 0.38/1.04  --sat_out_model                         small
% 0.38/1.04  --sat_out_clauses                       false
% 0.38/1.04  
% 0.38/1.04  ------ QBF Options
% 0.38/1.04  
% 0.38/1.04  --qbf_mode                              false
% 0.38/1.04  --qbf_elim_univ                         false
% 0.38/1.04  --qbf_dom_inst                          none
% 0.38/1.04  --qbf_dom_pre_inst                      false
% 0.38/1.04  --qbf_sk_in                             false
% 0.38/1.04  --qbf_pred_elim                         true
% 0.38/1.04  --qbf_split                             512
% 0.38/1.04  
% 0.38/1.04  ------ BMC1 Options
% 0.38/1.04  
% 0.38/1.04  --bmc1_incremental                      false
% 0.38/1.04  --bmc1_axioms                           reachable_all
% 0.38/1.04  --bmc1_min_bound                        0
% 0.38/1.04  --bmc1_max_bound                        -1
% 0.38/1.04  --bmc1_max_bound_default                -1
% 0.38/1.04  --bmc1_symbol_reachability              true
% 0.38/1.04  --bmc1_property_lemmas                  false
% 0.38/1.04  --bmc1_k_induction                      false
% 0.38/1.04  --bmc1_non_equiv_states                 false
% 0.38/1.04  --bmc1_deadlock                         false
% 0.38/1.04  --bmc1_ucm                              false
% 0.38/1.04  --bmc1_add_unsat_core                   none
% 0.38/1.04  --bmc1_unsat_core_children              false
% 0.38/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 0.38/1.04  --bmc1_out_stat                         full
% 0.38/1.04  --bmc1_ground_init                      false
% 0.38/1.04  --bmc1_pre_inst_next_state              false
% 0.38/1.04  --bmc1_pre_inst_state                   false
% 0.38/1.04  --bmc1_pre_inst_reach_state             false
% 0.38/1.04  --bmc1_out_unsat_core                   false
% 0.38/1.04  --bmc1_aig_witness_out                  false
% 0.38/1.04  --bmc1_verbose                          false
% 0.38/1.04  --bmc1_dump_clauses_tptp                false
% 0.38/1.04  --bmc1_dump_unsat_core_tptp             false
% 0.38/1.04  --bmc1_dump_file                        -
% 0.38/1.04  --bmc1_ucm_expand_uc_limit              128
% 0.38/1.04  --bmc1_ucm_n_expand_iterations          6
% 0.38/1.04  --bmc1_ucm_extend_mode                  1
% 0.38/1.04  --bmc1_ucm_init_mode                    2
% 0.38/1.04  --bmc1_ucm_cone_mode                    none
% 0.38/1.04  --bmc1_ucm_reduced_relation_type        0
% 0.38/1.04  --bmc1_ucm_relax_model                  4
% 0.38/1.04  --bmc1_ucm_full_tr_after_sat            true
% 0.38/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 0.38/1.04  --bmc1_ucm_layered_model                none
% 0.38/1.04  --bmc1_ucm_max_lemma_size               10
% 0.38/1.04  
% 0.38/1.04  ------ AIG Options
% 0.38/1.04  
% 0.38/1.04  --aig_mode                              false
% 0.38/1.04  
% 0.38/1.04  ------ Instantiation Options
% 0.38/1.04  
% 0.38/1.04  --instantiation_flag                    true
% 0.38/1.04  --inst_sos_flag                         false
% 0.38/1.04  --inst_sos_phase                        true
% 0.38/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.38/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.38/1.04  --inst_lit_sel_side                     num_symb
% 0.38/1.04  --inst_solver_per_active                1400
% 0.38/1.04  --inst_solver_calls_frac                1.
% 0.38/1.04  --inst_passive_queue_type               priority_queues
% 0.38/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.38/1.04  --inst_passive_queues_freq              [25;2]
% 0.38/1.04  --inst_dismatching                      true
% 0.38/1.04  --inst_eager_unprocessed_to_passive     true
% 0.38/1.04  --inst_prop_sim_given                   true
% 0.38/1.04  --inst_prop_sim_new                     false
% 0.38/1.04  --inst_subs_new                         false
% 0.38/1.04  --inst_eq_res_simp                      false
% 0.38/1.04  --inst_subs_given                       false
% 0.38/1.04  --inst_orphan_elimination               true
% 0.38/1.04  --inst_learning_loop_flag               true
% 0.38/1.04  --inst_learning_start                   3000
% 0.38/1.04  --inst_learning_factor                  2
% 0.38/1.04  --inst_start_prop_sim_after_learn       3
% 0.38/1.04  --inst_sel_renew                        solver
% 0.38/1.04  --inst_lit_activity_flag                true
% 0.38/1.04  --inst_restr_to_given                   false
% 0.38/1.04  --inst_activity_threshold               500
% 0.38/1.04  --inst_out_proof                        true
% 0.38/1.04  
% 0.38/1.04  ------ Resolution Options
% 0.38/1.04  
% 0.38/1.04  --resolution_flag                       true
% 0.38/1.04  --res_lit_sel                           adaptive
% 0.38/1.04  --res_lit_sel_side                      none
% 0.38/1.04  --res_ordering                          kbo
% 0.38/1.04  --res_to_prop_solver                    active
% 0.38/1.04  --res_prop_simpl_new                    false
% 0.38/1.04  --res_prop_simpl_given                  true
% 0.38/1.04  --res_passive_queue_type                priority_queues
% 0.38/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.38/1.04  --res_passive_queues_freq               [15;5]
% 0.38/1.04  --res_forward_subs                      full
% 0.38/1.04  --res_backward_subs                     full
% 0.38/1.04  --res_forward_subs_resolution           true
% 0.38/1.04  --res_backward_subs_resolution          true
% 0.38/1.04  --res_orphan_elimination                true
% 0.38/1.04  --res_time_limit                        2.
% 0.38/1.04  --res_out_proof                         true
% 0.38/1.04  
% 0.38/1.04  ------ Superposition Options
% 0.38/1.04  
% 0.38/1.04  --superposition_flag                    true
% 0.38/1.04  --sup_passive_queue_type                priority_queues
% 0.38/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.38/1.04  --sup_passive_queues_freq               [8;1;4]
% 0.38/1.04  --demod_completeness_check              fast
% 0.38/1.04  --demod_use_ground                      true
% 0.38/1.04  --sup_to_prop_solver                    passive
% 0.38/1.04  --sup_prop_simpl_new                    true
% 0.38/1.04  --sup_prop_simpl_given                  true
% 0.38/1.04  --sup_fun_splitting                     false
% 0.38/1.04  --sup_smt_interval                      50000
% 0.38/1.04  
% 0.38/1.04  ------ Superposition Simplification Setup
% 0.38/1.04  
% 0.38/1.04  --sup_indices_passive                   []
% 0.38/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.38/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.38/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.38/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 0.38/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.38/1.04  --sup_full_bw                           [BwDemod]
% 0.38/1.04  --sup_immed_triv                        [TrivRules]
% 0.38/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.38/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.38/1.04  --sup_immed_bw_main                     []
% 0.38/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.38/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 0.38/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.38/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.38/1.04  
% 0.38/1.04  ------ Combination Options
% 0.38/1.04  
% 0.38/1.04  --comb_res_mult                         3
% 0.38/1.04  --comb_sup_mult                         2
% 0.38/1.04  --comb_inst_mult                        10
% 0.38/1.04  
% 0.38/1.04  ------ Debug Options
% 0.38/1.04  
% 0.38/1.04  --dbg_backtrace                         false
% 0.38/1.04  --dbg_dump_prop_clauses                 false
% 0.38/1.04  --dbg_dump_prop_clauses_file            -
% 0.38/1.04  --dbg_out_stat                          false
% 0.38/1.04  ------ Parsing...
% 0.38/1.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.38/1.04  
% 0.38/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 0.38/1.04  
% 0.38/1.04  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.38/1.04  
% 0.38/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.38/1.04  ------ Proving...
% 0.38/1.04  ------ Problem Properties 
% 0.38/1.04  
% 0.38/1.04  
% 0.38/1.04  clauses                                 14
% 0.38/1.04  conjectures                             2
% 0.38/1.04  EPR                                     2
% 0.38/1.04  Horn                                    10
% 0.38/1.04  unary                                   3
% 0.38/1.04  binary                                  10
% 0.38/1.04  lits                                    26
% 0.38/1.04  lits eq                                 9
% 0.38/1.04  fd_pure                                 0
% 0.38/1.04  fd_pseudo                               0
% 0.38/1.04  fd_cond                                 0
% 0.38/1.04  fd_pseudo_cond                          0
% 0.38/1.04  AC symbols                              0
% 0.38/1.04  
% 0.38/1.04  ------ Schedule dynamic 5 is on 
% 0.38/1.04  
% 0.38/1.04  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.38/1.04  
% 0.38/1.04  
% 0.38/1.04  ------ 
% 0.38/1.04  Current options:
% 0.38/1.04  ------ 
% 0.38/1.04  
% 0.38/1.04  ------ Input Options
% 0.38/1.04  
% 0.38/1.04  --out_options                           all
% 0.38/1.04  --tptp_safe_out                         true
% 0.38/1.04  --problem_path                          ""
% 0.38/1.04  --include_path                          ""
% 0.38/1.04  --clausifier                            res/vclausify_rel
% 0.38/1.04  --clausifier_options                    --mode clausify
% 0.38/1.04  --stdin                                 false
% 0.38/1.04  --stats_out                             all
% 0.38/1.04  
% 0.38/1.04  ------ General Options
% 0.38/1.04  
% 0.38/1.04  --fof                                   false
% 0.38/1.04  --time_out_real                         305.
% 0.38/1.04  --time_out_virtual                      -1.
% 0.38/1.04  --symbol_type_check                     false
% 0.38/1.04  --clausify_out                          false
% 0.38/1.04  --sig_cnt_out                           false
% 0.38/1.04  --trig_cnt_out                          false
% 0.38/1.04  --trig_cnt_out_tolerance                1.
% 0.38/1.04  --trig_cnt_out_sk_spl                   false
% 0.38/1.04  --abstr_cl_out                          false
% 0.38/1.04  
% 0.38/1.04  ------ Global Options
% 0.38/1.04  
% 0.38/1.04  --schedule                              default
% 0.38/1.04  --add_important_lit                     false
% 0.38/1.04  --prop_solver_per_cl                    1000
% 0.38/1.04  --min_unsat_core                        false
% 0.38/1.04  --soft_assumptions                      false
% 0.38/1.04  --soft_lemma_size                       3
% 0.38/1.04  --prop_impl_unit_size                   0
% 0.38/1.04  --prop_impl_unit                        []
% 0.38/1.04  --share_sel_clauses                     true
% 0.38/1.04  --reset_solvers                         false
% 0.38/1.04  --bc_imp_inh                            [conj_cone]
% 0.38/1.04  --conj_cone_tolerance                   3.
% 0.38/1.04  --extra_neg_conj                        none
% 0.38/1.04  --large_theory_mode                     true
% 0.38/1.04  --prolific_symb_bound                   200
% 0.38/1.04  --lt_threshold                          2000
% 0.38/1.04  --clause_weak_htbl                      true
% 0.38/1.04  --gc_record_bc_elim                     false
% 0.38/1.04  
% 0.38/1.04  ------ Preprocessing Options
% 0.38/1.04  
% 0.38/1.04  --preprocessing_flag                    true
% 0.38/1.04  --time_out_prep_mult                    0.1
% 0.38/1.04  --splitting_mode                        input
% 0.38/1.04  --splitting_grd                         true
% 0.38/1.04  --splitting_cvd                         false
% 0.38/1.04  --splitting_cvd_svl                     false
% 0.38/1.04  --splitting_nvd                         32
% 0.38/1.04  --sub_typing                            true
% 0.38/1.04  --prep_gs_sim                           true
% 0.38/1.04  --prep_unflatten                        true
% 0.38/1.04  --prep_res_sim                          true
% 0.38/1.04  --prep_upred                            true
% 0.38/1.04  --prep_sem_filter                       exhaustive
% 0.38/1.04  --prep_sem_filter_out                   false
% 0.38/1.04  --pred_elim                             true
% 0.38/1.04  --res_sim_input                         true
% 0.38/1.04  --eq_ax_congr_red                       true
% 0.38/1.04  --pure_diseq_elim                       true
% 0.38/1.04  --brand_transform                       false
% 0.38/1.04  --non_eq_to_eq                          false
% 0.38/1.04  --prep_def_merge                        true
% 0.38/1.04  --prep_def_merge_prop_impl              false
% 0.38/1.04  --prep_def_merge_mbd                    true
% 0.38/1.04  --prep_def_merge_tr_red                 false
% 0.38/1.04  --prep_def_merge_tr_cl                  false
% 0.38/1.04  --smt_preprocessing                     true
% 0.38/1.04  --smt_ac_axioms                         fast
% 0.38/1.04  --preprocessed_out                      false
% 0.38/1.04  --preprocessed_stats                    false
% 0.38/1.04  
% 0.38/1.04  ------ Abstraction refinement Options
% 0.38/1.04  
% 0.38/1.04  --abstr_ref                             []
% 0.38/1.04  --abstr_ref_prep                        false
% 0.38/1.04  --abstr_ref_until_sat                   false
% 0.38/1.04  --abstr_ref_sig_restrict                funpre
% 0.38/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 0.38/1.04  --abstr_ref_under                       []
% 0.38/1.04  
% 0.38/1.04  ------ SAT Options
% 0.38/1.04  
% 0.38/1.04  --sat_mode                              false
% 0.38/1.04  --sat_fm_restart_options                ""
% 0.38/1.04  --sat_gr_def                            false
% 0.38/1.04  --sat_epr_types                         true
% 0.38/1.04  --sat_non_cyclic_types                  false
% 0.38/1.04  --sat_finite_models                     false
% 0.38/1.04  --sat_fm_lemmas                         false
% 0.38/1.04  --sat_fm_prep                           false
% 0.38/1.04  --sat_fm_uc_incr                        true
% 0.38/1.04  --sat_out_model                         small
% 0.38/1.04  --sat_out_clauses                       false
% 0.38/1.04  
% 0.38/1.04  ------ QBF Options
% 0.38/1.04  
% 0.38/1.04  --qbf_mode                              false
% 0.38/1.04  --qbf_elim_univ                         false
% 0.38/1.04  --qbf_dom_inst                          none
% 0.38/1.04  --qbf_dom_pre_inst                      false
% 0.38/1.04  --qbf_sk_in                             false
% 0.38/1.04  --qbf_pred_elim                         true
% 0.38/1.04  --qbf_split                             512
% 0.38/1.04  
% 0.38/1.04  ------ BMC1 Options
% 0.38/1.04  
% 0.38/1.04  --bmc1_incremental                      false
% 0.38/1.04  --bmc1_axioms                           reachable_all
% 0.38/1.04  --bmc1_min_bound                        0
% 0.38/1.04  --bmc1_max_bound                        -1
% 0.38/1.04  --bmc1_max_bound_default                -1
% 0.38/1.04  --bmc1_symbol_reachability              true
% 0.38/1.04  --bmc1_property_lemmas                  false
% 0.38/1.04  --bmc1_k_induction                      false
% 0.38/1.04  --bmc1_non_equiv_states                 false
% 0.38/1.04  --bmc1_deadlock                         false
% 0.38/1.04  --bmc1_ucm                              false
% 0.38/1.04  --bmc1_add_unsat_core                   none
% 0.38/1.04  --bmc1_unsat_core_children              false
% 0.38/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 0.38/1.04  --bmc1_out_stat                         full
% 0.38/1.04  --bmc1_ground_init                      false
% 0.38/1.04  --bmc1_pre_inst_next_state              false
% 0.38/1.04  --bmc1_pre_inst_state                   false
% 0.38/1.04  --bmc1_pre_inst_reach_state             false
% 0.38/1.04  --bmc1_out_unsat_core                   false
% 0.38/1.04  --bmc1_aig_witness_out                  false
% 0.38/1.04  --bmc1_verbose                          false
% 0.38/1.04  --bmc1_dump_clauses_tptp                false
% 0.38/1.04  --bmc1_dump_unsat_core_tptp             false
% 0.38/1.04  --bmc1_dump_file                        -
% 0.38/1.04  --bmc1_ucm_expand_uc_limit              128
% 0.38/1.04  --bmc1_ucm_n_expand_iterations          6
% 0.38/1.04  --bmc1_ucm_extend_mode                  1
% 0.38/1.04  --bmc1_ucm_init_mode                    2
% 0.38/1.04  --bmc1_ucm_cone_mode                    none
% 0.38/1.04  --bmc1_ucm_reduced_relation_type        0
% 0.38/1.04  --bmc1_ucm_relax_model                  4
% 0.38/1.04  --bmc1_ucm_full_tr_after_sat            true
% 0.38/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 0.38/1.04  --bmc1_ucm_layered_model                none
% 0.38/1.04  --bmc1_ucm_max_lemma_size               10
% 0.38/1.04  
% 0.38/1.04  ------ AIG Options
% 0.38/1.04  
% 0.38/1.04  --aig_mode                              false
% 0.38/1.04  
% 0.38/1.04  ------ Instantiation Options
% 0.38/1.04  
% 0.38/1.04  --instantiation_flag                    true
% 0.38/1.04  --inst_sos_flag                         false
% 0.38/1.04  --inst_sos_phase                        true
% 0.38/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.38/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.38/1.04  --inst_lit_sel_side                     none
% 0.38/1.04  --inst_solver_per_active                1400
% 0.38/1.04  --inst_solver_calls_frac                1.
% 0.38/1.04  --inst_passive_queue_type               priority_queues
% 0.38/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.38/1.04  --inst_passive_queues_freq              [25;2]
% 0.38/1.04  --inst_dismatching                      true
% 0.38/1.04  --inst_eager_unprocessed_to_passive     true
% 0.38/1.04  --inst_prop_sim_given                   true
% 0.38/1.04  --inst_prop_sim_new                     false
% 0.38/1.04  --inst_subs_new                         false
% 0.38/1.04  --inst_eq_res_simp                      false
% 0.38/1.04  --inst_subs_given                       false
% 0.38/1.04  --inst_orphan_elimination               true
% 0.38/1.04  --inst_learning_loop_flag               true
% 0.38/1.04  --inst_learning_start                   3000
% 0.38/1.04  --inst_learning_factor                  2
% 0.38/1.04  --inst_start_prop_sim_after_learn       3
% 0.38/1.04  --inst_sel_renew                        solver
% 0.38/1.04  --inst_lit_activity_flag                true
% 0.38/1.04  --inst_restr_to_given                   false
% 0.38/1.04  --inst_activity_threshold               500
% 0.38/1.04  --inst_out_proof                        true
% 0.38/1.04  
% 0.38/1.04  ------ Resolution Options
% 0.38/1.04  
% 0.38/1.04  --resolution_flag                       false
% 0.38/1.04  --res_lit_sel                           adaptive
% 0.38/1.04  --res_lit_sel_side                      none
% 0.38/1.04  --res_ordering                          kbo
% 0.38/1.04  --res_to_prop_solver                    active
% 0.38/1.04  --res_prop_simpl_new                    false
% 0.38/1.04  --res_prop_simpl_given                  true
% 0.38/1.04  --res_passive_queue_type                priority_queues
% 0.38/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.38/1.04  --res_passive_queues_freq               [15;5]
% 0.38/1.04  --res_forward_subs                      full
% 0.38/1.04  --res_backward_subs                     full
% 0.38/1.04  --res_forward_subs_resolution           true
% 0.38/1.04  --res_backward_subs_resolution          true
% 0.38/1.04  --res_orphan_elimination                true
% 0.38/1.04  --res_time_limit                        2.
% 0.38/1.04  --res_out_proof                         true
% 0.38/1.04  
% 0.38/1.04  ------ Superposition Options
% 0.38/1.04  
% 0.38/1.04  --superposition_flag                    true
% 0.38/1.04  --sup_passive_queue_type                priority_queues
% 0.38/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.38/1.04  --sup_passive_queues_freq               [8;1;4]
% 0.38/1.04  --demod_completeness_check              fast
% 0.38/1.04  --demod_use_ground                      true
% 0.38/1.04  --sup_to_prop_solver                    passive
% 0.38/1.04  --sup_prop_simpl_new                    true
% 0.38/1.04  --sup_prop_simpl_given                  true
% 0.38/1.04  --sup_fun_splitting                     false
% 0.38/1.04  --sup_smt_interval                      50000
% 0.38/1.04  
% 0.38/1.04  ------ Superposition Simplification Setup
% 0.38/1.04  
% 0.38/1.04  --sup_indices_passive                   []
% 0.38/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.38/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.38/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.38/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 0.38/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.38/1.04  --sup_full_bw                           [BwDemod]
% 0.38/1.04  --sup_immed_triv                        [TrivRules]
% 0.38/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.38/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.38/1.04  --sup_immed_bw_main                     []
% 0.38/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.38/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 0.38/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.38/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.38/1.04  
% 0.38/1.04  ------ Combination Options
% 0.38/1.04  
% 0.38/1.04  --comb_res_mult                         3
% 0.38/1.04  --comb_sup_mult                         2
% 0.38/1.04  --comb_inst_mult                        10
% 0.38/1.04  
% 0.38/1.04  ------ Debug Options
% 0.38/1.04  
% 0.38/1.04  --dbg_backtrace                         false
% 0.38/1.04  --dbg_dump_prop_clauses                 false
% 0.38/1.04  --dbg_dump_prop_clauses_file            -
% 0.38/1.04  --dbg_out_stat                          false
% 0.38/1.04  
% 0.38/1.04  
% 0.38/1.04  
% 0.38/1.04  
% 0.38/1.04  ------ Proving...
% 0.38/1.04  
% 0.38/1.04  
% 0.38/1.04  % SZS status Theorem for theBenchmark.p
% 0.38/1.04  
% 0.38/1.04  % SZS output start CNFRefutation for theBenchmark.p
% 0.38/1.04  
% 0.38/1.04  fof(f14,axiom,(
% 0.38/1.04    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) <=> ~r2_hidden(X0,X1))),
% 0.38/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.38/1.04  
% 0.38/1.04  fof(f31,plain,(
% 0.38/1.04    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) | r2_hidden(X0,X1)) & (~r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0)))),
% 0.38/1.04    inference(nnf_transformation,[],[f14])).
% 0.38/1.04  
% 0.38/1.04  fof(f53,plain,(
% 0.38/1.04    ( ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) | r2_hidden(X0,X1)) )),
% 0.38/1.04    inference(cnf_transformation,[],[f31])).
% 0.38/1.04  
% 0.38/1.04  fof(f4,axiom,(
% 0.38/1.04    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.38/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.38/1.04  
% 0.38/1.04  fof(f42,plain,(
% 0.38/1.04    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.38/1.04    inference(cnf_transformation,[],[f4])).
% 0.38/1.04  
% 0.38/1.04  fof(f19,axiom,(
% 0.38/1.04    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.38/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.38/1.04  
% 0.38/1.04  fof(f58,plain,(
% 0.38/1.04    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.38/1.04    inference(cnf_transformation,[],[f19])).
% 0.38/1.04  
% 0.38/1.04  fof(f69,plain,(
% 0.38/1.04    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.38/1.04    inference(definition_unfolding,[],[f58,f68])).
% 0.38/1.04  
% 0.38/1.04  fof(f70,plain,(
% 0.38/1.04    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 0.38/1.04    inference(definition_unfolding,[],[f42,f69])).
% 0.38/1.04  
% 0.38/1.04  fof(f6,axiom,(
% 0.38/1.04    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.38/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.38/1.04  
% 0.38/1.04  fof(f44,plain,(
% 0.38/1.04    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.38/1.04    inference(cnf_transformation,[],[f6])).
% 0.38/1.04  
% 0.38/1.04  fof(f7,axiom,(
% 0.38/1.04    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.38/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.38/1.04  
% 0.38/1.04  fof(f45,plain,(
% 0.38/1.04    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.38/1.04    inference(cnf_transformation,[],[f7])).
% 0.38/1.04  
% 0.38/1.04  fof(f8,axiom,(
% 0.38/1.04    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.38/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.38/1.04  
% 0.38/1.04  fof(f46,plain,(
% 0.38/1.04    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.38/1.04    inference(cnf_transformation,[],[f8])).
% 0.38/1.04  
% 0.38/1.04  fof(f9,axiom,(
% 0.38/1.04    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.38/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.38/1.04  
% 0.38/1.04  fof(f47,plain,(
% 0.38/1.04    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 0.38/1.04    inference(cnf_transformation,[],[f9])).
% 0.38/1.04  
% 0.38/1.04  fof(f10,axiom,(
% 0.38/1.04    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 0.38/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.38/1.04  
% 0.38/1.04  fof(f48,plain,(
% 0.38/1.04    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 0.38/1.04    inference(cnf_transformation,[],[f10])).
% 0.38/1.04  
% 0.38/1.04  fof(f11,axiom,(
% 0.38/1.04    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 0.38/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.38/1.04  
% 0.38/1.04  fof(f49,plain,(
% 0.38/1.04    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 0.38/1.04    inference(cnf_transformation,[],[f11])).
% 0.38/1.04  
% 0.38/1.04  fof(f12,axiom,(
% 0.38/1.04    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 0.38/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.38/1.04  
% 0.38/1.04  fof(f50,plain,(
% 0.38/1.04    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 0.38/1.04    inference(cnf_transformation,[],[f12])).
% 0.38/1.04  
% 0.38/1.04  fof(f64,plain,(
% 0.38/1.04    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.38/1.04    inference(definition_unfolding,[],[f49,f50])).
% 0.38/1.04  
% 0.38/1.04  fof(f65,plain,(
% 0.38/1.04    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.38/1.04    inference(definition_unfolding,[],[f48,f64])).
% 0.38/1.04  
% 0.38/1.04  fof(f66,plain,(
% 0.38/1.04    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.38/1.04    inference(definition_unfolding,[],[f47,f65])).
% 0.38/1.04  
% 0.38/1.04  fof(f67,plain,(
% 0.38/1.04    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.38/1.04    inference(definition_unfolding,[],[f46,f66])).
% 0.38/1.04  
% 0.38/1.04  fof(f68,plain,(
% 0.38/1.04    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.38/1.04    inference(definition_unfolding,[],[f45,f67])).
% 0.38/1.04  
% 0.38/1.04  fof(f71,plain,(
% 0.38/1.04    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.38/1.04    inference(definition_unfolding,[],[f44,f68])).
% 0.38/1.04  
% 0.38/1.04  fof(f75,plain,(
% 0.38/1.04    ( ! [X0,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) | r2_hidden(X0,X1)) )),
% 0.38/1.04    inference(definition_unfolding,[],[f53,f70,f71,f71])).
% 0.38/1.04  
% 0.38/1.04  fof(f21,conjecture,(
% 0.38/1.04    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k2_relat_1(X1)) <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))))),
% 0.38/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.38/1.04  
% 0.38/1.04  fof(f22,negated_conjecture,(
% 0.38/1.04    ~! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k2_relat_1(X1)) <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))))),
% 0.38/1.04    inference(negated_conjecture,[],[f21])).
% 0.38/1.04  
% 0.38/1.04  fof(f28,plain,(
% 0.38/1.04    ? [X0,X1] : ((r2_hidden(X0,k2_relat_1(X1)) <~> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))) & v1_relat_1(X1))),
% 0.38/1.04    inference(ennf_transformation,[],[f22])).
% 0.38/1.04  
% 0.38/1.04  fof(f33,plain,(
% 0.38/1.04    ? [X0,X1] : (((k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0)) | ~r2_hidden(X0,k2_relat_1(X1))) & (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) | r2_hidden(X0,k2_relat_1(X1)))) & v1_relat_1(X1))),
% 0.38/1.04    inference(nnf_transformation,[],[f28])).
% 0.38/1.04  
% 0.38/1.04  fof(f34,plain,(
% 0.38/1.04    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0)) | ~r2_hidden(X0,k2_relat_1(X1))) & (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) | r2_hidden(X0,k2_relat_1(X1))) & v1_relat_1(X1))),
% 0.38/1.04    inference(flattening,[],[f33])).
% 0.38/1.04  
% 0.38/1.04  fof(f35,plain,(
% 0.38/1.04    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0)) | ~r2_hidden(X0,k2_relat_1(X1))) & (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) | r2_hidden(X0,k2_relat_1(X1))) & v1_relat_1(X1)) => ((k1_xboole_0 = k10_relat_1(sK2,k1_tarski(sK1)) | ~r2_hidden(sK1,k2_relat_1(sK2))) & (k1_xboole_0 != k10_relat_1(sK2,k1_tarski(sK1)) | r2_hidden(sK1,k2_relat_1(sK2))) & v1_relat_1(sK2))),
% 0.38/1.04    introduced(choice_axiom,[])).
% 0.38/1.04  
% 0.38/1.04  fof(f36,plain,(
% 0.38/1.04    (k1_xboole_0 = k10_relat_1(sK2,k1_tarski(sK1)) | ~r2_hidden(sK1,k2_relat_1(sK2))) & (k1_xboole_0 != k10_relat_1(sK2,k1_tarski(sK1)) | r2_hidden(sK1,k2_relat_1(sK2))) & v1_relat_1(sK2)),
% 0.38/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f34,f35])).
% 0.38/1.04  
% 0.38/1.04  fof(f63,plain,(
% 0.38/1.04    k1_xboole_0 = k10_relat_1(sK2,k1_tarski(sK1)) | ~r2_hidden(sK1,k2_relat_1(sK2))),
% 0.38/1.04    inference(cnf_transformation,[],[f36])).
% 0.38/1.04  
% 0.38/1.04  fof(f1,axiom,(
% 0.38/1.04    k1_xboole_0 = o_0_0_xboole_0),
% 0.38/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.38/1.04  
% 0.38/1.04  fof(f37,plain,(
% 0.38/1.04    k1_xboole_0 = o_0_0_xboole_0),
% 0.38/1.04    inference(cnf_transformation,[],[f1])).
% 0.38/1.04  
% 0.38/1.04  fof(f81,plain,(
% 0.38/1.04    o_0_0_xboole_0 = k10_relat_1(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) | ~r2_hidden(sK1,k2_relat_1(sK2))),
% 0.38/1.04    inference(definition_unfolding,[],[f63,f37,f71])).
% 0.38/1.04  
% 0.38/1.04  fof(f13,axiom,(
% 0.38/1.04    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.38/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.38/1.04  
% 0.38/1.04  fof(f26,plain,(
% 0.38/1.04    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.38/1.04    inference(ennf_transformation,[],[f13])).
% 0.38/1.04  
% 0.38/1.04  fof(f51,plain,(
% 0.38/1.04    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.38/1.04    inference(cnf_transformation,[],[f26])).
% 0.38/1.04  
% 0.38/1.04  fof(f74,plain,(
% 0.38/1.04    ( ! [X0,X1] : (r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 0.38/1.04    inference(definition_unfolding,[],[f51,f71])).
% 0.38/1.04  
% 0.38/1.04  fof(f2,axiom,(
% 0.38/1.04    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.38/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.38/1.04  
% 0.38/1.04  fof(f24,plain,(
% 0.38/1.04    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.38/1.04    inference(ennf_transformation,[],[f2])).
% 0.38/1.04  
% 0.38/1.04  fof(f38,plain,(
% 0.38/1.04    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.38/1.04    inference(cnf_transformation,[],[f24])).
% 0.38/1.04  
% 0.38/1.04  fof(f52,plain,(
% 0.38/1.04    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0)) )),
% 0.38/1.04    inference(cnf_transformation,[],[f31])).
% 0.38/1.04  
% 0.38/1.04  fof(f76,plain,(
% 0.38/1.04    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.38/1.04    inference(definition_unfolding,[],[f52,f70,f71,f71])).
% 0.38/1.04  
% 0.38/1.04  fof(f20,axiom,(
% 0.38/1.04    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 0.38/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.38/1.04  
% 0.38/1.04  fof(f27,plain,(
% 0.38/1.04    ! [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.38/1.04    inference(ennf_transformation,[],[f20])).
% 0.38/1.04  
% 0.38/1.04  fof(f32,plain,(
% 0.38/1.04    ! [X0,X1] : (((k1_xboole_0 = k10_relat_1(X1,X0) | ~r1_xboole_0(k2_relat_1(X1),X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.38/1.04    inference(nnf_transformation,[],[f27])).
% 0.38/1.04  
% 0.38/1.04  fof(f60,plain,(
% 0.38/1.04    ( ! [X0,X1] : (k1_xboole_0 = k10_relat_1(X1,X0) | ~r1_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.38/1.04    inference(cnf_transformation,[],[f32])).
% 0.38/1.04  
% 0.38/1.04  fof(f79,plain,(
% 0.38/1.04    ( ! [X0,X1] : (o_0_0_xboole_0 = k10_relat_1(X1,X0) | ~r1_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.38/1.04    inference(definition_unfolding,[],[f60,f37])).
% 0.38/1.04  
% 0.38/1.04  fof(f61,plain,(
% 0.38/1.04    v1_relat_1(sK2)),
% 0.38/1.04    inference(cnf_transformation,[],[f36])).
% 0.38/1.04  
% 0.38/1.04  fof(f59,plain,(
% 0.38/1.04    ( ! [X0,X1] : (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.38/1.04    inference(cnf_transformation,[],[f32])).
% 0.38/1.04  
% 0.38/1.04  fof(f80,plain,(
% 0.38/1.04    ( ! [X0,X1] : (r1_xboole_0(k2_relat_1(X1),X0) | o_0_0_xboole_0 != k10_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.38/1.04    inference(definition_unfolding,[],[f59,f37])).
% 0.38/1.04  
% 0.38/1.04  fof(f62,plain,(
% 0.38/1.04    k1_xboole_0 != k10_relat_1(sK2,k1_tarski(sK1)) | r2_hidden(sK1,k2_relat_1(sK2))),
% 0.38/1.04    inference(cnf_transformation,[],[f36])).
% 0.38/1.04  
% 0.38/1.04  fof(f82,plain,(
% 0.38/1.04    o_0_0_xboole_0 != k10_relat_1(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) | r2_hidden(sK1,k2_relat_1(sK2))),
% 0.38/1.04    inference(definition_unfolding,[],[f62,f37,f71])).
% 0.38/1.04  
% 0.38/1.04  fof(f3,axiom,(
% 0.38/1.04    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.38/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.38/1.04  
% 0.38/1.04  fof(f23,plain,(
% 0.38/1.04    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.38/1.04    inference(rectify,[],[f3])).
% 0.38/1.04  
% 0.38/1.04  fof(f25,plain,(
% 0.38/1.04    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.38/1.04    inference(ennf_transformation,[],[f23])).
% 0.38/1.04  
% 0.38/1.04  fof(f29,plain,(
% 0.38/1.04    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 0.38/1.04    introduced(choice_axiom,[])).
% 0.38/1.04  
% 0.38/1.04  fof(f30,plain,(
% 0.38/1.04    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.38/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f29])).
% 0.38/1.04  
% 0.38/1.04  fof(f41,plain,(
% 0.38/1.04    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.38/1.04    inference(cnf_transformation,[],[f30])).
% 0.38/1.04  
% 0.38/1.04  fof(f15,axiom,(
% 0.38/1.04    ! [X0,X1] : k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k1_tarski(X0)),
% 0.38/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.38/1.04  
% 0.38/1.04  fof(f54,plain,(
% 0.38/1.04    ( ! [X0,X1] : (k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k1_tarski(X0)) )),
% 0.38/1.04    inference(cnf_transformation,[],[f15])).
% 0.38/1.04  
% 0.38/1.04  fof(f77,plain,(
% 0.38/1.04    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 0.38/1.04    inference(definition_unfolding,[],[f54,f69,f71,f68,f71])).
% 0.38/1.04  
% 0.38/1.04  fof(f5,axiom,(
% 0.38/1.04    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.38/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.38/1.04  
% 0.38/1.04  fof(f43,plain,(
% 0.38/1.04    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.38/1.04    inference(cnf_transformation,[],[f5])).
% 0.38/1.04  
% 0.38/1.04  fof(f73,plain,(
% 0.38/1.04    ( ! [X0] : (o_0_0_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.38/1.04    inference(definition_unfolding,[],[f43,f37])).
% 0.38/1.04  
% 0.38/1.04  fof(f17,axiom,(
% 0.38/1.04    ! [X0] : v1_xboole_0(k1_subset_1(X0))),
% 0.38/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.38/1.04  
% 0.38/1.04  fof(f56,plain,(
% 0.38/1.04    ( ! [X0] : (v1_xboole_0(k1_subset_1(X0))) )),
% 0.38/1.04    inference(cnf_transformation,[],[f17])).
% 0.38/1.04  
% 0.38/1.04  fof(f16,axiom,(
% 0.38/1.04    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 0.38/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.38/1.04  
% 0.38/1.04  fof(f55,plain,(
% 0.38/1.04    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 0.38/1.04    inference(cnf_transformation,[],[f16])).
% 0.38/1.04  
% 0.38/1.04  fof(f72,plain,(
% 0.38/1.04    ( ! [X0] : (o_0_0_xboole_0 = k1_subset_1(X0)) )),
% 0.38/1.04    inference(definition_unfolding,[],[f55,f37])).
% 0.38/1.04  
% 0.38/1.04  fof(f78,plain,(
% 0.38/1.04    v1_xboole_0(o_0_0_xboole_0)),
% 0.38/1.04    inference(definition_unfolding,[],[f56,f72])).
% 0.38/1.04  
% 0.38/1.04  fof(f18,axiom,(
% 0.38/1.04    ! [X0,X1,X2,X3,X4,X5,X6,X7] : ~v1_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))),
% 0.38/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.38/1.04  
% 0.38/1.04  fof(f57,plain,(
% 0.38/1.04    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (~v1_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))) )),
% 0.38/1.04    inference(cnf_transformation,[],[f18])).
% 0.38/1.04  
% 0.38/1.04  cnf(c_6,plain,
% 0.38/1.04      ( r2_hidden(X0,X1)
% 0.38/1.04      | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 0.38/1.04      inference(cnf_transformation,[],[f75]) ).
% 0.38/1.04  
% 0.38/1.04  cnf(c_374,plain,
% 0.38/1.04      ( r2_hidden(X0_41,X1_41)
% 0.38/1.04      | k5_xboole_0(k6_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41),k1_setfam_1(k6_enumset1(k6_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41),k6_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41),k6_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41),k6_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41),k6_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41),k6_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41),k6_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41),X1_41))) = k6_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41) ),
% 0.38/1.04      inference(subtyping,[status(esa)],[c_6]) ).
% 0.38/1.04  
% 0.38/1.04  cnf(c_735,plain,
% 0.38/1.04      ( k5_xboole_0(k6_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41),k1_setfam_1(k6_enumset1(k6_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41),k6_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41),k6_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41),k6_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41),k6_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41),k6_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41),k6_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41),X1_41))) = k6_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41)
% 0.38/1.04      | r2_hidden(X0_41,X1_41) = iProver_top ),
% 0.38/1.04      inference(predicate_to_equality,[status(thm)],[c_374]) ).
% 0.38/1.04  
% 0.38/1.04  cnf(c_13,negated_conjecture,
% 0.38/1.04      ( ~ r2_hidden(sK1,k2_relat_1(sK2))
% 0.38/1.04      | o_0_0_xboole_0 = k10_relat_1(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
% 0.38/1.04      inference(cnf_transformation,[],[f81]) ).
% 0.38/1.04  
% 0.38/1.04  cnf(c_371,negated_conjecture,
% 0.38/1.04      ( ~ r2_hidden(sK1,k2_relat_1(sK2))
% 0.38/1.04      | o_0_0_xboole_0 = k10_relat_1(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
% 0.38/1.04      inference(subtyping,[status(esa)],[c_13]) ).
% 0.38/1.04  
% 0.38/1.04  cnf(c_737,plain,
% 0.38/1.04      ( o_0_0_xboole_0 = k10_relat_1(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
% 0.38/1.04      | r2_hidden(sK1,k2_relat_1(sK2)) != iProver_top ),
% 0.38/1.04      inference(predicate_to_equality,[status(thm)],[c_371]) ).
% 0.38/1.04  
% 0.38/1.04  cnf(c_1072,plain,
% 0.38/1.04      ( k10_relat_1(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = o_0_0_xboole_0
% 0.38/1.04      | k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_setfam_1(k6_enumset1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k2_relat_1(sK2)))) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
% 0.38/1.04      inference(superposition,[status(thm)],[c_735,c_737]) ).
% 0.38/1.04  
% 0.38/1.04  cnf(c_5,plain,
% 0.38/1.04      ( r2_hidden(X0,X1)
% 0.38/1.04      | r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
% 0.38/1.04      inference(cnf_transformation,[],[f74]) ).
% 0.38/1.04  
% 0.38/1.04  cnf(c_375,plain,
% 0.38/1.04      ( r2_hidden(X0_41,X1_41)
% 0.38/1.04      | r1_xboole_0(k6_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41),X1_41) ),
% 0.38/1.04      inference(subtyping,[status(esa)],[c_5]) ).
% 0.38/1.04  
% 0.38/1.04  cnf(c_834,plain,
% 0.38/1.04      ( r2_hidden(sK1,k2_relat_1(sK2))
% 0.38/1.04      | r1_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k2_relat_1(sK2)) ),
% 0.38/1.04      inference(instantiation,[status(thm)],[c_375]) ).
% 0.38/1.04  
% 0.38/1.04  cnf(c_0,plain,
% 0.38/1.04      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 0.38/1.04      inference(cnf_transformation,[],[f38]) ).
% 0.38/1.04  
% 0.38/1.04  cnf(c_380,plain,
% 0.38/1.04      ( ~ r1_xboole_0(X0_41,X1_41) | r1_xboole_0(X1_41,X0_41) ),
% 0.38/1.04      inference(subtyping,[status(esa)],[c_0]) ).
% 0.38/1.04  
% 0.38/1.04  cnf(c_849,plain,
% 0.38/1.04      ( ~ r1_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k2_relat_1(sK2))
% 0.38/1.04      | r1_xboole_0(k2_relat_1(sK2),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
% 0.38/1.04      inference(instantiation,[status(thm)],[c_380]) ).
% 0.38/1.04  
% 0.38/1.04  cnf(c_7,plain,
% 0.38/1.04      ( ~ r2_hidden(X0,X1)
% 0.38/1.04      | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 0.38/1.04      inference(cnf_transformation,[],[f76]) ).
% 0.38/1.04  
% 0.38/1.04  cnf(c_373,plain,
% 0.38/1.04      ( ~ r2_hidden(X0_41,X1_41)
% 0.38/1.04      | k5_xboole_0(k6_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41),k1_setfam_1(k6_enumset1(k6_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41),k6_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41),k6_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41),k6_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41),k6_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41),k6_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41),k6_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41),X1_41))) != k6_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41) ),
% 0.38/1.04      inference(subtyping,[status(esa)],[c_7]) ).
% 0.38/1.04  
% 0.38/1.04  cnf(c_857,plain,
% 0.38/1.04      ( ~ r2_hidden(sK1,k2_relat_1(sK2))
% 0.38/1.04      | k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_setfam_1(k6_enumset1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k2_relat_1(sK2)))) != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
% 0.38/1.04      inference(instantiation,[status(thm)],[c_373]) ).
% 0.38/1.04  
% 0.38/1.04  cnf(c_11,plain,
% 0.38/1.04      ( ~ r1_xboole_0(k2_relat_1(X0),X1)
% 0.38/1.04      | ~ v1_relat_1(X0)
% 0.38/1.04      | k10_relat_1(X0,X1) = o_0_0_xboole_0 ),
% 0.38/1.04      inference(cnf_transformation,[],[f79]) ).
% 0.38/1.04  
% 0.38/1.04  cnf(c_15,negated_conjecture,
% 0.38/1.04      ( v1_relat_1(sK2) ),
% 0.38/1.04      inference(cnf_transformation,[],[f61]) ).
% 0.38/1.04  
% 0.38/1.04  cnf(c_222,plain,
% 0.38/1.04      ( ~ r1_xboole_0(k2_relat_1(X0),X1)
% 0.38/1.04      | k10_relat_1(X0,X1) = o_0_0_xboole_0
% 0.38/1.04      | sK2 != X0 ),
% 0.38/1.04      inference(resolution_lifted,[status(thm)],[c_11,c_15]) ).
% 0.38/1.04  
% 0.38/1.04  cnf(c_223,plain,
% 0.38/1.04      ( ~ r1_xboole_0(k2_relat_1(sK2),X0)
% 0.38/1.04      | k10_relat_1(sK2,X0) = o_0_0_xboole_0 ),
% 0.38/1.04      inference(unflattening,[status(thm)],[c_222]) ).
% 0.38/1.04  
% 0.38/1.04  cnf(c_293,plain,
% 0.38/1.04      ( ~ r1_xboole_0(k2_relat_1(sK2),X0)
% 0.38/1.04      | k10_relat_1(sK2,X0) = o_0_0_xboole_0 ),
% 0.38/1.04      inference(prop_impl,[status(thm)],[c_223]) ).
% 0.38/1.04  
% 0.38/1.04  cnf(c_367,plain,
% 0.38/1.04      ( ~ r1_xboole_0(k2_relat_1(sK2),X0_41)
% 0.38/1.04      | k10_relat_1(sK2,X0_41) = o_0_0_xboole_0 ),
% 0.38/1.04      inference(subtyping,[status(esa)],[c_293]) ).
% 0.38/1.04  
% 0.38/1.04  cnf(c_916,plain,
% 0.38/1.04      ( ~ r1_xboole_0(k2_relat_1(sK2),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
% 0.38/1.04      | k10_relat_1(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = o_0_0_xboole_0 ),
% 0.38/1.04      inference(instantiation,[status(thm)],[c_367]) ).
% 0.38/1.04  
% 0.38/1.04  cnf(c_1085,plain,
% 0.38/1.04      ( k10_relat_1(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = o_0_0_xboole_0 ),
% 0.38/1.04      inference(global_propositional_subsumption,
% 0.38/1.04                [status(thm)],
% 0.38/1.04                [c_1072,c_834,c_849,c_857,c_916]) ).
% 0.38/1.04  
% 0.38/1.04  cnf(c_12,plain,
% 0.38/1.04      ( r1_xboole_0(k2_relat_1(X0),X1)
% 0.38/1.04      | ~ v1_relat_1(X0)
% 0.38/1.04      | k10_relat_1(X0,X1) != o_0_0_xboole_0 ),
% 0.38/1.04      inference(cnf_transformation,[],[f80]) ).
% 0.38/1.04  
% 0.38/1.04  cnf(c_210,plain,
% 0.38/1.04      ( r1_xboole_0(k2_relat_1(X0),X1)
% 0.38/1.04      | k10_relat_1(X0,X1) != o_0_0_xboole_0
% 0.38/1.04      | sK2 != X0 ),
% 0.38/1.04      inference(resolution_lifted,[status(thm)],[c_12,c_15]) ).
% 0.38/1.04  
% 0.38/1.04  cnf(c_211,plain,
% 0.38/1.04      ( r1_xboole_0(k2_relat_1(sK2),X0)
% 0.38/1.04      | k10_relat_1(sK2,X0) != o_0_0_xboole_0 ),
% 0.38/1.04      inference(unflattening,[status(thm)],[c_210]) ).
% 0.38/1.04  
% 0.38/1.04  cnf(c_291,plain,
% 0.38/1.04      ( r1_xboole_0(k2_relat_1(sK2),X0)
% 0.38/1.04      | k10_relat_1(sK2,X0) != o_0_0_xboole_0 ),
% 0.38/1.04      inference(prop_impl,[status(thm)],[c_211]) ).
% 0.38/1.04  
% 0.38/1.04  cnf(c_368,plain,
% 0.38/1.04      ( r1_xboole_0(k2_relat_1(sK2),X0_41)
% 0.38/1.04      | k10_relat_1(sK2,X0_41) != o_0_0_xboole_0 ),
% 0.38/1.04      inference(subtyping,[status(esa)],[c_291]) ).
% 0.38/1.04  
% 0.38/1.04  cnf(c_739,plain,
% 0.38/1.04      ( k10_relat_1(sK2,X0_41) != o_0_0_xboole_0
% 0.38/1.04      | r1_xboole_0(k2_relat_1(sK2),X0_41) = iProver_top ),
% 0.38/1.04      inference(predicate_to_equality,[status(thm)],[c_368]) ).
% 0.38/1.04  
% 0.38/1.04  cnf(c_1094,plain,
% 0.38/1.04      ( r1_xboole_0(k2_relat_1(sK2),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = iProver_top ),
% 0.38/1.04      inference(superposition,[status(thm)],[c_1085,c_739]) ).
% 0.38/1.04  
% 0.38/1.04  cnf(c_730,plain,
% 0.38/1.04      ( r1_xboole_0(X0_41,X1_41) != iProver_top
% 0.38/1.04      | r1_xboole_0(X1_41,X0_41) = iProver_top ),
% 0.38/1.04      inference(predicate_to_equality,[status(thm)],[c_380]) ).
% 0.38/1.04  
% 0.38/1.04  cnf(c_1125,plain,
% 0.38/1.04      ( r1_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k2_relat_1(sK2)) = iProver_top ),
% 0.38/1.04      inference(superposition,[status(thm)],[c_1094,c_730]) ).
% 0.38/1.04  
% 0.38/1.04  cnf(c_14,negated_conjecture,
% 0.38/1.04      ( r2_hidden(sK1,k2_relat_1(sK2))
% 0.38/1.04      | o_0_0_xboole_0 != k10_relat_1(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
% 0.38/1.04      inference(cnf_transformation,[],[f82]) ).
% 0.38/1.04  
% 0.38/1.04  cnf(c_370,negated_conjecture,
% 0.38/1.04      ( r2_hidden(sK1,k2_relat_1(sK2))
% 0.38/1.04      | o_0_0_xboole_0 != k10_relat_1(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
% 0.38/1.04      inference(subtyping,[status(esa)],[c_14]) ).
% 0.38/1.04  
% 0.38/1.04  cnf(c_738,plain,
% 0.38/1.04      ( o_0_0_xboole_0 != k10_relat_1(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
% 0.38/1.04      | r2_hidden(sK1,k2_relat_1(sK2)) = iProver_top ),
% 0.38/1.04      inference(predicate_to_equality,[status(thm)],[c_370]) ).
% 0.38/1.04  
% 0.38/1.04  cnf(c_1088,plain,
% 0.38/1.04      ( o_0_0_xboole_0 != o_0_0_xboole_0
% 0.38/1.04      | r2_hidden(sK1,k2_relat_1(sK2)) = iProver_top ),
% 0.38/1.04      inference(demodulation,[status(thm)],[c_1085,c_738]) ).
% 0.38/1.04  
% 0.38/1.04  cnf(c_1090,plain,
% 0.38/1.04      ( r2_hidden(sK1,k2_relat_1(sK2)) = iProver_top ),
% 0.38/1.04      inference(equality_resolution_simp,[status(thm)],[c_1088]) ).
% 0.38/1.04  
% 0.38/1.04  cnf(c_1,plain,
% 0.38/1.04      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 0.38/1.04      inference(cnf_transformation,[],[f41]) ).
% 0.38/1.04  
% 0.38/1.04  cnf(c_379,plain,
% 0.38/1.04      ( ~ r2_hidden(X0_41,X1_41)
% 0.38/1.04      | ~ r2_hidden(X0_41,X2_41)
% 0.38/1.04      | ~ r1_xboole_0(X2_41,X1_41) ),
% 0.38/1.04      inference(subtyping,[status(esa)],[c_1]) ).
% 0.38/1.04  
% 0.38/1.04  cnf(c_731,plain,
% 0.38/1.04      ( r2_hidden(X0_41,X1_41) != iProver_top
% 0.38/1.04      | r2_hidden(X0_41,X2_41) != iProver_top
% 0.38/1.04      | r1_xboole_0(X2_41,X1_41) != iProver_top ),
% 0.38/1.04      inference(predicate_to_equality,[status(thm)],[c_379]) ).
% 0.38/1.04  
% 0.38/1.04  cnf(c_1118,plain,
% 0.38/1.04      ( r2_hidden(sK1,X0_41) != iProver_top
% 0.38/1.04      | r1_xboole_0(X0_41,k2_relat_1(sK2)) != iProver_top ),
% 0.38/1.04      inference(superposition,[status(thm)],[c_1090,c_731]) ).
% 0.38/1.04  
% 0.38/1.04  cnf(c_1170,plain,
% 0.38/1.04      ( r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) != iProver_top ),
% 0.38/1.04      inference(superposition,[status(thm)],[c_1125,c_1118]) ).
% 0.38/1.04  
% 0.38/1.04  cnf(c_1256,plain,
% 0.38/1.04      ( k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_setfam_1(k6_enumset1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
% 0.38/1.04      inference(superposition,[status(thm)],[c_735,c_1170]) ).
% 0.38/1.04  
% 0.38/1.04  cnf(c_8,plain,
% 0.38/1.04      ( k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 0.38/1.04      inference(cnf_transformation,[],[f77]) ).
% 0.38/1.04  
% 0.38/1.04  cnf(c_372,plain,
% 0.38/1.04      ( k1_setfam_1(k6_enumset1(k6_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41),k6_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41),k6_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41),k6_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41),k6_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41),k6_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41),k6_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41),k6_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X1_41))) = k6_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41,X0_41) ),
% 0.38/1.04      inference(subtyping,[status(esa)],[c_8]) ).
% 0.38/1.04  
% 0.38/1.04  cnf(c_4,plain,
% 0.38/1.04      ( k5_xboole_0(X0,X0) = o_0_0_xboole_0 ),
% 0.38/1.04      inference(cnf_transformation,[],[f73]) ).
% 0.38/1.04  
% 0.38/1.04  cnf(c_376,plain,
% 0.38/1.04      ( k5_xboole_0(X0_41,X0_41) = o_0_0_xboole_0 ),
% 0.38/1.04      inference(subtyping,[status(esa)],[c_4]) ).
% 0.38/1.04  
% 0.38/1.04  cnf(c_1257,plain,
% 0.38/1.04      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = o_0_0_xboole_0 ),
% 0.38/1.04      inference(demodulation,[status(thm)],[c_1256,c_372,c_376]) ).
% 0.38/1.04  
% 0.38/1.04  cnf(c_9,plain,
% 0.38/1.04      ( v1_xboole_0(o_0_0_xboole_0) ),
% 0.38/1.04      inference(cnf_transformation,[],[f78]) ).
% 0.38/1.04  
% 0.38/1.04  cnf(c_10,plain,
% 0.38/1.04      ( ~ v1_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
% 0.38/1.04      inference(cnf_transformation,[],[f57]) ).
% 0.38/1.04  
% 0.38/1.04  cnf(c_204,plain,
% 0.38/1.04      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != o_0_0_xboole_0 ),
% 0.38/1.04      inference(resolution_lifted,[status(thm)],[c_9,c_10]) ).
% 0.38/1.04  
% 0.38/1.04  cnf(c_369,plain,
% 0.38/1.04      ( k6_enumset1(X0_41,X1_41,X2_41,X3_41,X4_41,X5_41,X6_41,X7_41) != o_0_0_xboole_0 ),
% 0.38/1.04      inference(subtyping,[status(esa)],[c_204]) ).
% 0.38/1.04  
% 0.38/1.04  cnf(c_413,plain,
% 0.38/1.04      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != o_0_0_xboole_0 ),
% 0.38/1.04      inference(instantiation,[status(thm)],[c_369]) ).
% 0.38/1.04  
% 0.38/1.04  cnf(contradiction,plain,
% 0.38/1.04      ( $false ),
% 0.38/1.04      inference(minisat,[status(thm)],[c_1257,c_413]) ).
% 0.38/1.04  
% 0.38/1.04  
% 0.38/1.04  % SZS output end CNFRefutation for theBenchmark.p
% 0.38/1.04  
% 0.38/1.04  ------                               Statistics
% 0.38/1.04  
% 0.38/1.04  ------ General
% 0.38/1.04  
% 0.38/1.04  abstr_ref_over_cycles:                  0
% 0.38/1.04  abstr_ref_under_cycles:                 0
% 0.38/1.04  gc_basic_clause_elim:                   0
% 0.38/1.04  forced_gc_time:                         0
% 0.38/1.04  parsing_time:                           0.009
% 0.38/1.04  unif_index_cands_time:                  0.
% 0.38/1.04  unif_index_add_time:                    0.
% 0.38/1.04  orderings_time:                         0.
% 0.38/1.04  out_proof_time:                         0.015
% 0.38/1.04  total_time:                             0.08
% 0.38/1.04  num_of_symbols:                         46
% 0.38/1.04  num_of_terms:                           914
% 0.38/1.04  
% 0.38/1.04  ------ Preprocessing
% 0.38/1.04  
% 0.38/1.04  num_of_splits:                          0
% 0.38/1.04  num_of_split_atoms:                     0
% 0.38/1.04  num_of_reused_defs:                     0
% 0.38/1.04  num_eq_ax_congr_red:                    11
% 0.38/1.04  num_of_sem_filtered_clauses:            1
% 0.38/1.04  num_of_subtypes:                        2
% 0.38/1.04  monotx_restored_types:                  0
% 0.38/1.04  sat_num_of_epr_types:                   0
% 0.38/1.04  sat_num_of_non_cyclic_types:            0
% 0.38/1.04  sat_guarded_non_collapsed_types:        0
% 0.38/1.04  num_pure_diseq_elim:                    0
% 0.38/1.04  simp_replaced_by:                       0
% 0.38/1.04  res_preprocessed:                       75
% 0.38/1.04  prep_upred:                             0
% 0.38/1.04  prep_unflattend:                        2
% 0.38/1.04  smt_new_axioms:                         0
% 0.38/1.04  pred_elim_cands:                        2
% 0.38/1.04  pred_elim:                              2
% 0.38/1.04  pred_elim_cl:                           2
% 0.38/1.04  pred_elim_cycles:                       4
% 0.38/1.04  merged_defs:                            22
% 0.38/1.04  merged_defs_ncl:                        0
% 0.38/1.04  bin_hyper_res:                          22
% 0.38/1.04  prep_cycles:                            4
% 0.38/1.04  pred_elim_time:                         0.001
% 0.38/1.04  splitting_time:                         0.
% 0.38/1.04  sem_filter_time:                        0.
% 0.38/1.04  monotx_time:                            0.
% 0.38/1.04  subtype_inf_time:                       0.001
% 0.38/1.04  
% 0.38/1.04  ------ Problem properties
% 0.38/1.04  
% 0.38/1.04  clauses:                                14
% 0.38/1.04  conjectures:                            2
% 0.38/1.04  epr:                                    2
% 0.38/1.04  horn:                                   10
% 0.38/1.04  ground:                                 2
% 0.38/1.04  unary:                                  3
% 0.38/1.04  binary:                                 10
% 0.38/1.04  lits:                                   26
% 0.38/1.04  lits_eq:                                9
% 0.38/1.04  fd_pure:                                0
% 0.38/1.04  fd_pseudo:                              0
% 0.38/1.04  fd_cond:                                0
% 0.38/1.04  fd_pseudo_cond:                         0
% 0.38/1.04  ac_symbols:                             0
% 0.38/1.04  
% 0.38/1.04  ------ Propositional Solver
% 0.38/1.04  
% 0.38/1.04  prop_solver_calls:                      27
% 0.38/1.04  prop_fast_solver_calls:                 364
% 0.38/1.04  smt_solver_calls:                       0
% 0.38/1.04  smt_fast_solver_calls:                  0
% 0.38/1.04  prop_num_of_clauses:                    323
% 0.38/1.04  prop_preprocess_simplified:             2175
% 0.38/1.04  prop_fo_subsumed:                       1
% 0.38/1.04  prop_solver_time:                       0.
% 0.38/1.04  smt_solver_time:                        0.
% 0.38/1.04  smt_fast_solver_time:                   0.
% 0.38/1.04  prop_fast_solver_time:                  0.
% 0.38/1.04  prop_unsat_core_time:                   0.
% 0.38/1.04  
% 0.38/1.04  ------ QBF
% 0.38/1.04  
% 0.38/1.04  qbf_q_res:                              0
% 0.38/1.04  qbf_num_tautologies:                    0
% 0.38/1.04  qbf_prep_cycles:                        0
% 0.38/1.04  
% 0.38/1.04  ------ BMC1
% 0.38/1.04  
% 0.38/1.04  bmc1_current_bound:                     -1
% 0.38/1.04  bmc1_last_solved_bound:                 -1
% 0.38/1.04  bmc1_unsat_core_size:                   -1
% 0.38/1.04  bmc1_unsat_core_parents_size:           -1
% 0.38/1.04  bmc1_merge_next_fun:                    0
% 0.38/1.04  bmc1_unsat_core_clauses_time:           0.
% 0.38/1.04  
% 0.38/1.04  ------ Instantiation
% 0.38/1.04  
% 0.38/1.04  inst_num_of_clauses:                    103
% 0.38/1.04  inst_num_in_passive:                    36
% 0.38/1.04  inst_num_in_active:                     59
% 0.38/1.04  inst_num_in_unprocessed:                8
% 0.38/1.04  inst_num_of_loops:                      100
% 0.38/1.04  inst_num_of_learning_restarts:          0
% 0.38/1.04  inst_num_moves_active_passive:          38
% 0.38/1.04  inst_lit_activity:                      0
% 0.38/1.04  inst_lit_activity_moves:                0
% 0.38/1.04  inst_num_tautologies:                   0
% 0.38/1.04  inst_num_prop_implied:                  0
% 0.38/1.04  inst_num_existing_simplified:           0
% 0.38/1.04  inst_num_eq_res_simplified:             0
% 0.38/1.04  inst_num_child_elim:                    0
% 0.38/1.04  inst_num_of_dismatching_blockings:      6
% 0.38/1.04  inst_num_of_non_proper_insts:           104
% 0.38/1.04  inst_num_of_duplicates:                 0
% 0.38/1.04  inst_inst_num_from_inst_to_res:         0
% 0.38/1.04  inst_dismatching_checking_time:         0.
% 0.38/1.04  
% 0.38/1.04  ------ Resolution
% 0.38/1.04  
% 0.38/1.04  res_num_of_clauses:                     0
% 0.38/1.04  res_num_in_passive:                     0
% 0.38/1.04  res_num_in_active:                      0
% 0.38/1.04  res_num_of_loops:                       79
% 0.38/1.04  res_forward_subset_subsumed:            8
% 0.38/1.04  res_backward_subset_subsumed:           0
% 0.38/1.04  res_forward_subsumed:                   0
% 0.38/1.04  res_backward_subsumed:                  0
% 0.38/1.04  res_forward_subsumption_resolution:     0
% 0.38/1.04  res_backward_subsumption_resolution:    0
% 0.38/1.04  res_clause_to_clause_subsumption:       31
% 0.38/1.04  res_orphan_elimination:                 0
% 0.38/1.04  res_tautology_del:                      59
% 0.38/1.04  res_num_eq_res_simplified:              0
% 0.38/1.04  res_num_sel_changes:                    0
% 0.38/1.04  res_moves_from_active_to_pass:          0
% 0.38/1.04  
% 0.38/1.04  ------ Superposition
% 0.38/1.04  
% 0.38/1.04  sup_time_total:                         0.
% 0.38/1.04  sup_time_generating:                    0.
% 0.38/1.04  sup_time_sim_full:                      0.
% 0.38/1.04  sup_time_sim_immed:                     0.
% 0.38/1.04  
% 0.38/1.04  sup_num_of_clauses:                     24
% 0.38/1.04  sup_num_in_active:                      17
% 0.38/1.04  sup_num_in_passive:                     7
% 0.38/1.04  sup_num_of_loops:                       18
% 0.38/1.04  sup_fw_superposition:                   2
% 0.38/1.04  sup_bw_superposition:                   11
% 0.38/1.04  sup_immediate_simplified:               1
% 0.38/1.04  sup_given_eliminated:                   0
% 0.38/1.04  comparisons_done:                       0
% 0.38/1.04  comparisons_avoided:                    0
% 0.38/1.04  
% 0.38/1.04  ------ Simplifications
% 0.38/1.04  
% 0.38/1.04  
% 0.38/1.04  sim_fw_subset_subsumed:                 0
% 0.38/1.04  sim_bw_subset_subsumed:                 0
% 0.38/1.04  sim_fw_subsumed:                        0
% 0.38/1.04  sim_bw_subsumed:                        0
% 0.38/1.04  sim_fw_subsumption_res:                 0
% 0.38/1.04  sim_bw_subsumption_res:                 0
% 0.38/1.04  sim_tautology_del:                      0
% 0.38/1.04  sim_eq_tautology_del:                   1
% 0.38/1.04  sim_eq_res_simp:                        1
% 0.38/1.04  sim_fw_demodulated:                     1
% 0.38/1.04  sim_bw_demodulated:                     2
% 0.38/1.04  sim_light_normalised:                   0
% 0.38/1.04  sim_joinable_taut:                      0
% 0.38/1.04  sim_joinable_simp:                      0
% 0.38/1.04  sim_ac_normalised:                      0
% 0.38/1.04  sim_smt_subsumption:                    0
% 0.38/1.04  
%------------------------------------------------------------------------------
