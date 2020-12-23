%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:47:33 EST 2020

% Result     : Theorem 51.06s
% Output     : CNFRefutation 51.06s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 288 expanded)
%              Number of clauses        :   84 ( 109 expanded)
%              Number of leaves         :   21 (  64 expanded)
%              Depth                    :   17
%              Number of atoms          :  416 ( 968 expanded)
%              Number of equality atoms :  137 ( 319 expanded)
%              Maximal formula depth    :   11 (   4 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
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

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f27])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k2_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k10_relat_1(X1,X0)
        <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <~> r1_xboole_0(k2_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f38,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f39,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f40,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 != k10_relat_1(X1,X0) )
        & ( r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 = k10_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k2_relat_1(sK4),sK3)
        | k1_xboole_0 != k10_relat_1(sK4,sK3) )
      & ( r1_xboole_0(k2_relat_1(sK4),sK3)
        | k1_xboole_0 = k10_relat_1(sK4,sK3) )
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ( ~ r1_xboole_0(k2_relat_1(sK4),sK3)
      | k1_xboole_0 != k10_relat_1(sK4,sK3) )
    & ( r1_xboole_0(k2_relat_1(sK4),sK3)
      | k1_xboole_0 = k10_relat_1(sK4,sK3) )
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f39,f40])).

fof(f65,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

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
    inference(nnf_transformation,[],[f22])).

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
     => ( r2_hidden(sK2(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK2(X0,X1,X2)),X2)
        & r2_hidden(sK2(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f35,f36])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X0,X3),X2)
      | ~ r2_hidden(X3,k2_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
        & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f66,plain,
    ( r1_xboole_0(k2_relat_1(sK4),sK3)
    | k1_xboole_0 = k10_relat_1(sK4,sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f68,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f46,f48])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f6,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k4_xboole_0(k2_relat_1(X1),k4_xboole_0(k2_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f62,f48])).

fof(f67,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK4),sK3)
    | k1_xboole_0 != k10_relat_1(sK4,sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f57,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_705,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_277096,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k10_relat_1(sK4,sK3),k10_relat_1(sK4,sK3))
    | k10_relat_1(sK4,sK3) != X0
    | k10_relat_1(sK4,sK3) != X1 ),
    inference(instantiation,[status(thm)],[c_705])).

cnf(c_277098,plain,
    ( r1_xboole_0(k10_relat_1(sK4,sK3),k10_relat_1(sK4,sK3))
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | k10_relat_1(sK4,sK3) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_277096])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_177997,plain,
    ( ~ r2_hidden(sK1(sK0(k2_relat_1(sK4),sK3),k1_relat_1(sK4),sK4),X0)
    | ~ r2_hidden(sK1(sK0(k2_relat_1(sK4),sK3),k1_relat_1(sK4),sK4),k10_relat_1(sK4,sK3))
    | ~ r1_xboole_0(k10_relat_1(sK4,sK3),X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_211468,plain,
    ( ~ r2_hidden(sK1(sK0(k2_relat_1(sK4),sK3),k1_relat_1(sK4),sK4),k10_relat_1(sK4,sK3))
    | ~ r1_xboole_0(k10_relat_1(sK4,sK3),k10_relat_1(sK4,sK3)) ),
    inference(instantiation,[status(thm)],[c_177997])).

cnf(c_20,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_24,negated_conjecture,
    ( v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_372,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_24])).

cnf(c_373,plain,
    ( r2_hidden(X0,k2_relat_1(sK4))
    | ~ r2_hidden(k4_tarski(X1,X0),sK4) ),
    inference(unflattening,[status(thm)],[c_372])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(X0,k2_relat_1(X3))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_320,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(X0,k2_relat_1(X3))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | sK4 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_24])).

cnf(c_321,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(sK4,X1))
    | ~ r2_hidden(X0,k2_relat_1(sK4))
    | ~ r2_hidden(k4_tarski(X2,X0),sK4) ),
    inference(unflattening,[status(thm)],[c_320])).

cnf(c_382,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(sK4,X1))
    | ~ r2_hidden(k4_tarski(X2,X0),sK4) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_373,c_321])).

cnf(c_159334,plain,
    ( r2_hidden(X0,k10_relat_1(sK4,sK3))
    | ~ r2_hidden(k4_tarski(X0,sK0(k2_relat_1(sK4),sK3)),sK4)
    | ~ r2_hidden(sK0(k2_relat_1(sK4),sK3),sK3) ),
    inference(instantiation,[status(thm)],[c_382])).

cnf(c_168216,plain,
    ( r2_hidden(sK1(sK0(k2_relat_1(sK4),sK3),k1_relat_1(sK4),sK4),k10_relat_1(sK4,sK3))
    | ~ r2_hidden(k4_tarski(sK1(sK0(k2_relat_1(sK4),sK3),k1_relat_1(sK4),sK4),sK0(k2_relat_1(sK4),sK3)),sK4)
    | ~ r2_hidden(sK0(k2_relat_1(sK4),sK3),sK3) ),
    inference(instantiation,[status(thm)],[c_159334])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_436,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_24])).

cnf(c_437,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK4,X1))
    | r2_hidden(k4_tarski(sK1(X0,X1,sK4),X0),sK4) ),
    inference(unflattening,[status(thm)],[c_436])).

cnf(c_167711,plain,
    ( r2_hidden(k4_tarski(sK1(sK0(k2_relat_1(sK4),sK3),k1_relat_1(sK4),sK4),sK0(k2_relat_1(sK4),sK3)),sK4)
    | ~ r2_hidden(sK0(k2_relat_1(sK4),sK3),k9_relat_1(sK4,k1_relat_1(sK4))) ),
    inference(instantiation,[status(thm)],[c_437])).

cnf(c_706,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_4367,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK0(k2_relat_1(sK4),sK3),k2_relat_1(sK4))
    | X0 != sK0(k2_relat_1(sK4),sK3)
    | X1 != k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_706])).

cnf(c_26091,plain,
    ( r2_hidden(sK0(k2_relat_1(sK4),sK3),X0)
    | ~ r2_hidden(sK0(k2_relat_1(sK4),sK3),k2_relat_1(sK4))
    | X0 != k2_relat_1(sK4)
    | sK0(k2_relat_1(sK4),sK3) != sK0(k2_relat_1(sK4),sK3) ),
    inference(instantiation,[status(thm)],[c_4367])).

cnf(c_62512,plain,
    ( r2_hidden(sK0(k2_relat_1(sK4),sK3),k9_relat_1(sK4,k1_relat_1(sK4)))
    | ~ r2_hidden(sK0(k2_relat_1(sK4),sK3),k2_relat_1(sK4))
    | k9_relat_1(sK4,k1_relat_1(sK4)) != k2_relat_1(sK4)
    | sK0(k2_relat_1(sK4),sK3) != sK0(k2_relat_1(sK4),sK3) ),
    inference(instantiation,[status(thm)],[c_26091])).

cnf(c_704,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_703,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3006,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_704,c_703])).

cnf(c_23,negated_conjecture,
    ( r1_xboole_0(k2_relat_1(sK4),sK3)
    | k1_xboole_0 = k10_relat_1(sK4,sK3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_5631,plain,
    ( r1_xboole_0(k2_relat_1(sK4),sK3)
    | k10_relat_1(sK4,sK3) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3006,c_23])).

cnf(c_5841,plain,
    ( r1_xboole_0(k2_relat_1(sK4),sK3)
    | X0 != k1_xboole_0
    | k10_relat_1(sK4,sK3) = X0 ),
    inference(resolution,[status(thm)],[c_5631,c_704])).

cnf(c_4,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1708,plain,
    ( k4_xboole_0(k10_relat_1(sK4,sK3),k4_xboole_0(k10_relat_1(sK4,sK3),k1_xboole_0)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1569,plain,
    ( X0 != X1
    | X0 = k4_xboole_0(k10_relat_1(sK4,sK3),X2)
    | k4_xboole_0(k10_relat_1(sK4,sK3),X2) != X1 ),
    inference(instantiation,[status(thm)],[c_704])).

cnf(c_2177,plain,
    ( X0 = k4_xboole_0(k10_relat_1(sK4,sK3),k4_xboole_0(k10_relat_1(sK4,sK3),k1_xboole_0))
    | X0 != k1_xboole_0
    | k4_xboole_0(k10_relat_1(sK4,sK3),k4_xboole_0(k10_relat_1(sK4,sK3),k1_xboole_0)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1569])).

cnf(c_1390,plain,
    ( X0 != X1
    | k10_relat_1(sK4,sK3) != X1
    | k10_relat_1(sK4,sK3) = X0 ),
    inference(instantiation,[status(thm)],[c_704])).

cnf(c_1486,plain,
    ( X0 != k4_xboole_0(k10_relat_1(sK4,sK3),X1)
    | k10_relat_1(sK4,sK3) = X0
    | k10_relat_1(sK4,sK3) != k4_xboole_0(k10_relat_1(sK4,sK3),X1) ),
    inference(instantiation,[status(thm)],[c_1390])).

cnf(c_3720,plain,
    ( X0 != k4_xboole_0(k10_relat_1(sK4,sK3),k4_xboole_0(k10_relat_1(sK4,sK3),k1_xboole_0))
    | k10_relat_1(sK4,sK3) = X0
    | k10_relat_1(sK4,sK3) != k4_xboole_0(k10_relat_1(sK4,sK3),k4_xboole_0(k10_relat_1(sK4,sK3),k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_1486])).

cnf(c_4512,plain,
    ( k10_relat_1(sK4,sK3) != X0
    | k10_relat_1(sK4,sK3) = k4_xboole_0(k10_relat_1(sK4,sK3),k4_xboole_0(k10_relat_1(sK4,sK3),k1_xboole_0))
    | k4_xboole_0(k10_relat_1(sK4,sK3),k4_xboole_0(k10_relat_1(sK4,sK3),k1_xboole_0)) != X0 ),
    inference(instantiation,[status(thm)],[c_1390])).

cnf(c_4513,plain,
    ( k10_relat_1(sK4,sK3) = k4_xboole_0(k10_relat_1(sK4,sK3),k4_xboole_0(k10_relat_1(sK4,sK3),k1_xboole_0))
    | k10_relat_1(sK4,sK3) != k1_xboole_0
    | k4_xboole_0(k10_relat_1(sK4,sK3),k4_xboole_0(k10_relat_1(sK4,sK3),k1_xboole_0)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4512])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1235,plain,
    ( r2_hidden(sK0(X0,X1),X1) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK2(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_412,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK2(X0,X2,X1),X2)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_24])).

cnf(c_413,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK4,X1))
    | r2_hidden(sK2(X0,X1,sK4),X1) ),
    inference(unflattening,[status(thm)],[c_412])).

cnf(c_1221,plain,
    ( r2_hidden(X0,k10_relat_1(sK4,X1)) != iProver_top
    | r2_hidden(sK2(X0,X1,sK4),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_413])).

cnf(c_6,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1233,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1230,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_xboole_0(k1_tarski(X0),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1858,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1233,c_1230])).

cnf(c_2195,plain,
    ( r2_hidden(X0,k10_relat_1(sK4,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1221,c_1858])).

cnf(c_5816,plain,
    ( r1_xboole_0(X0,k10_relat_1(sK4,k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1235,c_2195])).

cnf(c_8,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1231,plain,
    ( k4_xboole_0(X0,X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_7391,plain,
    ( k4_xboole_0(X0,k10_relat_1(sK4,k1_xboole_0)) = X0 ),
    inference(superposition,[status(thm)],[c_5816,c_1231])).

cnf(c_5,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1316,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5,c_4])).

cnf(c_7713,plain,
    ( k10_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7391,c_1316])).

cnf(c_19,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k4_xboole_0(k2_relat_1(X0),k4_xboole_0(k2_relat_1(X0),X1))) = k10_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_460,plain,
    ( k10_relat_1(X0,k4_xboole_0(k2_relat_1(X0),k4_xboole_0(k2_relat_1(X0),X1))) = k10_relat_1(X0,X1)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_24])).

cnf(c_461,plain,
    ( k10_relat_1(sK4,k4_xboole_0(k2_relat_1(sK4),k4_xboole_0(k2_relat_1(sK4),X0))) = k10_relat_1(sK4,X0) ),
    inference(unflattening,[status(thm)],[c_460])).

cnf(c_1294,plain,
    ( k10_relat_1(sK4,k4_xboole_0(k2_relat_1(sK4),k2_relat_1(sK4))) = k10_relat_1(sK4,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_5,c_461])).

cnf(c_1228,plain,
    ( k1_xboole_0 = k10_relat_1(sK4,sK3)
    | r1_xboole_0(k2_relat_1(sK4),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1410,plain,
    ( k10_relat_1(sK4,sK3) = k1_xboole_0
    | k4_xboole_0(k2_relat_1(sK4),sK3) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1228,c_1231])).

cnf(c_3153,plain,
    ( k10_relat_1(sK4,k4_xboole_0(k2_relat_1(sK4),k2_relat_1(sK4))) = k10_relat_1(sK4,sK3)
    | k10_relat_1(sK4,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1410,c_461])).

cnf(c_6532,plain,
    ( k10_relat_1(sK4,sK3) = k1_xboole_0
    | k10_relat_1(sK4,k1_xboole_0) = k10_relat_1(sK4,sK3) ),
    inference(superposition,[status(thm)],[c_1294,c_3153])).

cnf(c_22,negated_conjecture,
    ( ~ r1_xboole_0(k2_relat_1(sK4),sK3)
    | k1_xboole_0 != k10_relat_1(sK4,sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1229,plain,
    ( k1_xboole_0 != k10_relat_1(sK4,sK3)
    | r1_xboole_0(k2_relat_1(sK4),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_11936,plain,
    ( k10_relat_1(sK4,sK3) = k1_xboole_0
    | k10_relat_1(sK4,k1_xboole_0) != k1_xboole_0
    | r1_xboole_0(k2_relat_1(sK4),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6532,c_1229])).

cnf(c_11940,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK4),sK3)
    | k10_relat_1(sK4,sK3) = k1_xboole_0
    | k10_relat_1(sK4,k1_xboole_0) != k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_11936])).

cnf(c_16175,plain,
    ( X0 != k1_xboole_0
    | k10_relat_1(sK4,sK3) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5841,c_1708,c_2177,c_3720,c_4513,c_7713,c_11940])).

cnf(c_16177,plain,
    ( k10_relat_1(sK4,sK3) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_16175])).

cnf(c_12340,plain,
    ( sK0(k2_relat_1(sK4),sK3) = sK0(k2_relat_1(sK4),sK3) ),
    inference(instantiation,[status(thm)],[c_703])).

cnf(c_1366,plain,
    ( k10_relat_1(sK4,sK3) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k10_relat_1(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_704])).

cnf(c_1367,plain,
    ( k10_relat_1(sK4,sK3) != k1_xboole_0
    | k1_xboole_0 = k10_relat_1(sK4,sK3)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1366])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1339,plain,
    ( r2_hidden(sK0(k2_relat_1(sK4),sK3),k2_relat_1(sK4))
    | r1_xboole_0(k2_relat_1(sK4),sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1336,plain,
    ( r2_hidden(sK0(k2_relat_1(sK4),sK3),sK3)
    | r1_xboole_0(k2_relat_1(sK4),sK3) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_726,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_703])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_466,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_24])).

cnf(c_467,plain,
    ( k9_relat_1(sK4,k1_relat_1(sK4)) = k2_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_466])).

cnf(c_74,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_277098,c_211468,c_168216,c_167711,c_62512,c_16177,c_12340,c_1367,c_1339,c_1336,c_726,c_467,c_74,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:56:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 51.06/7.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 51.06/7.00  
% 51.06/7.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 51.06/7.00  
% 51.06/7.00  ------  iProver source info
% 51.06/7.00  
% 51.06/7.00  git: date: 2020-06-30 10:37:57 +0100
% 51.06/7.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 51.06/7.00  git: non_committed_changes: false
% 51.06/7.00  git: last_make_outside_of_git: false
% 51.06/7.00  
% 51.06/7.00  ------ 
% 51.06/7.00  ------ Parsing...
% 51.06/7.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 51.06/7.00  
% 51.06/7.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 51.06/7.00  
% 51.06/7.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 51.06/7.00  
% 51.06/7.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 51.06/7.00  ------ Proving...
% 51.06/7.00  ------ Problem Properties 
% 51.06/7.00  
% 51.06/7.00  
% 51.06/7.00  clauses                                 24
% 51.06/7.00  conjectures                             2
% 51.06/7.00  EPR                                     3
% 51.06/7.00  Horn                                    21
% 51.06/7.00  unary                                   5
% 51.06/7.00  binary                                  16
% 51.06/7.00  lits                                    46
% 51.06/7.00  lits eq                                 8
% 51.06/7.00  fd_pure                                 0
% 51.06/7.00  fd_pseudo                               0
% 51.06/7.00  fd_cond                                 0
% 51.06/7.00  fd_pseudo_cond                          0
% 51.06/7.00  AC symbols                              0
% 51.06/7.00  
% 51.06/7.00  ------ Input Options Time Limit: Unbounded
% 51.06/7.00  
% 51.06/7.00  
% 51.06/7.00  ------ 
% 51.06/7.00  Current options:
% 51.06/7.00  ------ 
% 51.06/7.00  
% 51.06/7.00  
% 51.06/7.00  
% 51.06/7.00  
% 51.06/7.00  ------ Proving...
% 51.06/7.00  
% 51.06/7.00  
% 51.06/7.00  % SZS status Theorem for theBenchmark.p
% 51.06/7.00  
% 51.06/7.00  % SZS output start CNFRefutation for theBenchmark.p
% 51.06/7.00  
% 51.06/7.00  fof(f2,axiom,(
% 51.06/7.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 51.06/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.06/7.00  
% 51.06/7.00  fof(f16,plain,(
% 51.06/7.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 51.06/7.00    inference(rectify,[],[f2])).
% 51.06/7.00  
% 51.06/7.00  fof(f18,plain,(
% 51.06/7.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 51.06/7.00    inference(ennf_transformation,[],[f16])).
% 51.06/7.00  
% 51.06/7.00  fof(f27,plain,(
% 51.06/7.00    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 51.06/7.00    introduced(choice_axiom,[])).
% 51.06/7.00  
% 51.06/7.00  fof(f28,plain,(
% 51.06/7.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 51.06/7.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f27])).
% 51.06/7.00  
% 51.06/7.00  fof(f45,plain,(
% 51.06/7.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 51.06/7.00    inference(cnf_transformation,[],[f28])).
% 51.06/7.00  
% 51.06/7.00  fof(f13,axiom,(
% 51.06/7.00    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 51.06/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.06/7.00  
% 51.06/7.00  fof(f24,plain,(
% 51.06/7.00    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 51.06/7.00    inference(ennf_transformation,[],[f13])).
% 51.06/7.00  
% 51.06/7.00  fof(f25,plain,(
% 51.06/7.00    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 51.06/7.00    inference(flattening,[],[f24])).
% 51.06/7.00  
% 51.06/7.00  fof(f64,plain,(
% 51.06/7.00    ( ! [X2,X0,X1] : (r2_hidden(X1,k2_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 51.06/7.00    inference(cnf_transformation,[],[f25])).
% 51.06/7.00  
% 51.06/7.00  fof(f14,conjecture,(
% 51.06/7.00    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 51.06/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.06/7.00  
% 51.06/7.00  fof(f15,negated_conjecture,(
% 51.06/7.00    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 51.06/7.00    inference(negated_conjecture,[],[f14])).
% 51.06/7.00  
% 51.06/7.00  fof(f26,plain,(
% 51.06/7.00    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <~> r1_xboole_0(k2_relat_1(X1),X0)) & v1_relat_1(X1))),
% 51.06/7.00    inference(ennf_transformation,[],[f15])).
% 51.06/7.00  
% 51.06/7.00  fof(f38,plain,(
% 51.06/7.00    ? [X0,X1] : (((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0))) & v1_relat_1(X1))),
% 51.06/7.00    inference(nnf_transformation,[],[f26])).
% 51.06/7.00  
% 51.06/7.00  fof(f39,plain,(
% 51.06/7.00    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1))),
% 51.06/7.00    inference(flattening,[],[f38])).
% 51.06/7.00  
% 51.06/7.00  fof(f40,plain,(
% 51.06/7.00    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k2_relat_1(sK4),sK3) | k1_xboole_0 != k10_relat_1(sK4,sK3)) & (r1_xboole_0(k2_relat_1(sK4),sK3) | k1_xboole_0 = k10_relat_1(sK4,sK3)) & v1_relat_1(sK4))),
% 51.06/7.00    introduced(choice_axiom,[])).
% 51.06/7.00  
% 51.06/7.00  fof(f41,plain,(
% 51.06/7.00    (~r1_xboole_0(k2_relat_1(sK4),sK3) | k1_xboole_0 != k10_relat_1(sK4,sK3)) & (r1_xboole_0(k2_relat_1(sK4),sK3) | k1_xboole_0 = k10_relat_1(sK4,sK3)) & v1_relat_1(sK4)),
% 51.06/7.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f39,f40])).
% 51.06/7.00  
% 51.06/7.00  fof(f65,plain,(
% 51.06/7.00    v1_relat_1(sK4)),
% 51.06/7.00    inference(cnf_transformation,[],[f41])).
% 51.06/7.00  
% 51.06/7.00  fof(f11,axiom,(
% 51.06/7.00    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 51.06/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.06/7.00  
% 51.06/7.00  fof(f22,plain,(
% 51.06/7.00    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 51.06/7.00    inference(ennf_transformation,[],[f11])).
% 51.06/7.00  
% 51.06/7.00  fof(f34,plain,(
% 51.06/7.00    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 51.06/7.00    inference(nnf_transformation,[],[f22])).
% 51.06/7.00  
% 51.06/7.00  fof(f35,plain,(
% 51.06/7.00    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 51.06/7.00    inference(rectify,[],[f34])).
% 51.06/7.00  
% 51.06/7.00  fof(f36,plain,(
% 51.06/7.00    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK2(X0,X1,X2)),X2) & r2_hidden(sK2(X0,X1,X2),k2_relat_1(X2))))),
% 51.06/7.00    introduced(choice_axiom,[])).
% 51.06/7.00  
% 51.06/7.00  fof(f37,plain,(
% 51.06/7.00    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK2(X0,X1,X2)),X2) & r2_hidden(sK2(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 51.06/7.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f35,f36])).
% 51.06/7.00  
% 51.06/7.00  fof(f61,plain,(
% 51.06/7.00    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,k10_relat_1(X2,X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 51.06/7.00    inference(cnf_transformation,[],[f37])).
% 51.06/7.00  
% 51.06/7.00  fof(f9,axiom,(
% 51.06/7.00    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 51.06/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.06/7.00  
% 51.06/7.00  fof(f20,plain,(
% 51.06/7.00    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 51.06/7.00    inference(ennf_transformation,[],[f9])).
% 51.06/7.00  
% 51.06/7.00  fof(f30,plain,(
% 51.06/7.00    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 51.06/7.00    inference(nnf_transformation,[],[f20])).
% 51.06/7.00  
% 51.06/7.00  fof(f31,plain,(
% 51.06/7.00    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 51.06/7.00    inference(rectify,[],[f30])).
% 51.06/7.00  
% 51.06/7.00  fof(f32,plain,(
% 51.06/7.00    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))))),
% 51.06/7.00    introduced(choice_axiom,[])).
% 51.06/7.00  
% 51.06/7.00  fof(f33,plain,(
% 51.06/7.00    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 51.06/7.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).
% 51.06/7.00  
% 51.06/7.00  fof(f54,plain,(
% 51.06/7.00    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 51.06/7.00    inference(cnf_transformation,[],[f33])).
% 51.06/7.00  
% 51.06/7.00  fof(f66,plain,(
% 51.06/7.00    r1_xboole_0(k2_relat_1(sK4),sK3) | k1_xboole_0 = k10_relat_1(sK4,sK3)),
% 51.06/7.00    inference(cnf_transformation,[],[f41])).
% 51.06/7.00  
% 51.06/7.00  fof(f3,axiom,(
% 51.06/7.00    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 51.06/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.06/7.00  
% 51.06/7.00  fof(f46,plain,(
% 51.06/7.00    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 51.06/7.00    inference(cnf_transformation,[],[f3])).
% 51.06/7.00  
% 51.06/7.00  fof(f5,axiom,(
% 51.06/7.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 51.06/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.06/7.00  
% 51.06/7.00  fof(f48,plain,(
% 51.06/7.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 51.06/7.00    inference(cnf_transformation,[],[f5])).
% 51.06/7.00  
% 51.06/7.00  fof(f68,plain,(
% 51.06/7.00    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 51.06/7.00    inference(definition_unfolding,[],[f46,f48])).
% 51.06/7.00  
% 51.06/7.00  fof(f44,plain,(
% 51.06/7.00    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 51.06/7.00    inference(cnf_transformation,[],[f28])).
% 51.06/7.00  
% 51.06/7.00  fof(f60,plain,(
% 51.06/7.00    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 51.06/7.00    inference(cnf_transformation,[],[f37])).
% 51.06/7.00  
% 51.06/7.00  fof(f6,axiom,(
% 51.06/7.00    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 51.06/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.06/7.00  
% 51.06/7.00  fof(f49,plain,(
% 51.06/7.00    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 51.06/7.00    inference(cnf_transformation,[],[f6])).
% 51.06/7.00  
% 51.06/7.00  fof(f8,axiom,(
% 51.06/7.00    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 51.06/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.06/7.00  
% 51.06/7.00  fof(f19,plain,(
% 51.06/7.00    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 51.06/7.00    inference(ennf_transformation,[],[f8])).
% 51.06/7.00  
% 51.06/7.00  fof(f52,plain,(
% 51.06/7.00    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1)) )),
% 51.06/7.00    inference(cnf_transformation,[],[f19])).
% 51.06/7.00  
% 51.06/7.00  fof(f7,axiom,(
% 51.06/7.00    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 51.06/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.06/7.00  
% 51.06/7.00  fof(f29,plain,(
% 51.06/7.00    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 51.06/7.00    inference(nnf_transformation,[],[f7])).
% 51.06/7.00  
% 51.06/7.00  fof(f50,plain,(
% 51.06/7.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 51.06/7.00    inference(cnf_transformation,[],[f29])).
% 51.06/7.00  
% 51.06/7.00  fof(f4,axiom,(
% 51.06/7.00    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 51.06/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.06/7.00  
% 51.06/7.00  fof(f47,plain,(
% 51.06/7.00    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 51.06/7.00    inference(cnf_transformation,[],[f4])).
% 51.06/7.00  
% 51.06/7.00  fof(f12,axiom,(
% 51.06/7.00    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 51.06/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.06/7.00  
% 51.06/7.00  fof(f23,plain,(
% 51.06/7.00    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 51.06/7.00    inference(ennf_transformation,[],[f12])).
% 51.06/7.00  
% 51.06/7.00  fof(f62,plain,(
% 51.06/7.00    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 51.06/7.00    inference(cnf_transformation,[],[f23])).
% 51.06/7.00  
% 51.06/7.00  fof(f69,plain,(
% 51.06/7.00    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k4_xboole_0(k2_relat_1(X1),k4_xboole_0(k2_relat_1(X1),X0))) | ~v1_relat_1(X1)) )),
% 51.06/7.00    inference(definition_unfolding,[],[f62,f48])).
% 51.06/7.00  
% 51.06/7.00  fof(f67,plain,(
% 51.06/7.00    ~r1_xboole_0(k2_relat_1(sK4),sK3) | k1_xboole_0 != k10_relat_1(sK4,sK3)),
% 51.06/7.00    inference(cnf_transformation,[],[f41])).
% 51.06/7.00  
% 51.06/7.00  fof(f43,plain,(
% 51.06/7.00    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 51.06/7.00    inference(cnf_transformation,[],[f28])).
% 51.06/7.00  
% 51.06/7.00  fof(f10,axiom,(
% 51.06/7.00    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 51.06/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.06/7.00  
% 51.06/7.00  fof(f21,plain,(
% 51.06/7.00    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 51.06/7.00    inference(ennf_transformation,[],[f10])).
% 51.06/7.00  
% 51.06/7.00  fof(f57,plain,(
% 51.06/7.00    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 51.06/7.00    inference(cnf_transformation,[],[f21])).
% 51.06/7.00  
% 51.06/7.00  cnf(c_705,plain,
% 51.06/7.00      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 51.06/7.00      theory(equality) ).
% 51.06/7.00  
% 51.06/7.00  cnf(c_277096,plain,
% 51.06/7.00      ( ~ r1_xboole_0(X0,X1)
% 51.06/7.00      | r1_xboole_0(k10_relat_1(sK4,sK3),k10_relat_1(sK4,sK3))
% 51.06/7.00      | k10_relat_1(sK4,sK3) != X0
% 51.06/7.00      | k10_relat_1(sK4,sK3) != X1 ),
% 51.06/7.00      inference(instantiation,[status(thm)],[c_705]) ).
% 51.06/7.00  
% 51.06/7.00  cnf(c_277098,plain,
% 51.06/7.00      ( r1_xboole_0(k10_relat_1(sK4,sK3),k10_relat_1(sK4,sK3))
% 51.06/7.00      | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 51.06/7.00      | k10_relat_1(sK4,sK3) != k1_xboole_0 ),
% 51.06/7.00      inference(instantiation,[status(thm)],[c_277096]) ).
% 51.06/7.00  
% 51.06/7.00  cnf(c_1,plain,
% 51.06/7.00      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 51.06/7.00      inference(cnf_transformation,[],[f45]) ).
% 51.06/7.00  
% 51.06/7.00  cnf(c_177997,plain,
% 51.06/7.00      ( ~ r2_hidden(sK1(sK0(k2_relat_1(sK4),sK3),k1_relat_1(sK4),sK4),X0)
% 51.06/7.00      | ~ r2_hidden(sK1(sK0(k2_relat_1(sK4),sK3),k1_relat_1(sK4),sK4),k10_relat_1(sK4,sK3))
% 51.06/7.00      | ~ r1_xboole_0(k10_relat_1(sK4,sK3),X0) ),
% 51.06/7.00      inference(instantiation,[status(thm)],[c_1]) ).
% 51.06/7.00  
% 51.06/7.00  cnf(c_211468,plain,
% 51.06/7.00      ( ~ r2_hidden(sK1(sK0(k2_relat_1(sK4),sK3),k1_relat_1(sK4),sK4),k10_relat_1(sK4,sK3))
% 51.06/7.00      | ~ r1_xboole_0(k10_relat_1(sK4,sK3),k10_relat_1(sK4,sK3)) ),
% 51.06/7.00      inference(instantiation,[status(thm)],[c_177997]) ).
% 51.06/7.00  
% 51.06/7.00  cnf(c_20,plain,
% 51.06/7.00      ( r2_hidden(X0,k2_relat_1(X1))
% 51.06/7.00      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 51.06/7.00      | ~ v1_relat_1(X1) ),
% 51.06/7.00      inference(cnf_transformation,[],[f64]) ).
% 51.06/7.00  
% 51.06/7.00  cnf(c_24,negated_conjecture,
% 51.06/7.00      ( v1_relat_1(sK4) ),
% 51.06/7.00      inference(cnf_transformation,[],[f65]) ).
% 51.06/7.00  
% 51.06/7.00  cnf(c_372,plain,
% 51.06/7.00      ( r2_hidden(X0,k2_relat_1(X1))
% 51.06/7.00      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 51.06/7.00      | sK4 != X1 ),
% 51.06/7.00      inference(resolution_lifted,[status(thm)],[c_20,c_24]) ).
% 51.06/7.00  
% 51.06/7.00  cnf(c_373,plain,
% 51.06/7.00      ( r2_hidden(X0,k2_relat_1(sK4))
% 51.06/7.00      | ~ r2_hidden(k4_tarski(X1,X0),sK4) ),
% 51.06/7.00      inference(unflattening,[status(thm)],[c_372]) ).
% 51.06/7.00  
% 51.06/7.00  cnf(c_15,plain,
% 51.06/7.00      ( ~ r2_hidden(X0,X1)
% 51.06/7.00      | r2_hidden(X2,k10_relat_1(X3,X1))
% 51.06/7.00      | ~ r2_hidden(X0,k2_relat_1(X3))
% 51.06/7.00      | ~ r2_hidden(k4_tarski(X2,X0),X3)
% 51.06/7.00      | ~ v1_relat_1(X3) ),
% 51.06/7.00      inference(cnf_transformation,[],[f61]) ).
% 51.06/7.00  
% 51.06/7.00  cnf(c_320,plain,
% 51.06/7.00      ( ~ r2_hidden(X0,X1)
% 51.06/7.00      | r2_hidden(X2,k10_relat_1(X3,X1))
% 51.06/7.00      | ~ r2_hidden(X0,k2_relat_1(X3))
% 51.06/7.00      | ~ r2_hidden(k4_tarski(X2,X0),X3)
% 51.06/7.00      | sK4 != X3 ),
% 51.06/7.00      inference(resolution_lifted,[status(thm)],[c_15,c_24]) ).
% 51.06/7.00  
% 51.06/7.00  cnf(c_321,plain,
% 51.06/7.00      ( ~ r2_hidden(X0,X1)
% 51.06/7.00      | r2_hidden(X2,k10_relat_1(sK4,X1))
% 51.06/7.00      | ~ r2_hidden(X0,k2_relat_1(sK4))
% 51.06/7.00      | ~ r2_hidden(k4_tarski(X2,X0),sK4) ),
% 51.06/7.00      inference(unflattening,[status(thm)],[c_320]) ).
% 51.06/7.00  
% 51.06/7.00  cnf(c_382,plain,
% 51.06/7.00      ( ~ r2_hidden(X0,X1)
% 51.06/7.00      | r2_hidden(X2,k10_relat_1(sK4,X1))
% 51.06/7.00      | ~ r2_hidden(k4_tarski(X2,X0),sK4) ),
% 51.06/7.00      inference(backward_subsumption_resolution,
% 51.06/7.00                [status(thm)],
% 51.06/7.00                [c_373,c_321]) ).
% 51.06/7.00  
% 51.06/7.00  cnf(c_159334,plain,
% 51.06/7.00      ( r2_hidden(X0,k10_relat_1(sK4,sK3))
% 51.06/7.00      | ~ r2_hidden(k4_tarski(X0,sK0(k2_relat_1(sK4),sK3)),sK4)
% 51.06/7.00      | ~ r2_hidden(sK0(k2_relat_1(sK4),sK3),sK3) ),
% 51.06/7.00      inference(instantiation,[status(thm)],[c_382]) ).
% 51.06/7.00  
% 51.06/7.00  cnf(c_168216,plain,
% 51.06/7.00      ( r2_hidden(sK1(sK0(k2_relat_1(sK4),sK3),k1_relat_1(sK4),sK4),k10_relat_1(sK4,sK3))
% 51.06/7.00      | ~ r2_hidden(k4_tarski(sK1(sK0(k2_relat_1(sK4),sK3),k1_relat_1(sK4),sK4),sK0(k2_relat_1(sK4),sK3)),sK4)
% 51.06/7.00      | ~ r2_hidden(sK0(k2_relat_1(sK4),sK3),sK3) ),
% 51.06/7.00      inference(instantiation,[status(thm)],[c_159334]) ).
% 51.06/7.00  
% 51.06/7.00  cnf(c_12,plain,
% 51.06/7.00      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 51.06/7.00      | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
% 51.06/7.00      | ~ v1_relat_1(X1) ),
% 51.06/7.00      inference(cnf_transformation,[],[f54]) ).
% 51.06/7.00  
% 51.06/7.00  cnf(c_436,plain,
% 51.06/7.00      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 51.06/7.00      | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
% 51.06/7.00      | sK4 != X1 ),
% 51.06/7.00      inference(resolution_lifted,[status(thm)],[c_12,c_24]) ).
% 51.06/7.00  
% 51.06/7.00  cnf(c_437,plain,
% 51.06/7.00      ( ~ r2_hidden(X0,k9_relat_1(sK4,X1))
% 51.06/7.00      | r2_hidden(k4_tarski(sK1(X0,X1,sK4),X0),sK4) ),
% 51.06/7.00      inference(unflattening,[status(thm)],[c_436]) ).
% 51.06/7.00  
% 51.06/7.00  cnf(c_167711,plain,
% 51.06/7.00      ( r2_hidden(k4_tarski(sK1(sK0(k2_relat_1(sK4),sK3),k1_relat_1(sK4),sK4),sK0(k2_relat_1(sK4),sK3)),sK4)
% 51.06/7.00      | ~ r2_hidden(sK0(k2_relat_1(sK4),sK3),k9_relat_1(sK4,k1_relat_1(sK4))) ),
% 51.06/7.01      inference(instantiation,[status(thm)],[c_437]) ).
% 51.06/7.01  
% 51.06/7.01  cnf(c_706,plain,
% 51.06/7.01      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 51.06/7.01      theory(equality) ).
% 51.06/7.01  
% 51.06/7.01  cnf(c_4367,plain,
% 51.06/7.01      ( r2_hidden(X0,X1)
% 51.06/7.01      | ~ r2_hidden(sK0(k2_relat_1(sK4),sK3),k2_relat_1(sK4))
% 51.06/7.01      | X0 != sK0(k2_relat_1(sK4),sK3)
% 51.06/7.01      | X1 != k2_relat_1(sK4) ),
% 51.06/7.01      inference(instantiation,[status(thm)],[c_706]) ).
% 51.06/7.01  
% 51.06/7.01  cnf(c_26091,plain,
% 51.06/7.01      ( r2_hidden(sK0(k2_relat_1(sK4),sK3),X0)
% 51.06/7.01      | ~ r2_hidden(sK0(k2_relat_1(sK4),sK3),k2_relat_1(sK4))
% 51.06/7.01      | X0 != k2_relat_1(sK4)
% 51.06/7.01      | sK0(k2_relat_1(sK4),sK3) != sK0(k2_relat_1(sK4),sK3) ),
% 51.06/7.01      inference(instantiation,[status(thm)],[c_4367]) ).
% 51.06/7.01  
% 51.06/7.01  cnf(c_62512,plain,
% 51.06/7.01      ( r2_hidden(sK0(k2_relat_1(sK4),sK3),k9_relat_1(sK4,k1_relat_1(sK4)))
% 51.06/7.01      | ~ r2_hidden(sK0(k2_relat_1(sK4),sK3),k2_relat_1(sK4))
% 51.06/7.01      | k9_relat_1(sK4,k1_relat_1(sK4)) != k2_relat_1(sK4)
% 51.06/7.01      | sK0(k2_relat_1(sK4),sK3) != sK0(k2_relat_1(sK4),sK3) ),
% 51.06/7.01      inference(instantiation,[status(thm)],[c_26091]) ).
% 51.06/7.01  
% 51.06/7.01  cnf(c_704,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 51.06/7.01  
% 51.06/7.01  cnf(c_703,plain,( X0 = X0 ),theory(equality) ).
% 51.06/7.01  
% 51.06/7.01  cnf(c_3006,plain,
% 51.06/7.01      ( X0 != X1 | X1 = X0 ),
% 51.06/7.01      inference(resolution,[status(thm)],[c_704,c_703]) ).
% 51.06/7.01  
% 51.06/7.01  cnf(c_23,negated_conjecture,
% 51.06/7.01      ( r1_xboole_0(k2_relat_1(sK4),sK3)
% 51.06/7.01      | k1_xboole_0 = k10_relat_1(sK4,sK3) ),
% 51.06/7.01      inference(cnf_transformation,[],[f66]) ).
% 51.06/7.01  
% 51.06/7.01  cnf(c_5631,plain,
% 51.06/7.01      ( r1_xboole_0(k2_relat_1(sK4),sK3)
% 51.06/7.01      | k10_relat_1(sK4,sK3) = k1_xboole_0 ),
% 51.06/7.01      inference(resolution,[status(thm)],[c_3006,c_23]) ).
% 51.06/7.01  
% 51.06/7.01  cnf(c_5841,plain,
% 51.06/7.01      ( r1_xboole_0(k2_relat_1(sK4),sK3)
% 51.06/7.01      | X0 != k1_xboole_0
% 51.06/7.01      | k10_relat_1(sK4,sK3) = X0 ),
% 51.06/7.01      inference(resolution,[status(thm)],[c_5631,c_704]) ).
% 51.06/7.01  
% 51.06/7.01  cnf(c_4,plain,
% 51.06/7.01      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 51.06/7.01      inference(cnf_transformation,[],[f68]) ).
% 51.06/7.01  
% 51.06/7.01  cnf(c_1708,plain,
% 51.06/7.01      ( k4_xboole_0(k10_relat_1(sK4,sK3),k4_xboole_0(k10_relat_1(sK4,sK3),k1_xboole_0)) = k1_xboole_0 ),
% 51.06/7.01      inference(instantiation,[status(thm)],[c_4]) ).
% 51.06/7.01  
% 51.06/7.01  cnf(c_1569,plain,
% 51.06/7.01      ( X0 != X1
% 51.06/7.01      | X0 = k4_xboole_0(k10_relat_1(sK4,sK3),X2)
% 51.06/7.01      | k4_xboole_0(k10_relat_1(sK4,sK3),X2) != X1 ),
% 51.06/7.01      inference(instantiation,[status(thm)],[c_704]) ).
% 51.06/7.01  
% 51.06/7.01  cnf(c_2177,plain,
% 51.06/7.01      ( X0 = k4_xboole_0(k10_relat_1(sK4,sK3),k4_xboole_0(k10_relat_1(sK4,sK3),k1_xboole_0))
% 51.06/7.01      | X0 != k1_xboole_0
% 51.06/7.01      | k4_xboole_0(k10_relat_1(sK4,sK3),k4_xboole_0(k10_relat_1(sK4,sK3),k1_xboole_0)) != k1_xboole_0 ),
% 51.06/7.01      inference(instantiation,[status(thm)],[c_1569]) ).
% 51.06/7.01  
% 51.06/7.01  cnf(c_1390,plain,
% 51.06/7.01      ( X0 != X1
% 51.06/7.01      | k10_relat_1(sK4,sK3) != X1
% 51.06/7.01      | k10_relat_1(sK4,sK3) = X0 ),
% 51.06/7.01      inference(instantiation,[status(thm)],[c_704]) ).
% 51.06/7.01  
% 51.06/7.01  cnf(c_1486,plain,
% 51.06/7.01      ( X0 != k4_xboole_0(k10_relat_1(sK4,sK3),X1)
% 51.06/7.01      | k10_relat_1(sK4,sK3) = X0
% 51.06/7.01      | k10_relat_1(sK4,sK3) != k4_xboole_0(k10_relat_1(sK4,sK3),X1) ),
% 51.06/7.01      inference(instantiation,[status(thm)],[c_1390]) ).
% 51.06/7.01  
% 51.06/7.01  cnf(c_3720,plain,
% 51.06/7.01      ( X0 != k4_xboole_0(k10_relat_1(sK4,sK3),k4_xboole_0(k10_relat_1(sK4,sK3),k1_xboole_0))
% 51.06/7.01      | k10_relat_1(sK4,sK3) = X0
% 51.06/7.01      | k10_relat_1(sK4,sK3) != k4_xboole_0(k10_relat_1(sK4,sK3),k4_xboole_0(k10_relat_1(sK4,sK3),k1_xboole_0)) ),
% 51.06/7.01      inference(instantiation,[status(thm)],[c_1486]) ).
% 51.06/7.01  
% 51.06/7.01  cnf(c_4512,plain,
% 51.06/7.01      ( k10_relat_1(sK4,sK3) != X0
% 51.06/7.01      | k10_relat_1(sK4,sK3) = k4_xboole_0(k10_relat_1(sK4,sK3),k4_xboole_0(k10_relat_1(sK4,sK3),k1_xboole_0))
% 51.06/7.01      | k4_xboole_0(k10_relat_1(sK4,sK3),k4_xboole_0(k10_relat_1(sK4,sK3),k1_xboole_0)) != X0 ),
% 51.06/7.01      inference(instantiation,[status(thm)],[c_1390]) ).
% 51.06/7.01  
% 51.06/7.01  cnf(c_4513,plain,
% 51.06/7.01      ( k10_relat_1(sK4,sK3) = k4_xboole_0(k10_relat_1(sK4,sK3),k4_xboole_0(k10_relat_1(sK4,sK3),k1_xboole_0))
% 51.06/7.01      | k10_relat_1(sK4,sK3) != k1_xboole_0
% 51.06/7.01      | k4_xboole_0(k10_relat_1(sK4,sK3),k4_xboole_0(k10_relat_1(sK4,sK3),k1_xboole_0)) != k1_xboole_0 ),
% 51.06/7.01      inference(instantiation,[status(thm)],[c_4512]) ).
% 51.06/7.01  
% 51.06/7.01  cnf(c_2,plain,
% 51.06/7.01      ( r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1) ),
% 51.06/7.01      inference(cnf_transformation,[],[f44]) ).
% 51.06/7.01  
% 51.06/7.01  cnf(c_1235,plain,
% 51.06/7.01      ( r2_hidden(sK0(X0,X1),X1) = iProver_top
% 51.06/7.01      | r1_xboole_0(X0,X1) = iProver_top ),
% 51.06/7.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 51.06/7.01  
% 51.06/7.01  cnf(c_16,plain,
% 51.06/7.01      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 51.06/7.01      | r2_hidden(sK2(X0,X2,X1),X2)
% 51.06/7.01      | ~ v1_relat_1(X1) ),
% 51.06/7.01      inference(cnf_transformation,[],[f60]) ).
% 51.06/7.01  
% 51.06/7.01  cnf(c_412,plain,
% 51.06/7.01      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 51.06/7.01      | r2_hidden(sK2(X0,X2,X1),X2)
% 51.06/7.01      | sK4 != X1 ),
% 51.06/7.01      inference(resolution_lifted,[status(thm)],[c_16,c_24]) ).
% 51.06/7.01  
% 51.06/7.01  cnf(c_413,plain,
% 51.06/7.01      ( ~ r2_hidden(X0,k10_relat_1(sK4,X1))
% 51.06/7.01      | r2_hidden(sK2(X0,X1,sK4),X1) ),
% 51.06/7.01      inference(unflattening,[status(thm)],[c_412]) ).
% 51.06/7.01  
% 51.06/7.01  cnf(c_1221,plain,
% 51.06/7.01      ( r2_hidden(X0,k10_relat_1(sK4,X1)) != iProver_top
% 51.06/7.01      | r2_hidden(sK2(X0,X1,sK4),X1) = iProver_top ),
% 51.06/7.01      inference(predicate_to_equality,[status(thm)],[c_413]) ).
% 51.06/7.01  
% 51.06/7.01  cnf(c_6,plain,
% 51.06/7.01      ( r1_xboole_0(X0,k1_xboole_0) ),
% 51.06/7.01      inference(cnf_transformation,[],[f49]) ).
% 51.06/7.01  
% 51.06/7.01  cnf(c_1233,plain,
% 51.06/7.01      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 51.06/7.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 51.06/7.01  
% 51.06/7.01  cnf(c_9,plain,
% 51.06/7.01      ( ~ r2_hidden(X0,X1) | ~ r1_xboole_0(k1_tarski(X0),X1) ),
% 51.06/7.01      inference(cnf_transformation,[],[f52]) ).
% 51.06/7.01  
% 51.06/7.01  cnf(c_1230,plain,
% 51.06/7.01      ( r2_hidden(X0,X1) != iProver_top
% 51.06/7.01      | r1_xboole_0(k1_tarski(X0),X1) != iProver_top ),
% 51.06/7.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 51.06/7.01  
% 51.06/7.01  cnf(c_1858,plain,
% 51.06/7.01      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 51.06/7.01      inference(superposition,[status(thm)],[c_1233,c_1230]) ).
% 51.06/7.01  
% 51.06/7.01  cnf(c_2195,plain,
% 51.06/7.01      ( r2_hidden(X0,k10_relat_1(sK4,k1_xboole_0)) != iProver_top ),
% 51.06/7.01      inference(superposition,[status(thm)],[c_1221,c_1858]) ).
% 51.06/7.01  
% 51.06/7.01  cnf(c_5816,plain,
% 51.06/7.01      ( r1_xboole_0(X0,k10_relat_1(sK4,k1_xboole_0)) = iProver_top ),
% 51.06/7.01      inference(superposition,[status(thm)],[c_1235,c_2195]) ).
% 51.06/7.01  
% 51.06/7.01  cnf(c_8,plain,
% 51.06/7.01      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 51.06/7.01      inference(cnf_transformation,[],[f50]) ).
% 51.06/7.01  
% 51.06/7.01  cnf(c_1231,plain,
% 51.06/7.01      ( k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 51.06/7.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 51.06/7.01  
% 51.06/7.01  cnf(c_7391,plain,
% 51.06/7.01      ( k4_xboole_0(X0,k10_relat_1(sK4,k1_xboole_0)) = X0 ),
% 51.06/7.01      inference(superposition,[status(thm)],[c_5816,c_1231]) ).
% 51.06/7.01  
% 51.06/7.01  cnf(c_5,plain,
% 51.06/7.01      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 51.06/7.01      inference(cnf_transformation,[],[f47]) ).
% 51.06/7.01  
% 51.06/7.01  cnf(c_1316,plain,
% 51.06/7.01      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 51.06/7.01      inference(superposition,[status(thm)],[c_5,c_4]) ).
% 51.06/7.01  
% 51.06/7.01  cnf(c_7713,plain,
% 51.06/7.01      ( k10_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
% 51.06/7.01      inference(superposition,[status(thm)],[c_7391,c_1316]) ).
% 51.06/7.01  
% 51.06/7.01  cnf(c_19,plain,
% 51.06/7.01      ( ~ v1_relat_1(X0)
% 51.06/7.01      | k10_relat_1(X0,k4_xboole_0(k2_relat_1(X0),k4_xboole_0(k2_relat_1(X0),X1))) = k10_relat_1(X0,X1) ),
% 51.06/7.01      inference(cnf_transformation,[],[f69]) ).
% 51.06/7.01  
% 51.06/7.01  cnf(c_460,plain,
% 51.06/7.01      ( k10_relat_1(X0,k4_xboole_0(k2_relat_1(X0),k4_xboole_0(k2_relat_1(X0),X1))) = k10_relat_1(X0,X1)
% 51.06/7.01      | sK4 != X0 ),
% 51.06/7.01      inference(resolution_lifted,[status(thm)],[c_19,c_24]) ).
% 51.06/7.01  
% 51.06/7.01  cnf(c_461,plain,
% 51.06/7.01      ( k10_relat_1(sK4,k4_xboole_0(k2_relat_1(sK4),k4_xboole_0(k2_relat_1(sK4),X0))) = k10_relat_1(sK4,X0) ),
% 51.06/7.01      inference(unflattening,[status(thm)],[c_460]) ).
% 51.06/7.01  
% 51.06/7.01  cnf(c_1294,plain,
% 51.06/7.01      ( k10_relat_1(sK4,k4_xboole_0(k2_relat_1(sK4),k2_relat_1(sK4))) = k10_relat_1(sK4,k1_xboole_0) ),
% 51.06/7.01      inference(superposition,[status(thm)],[c_5,c_461]) ).
% 51.06/7.01  
% 51.06/7.01  cnf(c_1228,plain,
% 51.06/7.01      ( k1_xboole_0 = k10_relat_1(sK4,sK3)
% 51.06/7.01      | r1_xboole_0(k2_relat_1(sK4),sK3) = iProver_top ),
% 51.06/7.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 51.06/7.01  
% 51.06/7.01  cnf(c_1410,plain,
% 51.06/7.01      ( k10_relat_1(sK4,sK3) = k1_xboole_0
% 51.06/7.01      | k4_xboole_0(k2_relat_1(sK4),sK3) = k2_relat_1(sK4) ),
% 51.06/7.01      inference(superposition,[status(thm)],[c_1228,c_1231]) ).
% 51.06/7.01  
% 51.06/7.01  cnf(c_3153,plain,
% 51.06/7.01      ( k10_relat_1(sK4,k4_xboole_0(k2_relat_1(sK4),k2_relat_1(sK4))) = k10_relat_1(sK4,sK3)
% 51.06/7.01      | k10_relat_1(sK4,sK3) = k1_xboole_0 ),
% 51.06/7.01      inference(superposition,[status(thm)],[c_1410,c_461]) ).
% 51.06/7.01  
% 51.06/7.01  cnf(c_6532,plain,
% 51.06/7.01      ( k10_relat_1(sK4,sK3) = k1_xboole_0
% 51.06/7.01      | k10_relat_1(sK4,k1_xboole_0) = k10_relat_1(sK4,sK3) ),
% 51.06/7.01      inference(superposition,[status(thm)],[c_1294,c_3153]) ).
% 51.06/7.01  
% 51.06/7.01  cnf(c_22,negated_conjecture,
% 51.06/7.01      ( ~ r1_xboole_0(k2_relat_1(sK4),sK3)
% 51.06/7.01      | k1_xboole_0 != k10_relat_1(sK4,sK3) ),
% 51.06/7.01      inference(cnf_transformation,[],[f67]) ).
% 51.06/7.01  
% 51.06/7.01  cnf(c_1229,plain,
% 51.06/7.01      ( k1_xboole_0 != k10_relat_1(sK4,sK3)
% 51.06/7.01      | r1_xboole_0(k2_relat_1(sK4),sK3) != iProver_top ),
% 51.06/7.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 51.06/7.01  
% 51.06/7.01  cnf(c_11936,plain,
% 51.06/7.01      ( k10_relat_1(sK4,sK3) = k1_xboole_0
% 51.06/7.01      | k10_relat_1(sK4,k1_xboole_0) != k1_xboole_0
% 51.06/7.01      | r1_xboole_0(k2_relat_1(sK4),sK3) != iProver_top ),
% 51.06/7.01      inference(superposition,[status(thm)],[c_6532,c_1229]) ).
% 51.06/7.01  
% 51.06/7.01  cnf(c_11940,plain,
% 51.06/7.01      ( ~ r1_xboole_0(k2_relat_1(sK4),sK3)
% 51.06/7.01      | k10_relat_1(sK4,sK3) = k1_xboole_0
% 51.06/7.01      | k10_relat_1(sK4,k1_xboole_0) != k1_xboole_0 ),
% 51.06/7.01      inference(predicate_to_equality_rev,[status(thm)],[c_11936]) ).
% 51.06/7.01  
% 51.06/7.01  cnf(c_16175,plain,
% 51.06/7.01      ( X0 != k1_xboole_0 | k10_relat_1(sK4,sK3) = X0 ),
% 51.06/7.01      inference(global_propositional_subsumption,
% 51.06/7.01                [status(thm)],
% 51.06/7.01                [c_5841,c_1708,c_2177,c_3720,c_4513,c_7713,c_11940]) ).
% 51.06/7.01  
% 51.06/7.01  cnf(c_16177,plain,
% 51.06/7.01      ( k10_relat_1(sK4,sK3) = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 51.06/7.01      inference(instantiation,[status(thm)],[c_16175]) ).
% 51.06/7.01  
% 51.06/7.01  cnf(c_12340,plain,
% 51.06/7.01      ( sK0(k2_relat_1(sK4),sK3) = sK0(k2_relat_1(sK4),sK3) ),
% 51.06/7.01      inference(instantiation,[status(thm)],[c_703]) ).
% 51.06/7.01  
% 51.06/7.01  cnf(c_1366,plain,
% 51.06/7.01      ( k10_relat_1(sK4,sK3) != X0
% 51.06/7.01      | k1_xboole_0 != X0
% 51.06/7.01      | k1_xboole_0 = k10_relat_1(sK4,sK3) ),
% 51.06/7.01      inference(instantiation,[status(thm)],[c_704]) ).
% 51.06/7.01  
% 51.06/7.01  cnf(c_1367,plain,
% 51.06/7.01      ( k10_relat_1(sK4,sK3) != k1_xboole_0
% 51.06/7.01      | k1_xboole_0 = k10_relat_1(sK4,sK3)
% 51.06/7.01      | k1_xboole_0 != k1_xboole_0 ),
% 51.06/7.01      inference(instantiation,[status(thm)],[c_1366]) ).
% 51.06/7.01  
% 51.06/7.01  cnf(c_3,plain,
% 51.06/7.01      ( r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1) ),
% 51.06/7.01      inference(cnf_transformation,[],[f43]) ).
% 51.06/7.01  
% 51.06/7.01  cnf(c_1339,plain,
% 51.06/7.01      ( r2_hidden(sK0(k2_relat_1(sK4),sK3),k2_relat_1(sK4))
% 51.06/7.01      | r1_xboole_0(k2_relat_1(sK4),sK3) ),
% 51.06/7.01      inference(instantiation,[status(thm)],[c_3]) ).
% 51.06/7.01  
% 51.06/7.01  cnf(c_1336,plain,
% 51.06/7.01      ( r2_hidden(sK0(k2_relat_1(sK4),sK3),sK3)
% 51.06/7.01      | r1_xboole_0(k2_relat_1(sK4),sK3) ),
% 51.06/7.01      inference(instantiation,[status(thm)],[c_2]) ).
% 51.06/7.01  
% 51.06/7.01  cnf(c_726,plain,
% 51.06/7.01      ( k1_xboole_0 = k1_xboole_0 ),
% 51.06/7.01      inference(instantiation,[status(thm)],[c_703]) ).
% 51.06/7.01  
% 51.06/7.01  cnf(c_14,plain,
% 51.06/7.01      ( ~ v1_relat_1(X0)
% 51.06/7.01      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 51.06/7.01      inference(cnf_transformation,[],[f57]) ).
% 51.06/7.01  
% 51.06/7.01  cnf(c_466,plain,
% 51.06/7.01      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | sK4 != X0 ),
% 51.06/7.01      inference(resolution_lifted,[status(thm)],[c_14,c_24]) ).
% 51.06/7.01  
% 51.06/7.01  cnf(c_467,plain,
% 51.06/7.01      ( k9_relat_1(sK4,k1_relat_1(sK4)) = k2_relat_1(sK4) ),
% 51.06/7.01      inference(unflattening,[status(thm)],[c_466]) ).
% 51.06/7.01  
% 51.06/7.01  cnf(c_74,plain,
% 51.06/7.01      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 51.06/7.01      inference(instantiation,[status(thm)],[c_6]) ).
% 51.06/7.01  
% 51.06/7.01  cnf(contradiction,plain,
% 51.06/7.01      ( $false ),
% 51.06/7.01      inference(minisat,
% 51.06/7.01                [status(thm)],
% 51.06/7.01                [c_277098,c_211468,c_168216,c_167711,c_62512,c_16177,
% 51.06/7.01                 c_12340,c_1367,c_1339,c_1336,c_726,c_467,c_74,c_22]) ).
% 51.06/7.01  
% 51.06/7.01  
% 51.06/7.01  % SZS output end CNFRefutation for theBenchmark.p
% 51.06/7.01  
% 51.06/7.01  ------                               Statistics
% 51.06/7.01  
% 51.06/7.01  ------ Selected
% 51.06/7.01  
% 51.06/7.01  total_time:                             6.258
% 51.06/7.01  
%------------------------------------------------------------------------------
