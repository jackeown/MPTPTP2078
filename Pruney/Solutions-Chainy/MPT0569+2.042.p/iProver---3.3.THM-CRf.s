%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:47:34 EST 2020

% Result     : Theorem 4.04s
% Output     : CNFRefutation 4.04s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 300 expanded)
%              Number of clauses        :   63 (  93 expanded)
%              Number of leaves         :   16 (  60 expanded)
%              Depth                    :   20
%              Number of atoms          :  376 (1187 expanded)
%              Number of equality atoms :  100 ( 274 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
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

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f23])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f53,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k10_relat_1(X1,X0)
        <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <~> r1_xboole_0(k2_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f37,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f38,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f39,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 != k10_relat_1(X1,X0) )
        & ( r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 = k10_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k2_relat_1(sK6),sK5)
        | k1_xboole_0 != k10_relat_1(sK6,sK5) )
      & ( r1_xboole_0(k2_relat_1(sK6),sK5)
        | k1_xboole_0 = k10_relat_1(sK6,sK5) )
      & v1_relat_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ( ~ r1_xboole_0(k2_relat_1(sK6),sK5)
      | k1_xboole_0 != k10_relat_1(sK6,sK5) )
    & ( r1_xboole_0(k2_relat_1(sK6),sK5)
      | k1_xboole_0 = k10_relat_1(sK6,sK5) )
    & v1_relat_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f38,f39])).

fof(f60,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f40])).

fof(f61,plain,
    ( r1_xboole_0(k2_relat_1(sK6),sK5)
    | k1_xboole_0 = k10_relat_1(sK6,sK5) ),
    inference(cnf_transformation,[],[f40])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f27])).

fof(f46,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f33,plain,(
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

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK4(X0,X1,X2)),X2)
        & r2_hidden(sK4(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(X0,sK4(X0,X1,X2)),X2)
            & r2_hidden(sK4(X0,X1,X2),k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f34,f35])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),k2_relat_1(X2))
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f29,plain,(
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

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK3(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2)
        & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2)
            & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f31])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k2_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X0,X3),X2)
      | ~ r2_hidden(X3,k2_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f4,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f25])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f62,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK6),sK5)
    | k1_xboole_0 != k10_relat_1(sK6,sK5) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1500,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1501,plain,
    ( r2_hidden(sK0(X0,X1),X1) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_21,negated_conjecture,
    ( v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_426,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_21])).

cnf(c_427,plain,
    ( k9_relat_1(sK6,k1_relat_1(sK6)) = k2_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_426])).

cnf(c_20,negated_conjecture,
    ( r1_xboole_0(k2_relat_1(sK6),sK5)
    | k1_xboole_0 = k10_relat_1(sK6,sK5) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1494,plain,
    ( k1_xboole_0 = k10_relat_1(sK6,sK5)
    | r1_xboole_0(k2_relat_1(sK6),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_5,plain,
    ( r2_hidden(sK2(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1497,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK4(X0,X2,X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_354,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK4(X0,X2,X1),k2_relat_1(X1))
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_21])).

cnf(c_355,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK6,X1))
    | r2_hidden(sK4(X0,X1,sK6),k2_relat_1(sK6)) ),
    inference(unflattening,[status(thm)],[c_354])).

cnf(c_1489,plain,
    ( r2_hidden(X0,k10_relat_1(sK6,X1)) != iProver_top
    | r2_hidden(sK4(X0,X1,sK6),k2_relat_1(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_355])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK4(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_378,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK4(X0,X2,X1),X2)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_21])).

cnf(c_379,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK6,X1))
    | r2_hidden(sK4(X0,X1,sK6),X1) ),
    inference(unflattening,[status(thm)],[c_378])).

cnf(c_1487,plain,
    ( r2_hidden(X0,k10_relat_1(sK6,X1)) != iProver_top
    | r2_hidden(sK4(X0,X1,sK6),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_379])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1502,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r1_xboole_0(X2,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2347,plain,
    ( r2_hidden(X0,k10_relat_1(sK6,X1)) != iProver_top
    | r2_hidden(sK4(X0,X1,sK6),X2) != iProver_top
    | r1_xboole_0(X2,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1487,c_1502])).

cnf(c_6563,plain,
    ( r2_hidden(X0,k10_relat_1(sK6,X1)) != iProver_top
    | r1_xboole_0(k2_relat_1(sK6),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1489,c_2347])).

cnf(c_6774,plain,
    ( k10_relat_1(sK6,X0) = k1_xboole_0
    | r1_xboole_0(k2_relat_1(sK6),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1497,c_6563])).

cnf(c_9185,plain,
    ( k10_relat_1(sK6,sK5) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1494,c_6774])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK3(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_402,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK3(X0,X2,X1),X0),X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_21])).

cnf(c_403,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK6,X1))
    | r2_hidden(k4_tarski(sK3(X0,X1,sK6),X0),sK6) ),
    inference(unflattening,[status(thm)],[c_402])).

cnf(c_1485,plain,
    ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | r2_hidden(k4_tarski(sK3(X0,X1,sK6),X0),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_403])).

cnf(c_17,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_338,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_21])).

cnf(c_339,plain,
    ( r2_hidden(X0,k2_relat_1(sK6))
    | ~ r2_hidden(k4_tarski(X1,X0),sK6) ),
    inference(unflattening,[status(thm)],[c_338])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(X0,k2_relat_1(X3))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_286,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(X0,k2_relat_1(X3))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | sK6 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_21])).

cnf(c_287,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(sK6,X1))
    | ~ r2_hidden(X0,k2_relat_1(sK6))
    | ~ r2_hidden(k4_tarski(X2,X0),sK6) ),
    inference(unflattening,[status(thm)],[c_286])).

cnf(c_348,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(sK6,X1))
    | ~ r2_hidden(k4_tarski(X2,X0),sK6) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_339,c_287])).

cnf(c_1490,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,k10_relat_1(sK6,X1)) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_348])).

cnf(c_2143,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k9_relat_1(sK6,X2)) != iProver_top
    | r2_hidden(sK3(X0,X2,sK6),k10_relat_1(sK6,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1485,c_1490])).

cnf(c_9516,plain,
    ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(sK3(X0,X1,sK6),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_9185,c_2143])).

cnf(c_6,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1499,plain,
    ( r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2219,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r1_xboole_0(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_1499])).

cnf(c_7,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1496,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2317,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2219,c_1496])).

cnf(c_13039,plain,
    ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_9516,c_2317])).

cnf(c_13048,plain,
    ( r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_427,c_13039])).

cnf(c_13091,plain,
    ( r2_hidden(sK0(X0,k2_relat_1(sK6)),sK5) != iProver_top
    | r1_xboole_0(X0,k2_relat_1(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1501,c_13048])).

cnf(c_13201,plain,
    ( r1_xboole_0(sK5,k2_relat_1(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1500,c_13091])).

cnf(c_1678,plain,
    ( ~ r2_hidden(sK0(k2_relat_1(sK6),sK5),X0)
    | ~ r2_hidden(sK0(k2_relat_1(sK6),sK5),k2_relat_1(sK6))
    | ~ r1_xboole_0(X0,k2_relat_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1934,plain,
    ( ~ r2_hidden(sK0(k2_relat_1(sK6),sK5),k2_relat_1(sK6))
    | ~ r2_hidden(sK0(k2_relat_1(sK6),sK5),sK5)
    | ~ r1_xboole_0(sK5,k2_relat_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_1678])).

cnf(c_1935,plain,
    ( r2_hidden(sK0(k2_relat_1(sK6),sK5),k2_relat_1(sK6)) != iProver_top
    | r2_hidden(sK0(k2_relat_1(sK6),sK5),sK5) != iProver_top
    | r1_xboole_0(sK5,k2_relat_1(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1934])).

cnf(c_19,negated_conjecture,
    ( ~ r1_xboole_0(k2_relat_1(sK6),sK5)
    | k1_xboole_0 != k10_relat_1(sK6,sK5) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_166,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK6),sK5)
    | k1_xboole_0 != k10_relat_1(sK6,sK5) ),
    inference(prop_impl,[status(thm)],[c_19])).

cnf(c_562,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | k10_relat_1(sK6,sK5) != k1_xboole_0
    | k2_relat_1(sK6) != X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_166])).

cnf(c_563,plain,
    ( r2_hidden(sK0(k2_relat_1(sK6),sK5),sK5)
    | k10_relat_1(sK6,sK5) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_562])).

cnf(c_564,plain,
    ( k10_relat_1(sK6,sK5) != k1_xboole_0
    | r2_hidden(sK0(k2_relat_1(sK6),sK5),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_563])).

cnf(c_552,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | k10_relat_1(sK6,sK5) != k1_xboole_0
    | k2_relat_1(sK6) != X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_166])).

cnf(c_553,plain,
    ( r2_hidden(sK0(k2_relat_1(sK6),sK5),k2_relat_1(sK6))
    | k10_relat_1(sK6,sK5) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_552])).

cnf(c_554,plain,
    ( k10_relat_1(sK6,sK5) != k1_xboole_0
    | r2_hidden(sK0(k2_relat_1(sK6),sK5),k2_relat_1(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_553])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13201,c_9185,c_1935,c_564,c_554])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:33:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 4.04/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.04/1.02  
% 4.04/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.04/1.02  
% 4.04/1.02  ------  iProver source info
% 4.04/1.02  
% 4.04/1.02  git: date: 2020-06-30 10:37:57 +0100
% 4.04/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.04/1.02  git: non_committed_changes: false
% 4.04/1.02  git: last_make_outside_of_git: false
% 4.04/1.02  
% 4.04/1.02  ------ 
% 4.04/1.02  
% 4.04/1.02  ------ Input Options
% 4.04/1.02  
% 4.04/1.02  --out_options                           all
% 4.04/1.02  --tptp_safe_out                         true
% 4.04/1.02  --problem_path                          ""
% 4.04/1.02  --include_path                          ""
% 4.04/1.02  --clausifier                            res/vclausify_rel
% 4.04/1.02  --clausifier_options                    --mode clausify
% 4.04/1.02  --stdin                                 false
% 4.04/1.02  --stats_out                             all
% 4.04/1.02  
% 4.04/1.02  ------ General Options
% 4.04/1.02  
% 4.04/1.02  --fof                                   false
% 4.04/1.02  --time_out_real                         305.
% 4.04/1.02  --time_out_virtual                      -1.
% 4.04/1.02  --symbol_type_check                     false
% 4.04/1.02  --clausify_out                          false
% 4.04/1.02  --sig_cnt_out                           false
% 4.04/1.02  --trig_cnt_out                          false
% 4.04/1.02  --trig_cnt_out_tolerance                1.
% 4.04/1.02  --trig_cnt_out_sk_spl                   false
% 4.04/1.02  --abstr_cl_out                          false
% 4.04/1.02  
% 4.04/1.02  ------ Global Options
% 4.04/1.02  
% 4.04/1.02  --schedule                              default
% 4.04/1.02  --add_important_lit                     false
% 4.04/1.02  --prop_solver_per_cl                    1000
% 4.04/1.02  --min_unsat_core                        false
% 4.04/1.02  --soft_assumptions                      false
% 4.04/1.02  --soft_lemma_size                       3
% 4.04/1.02  --prop_impl_unit_size                   0
% 4.04/1.02  --prop_impl_unit                        []
% 4.04/1.02  --share_sel_clauses                     true
% 4.04/1.02  --reset_solvers                         false
% 4.04/1.02  --bc_imp_inh                            [conj_cone]
% 4.04/1.02  --conj_cone_tolerance                   3.
% 4.04/1.02  --extra_neg_conj                        none
% 4.04/1.02  --large_theory_mode                     true
% 4.04/1.02  --prolific_symb_bound                   200
% 4.04/1.02  --lt_threshold                          2000
% 4.04/1.02  --clause_weak_htbl                      true
% 4.04/1.02  --gc_record_bc_elim                     false
% 4.04/1.02  
% 4.04/1.02  ------ Preprocessing Options
% 4.04/1.02  
% 4.04/1.02  --preprocessing_flag                    true
% 4.04/1.02  --time_out_prep_mult                    0.1
% 4.04/1.02  --splitting_mode                        input
% 4.04/1.02  --splitting_grd                         true
% 4.04/1.02  --splitting_cvd                         false
% 4.04/1.02  --splitting_cvd_svl                     false
% 4.04/1.02  --splitting_nvd                         32
% 4.04/1.02  --sub_typing                            true
% 4.04/1.02  --prep_gs_sim                           true
% 4.04/1.02  --prep_unflatten                        true
% 4.04/1.02  --prep_res_sim                          true
% 4.04/1.02  --prep_upred                            true
% 4.04/1.02  --prep_sem_filter                       exhaustive
% 4.04/1.02  --prep_sem_filter_out                   false
% 4.04/1.02  --pred_elim                             true
% 4.04/1.02  --res_sim_input                         true
% 4.04/1.02  --eq_ax_congr_red                       true
% 4.04/1.02  --pure_diseq_elim                       true
% 4.04/1.02  --brand_transform                       false
% 4.04/1.02  --non_eq_to_eq                          false
% 4.04/1.02  --prep_def_merge                        true
% 4.04/1.02  --prep_def_merge_prop_impl              false
% 4.04/1.02  --prep_def_merge_mbd                    true
% 4.04/1.02  --prep_def_merge_tr_red                 false
% 4.04/1.02  --prep_def_merge_tr_cl                  false
% 4.04/1.02  --smt_preprocessing                     true
% 4.04/1.02  --smt_ac_axioms                         fast
% 4.04/1.02  --preprocessed_out                      false
% 4.04/1.02  --preprocessed_stats                    false
% 4.04/1.02  
% 4.04/1.02  ------ Abstraction refinement Options
% 4.04/1.02  
% 4.04/1.02  --abstr_ref                             []
% 4.04/1.02  --abstr_ref_prep                        false
% 4.04/1.02  --abstr_ref_until_sat                   false
% 4.04/1.02  --abstr_ref_sig_restrict                funpre
% 4.04/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 4.04/1.02  --abstr_ref_under                       []
% 4.04/1.02  
% 4.04/1.02  ------ SAT Options
% 4.04/1.02  
% 4.04/1.02  --sat_mode                              false
% 4.04/1.02  --sat_fm_restart_options                ""
% 4.04/1.02  --sat_gr_def                            false
% 4.04/1.02  --sat_epr_types                         true
% 4.04/1.02  --sat_non_cyclic_types                  false
% 4.04/1.02  --sat_finite_models                     false
% 4.04/1.02  --sat_fm_lemmas                         false
% 4.04/1.02  --sat_fm_prep                           false
% 4.04/1.02  --sat_fm_uc_incr                        true
% 4.04/1.02  --sat_out_model                         small
% 4.04/1.02  --sat_out_clauses                       false
% 4.04/1.02  
% 4.04/1.02  ------ QBF Options
% 4.04/1.02  
% 4.04/1.02  --qbf_mode                              false
% 4.04/1.02  --qbf_elim_univ                         false
% 4.04/1.02  --qbf_dom_inst                          none
% 4.04/1.02  --qbf_dom_pre_inst                      false
% 4.04/1.02  --qbf_sk_in                             false
% 4.04/1.02  --qbf_pred_elim                         true
% 4.04/1.02  --qbf_split                             512
% 4.04/1.02  
% 4.04/1.02  ------ BMC1 Options
% 4.04/1.02  
% 4.04/1.02  --bmc1_incremental                      false
% 4.04/1.02  --bmc1_axioms                           reachable_all
% 4.04/1.02  --bmc1_min_bound                        0
% 4.04/1.02  --bmc1_max_bound                        -1
% 4.04/1.02  --bmc1_max_bound_default                -1
% 4.04/1.02  --bmc1_symbol_reachability              true
% 4.04/1.02  --bmc1_property_lemmas                  false
% 4.04/1.02  --bmc1_k_induction                      false
% 4.04/1.02  --bmc1_non_equiv_states                 false
% 4.04/1.02  --bmc1_deadlock                         false
% 4.04/1.02  --bmc1_ucm                              false
% 4.04/1.02  --bmc1_add_unsat_core                   none
% 4.04/1.02  --bmc1_unsat_core_children              false
% 4.04/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 4.04/1.02  --bmc1_out_stat                         full
% 4.04/1.02  --bmc1_ground_init                      false
% 4.04/1.02  --bmc1_pre_inst_next_state              false
% 4.04/1.02  --bmc1_pre_inst_state                   false
% 4.04/1.02  --bmc1_pre_inst_reach_state             false
% 4.04/1.02  --bmc1_out_unsat_core                   false
% 4.04/1.02  --bmc1_aig_witness_out                  false
% 4.04/1.02  --bmc1_verbose                          false
% 4.04/1.02  --bmc1_dump_clauses_tptp                false
% 4.04/1.02  --bmc1_dump_unsat_core_tptp             false
% 4.04/1.02  --bmc1_dump_file                        -
% 4.04/1.02  --bmc1_ucm_expand_uc_limit              128
% 4.04/1.02  --bmc1_ucm_n_expand_iterations          6
% 4.04/1.02  --bmc1_ucm_extend_mode                  1
% 4.04/1.02  --bmc1_ucm_init_mode                    2
% 4.04/1.02  --bmc1_ucm_cone_mode                    none
% 4.04/1.02  --bmc1_ucm_reduced_relation_type        0
% 4.04/1.02  --bmc1_ucm_relax_model                  4
% 4.04/1.02  --bmc1_ucm_full_tr_after_sat            true
% 4.04/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 4.04/1.02  --bmc1_ucm_layered_model                none
% 4.04/1.02  --bmc1_ucm_max_lemma_size               10
% 4.04/1.02  
% 4.04/1.02  ------ AIG Options
% 4.04/1.02  
% 4.04/1.02  --aig_mode                              false
% 4.04/1.02  
% 4.04/1.02  ------ Instantiation Options
% 4.04/1.02  
% 4.04/1.02  --instantiation_flag                    true
% 4.04/1.02  --inst_sos_flag                         false
% 4.04/1.02  --inst_sos_phase                        true
% 4.04/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.04/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.04/1.02  --inst_lit_sel_side                     num_symb
% 4.04/1.02  --inst_solver_per_active                1400
% 4.04/1.02  --inst_solver_calls_frac                1.
% 4.04/1.02  --inst_passive_queue_type               priority_queues
% 4.04/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.04/1.02  --inst_passive_queues_freq              [25;2]
% 4.04/1.02  --inst_dismatching                      true
% 4.04/1.02  --inst_eager_unprocessed_to_passive     true
% 4.04/1.02  --inst_prop_sim_given                   true
% 4.04/1.02  --inst_prop_sim_new                     false
% 4.04/1.02  --inst_subs_new                         false
% 4.04/1.02  --inst_eq_res_simp                      false
% 4.04/1.02  --inst_subs_given                       false
% 4.04/1.02  --inst_orphan_elimination               true
% 4.04/1.02  --inst_learning_loop_flag               true
% 4.04/1.02  --inst_learning_start                   3000
% 4.04/1.02  --inst_learning_factor                  2
% 4.04/1.02  --inst_start_prop_sim_after_learn       3
% 4.04/1.02  --inst_sel_renew                        solver
% 4.04/1.02  --inst_lit_activity_flag                true
% 4.04/1.02  --inst_restr_to_given                   false
% 4.04/1.02  --inst_activity_threshold               500
% 4.04/1.02  --inst_out_proof                        true
% 4.04/1.02  
% 4.04/1.02  ------ Resolution Options
% 4.04/1.02  
% 4.04/1.02  --resolution_flag                       true
% 4.04/1.02  --res_lit_sel                           adaptive
% 4.04/1.02  --res_lit_sel_side                      none
% 4.04/1.02  --res_ordering                          kbo
% 4.04/1.02  --res_to_prop_solver                    active
% 4.04/1.02  --res_prop_simpl_new                    false
% 4.04/1.02  --res_prop_simpl_given                  true
% 4.04/1.02  --res_passive_queue_type                priority_queues
% 4.04/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.04/1.02  --res_passive_queues_freq               [15;5]
% 4.04/1.02  --res_forward_subs                      full
% 4.04/1.02  --res_backward_subs                     full
% 4.04/1.02  --res_forward_subs_resolution           true
% 4.04/1.02  --res_backward_subs_resolution          true
% 4.04/1.02  --res_orphan_elimination                true
% 4.04/1.02  --res_time_limit                        2.
% 4.04/1.02  --res_out_proof                         true
% 4.04/1.02  
% 4.04/1.02  ------ Superposition Options
% 4.04/1.02  
% 4.04/1.02  --superposition_flag                    true
% 4.04/1.02  --sup_passive_queue_type                priority_queues
% 4.04/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.04/1.02  --sup_passive_queues_freq               [8;1;4]
% 4.04/1.02  --demod_completeness_check              fast
% 4.04/1.02  --demod_use_ground                      true
% 4.04/1.02  --sup_to_prop_solver                    passive
% 4.04/1.02  --sup_prop_simpl_new                    true
% 4.04/1.02  --sup_prop_simpl_given                  true
% 4.04/1.02  --sup_fun_splitting                     false
% 4.04/1.02  --sup_smt_interval                      50000
% 4.04/1.02  
% 4.04/1.02  ------ Superposition Simplification Setup
% 4.04/1.02  
% 4.04/1.02  --sup_indices_passive                   []
% 4.04/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.04/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.04/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.04/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 4.04/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.04/1.02  --sup_full_bw                           [BwDemod]
% 4.04/1.02  --sup_immed_triv                        [TrivRules]
% 4.04/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.04/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.04/1.02  --sup_immed_bw_main                     []
% 4.04/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.04/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 4.04/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.04/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.04/1.02  
% 4.04/1.02  ------ Combination Options
% 4.04/1.02  
% 4.04/1.02  --comb_res_mult                         3
% 4.04/1.02  --comb_sup_mult                         2
% 4.04/1.02  --comb_inst_mult                        10
% 4.04/1.02  
% 4.04/1.02  ------ Debug Options
% 4.04/1.02  
% 4.04/1.02  --dbg_backtrace                         false
% 4.04/1.02  --dbg_dump_prop_clauses                 false
% 4.04/1.02  --dbg_dump_prop_clauses_file            -
% 4.04/1.02  --dbg_out_stat                          false
% 4.04/1.02  ------ Parsing...
% 4.04/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.04/1.02  
% 4.04/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 4.04/1.02  
% 4.04/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.04/1.02  
% 4.04/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.04/1.02  ------ Proving...
% 4.04/1.02  ------ Problem Properties 
% 4.04/1.02  
% 4.04/1.02  
% 4.04/1.02  clauses                                 21
% 4.04/1.02  conjectures                             2
% 4.04/1.02  EPR                                     2
% 4.04/1.02  Horn                                    16
% 4.04/1.02  unary                                   3
% 4.04/1.02  binary                                  15
% 4.04/1.02  lits                                    42
% 4.04/1.02  lits eq                                 5
% 4.04/1.02  fd_pure                                 0
% 4.04/1.02  fd_pseudo                               0
% 4.04/1.02  fd_cond                                 1
% 4.04/1.02  fd_pseudo_cond                          0
% 4.04/1.02  AC symbols                              0
% 4.04/1.02  
% 4.04/1.02  ------ Schedule dynamic 5 is on 
% 4.04/1.02  
% 4.04/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 4.04/1.02  
% 4.04/1.02  
% 4.04/1.02  ------ 
% 4.04/1.02  Current options:
% 4.04/1.02  ------ 
% 4.04/1.02  
% 4.04/1.02  ------ Input Options
% 4.04/1.02  
% 4.04/1.02  --out_options                           all
% 4.04/1.02  --tptp_safe_out                         true
% 4.04/1.02  --problem_path                          ""
% 4.04/1.02  --include_path                          ""
% 4.04/1.02  --clausifier                            res/vclausify_rel
% 4.04/1.02  --clausifier_options                    --mode clausify
% 4.04/1.02  --stdin                                 false
% 4.04/1.02  --stats_out                             all
% 4.04/1.02  
% 4.04/1.02  ------ General Options
% 4.04/1.02  
% 4.04/1.02  --fof                                   false
% 4.04/1.02  --time_out_real                         305.
% 4.04/1.02  --time_out_virtual                      -1.
% 4.04/1.02  --symbol_type_check                     false
% 4.04/1.02  --clausify_out                          false
% 4.04/1.02  --sig_cnt_out                           false
% 4.04/1.02  --trig_cnt_out                          false
% 4.04/1.02  --trig_cnt_out_tolerance                1.
% 4.04/1.02  --trig_cnt_out_sk_spl                   false
% 4.04/1.02  --abstr_cl_out                          false
% 4.04/1.02  
% 4.04/1.02  ------ Global Options
% 4.04/1.02  
% 4.04/1.02  --schedule                              default
% 4.04/1.02  --add_important_lit                     false
% 4.04/1.02  --prop_solver_per_cl                    1000
% 4.04/1.02  --min_unsat_core                        false
% 4.04/1.02  --soft_assumptions                      false
% 4.04/1.02  --soft_lemma_size                       3
% 4.04/1.02  --prop_impl_unit_size                   0
% 4.04/1.02  --prop_impl_unit                        []
% 4.04/1.02  --share_sel_clauses                     true
% 4.04/1.02  --reset_solvers                         false
% 4.04/1.02  --bc_imp_inh                            [conj_cone]
% 4.04/1.02  --conj_cone_tolerance                   3.
% 4.04/1.02  --extra_neg_conj                        none
% 4.04/1.02  --large_theory_mode                     true
% 4.04/1.02  --prolific_symb_bound                   200
% 4.04/1.02  --lt_threshold                          2000
% 4.04/1.02  --clause_weak_htbl                      true
% 4.04/1.02  --gc_record_bc_elim                     false
% 4.04/1.02  
% 4.04/1.02  ------ Preprocessing Options
% 4.04/1.02  
% 4.04/1.02  --preprocessing_flag                    true
% 4.04/1.02  --time_out_prep_mult                    0.1
% 4.04/1.02  --splitting_mode                        input
% 4.04/1.02  --splitting_grd                         true
% 4.04/1.02  --splitting_cvd                         false
% 4.04/1.02  --splitting_cvd_svl                     false
% 4.04/1.02  --splitting_nvd                         32
% 4.04/1.02  --sub_typing                            true
% 4.04/1.02  --prep_gs_sim                           true
% 4.04/1.02  --prep_unflatten                        true
% 4.04/1.02  --prep_res_sim                          true
% 4.04/1.02  --prep_upred                            true
% 4.04/1.02  --prep_sem_filter                       exhaustive
% 4.04/1.02  --prep_sem_filter_out                   false
% 4.04/1.02  --pred_elim                             true
% 4.04/1.02  --res_sim_input                         true
% 4.04/1.02  --eq_ax_congr_red                       true
% 4.04/1.02  --pure_diseq_elim                       true
% 4.04/1.02  --brand_transform                       false
% 4.04/1.02  --non_eq_to_eq                          false
% 4.04/1.02  --prep_def_merge                        true
% 4.04/1.02  --prep_def_merge_prop_impl              false
% 4.04/1.02  --prep_def_merge_mbd                    true
% 4.04/1.02  --prep_def_merge_tr_red                 false
% 4.04/1.02  --prep_def_merge_tr_cl                  false
% 4.04/1.02  --smt_preprocessing                     true
% 4.04/1.02  --smt_ac_axioms                         fast
% 4.04/1.02  --preprocessed_out                      false
% 4.04/1.02  --preprocessed_stats                    false
% 4.04/1.02  
% 4.04/1.02  ------ Abstraction refinement Options
% 4.04/1.02  
% 4.04/1.02  --abstr_ref                             []
% 4.04/1.02  --abstr_ref_prep                        false
% 4.04/1.02  --abstr_ref_until_sat                   false
% 4.04/1.02  --abstr_ref_sig_restrict                funpre
% 4.04/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 4.04/1.02  --abstr_ref_under                       []
% 4.04/1.02  
% 4.04/1.02  ------ SAT Options
% 4.04/1.02  
% 4.04/1.02  --sat_mode                              false
% 4.04/1.02  --sat_fm_restart_options                ""
% 4.04/1.02  --sat_gr_def                            false
% 4.04/1.02  --sat_epr_types                         true
% 4.04/1.02  --sat_non_cyclic_types                  false
% 4.04/1.02  --sat_finite_models                     false
% 4.04/1.02  --sat_fm_lemmas                         false
% 4.04/1.02  --sat_fm_prep                           false
% 4.04/1.02  --sat_fm_uc_incr                        true
% 4.04/1.02  --sat_out_model                         small
% 4.04/1.02  --sat_out_clauses                       false
% 4.04/1.02  
% 4.04/1.02  ------ QBF Options
% 4.04/1.02  
% 4.04/1.02  --qbf_mode                              false
% 4.04/1.02  --qbf_elim_univ                         false
% 4.04/1.02  --qbf_dom_inst                          none
% 4.04/1.02  --qbf_dom_pre_inst                      false
% 4.04/1.02  --qbf_sk_in                             false
% 4.04/1.02  --qbf_pred_elim                         true
% 4.04/1.02  --qbf_split                             512
% 4.04/1.02  
% 4.04/1.02  ------ BMC1 Options
% 4.04/1.02  
% 4.04/1.02  --bmc1_incremental                      false
% 4.04/1.02  --bmc1_axioms                           reachable_all
% 4.04/1.02  --bmc1_min_bound                        0
% 4.04/1.02  --bmc1_max_bound                        -1
% 4.04/1.02  --bmc1_max_bound_default                -1
% 4.04/1.02  --bmc1_symbol_reachability              true
% 4.04/1.02  --bmc1_property_lemmas                  false
% 4.04/1.02  --bmc1_k_induction                      false
% 4.04/1.02  --bmc1_non_equiv_states                 false
% 4.04/1.02  --bmc1_deadlock                         false
% 4.04/1.02  --bmc1_ucm                              false
% 4.04/1.02  --bmc1_add_unsat_core                   none
% 4.04/1.02  --bmc1_unsat_core_children              false
% 4.04/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 4.04/1.02  --bmc1_out_stat                         full
% 4.04/1.02  --bmc1_ground_init                      false
% 4.04/1.02  --bmc1_pre_inst_next_state              false
% 4.04/1.02  --bmc1_pre_inst_state                   false
% 4.04/1.02  --bmc1_pre_inst_reach_state             false
% 4.04/1.02  --bmc1_out_unsat_core                   false
% 4.04/1.02  --bmc1_aig_witness_out                  false
% 4.04/1.02  --bmc1_verbose                          false
% 4.04/1.02  --bmc1_dump_clauses_tptp                false
% 4.04/1.02  --bmc1_dump_unsat_core_tptp             false
% 4.04/1.02  --bmc1_dump_file                        -
% 4.04/1.02  --bmc1_ucm_expand_uc_limit              128
% 4.04/1.02  --bmc1_ucm_n_expand_iterations          6
% 4.04/1.02  --bmc1_ucm_extend_mode                  1
% 4.04/1.02  --bmc1_ucm_init_mode                    2
% 4.04/1.02  --bmc1_ucm_cone_mode                    none
% 4.04/1.02  --bmc1_ucm_reduced_relation_type        0
% 4.04/1.02  --bmc1_ucm_relax_model                  4
% 4.04/1.02  --bmc1_ucm_full_tr_after_sat            true
% 4.04/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 4.04/1.02  --bmc1_ucm_layered_model                none
% 4.04/1.02  --bmc1_ucm_max_lemma_size               10
% 4.04/1.02  
% 4.04/1.02  ------ AIG Options
% 4.04/1.02  
% 4.04/1.02  --aig_mode                              false
% 4.04/1.02  
% 4.04/1.02  ------ Instantiation Options
% 4.04/1.02  
% 4.04/1.02  --instantiation_flag                    true
% 4.04/1.02  --inst_sos_flag                         false
% 4.04/1.02  --inst_sos_phase                        true
% 4.04/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.04/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.04/1.02  --inst_lit_sel_side                     none
% 4.04/1.02  --inst_solver_per_active                1400
% 4.04/1.02  --inst_solver_calls_frac                1.
% 4.04/1.02  --inst_passive_queue_type               priority_queues
% 4.04/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.04/1.02  --inst_passive_queues_freq              [25;2]
% 4.04/1.02  --inst_dismatching                      true
% 4.04/1.02  --inst_eager_unprocessed_to_passive     true
% 4.04/1.02  --inst_prop_sim_given                   true
% 4.04/1.02  --inst_prop_sim_new                     false
% 4.04/1.02  --inst_subs_new                         false
% 4.04/1.02  --inst_eq_res_simp                      false
% 4.04/1.02  --inst_subs_given                       false
% 4.04/1.02  --inst_orphan_elimination               true
% 4.04/1.02  --inst_learning_loop_flag               true
% 4.04/1.02  --inst_learning_start                   3000
% 4.04/1.02  --inst_learning_factor                  2
% 4.04/1.02  --inst_start_prop_sim_after_learn       3
% 4.04/1.02  --inst_sel_renew                        solver
% 4.04/1.02  --inst_lit_activity_flag                true
% 4.04/1.02  --inst_restr_to_given                   false
% 4.04/1.02  --inst_activity_threshold               500
% 4.04/1.02  --inst_out_proof                        true
% 4.04/1.02  
% 4.04/1.02  ------ Resolution Options
% 4.04/1.02  
% 4.04/1.02  --resolution_flag                       false
% 4.04/1.02  --res_lit_sel                           adaptive
% 4.04/1.02  --res_lit_sel_side                      none
% 4.04/1.02  --res_ordering                          kbo
% 4.04/1.02  --res_to_prop_solver                    active
% 4.04/1.02  --res_prop_simpl_new                    false
% 4.04/1.02  --res_prop_simpl_given                  true
% 4.04/1.02  --res_passive_queue_type                priority_queues
% 4.04/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.04/1.02  --res_passive_queues_freq               [15;5]
% 4.04/1.02  --res_forward_subs                      full
% 4.04/1.02  --res_backward_subs                     full
% 4.04/1.02  --res_forward_subs_resolution           true
% 4.04/1.02  --res_backward_subs_resolution          true
% 4.04/1.02  --res_orphan_elimination                true
% 4.04/1.02  --res_time_limit                        2.
% 4.04/1.02  --res_out_proof                         true
% 4.04/1.02  
% 4.04/1.02  ------ Superposition Options
% 4.04/1.02  
% 4.04/1.02  --superposition_flag                    true
% 4.04/1.02  --sup_passive_queue_type                priority_queues
% 4.04/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.04/1.02  --sup_passive_queues_freq               [8;1;4]
% 4.04/1.02  --demod_completeness_check              fast
% 4.04/1.03  --demod_use_ground                      true
% 4.04/1.03  --sup_to_prop_solver                    passive
% 4.04/1.03  --sup_prop_simpl_new                    true
% 4.04/1.03  --sup_prop_simpl_given                  true
% 4.04/1.03  --sup_fun_splitting                     false
% 4.04/1.03  --sup_smt_interval                      50000
% 4.04/1.03  
% 4.04/1.03  ------ Superposition Simplification Setup
% 4.04/1.03  
% 4.04/1.03  --sup_indices_passive                   []
% 4.04/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.04/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.04/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.04/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 4.04/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.04/1.03  --sup_full_bw                           [BwDemod]
% 4.04/1.03  --sup_immed_triv                        [TrivRules]
% 4.04/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.04/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.04/1.03  --sup_immed_bw_main                     []
% 4.04/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.04/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 4.04/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.04/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.04/1.03  
% 4.04/1.03  ------ Combination Options
% 4.04/1.03  
% 4.04/1.03  --comb_res_mult                         3
% 4.04/1.03  --comb_sup_mult                         2
% 4.04/1.03  --comb_inst_mult                        10
% 4.04/1.03  
% 4.04/1.03  ------ Debug Options
% 4.04/1.03  
% 4.04/1.03  --dbg_backtrace                         false
% 4.04/1.03  --dbg_dump_prop_clauses                 false
% 4.04/1.03  --dbg_dump_prop_clauses_file            -
% 4.04/1.03  --dbg_out_stat                          false
% 4.04/1.03  
% 4.04/1.03  
% 4.04/1.03  
% 4.04/1.03  
% 4.04/1.03  ------ Proving...
% 4.04/1.03  
% 4.04/1.03  
% 4.04/1.03  % SZS status Theorem for theBenchmark.p
% 4.04/1.03  
% 4.04/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 4.04/1.03  
% 4.04/1.03  fof(f1,axiom,(
% 4.04/1.03    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 4.04/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.04/1.03  
% 4.04/1.03  fof(f12,plain,(
% 4.04/1.03    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 4.04/1.03    inference(rectify,[],[f1])).
% 4.04/1.03  
% 4.04/1.03  fof(f14,plain,(
% 4.04/1.03    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 4.04/1.03    inference(ennf_transformation,[],[f12])).
% 4.04/1.03  
% 4.04/1.03  fof(f23,plain,(
% 4.04/1.03    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 4.04/1.03    introduced(choice_axiom,[])).
% 4.04/1.03  
% 4.04/1.03  fof(f24,plain,(
% 4.04/1.03    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 4.04/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f23])).
% 4.04/1.03  
% 4.04/1.03  fof(f41,plain,(
% 4.04/1.03    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 4.04/1.03    inference(cnf_transformation,[],[f24])).
% 4.04/1.03  
% 4.04/1.03  fof(f42,plain,(
% 4.04/1.03    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 4.04/1.03    inference(cnf_transformation,[],[f24])).
% 4.04/1.03  
% 4.04/1.03  fof(f7,axiom,(
% 4.04/1.03    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 4.04/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.04/1.03  
% 4.04/1.03  fof(f18,plain,(
% 4.04/1.03    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 4.04/1.03    inference(ennf_transformation,[],[f7])).
% 4.04/1.03  
% 4.04/1.03  fof(f53,plain,(
% 4.04/1.03    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 4.04/1.03    inference(cnf_transformation,[],[f18])).
% 4.04/1.03  
% 4.04/1.03  fof(f10,conjecture,(
% 4.04/1.03    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 4.04/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.04/1.03  
% 4.04/1.03  fof(f11,negated_conjecture,(
% 4.04/1.03    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 4.04/1.03    inference(negated_conjecture,[],[f10])).
% 4.04/1.03  
% 4.04/1.03  fof(f22,plain,(
% 4.04/1.03    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <~> r1_xboole_0(k2_relat_1(X1),X0)) & v1_relat_1(X1))),
% 4.04/1.03    inference(ennf_transformation,[],[f11])).
% 4.04/1.03  
% 4.04/1.03  fof(f37,plain,(
% 4.04/1.03    ? [X0,X1] : (((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0))) & v1_relat_1(X1))),
% 4.04/1.03    inference(nnf_transformation,[],[f22])).
% 4.04/1.03  
% 4.04/1.03  fof(f38,plain,(
% 4.04/1.03    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1))),
% 4.04/1.03    inference(flattening,[],[f37])).
% 4.04/1.03  
% 4.04/1.03  fof(f39,plain,(
% 4.04/1.03    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k2_relat_1(sK6),sK5) | k1_xboole_0 != k10_relat_1(sK6,sK5)) & (r1_xboole_0(k2_relat_1(sK6),sK5) | k1_xboole_0 = k10_relat_1(sK6,sK5)) & v1_relat_1(sK6))),
% 4.04/1.03    introduced(choice_axiom,[])).
% 4.04/1.03  
% 4.04/1.03  fof(f40,plain,(
% 4.04/1.03    (~r1_xboole_0(k2_relat_1(sK6),sK5) | k1_xboole_0 != k10_relat_1(sK6,sK5)) & (r1_xboole_0(k2_relat_1(sK6),sK5) | k1_xboole_0 = k10_relat_1(sK6,sK5)) & v1_relat_1(sK6)),
% 4.04/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f38,f39])).
% 4.04/1.03  
% 4.04/1.03  fof(f60,plain,(
% 4.04/1.03    v1_relat_1(sK6)),
% 4.04/1.03    inference(cnf_transformation,[],[f40])).
% 4.04/1.03  
% 4.04/1.03  fof(f61,plain,(
% 4.04/1.03    r1_xboole_0(k2_relat_1(sK6),sK5) | k1_xboole_0 = k10_relat_1(sK6,sK5)),
% 4.04/1.03    inference(cnf_transformation,[],[f40])).
% 4.04/1.03  
% 4.04/1.03  fof(f3,axiom,(
% 4.04/1.03    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 4.04/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.04/1.03  
% 4.04/1.03  fof(f16,plain,(
% 4.04/1.03    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 4.04/1.03    inference(ennf_transformation,[],[f3])).
% 4.04/1.03  
% 4.04/1.03  fof(f27,plain,(
% 4.04/1.03    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 4.04/1.03    introduced(choice_axiom,[])).
% 4.04/1.03  
% 4.04/1.03  fof(f28,plain,(
% 4.04/1.03    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 4.04/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f27])).
% 4.04/1.03  
% 4.04/1.03  fof(f46,plain,(
% 4.04/1.03    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 4.04/1.03    inference(cnf_transformation,[],[f28])).
% 4.04/1.03  
% 4.04/1.03  fof(f8,axiom,(
% 4.04/1.03    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 4.04/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.04/1.03  
% 4.04/1.03  fof(f19,plain,(
% 4.04/1.03    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 4.04/1.03    inference(ennf_transformation,[],[f8])).
% 4.04/1.03  
% 4.04/1.03  fof(f33,plain,(
% 4.04/1.03    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 4.04/1.03    inference(nnf_transformation,[],[f19])).
% 4.04/1.03  
% 4.04/1.03  fof(f34,plain,(
% 4.04/1.03    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 4.04/1.03    inference(rectify,[],[f33])).
% 4.04/1.03  
% 4.04/1.03  fof(f35,plain,(
% 4.04/1.03    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK4(X0,X1,X2)),X2) & r2_hidden(sK4(X0,X1,X2),k2_relat_1(X2))))),
% 4.04/1.03    introduced(choice_axiom,[])).
% 4.04/1.03  
% 4.04/1.03  fof(f36,plain,(
% 4.04/1.03    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK4(X0,X1,X2)),X2) & r2_hidden(sK4(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 4.04/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f34,f35])).
% 4.04/1.03  
% 4.04/1.03  fof(f54,plain,(
% 4.04/1.03    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),k2_relat_1(X2)) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 4.04/1.03    inference(cnf_transformation,[],[f36])).
% 4.04/1.03  
% 4.04/1.03  fof(f56,plain,(
% 4.04/1.03    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 4.04/1.03    inference(cnf_transformation,[],[f36])).
% 4.04/1.03  
% 4.04/1.03  fof(f43,plain,(
% 4.04/1.03    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 4.04/1.03    inference(cnf_transformation,[],[f24])).
% 4.04/1.03  
% 4.04/1.03  fof(f6,axiom,(
% 4.04/1.03    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 4.04/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.04/1.03  
% 4.04/1.03  fof(f17,plain,(
% 4.04/1.03    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 4.04/1.03    inference(ennf_transformation,[],[f6])).
% 4.04/1.03  
% 4.04/1.03  fof(f29,plain,(
% 4.04/1.03    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 4.04/1.03    inference(nnf_transformation,[],[f17])).
% 4.04/1.03  
% 4.04/1.03  fof(f30,plain,(
% 4.04/1.03    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 4.04/1.03    inference(rectify,[],[f29])).
% 4.04/1.03  
% 4.04/1.03  fof(f31,plain,(
% 4.04/1.03    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2) & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2))))),
% 4.04/1.03    introduced(choice_axiom,[])).
% 4.04/1.03  
% 4.04/1.03  fof(f32,plain,(
% 4.04/1.03    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2) & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 4.04/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f31])).
% 4.04/1.03  
% 4.04/1.03  fof(f50,plain,(
% 4.04/1.03    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 4.04/1.03    inference(cnf_transformation,[],[f32])).
% 4.04/1.03  
% 4.04/1.03  fof(f9,axiom,(
% 4.04/1.03    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 4.04/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.04/1.03  
% 4.04/1.03  fof(f20,plain,(
% 4.04/1.03    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 4.04/1.03    inference(ennf_transformation,[],[f9])).
% 4.04/1.03  
% 4.04/1.03  fof(f21,plain,(
% 4.04/1.03    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 4.04/1.03    inference(flattening,[],[f20])).
% 4.04/1.03  
% 4.04/1.03  fof(f59,plain,(
% 4.04/1.03    ( ! [X2,X0,X1] : (r2_hidden(X1,k2_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 4.04/1.03    inference(cnf_transformation,[],[f21])).
% 4.04/1.03  
% 4.04/1.03  fof(f57,plain,(
% 4.04/1.03    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,k10_relat_1(X2,X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 4.04/1.03    inference(cnf_transformation,[],[f36])).
% 4.04/1.03  
% 4.04/1.03  fof(f4,axiom,(
% 4.04/1.03    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 4.04/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.04/1.03  
% 4.04/1.03  fof(f47,plain,(
% 4.04/1.03    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 4.04/1.03    inference(cnf_transformation,[],[f4])).
% 4.04/1.03  
% 4.04/1.03  fof(f2,axiom,(
% 4.04/1.03    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 4.04/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.04/1.03  
% 4.04/1.03  fof(f13,plain,(
% 4.04/1.03    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 4.04/1.03    inference(rectify,[],[f2])).
% 4.04/1.03  
% 4.04/1.03  fof(f15,plain,(
% 4.04/1.03    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 4.04/1.03    inference(ennf_transformation,[],[f13])).
% 4.04/1.03  
% 4.04/1.03  fof(f25,plain,(
% 4.04/1.03    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 4.04/1.03    introduced(choice_axiom,[])).
% 4.04/1.03  
% 4.04/1.03  fof(f26,plain,(
% 4.04/1.03    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 4.04/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f25])).
% 4.04/1.03  
% 4.04/1.03  fof(f45,plain,(
% 4.04/1.03    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 4.04/1.03    inference(cnf_transformation,[],[f26])).
% 4.04/1.03  
% 4.04/1.03  fof(f5,axiom,(
% 4.04/1.03    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 4.04/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.04/1.03  
% 4.04/1.03  fof(f48,plain,(
% 4.04/1.03    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 4.04/1.03    inference(cnf_transformation,[],[f5])).
% 4.04/1.03  
% 4.04/1.03  fof(f62,plain,(
% 4.04/1.03    ~r1_xboole_0(k2_relat_1(sK6),sK5) | k1_xboole_0 != k10_relat_1(sK6,sK5)),
% 4.04/1.03    inference(cnf_transformation,[],[f40])).
% 4.04/1.03  
% 4.04/1.03  cnf(c_2,plain,
% 4.04/1.03      ( r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1) ),
% 4.04/1.03      inference(cnf_transformation,[],[f41]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_1500,plain,
% 4.04/1.03      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 4.04/1.03      | r1_xboole_0(X0,X1) = iProver_top ),
% 4.04/1.03      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_1,plain,
% 4.04/1.03      ( r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1) ),
% 4.04/1.03      inference(cnf_transformation,[],[f42]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_1501,plain,
% 4.04/1.03      ( r2_hidden(sK0(X0,X1),X1) = iProver_top
% 4.04/1.03      | r1_xboole_0(X0,X1) = iProver_top ),
% 4.04/1.03      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_12,plain,
% 4.04/1.03      ( ~ v1_relat_1(X0)
% 4.04/1.03      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 4.04/1.03      inference(cnf_transformation,[],[f53]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_21,negated_conjecture,
% 4.04/1.03      ( v1_relat_1(sK6) ),
% 4.04/1.03      inference(cnf_transformation,[],[f60]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_426,plain,
% 4.04/1.03      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | sK6 != X0 ),
% 4.04/1.03      inference(resolution_lifted,[status(thm)],[c_12,c_21]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_427,plain,
% 4.04/1.03      ( k9_relat_1(sK6,k1_relat_1(sK6)) = k2_relat_1(sK6) ),
% 4.04/1.03      inference(unflattening,[status(thm)],[c_426]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_20,negated_conjecture,
% 4.04/1.03      ( r1_xboole_0(k2_relat_1(sK6),sK5)
% 4.04/1.03      | k1_xboole_0 = k10_relat_1(sK6,sK5) ),
% 4.04/1.03      inference(cnf_transformation,[],[f61]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_1494,plain,
% 4.04/1.03      ( k1_xboole_0 = k10_relat_1(sK6,sK5)
% 4.04/1.03      | r1_xboole_0(k2_relat_1(sK6),sK5) = iProver_top ),
% 4.04/1.03      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_5,plain,
% 4.04/1.03      ( r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0 ),
% 4.04/1.03      inference(cnf_transformation,[],[f46]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_1497,plain,
% 4.04/1.03      ( k1_xboole_0 = X0 | r2_hidden(sK2(X0),X0) = iProver_top ),
% 4.04/1.03      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_16,plain,
% 4.04/1.03      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 4.04/1.03      | r2_hidden(sK4(X0,X2,X1),k2_relat_1(X1))
% 4.04/1.03      | ~ v1_relat_1(X1) ),
% 4.04/1.03      inference(cnf_transformation,[],[f54]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_354,plain,
% 4.04/1.03      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 4.04/1.03      | r2_hidden(sK4(X0,X2,X1),k2_relat_1(X1))
% 4.04/1.03      | sK6 != X1 ),
% 4.04/1.03      inference(resolution_lifted,[status(thm)],[c_16,c_21]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_355,plain,
% 4.04/1.03      ( ~ r2_hidden(X0,k10_relat_1(sK6,X1))
% 4.04/1.03      | r2_hidden(sK4(X0,X1,sK6),k2_relat_1(sK6)) ),
% 4.04/1.03      inference(unflattening,[status(thm)],[c_354]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_1489,plain,
% 4.04/1.03      ( r2_hidden(X0,k10_relat_1(sK6,X1)) != iProver_top
% 4.04/1.03      | r2_hidden(sK4(X0,X1,sK6),k2_relat_1(sK6)) = iProver_top ),
% 4.04/1.03      inference(predicate_to_equality,[status(thm)],[c_355]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_14,plain,
% 4.04/1.03      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 4.04/1.03      | r2_hidden(sK4(X0,X2,X1),X2)
% 4.04/1.03      | ~ v1_relat_1(X1) ),
% 4.04/1.03      inference(cnf_transformation,[],[f56]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_378,plain,
% 4.04/1.03      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 4.04/1.03      | r2_hidden(sK4(X0,X2,X1),X2)
% 4.04/1.03      | sK6 != X1 ),
% 4.04/1.03      inference(resolution_lifted,[status(thm)],[c_14,c_21]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_379,plain,
% 4.04/1.03      ( ~ r2_hidden(X0,k10_relat_1(sK6,X1))
% 4.04/1.03      | r2_hidden(sK4(X0,X1,sK6),X1) ),
% 4.04/1.03      inference(unflattening,[status(thm)],[c_378]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_1487,plain,
% 4.04/1.03      ( r2_hidden(X0,k10_relat_1(sK6,X1)) != iProver_top
% 4.04/1.03      | r2_hidden(sK4(X0,X1,sK6),X1) = iProver_top ),
% 4.04/1.03      inference(predicate_to_equality,[status(thm)],[c_379]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_0,plain,
% 4.04/1.03      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 4.04/1.03      inference(cnf_transformation,[],[f43]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_1502,plain,
% 4.04/1.03      ( r2_hidden(X0,X1) != iProver_top
% 4.04/1.03      | r2_hidden(X0,X2) != iProver_top
% 4.04/1.03      | r1_xboole_0(X2,X1) != iProver_top ),
% 4.04/1.03      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_2347,plain,
% 4.04/1.03      ( r2_hidden(X0,k10_relat_1(sK6,X1)) != iProver_top
% 4.04/1.03      | r2_hidden(sK4(X0,X1,sK6),X2) != iProver_top
% 4.04/1.03      | r1_xboole_0(X2,X1) != iProver_top ),
% 4.04/1.03      inference(superposition,[status(thm)],[c_1487,c_1502]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_6563,plain,
% 4.04/1.03      ( r2_hidden(X0,k10_relat_1(sK6,X1)) != iProver_top
% 4.04/1.03      | r1_xboole_0(k2_relat_1(sK6),X1) != iProver_top ),
% 4.04/1.03      inference(superposition,[status(thm)],[c_1489,c_2347]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_6774,plain,
% 4.04/1.03      ( k10_relat_1(sK6,X0) = k1_xboole_0
% 4.04/1.03      | r1_xboole_0(k2_relat_1(sK6),X0) != iProver_top ),
% 4.04/1.03      inference(superposition,[status(thm)],[c_1497,c_6563]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_9185,plain,
% 4.04/1.03      ( k10_relat_1(sK6,sK5) = k1_xboole_0 ),
% 4.04/1.03      inference(superposition,[status(thm)],[c_1494,c_6774]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_10,plain,
% 4.04/1.03      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 4.04/1.03      | r2_hidden(k4_tarski(sK3(X0,X2,X1),X0),X1)
% 4.04/1.03      | ~ v1_relat_1(X1) ),
% 4.04/1.03      inference(cnf_transformation,[],[f50]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_402,plain,
% 4.04/1.03      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 4.04/1.03      | r2_hidden(k4_tarski(sK3(X0,X2,X1),X0),X1)
% 4.04/1.03      | sK6 != X1 ),
% 4.04/1.03      inference(resolution_lifted,[status(thm)],[c_10,c_21]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_403,plain,
% 4.04/1.03      ( ~ r2_hidden(X0,k9_relat_1(sK6,X1))
% 4.04/1.03      | r2_hidden(k4_tarski(sK3(X0,X1,sK6),X0),sK6) ),
% 4.04/1.03      inference(unflattening,[status(thm)],[c_402]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_1485,plain,
% 4.04/1.03      ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 4.04/1.03      | r2_hidden(k4_tarski(sK3(X0,X1,sK6),X0),sK6) = iProver_top ),
% 4.04/1.03      inference(predicate_to_equality,[status(thm)],[c_403]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_17,plain,
% 4.04/1.03      ( r2_hidden(X0,k2_relat_1(X1))
% 4.04/1.03      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 4.04/1.03      | ~ v1_relat_1(X1) ),
% 4.04/1.03      inference(cnf_transformation,[],[f59]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_338,plain,
% 4.04/1.03      ( r2_hidden(X0,k2_relat_1(X1))
% 4.04/1.03      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 4.04/1.03      | sK6 != X1 ),
% 4.04/1.03      inference(resolution_lifted,[status(thm)],[c_17,c_21]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_339,plain,
% 4.04/1.03      ( r2_hidden(X0,k2_relat_1(sK6))
% 4.04/1.03      | ~ r2_hidden(k4_tarski(X1,X0),sK6) ),
% 4.04/1.03      inference(unflattening,[status(thm)],[c_338]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_13,plain,
% 4.04/1.03      ( ~ r2_hidden(X0,X1)
% 4.04/1.03      | r2_hidden(X2,k10_relat_1(X3,X1))
% 4.04/1.03      | ~ r2_hidden(X0,k2_relat_1(X3))
% 4.04/1.03      | ~ r2_hidden(k4_tarski(X2,X0),X3)
% 4.04/1.03      | ~ v1_relat_1(X3) ),
% 4.04/1.03      inference(cnf_transformation,[],[f57]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_286,plain,
% 4.04/1.03      ( ~ r2_hidden(X0,X1)
% 4.04/1.03      | r2_hidden(X2,k10_relat_1(X3,X1))
% 4.04/1.03      | ~ r2_hidden(X0,k2_relat_1(X3))
% 4.04/1.03      | ~ r2_hidden(k4_tarski(X2,X0),X3)
% 4.04/1.03      | sK6 != X3 ),
% 4.04/1.03      inference(resolution_lifted,[status(thm)],[c_13,c_21]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_287,plain,
% 4.04/1.03      ( ~ r2_hidden(X0,X1)
% 4.04/1.03      | r2_hidden(X2,k10_relat_1(sK6,X1))
% 4.04/1.03      | ~ r2_hidden(X0,k2_relat_1(sK6))
% 4.04/1.03      | ~ r2_hidden(k4_tarski(X2,X0),sK6) ),
% 4.04/1.03      inference(unflattening,[status(thm)],[c_286]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_348,plain,
% 4.04/1.03      ( ~ r2_hidden(X0,X1)
% 4.04/1.03      | r2_hidden(X2,k10_relat_1(sK6,X1))
% 4.04/1.03      | ~ r2_hidden(k4_tarski(X2,X0),sK6) ),
% 4.04/1.03      inference(backward_subsumption_resolution,
% 4.04/1.03                [status(thm)],
% 4.04/1.03                [c_339,c_287]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_1490,plain,
% 4.04/1.03      ( r2_hidden(X0,X1) != iProver_top
% 4.04/1.03      | r2_hidden(X2,k10_relat_1(sK6,X1)) = iProver_top
% 4.04/1.03      | r2_hidden(k4_tarski(X2,X0),sK6) != iProver_top ),
% 4.04/1.03      inference(predicate_to_equality,[status(thm)],[c_348]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_2143,plain,
% 4.04/1.03      ( r2_hidden(X0,X1) != iProver_top
% 4.04/1.03      | r2_hidden(X0,k9_relat_1(sK6,X2)) != iProver_top
% 4.04/1.03      | r2_hidden(sK3(X0,X2,sK6),k10_relat_1(sK6,X1)) = iProver_top ),
% 4.04/1.03      inference(superposition,[status(thm)],[c_1485,c_1490]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_9516,plain,
% 4.04/1.03      ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 4.04/1.03      | r2_hidden(X0,sK5) != iProver_top
% 4.04/1.03      | r2_hidden(sK3(X0,X1,sK6),k1_xboole_0) = iProver_top ),
% 4.04/1.03      inference(superposition,[status(thm)],[c_9185,c_2143]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_6,plain,
% 4.04/1.03      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 4.04/1.03      inference(cnf_transformation,[],[f47]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_3,plain,
% 4.04/1.03      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2)) | ~ r1_xboole_0(X1,X2) ),
% 4.04/1.03      inference(cnf_transformation,[],[f45]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_1499,plain,
% 4.04/1.03      ( r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top
% 4.04/1.03      | r1_xboole_0(X1,X2) != iProver_top ),
% 4.04/1.03      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_2219,plain,
% 4.04/1.03      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 4.04/1.03      | r1_xboole_0(X1,k1_xboole_0) != iProver_top ),
% 4.04/1.03      inference(superposition,[status(thm)],[c_6,c_1499]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_7,plain,
% 4.04/1.03      ( r1_xboole_0(X0,k1_xboole_0) ),
% 4.04/1.03      inference(cnf_transformation,[],[f48]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_1496,plain,
% 4.04/1.03      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 4.04/1.03      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_2317,plain,
% 4.04/1.03      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 4.04/1.03      inference(forward_subsumption_resolution,
% 4.04/1.03                [status(thm)],
% 4.04/1.03                [c_2219,c_1496]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_13039,plain,
% 4.04/1.03      ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 4.04/1.03      | r2_hidden(X0,sK5) != iProver_top ),
% 4.04/1.03      inference(forward_subsumption_resolution,
% 4.04/1.03                [status(thm)],
% 4.04/1.03                [c_9516,c_2317]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_13048,plain,
% 4.04/1.03      ( r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
% 4.04/1.03      | r2_hidden(X0,sK5) != iProver_top ),
% 4.04/1.03      inference(superposition,[status(thm)],[c_427,c_13039]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_13091,plain,
% 4.04/1.03      ( r2_hidden(sK0(X0,k2_relat_1(sK6)),sK5) != iProver_top
% 4.04/1.03      | r1_xboole_0(X0,k2_relat_1(sK6)) = iProver_top ),
% 4.04/1.03      inference(superposition,[status(thm)],[c_1501,c_13048]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_13201,plain,
% 4.04/1.03      ( r1_xboole_0(sK5,k2_relat_1(sK6)) = iProver_top ),
% 4.04/1.03      inference(superposition,[status(thm)],[c_1500,c_13091]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_1678,plain,
% 4.04/1.03      ( ~ r2_hidden(sK0(k2_relat_1(sK6),sK5),X0)
% 4.04/1.03      | ~ r2_hidden(sK0(k2_relat_1(sK6),sK5),k2_relat_1(sK6))
% 4.04/1.03      | ~ r1_xboole_0(X0,k2_relat_1(sK6)) ),
% 4.04/1.03      inference(instantiation,[status(thm)],[c_0]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_1934,plain,
% 4.04/1.03      ( ~ r2_hidden(sK0(k2_relat_1(sK6),sK5),k2_relat_1(sK6))
% 4.04/1.03      | ~ r2_hidden(sK0(k2_relat_1(sK6),sK5),sK5)
% 4.04/1.03      | ~ r1_xboole_0(sK5,k2_relat_1(sK6)) ),
% 4.04/1.03      inference(instantiation,[status(thm)],[c_1678]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_1935,plain,
% 4.04/1.03      ( r2_hidden(sK0(k2_relat_1(sK6),sK5),k2_relat_1(sK6)) != iProver_top
% 4.04/1.03      | r2_hidden(sK0(k2_relat_1(sK6),sK5),sK5) != iProver_top
% 4.04/1.03      | r1_xboole_0(sK5,k2_relat_1(sK6)) != iProver_top ),
% 4.04/1.03      inference(predicate_to_equality,[status(thm)],[c_1934]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_19,negated_conjecture,
% 4.04/1.03      ( ~ r1_xboole_0(k2_relat_1(sK6),sK5)
% 4.04/1.03      | k1_xboole_0 != k10_relat_1(sK6,sK5) ),
% 4.04/1.03      inference(cnf_transformation,[],[f62]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_166,plain,
% 4.04/1.03      ( ~ r1_xboole_0(k2_relat_1(sK6),sK5)
% 4.04/1.03      | k1_xboole_0 != k10_relat_1(sK6,sK5) ),
% 4.04/1.03      inference(prop_impl,[status(thm)],[c_19]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_562,plain,
% 4.04/1.03      ( r2_hidden(sK0(X0,X1),X1)
% 4.04/1.03      | k10_relat_1(sK6,sK5) != k1_xboole_0
% 4.04/1.03      | k2_relat_1(sK6) != X0
% 4.04/1.03      | sK5 != X1 ),
% 4.04/1.03      inference(resolution_lifted,[status(thm)],[c_1,c_166]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_563,plain,
% 4.04/1.03      ( r2_hidden(sK0(k2_relat_1(sK6),sK5),sK5)
% 4.04/1.03      | k10_relat_1(sK6,sK5) != k1_xboole_0 ),
% 4.04/1.03      inference(unflattening,[status(thm)],[c_562]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_564,plain,
% 4.04/1.03      ( k10_relat_1(sK6,sK5) != k1_xboole_0
% 4.04/1.03      | r2_hidden(sK0(k2_relat_1(sK6),sK5),sK5) = iProver_top ),
% 4.04/1.03      inference(predicate_to_equality,[status(thm)],[c_563]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_552,plain,
% 4.04/1.03      ( r2_hidden(sK0(X0,X1),X0)
% 4.04/1.03      | k10_relat_1(sK6,sK5) != k1_xboole_0
% 4.04/1.03      | k2_relat_1(sK6) != X0
% 4.04/1.03      | sK5 != X1 ),
% 4.04/1.03      inference(resolution_lifted,[status(thm)],[c_2,c_166]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_553,plain,
% 4.04/1.03      ( r2_hidden(sK0(k2_relat_1(sK6),sK5),k2_relat_1(sK6))
% 4.04/1.03      | k10_relat_1(sK6,sK5) != k1_xboole_0 ),
% 4.04/1.03      inference(unflattening,[status(thm)],[c_552]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_554,plain,
% 4.04/1.03      ( k10_relat_1(sK6,sK5) != k1_xboole_0
% 4.04/1.03      | r2_hidden(sK0(k2_relat_1(sK6),sK5),k2_relat_1(sK6)) = iProver_top ),
% 4.04/1.03      inference(predicate_to_equality,[status(thm)],[c_553]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(contradiction,plain,
% 4.04/1.03      ( $false ),
% 4.04/1.03      inference(minisat,[status(thm)],[c_13201,c_9185,c_1935,c_564,c_554]) ).
% 4.04/1.03  
% 4.04/1.03  
% 4.04/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 4.04/1.03  
% 4.04/1.03  ------                               Statistics
% 4.04/1.03  
% 4.04/1.03  ------ General
% 4.04/1.03  
% 4.04/1.03  abstr_ref_over_cycles:                  0
% 4.04/1.03  abstr_ref_under_cycles:                 0
% 4.04/1.03  gc_basic_clause_elim:                   0
% 4.04/1.03  forced_gc_time:                         0
% 4.04/1.03  parsing_time:                           0.016
% 4.04/1.03  unif_index_cands_time:                  0.
% 4.04/1.03  unif_index_add_time:                    0.
% 4.04/1.03  orderings_time:                         0.
% 4.04/1.03  out_proof_time:                         0.013
% 4.04/1.03  total_time:                             0.5
% 4.04/1.03  num_of_symbols:                         48
% 4.04/1.03  num_of_terms:                           9526
% 4.04/1.03  
% 4.04/1.03  ------ Preprocessing
% 4.04/1.03  
% 4.04/1.03  num_of_splits:                          0
% 4.04/1.03  num_of_split_atoms:                     0
% 4.04/1.03  num_of_reused_defs:                     0
% 4.04/1.03  num_eq_ax_congr_red:                    34
% 4.04/1.03  num_of_sem_filtered_clauses:            1
% 4.04/1.03  num_of_subtypes:                        0
% 4.04/1.03  monotx_restored_types:                  0
% 4.04/1.03  sat_num_of_epr_types:                   0
% 4.04/1.03  sat_num_of_non_cyclic_types:            0
% 4.04/1.03  sat_guarded_non_collapsed_types:        0
% 4.04/1.03  num_pure_diseq_elim:                    0
% 4.04/1.03  simp_replaced_by:                       0
% 4.04/1.03  res_preprocessed:                       110
% 4.04/1.03  prep_upred:                             0
% 4.04/1.03  prep_unflattend:                        65
% 4.04/1.03  smt_new_axioms:                         0
% 4.04/1.03  pred_elim_cands:                        2
% 4.04/1.03  pred_elim:                              1
% 4.04/1.03  pred_elim_cl:                           1
% 4.04/1.03  pred_elim_cycles:                       3
% 4.04/1.03  merged_defs:                            8
% 4.04/1.03  merged_defs_ncl:                        0
% 4.04/1.03  bin_hyper_res:                          8
% 4.04/1.03  prep_cycles:                            4
% 4.04/1.03  pred_elim_time:                         0.013
% 4.04/1.03  splitting_time:                         0.
% 4.04/1.03  sem_filter_time:                        0.
% 4.04/1.03  monotx_time:                            0.
% 4.04/1.03  subtype_inf_time:                       0.
% 4.04/1.03  
% 4.04/1.03  ------ Problem properties
% 4.04/1.03  
% 4.04/1.03  clauses:                                21
% 4.04/1.03  conjectures:                            2
% 4.04/1.03  epr:                                    2
% 4.04/1.03  horn:                                   16
% 4.04/1.03  ground:                                 3
% 4.04/1.03  unary:                                  3
% 4.04/1.03  binary:                                 15
% 4.04/1.03  lits:                                   42
% 4.04/1.03  lits_eq:                                5
% 4.04/1.03  fd_pure:                                0
% 4.04/1.03  fd_pseudo:                              0
% 4.04/1.03  fd_cond:                                1
% 4.04/1.03  fd_pseudo_cond:                         0
% 4.04/1.03  ac_symbols:                             0
% 4.04/1.03  
% 4.04/1.03  ------ Propositional Solver
% 4.04/1.03  
% 4.04/1.03  prop_solver_calls:                      30
% 4.04/1.03  prop_fast_solver_calls:                 938
% 4.04/1.03  smt_solver_calls:                       0
% 4.04/1.03  smt_fast_solver_calls:                  0
% 4.04/1.03  prop_num_of_clauses:                    4741
% 4.04/1.03  prop_preprocess_simplified:             7363
% 4.04/1.03  prop_fo_subsumed:                       4
% 4.04/1.03  prop_solver_time:                       0.
% 4.04/1.03  smt_solver_time:                        0.
% 4.04/1.03  smt_fast_solver_time:                   0.
% 4.04/1.03  prop_fast_solver_time:                  0.
% 4.04/1.03  prop_unsat_core_time:                   0.
% 4.04/1.03  
% 4.04/1.03  ------ QBF
% 4.04/1.03  
% 4.04/1.03  qbf_q_res:                              0
% 4.04/1.03  qbf_num_tautologies:                    0
% 4.04/1.03  qbf_prep_cycles:                        0
% 4.04/1.03  
% 4.04/1.03  ------ BMC1
% 4.04/1.03  
% 4.04/1.03  bmc1_current_bound:                     -1
% 4.04/1.03  bmc1_last_solved_bound:                 -1
% 4.04/1.03  bmc1_unsat_core_size:                   -1
% 4.04/1.03  bmc1_unsat_core_parents_size:           -1
% 4.04/1.03  bmc1_merge_next_fun:                    0
% 4.04/1.03  bmc1_unsat_core_clauses_time:           0.
% 4.04/1.03  
% 4.04/1.03  ------ Instantiation
% 4.04/1.03  
% 4.04/1.03  inst_num_of_clauses:                    1042
% 4.04/1.03  inst_num_in_passive:                    141
% 4.04/1.03  inst_num_in_active:                     524
% 4.04/1.03  inst_num_in_unprocessed:                377
% 4.04/1.03  inst_num_of_loops:                      790
% 4.04/1.03  inst_num_of_learning_restarts:          0
% 4.04/1.03  inst_num_moves_active_passive:          260
% 4.04/1.03  inst_lit_activity:                      0
% 4.04/1.03  inst_lit_activity_moves:                0
% 4.04/1.03  inst_num_tautologies:                   0
% 4.04/1.03  inst_num_prop_implied:                  0
% 4.04/1.03  inst_num_existing_simplified:           0
% 4.04/1.03  inst_num_eq_res_simplified:             0
% 4.04/1.03  inst_num_child_elim:                    0
% 4.04/1.03  inst_num_of_dismatching_blockings:      330
% 4.04/1.03  inst_num_of_non_proper_insts:           900
% 4.04/1.03  inst_num_of_duplicates:                 0
% 4.04/1.03  inst_inst_num_from_inst_to_res:         0
% 4.04/1.03  inst_dismatching_checking_time:         0.
% 4.04/1.03  
% 4.04/1.03  ------ Resolution
% 4.04/1.03  
% 4.04/1.03  res_num_of_clauses:                     0
% 4.04/1.03  res_num_in_passive:                     0
% 4.04/1.03  res_num_in_active:                      0
% 4.04/1.03  res_num_of_loops:                       114
% 4.04/1.03  res_forward_subset_subsumed:            55
% 4.04/1.03  res_backward_subset_subsumed:           0
% 4.04/1.03  res_forward_subsumed:                   0
% 4.04/1.03  res_backward_subsumed:                  0
% 4.04/1.03  res_forward_subsumption_resolution:     0
% 4.04/1.03  res_backward_subsumption_resolution:    2
% 4.04/1.03  res_clause_to_clause_subsumption:       1701
% 4.04/1.03  res_orphan_elimination:                 0
% 4.04/1.03  res_tautology_del:                      162
% 4.04/1.03  res_num_eq_res_simplified:              0
% 4.04/1.03  res_num_sel_changes:                    0
% 4.04/1.03  res_moves_from_active_to_pass:          0
% 4.04/1.03  
% 4.04/1.03  ------ Superposition
% 4.04/1.03  
% 4.04/1.03  sup_time_total:                         0.
% 4.04/1.03  sup_time_generating:                    0.
% 4.04/1.03  sup_time_sim_full:                      0.
% 4.04/1.03  sup_time_sim_immed:                     0.
% 4.04/1.03  
% 4.04/1.03  sup_num_of_clauses:                     551
% 4.04/1.03  sup_num_in_active:                      145
% 4.04/1.03  sup_num_in_passive:                     406
% 4.04/1.03  sup_num_of_loops:                       157
% 4.04/1.03  sup_fw_superposition:                   741
% 4.04/1.03  sup_bw_superposition:                   148
% 4.04/1.03  sup_immediate_simplified:               267
% 4.04/1.03  sup_given_eliminated:                   10
% 4.04/1.03  comparisons_done:                       0
% 4.04/1.03  comparisons_avoided:                    0
% 4.04/1.03  
% 4.04/1.03  ------ Simplifications
% 4.04/1.03  
% 4.04/1.03  
% 4.04/1.03  sim_fw_subset_subsumed:                 89
% 4.04/1.03  sim_bw_subset_subsumed:                 2
% 4.04/1.03  sim_fw_subsumed:                        121
% 4.04/1.03  sim_bw_subsumed:                        1
% 4.04/1.03  sim_fw_subsumption_res:                 2
% 4.04/1.03  sim_bw_subsumption_res:                 0
% 4.04/1.03  sim_tautology_del:                      5
% 4.04/1.03  sim_eq_tautology_del:                   12
% 4.04/1.03  sim_eq_res_simp:                        1
% 4.04/1.03  sim_fw_demodulated:                     1
% 4.04/1.03  sim_bw_demodulated:                     32
% 4.04/1.03  sim_light_normalised:                   135
% 4.04/1.03  sim_joinable_taut:                      0
% 4.04/1.03  sim_joinable_simp:                      0
% 4.04/1.03  sim_ac_normalised:                      0
% 4.04/1.03  sim_smt_subsumption:                    0
% 4.04/1.03  
%------------------------------------------------------------------------------
