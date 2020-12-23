%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:47:34 EST 2020

% Result     : Theorem 6.78s
% Output     : CNFRefutation 6.78s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 398 expanded)
%              Number of clauses        :   72 ( 129 expanded)
%              Number of leaves         :   18 (  81 expanded)
%              Depth                    :   15
%              Number of atoms          :  395 (1504 expanded)
%              Number of equality atoms :   78 ( 358 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   1 average)

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
    inference(rectify,[],[f2])).

fof(f15,plain,(
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

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f24])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k2_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

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

fof(f23,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <~> r1_xboole_0(k2_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f38,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

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
   => ( ( ~ r1_xboole_0(k2_relat_1(sK6),sK5)
        | k1_xboole_0 != k10_relat_1(sK6,sK5) )
      & ( r1_xboole_0(k2_relat_1(sK6),sK5)
        | k1_xboole_0 = k10_relat_1(sK6,sK5) )
      & v1_relat_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ( ~ r1_xboole_0(k2_relat_1(sK6),sK5)
      | k1_xboole_0 != k10_relat_1(sK6,sK5) )
    & ( r1_xboole_0(k2_relat_1(sK6),sK5)
      | k1_xboole_0 = k10_relat_1(sK6,sK5) )
    & v1_relat_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f39,f40])).

fof(f61,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f41])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

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
    inference(nnf_transformation,[],[f20])).

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
     => ( r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK4(X0,X1,X2)),X2)
        & r2_hidden(sK4(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f36])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X0,X3),X2)
      | ~ r2_hidden(X3,k2_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

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
    inference(nnf_transformation,[],[f18])).

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
     => ( r2_hidden(sK3(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2)
        & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f32])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2))
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f62,plain,
    ( r1_xboole_0(k2_relat_1(sK6),sK5)
    | k1_xboole_0 = k10_relat_1(sK6,sK5) ),
    inference(cnf_transformation,[],[f41])).

fof(f63,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK6),sK5)
    | k1_xboole_0 != k10_relat_1(sK6,sK5) ),
    inference(cnf_transformation,[],[f41])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f28])).

fof(f48,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),k2_relat_1(X2))
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f54,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_668,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3331,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(k1_xboole_0,X2)
    | X1 != X2
    | X0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_668])).

cnf(c_10238,plain,
    ( r1_xboole_0(k10_relat_1(sK6,sK5),X0)
    | ~ r1_xboole_0(k1_xboole_0,X1)
    | X0 != X1
    | k10_relat_1(sK6,sK5) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3331])).

cnf(c_14856,plain,
    ( r1_xboole_0(k10_relat_1(sK6,sK5),k1_relat_1(sK6))
    | ~ r1_xboole_0(k1_xboole_0,X0)
    | k10_relat_1(sK6,sK5) != k1_xboole_0
    | k1_relat_1(sK6) != X0 ),
    inference(instantiation,[status(thm)],[c_10238])).

cnf(c_30611,plain,
    ( r1_xboole_0(k10_relat_1(sK6,sK5),k1_relat_1(sK6))
    | ~ r1_xboole_0(k1_xboole_0,k1_relat_1(sK6))
    | k10_relat_1(sK6,sK5) != k1_xboole_0
    | k1_relat_1(sK6) != k1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_14856])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_5889,plain,
    ( ~ r2_hidden(sK3(sK0(k2_relat_1(sK6),sK5),k1_relat_1(sK6),sK6),X0)
    | ~ r2_hidden(sK3(sK0(k2_relat_1(sK6),sK5),k1_relat_1(sK6),sK6),k1_relat_1(sK6))
    | ~ r1_xboole_0(X0,k1_relat_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_14855,plain,
    ( ~ r2_hidden(sK3(sK0(k2_relat_1(sK6),sK5),k1_relat_1(sK6),sK6),k10_relat_1(sK6,sK5))
    | ~ r2_hidden(sK3(sK0(k2_relat_1(sK6),sK5),k1_relat_1(sK6),sK6),k1_relat_1(sK6))
    | ~ r1_xboole_0(k10_relat_1(sK6,sK5),k1_relat_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_5889])).

cnf(c_7,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_7700,plain,
    ( r1_xboole_0(k1_relat_1(sK6),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_17,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_21,negated_conjecture,
    ( v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_350,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_21])).

cnf(c_351,plain,
    ( r2_hidden(X0,k2_relat_1(sK6))
    | ~ r2_hidden(k4_tarski(X1,X0),sK6) ),
    inference(unflattening,[status(thm)],[c_350])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(X0,k2_relat_1(X3))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_298,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(X0,k2_relat_1(X3))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | sK6 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_21])).

cnf(c_299,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(sK6,X1))
    | ~ r2_hidden(X0,k2_relat_1(sK6))
    | ~ r2_hidden(k4_tarski(X2,X0),sK6) ),
    inference(unflattening,[status(thm)],[c_298])).

cnf(c_360,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(sK6,X1))
    | ~ r2_hidden(k4_tarski(X2,X0),sK6) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_351,c_299])).

cnf(c_1386,plain,
    ( r2_hidden(X0,k10_relat_1(sK6,sK5))
    | ~ r2_hidden(k4_tarski(X0,sK0(k2_relat_1(sK6),sK5)),sK6)
    | ~ r2_hidden(sK0(k2_relat_1(sK6),sK5),sK5) ),
    inference(instantiation,[status(thm)],[c_360])).

cnf(c_5881,plain,
    ( r2_hidden(sK3(sK0(k2_relat_1(sK6),sK5),k1_relat_1(sK6),sK6),k10_relat_1(sK6,sK5))
    | ~ r2_hidden(k4_tarski(sK3(sK0(k2_relat_1(sK6),sK5),k1_relat_1(sK6),sK6),sK0(k2_relat_1(sK6),sK5)),sK6)
    | ~ r2_hidden(sK0(k2_relat_1(sK6),sK5),sK5) ),
    inference(instantiation,[status(thm)],[c_1386])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK3(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_414,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK3(X0,X2,X1),X0),X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_21])).

cnf(c_415,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK6,X1))
    | r2_hidden(k4_tarski(sK3(X0,X1,sK6),X0),sK6) ),
    inference(unflattening,[status(thm)],[c_414])).

cnf(c_3515,plain,
    ( r2_hidden(k4_tarski(sK3(sK0(k2_relat_1(sK6),sK5),k1_relat_1(sK6),sK6),sK0(k2_relat_1(sK6),sK5)),sK6)
    | ~ r2_hidden(sK0(k2_relat_1(sK6),sK5),k9_relat_1(sK6,k1_relat_1(sK6))) ),
    inference(instantiation,[status(thm)],[c_415])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK3(X0,X2,X1),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_402,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK3(X0,X2,X1),k1_relat_1(X1))
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_21])).

cnf(c_403,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK6,X1))
    | r2_hidden(sK3(X0,X1,sK6),k1_relat_1(sK6)) ),
    inference(unflattening,[status(thm)],[c_402])).

cnf(c_3516,plain,
    ( r2_hidden(sK3(sK0(k2_relat_1(sK6),sK5),k1_relat_1(sK6),sK6),k1_relat_1(sK6))
    | ~ r2_hidden(sK0(k2_relat_1(sK6),sK5),k9_relat_1(sK6,k1_relat_1(sK6))) ),
    inference(instantiation,[status(thm)],[c_403])).

cnf(c_0,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_2000,plain,
    ( ~ r1_xboole_0(X0,k1_xboole_0)
    | r1_xboole_0(k1_xboole_0,X0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_3343,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK6),k1_xboole_0)
    | r1_xboole_0(k1_xboole_0,k1_relat_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_2000])).

cnf(c_20,negated_conjecture,
    ( r1_xboole_0(k2_relat_1(sK6),sK5)
    | k1_xboole_0 = k10_relat_1(sK6,sK5) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1151,plain,
    ( k1_xboole_0 = k10_relat_1(sK6,sK5)
    | r1_xboole_0(k2_relat_1(sK6),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1160,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1575,plain,
    ( k10_relat_1(sK6,sK5) = k1_xboole_0
    | r1_xboole_0(sK5,k2_relat_1(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1151,c_1160])).

cnf(c_1728,plain,
    ( k10_relat_1(sK6,sK5) = k1_xboole_0
    | r1_xboole_0(k2_relat_1(sK6),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1575,c_1160])).

cnf(c_19,negated_conjecture,
    ( ~ r1_xboole_0(k2_relat_1(sK6),sK5)
    | k1_xboole_0 != k10_relat_1(sK6,sK5) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_24,plain,
    ( k1_xboole_0 != k10_relat_1(sK6,sK5)
    | r1_xboole_0(k2_relat_1(sK6),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_6,plain,
    ( r2_hidden(sK2(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1322,plain,
    ( r2_hidden(sK2(k10_relat_1(sK6,sK5)),k10_relat_1(sK6,sK5))
    | k1_xboole_0 = k10_relat_1(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK4(X0,X2,X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_366,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK4(X0,X2,X1),k2_relat_1(X1))
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_21])).

cnf(c_367,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK6,X1))
    | r2_hidden(sK4(X0,X1,sK6),k2_relat_1(sK6)) ),
    inference(unflattening,[status(thm)],[c_366])).

cnf(c_1355,plain,
    ( r2_hidden(sK4(sK2(k10_relat_1(sK6,sK5)),sK5,sK6),k2_relat_1(sK6))
    | ~ r2_hidden(sK2(k10_relat_1(sK6,sK5)),k10_relat_1(sK6,sK5)) ),
    inference(instantiation,[status(thm)],[c_367])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK4(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_390,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK4(X0,X2,X1),X2)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_21])).

cnf(c_391,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK6,X1))
    | r2_hidden(sK4(X0,X1,sK6),X1) ),
    inference(unflattening,[status(thm)],[c_390])).

cnf(c_1353,plain,
    ( r2_hidden(sK4(sK2(k10_relat_1(sK6,sK5)),sK5,sK6),sK5)
    | ~ r2_hidden(sK2(k10_relat_1(sK6,sK5)),k10_relat_1(sK6,sK5)) ),
    inference(instantiation,[status(thm)],[c_391])).

cnf(c_1729,plain,
    ( r1_xboole_0(k2_relat_1(sK6),sK5)
    | k10_relat_1(sK6,sK5) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1728])).

cnf(c_1495,plain,
    ( ~ r2_hidden(sK4(sK2(k10_relat_1(sK6,sK5)),sK5,sK6),X0)
    | ~ r2_hidden(sK4(sK2(k10_relat_1(sK6,sK5)),sK5,sK6),sK5)
    | ~ r1_xboole_0(X0,sK5) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2128,plain,
    ( ~ r2_hidden(sK4(sK2(k10_relat_1(sK6,sK5)),sK5,sK6),k2_relat_1(sK6))
    | ~ r2_hidden(sK4(sK2(k10_relat_1(sK6,sK5)),sK5,sK6),sK5)
    | ~ r1_xboole_0(k2_relat_1(sK6),sK5) ),
    inference(instantiation,[status(thm)],[c_1495])).

cnf(c_3055,plain,
    ( k10_relat_1(sK6,sK5) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1728,c_24,c_1322,c_1355,c_1353,c_1729,c_2128])).

cnf(c_1152,plain,
    ( k1_xboole_0 != k10_relat_1(sK6,sK5)
    | r1_xboole_0(k2_relat_1(sK6),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3059,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k2_relat_1(sK6),sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3055,c_1152])).

cnf(c_3060,plain,
    ( r1_xboole_0(k2_relat_1(sK6),sK5) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3059])).

cnf(c_666,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1961,plain,
    ( sK0(k2_relat_1(sK6),sK5) = sK0(k2_relat_1(sK6),sK5) ),
    inference(instantiation,[status(thm)],[c_666])).

cnf(c_669,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1404,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK0(k2_relat_1(sK6),sK5),k2_relat_1(sK6))
    | X0 != sK0(k2_relat_1(sK6),sK5)
    | X1 != k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_669])).

cnf(c_1738,plain,
    ( r2_hidden(X0,k9_relat_1(sK6,k1_relat_1(sK6)))
    | ~ r2_hidden(sK0(k2_relat_1(sK6),sK5),k2_relat_1(sK6))
    | X0 != sK0(k2_relat_1(sK6),sK5)
    | k9_relat_1(sK6,k1_relat_1(sK6)) != k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_1404])).

cnf(c_1960,plain,
    ( r2_hidden(sK0(k2_relat_1(sK6),sK5),k9_relat_1(sK6,k1_relat_1(sK6)))
    | ~ r2_hidden(sK0(k2_relat_1(sK6),sK5),k2_relat_1(sK6))
    | k9_relat_1(sK6,k1_relat_1(sK6)) != k2_relat_1(sK6)
    | sK0(k2_relat_1(sK6),sK5) != sK0(k2_relat_1(sK6),sK5) ),
    inference(instantiation,[status(thm)],[c_1738])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1305,plain,
    ( r2_hidden(sK0(k2_relat_1(sK6),sK5),k2_relat_1(sK6))
    | r1_xboole_0(k2_relat_1(sK6),sK5) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1296,plain,
    ( r2_hidden(sK0(k2_relat_1(sK6),sK5),sK5)
    | r1_xboole_0(k2_relat_1(sK6),sK5) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_687,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_666])).

cnf(c_672,plain,
    ( X0 != X1
    | k1_relat_1(X0) = k1_relat_1(X1) ),
    theory(equality)).

cnf(c_681,plain,
    ( k1_relat_1(sK6) = k1_relat_1(sK6)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_672])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_44,plain,
    ( ~ v1_relat_1(sK6)
    | k9_relat_1(sK6,k1_relat_1(sK6)) = k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_23,plain,
    ( k1_xboole_0 = k10_relat_1(sK6,sK5)
    | r1_xboole_0(k2_relat_1(sK6),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_30611,c_14855,c_7700,c_5881,c_3515,c_3516,c_3343,c_3060,c_3055,c_1961,c_1960,c_1305,c_1296,c_687,c_681,c_44,c_19,c_23,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.33  % Computer   : n004.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 14:45:23 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running in FOF mode
% 6.78/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.78/1.48  
% 6.78/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.78/1.48  
% 6.78/1.48  ------  iProver source info
% 6.78/1.48  
% 6.78/1.48  git: date: 2020-06-30 10:37:57 +0100
% 6.78/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.78/1.48  git: non_committed_changes: false
% 6.78/1.48  git: last_make_outside_of_git: false
% 6.78/1.48  
% 6.78/1.48  ------ 
% 6.78/1.48  
% 6.78/1.48  ------ Input Options
% 6.78/1.48  
% 6.78/1.48  --out_options                           all
% 6.78/1.48  --tptp_safe_out                         true
% 6.78/1.48  --problem_path                          ""
% 6.78/1.48  --include_path                          ""
% 6.78/1.48  --clausifier                            res/vclausify_rel
% 6.78/1.48  --clausifier_options                    --mode clausify
% 6.78/1.48  --stdin                                 false
% 6.78/1.48  --stats_out                             all
% 6.78/1.48  
% 6.78/1.48  ------ General Options
% 6.78/1.48  
% 6.78/1.48  --fof                                   false
% 6.78/1.48  --time_out_real                         305.
% 6.78/1.48  --time_out_virtual                      -1.
% 6.78/1.48  --symbol_type_check                     false
% 6.78/1.48  --clausify_out                          false
% 6.78/1.48  --sig_cnt_out                           false
% 6.78/1.48  --trig_cnt_out                          false
% 6.78/1.48  --trig_cnt_out_tolerance                1.
% 6.78/1.48  --trig_cnt_out_sk_spl                   false
% 6.78/1.48  --abstr_cl_out                          false
% 6.78/1.48  
% 6.78/1.48  ------ Global Options
% 6.78/1.48  
% 6.78/1.48  --schedule                              default
% 6.78/1.48  --add_important_lit                     false
% 6.78/1.48  --prop_solver_per_cl                    1000
% 6.78/1.48  --min_unsat_core                        false
% 6.78/1.48  --soft_assumptions                      false
% 6.78/1.48  --soft_lemma_size                       3
% 6.78/1.48  --prop_impl_unit_size                   0
% 6.78/1.48  --prop_impl_unit                        []
% 6.78/1.48  --share_sel_clauses                     true
% 6.78/1.48  --reset_solvers                         false
% 6.78/1.48  --bc_imp_inh                            [conj_cone]
% 6.78/1.48  --conj_cone_tolerance                   3.
% 6.78/1.48  --extra_neg_conj                        none
% 6.78/1.48  --large_theory_mode                     true
% 6.78/1.48  --prolific_symb_bound                   200
% 6.78/1.48  --lt_threshold                          2000
% 6.78/1.48  --clause_weak_htbl                      true
% 6.78/1.48  --gc_record_bc_elim                     false
% 6.78/1.48  
% 6.78/1.48  ------ Preprocessing Options
% 6.78/1.48  
% 6.78/1.48  --preprocessing_flag                    true
% 6.78/1.48  --time_out_prep_mult                    0.1
% 6.78/1.48  --splitting_mode                        input
% 6.78/1.48  --splitting_grd                         true
% 6.78/1.48  --splitting_cvd                         false
% 6.78/1.48  --splitting_cvd_svl                     false
% 6.78/1.48  --splitting_nvd                         32
% 6.78/1.48  --sub_typing                            true
% 6.78/1.48  --prep_gs_sim                           true
% 6.78/1.48  --prep_unflatten                        true
% 6.78/1.48  --prep_res_sim                          true
% 6.78/1.48  --prep_upred                            true
% 6.78/1.48  --prep_sem_filter                       exhaustive
% 6.78/1.48  --prep_sem_filter_out                   false
% 6.78/1.48  --pred_elim                             true
% 6.78/1.48  --res_sim_input                         true
% 6.78/1.48  --eq_ax_congr_red                       true
% 6.78/1.48  --pure_diseq_elim                       true
% 6.78/1.48  --brand_transform                       false
% 6.78/1.48  --non_eq_to_eq                          false
% 6.78/1.48  --prep_def_merge                        true
% 6.78/1.48  --prep_def_merge_prop_impl              false
% 6.78/1.48  --prep_def_merge_mbd                    true
% 6.78/1.48  --prep_def_merge_tr_red                 false
% 6.78/1.48  --prep_def_merge_tr_cl                  false
% 6.78/1.48  --smt_preprocessing                     true
% 6.78/1.48  --smt_ac_axioms                         fast
% 6.78/1.48  --preprocessed_out                      false
% 6.78/1.48  --preprocessed_stats                    false
% 6.78/1.48  
% 6.78/1.48  ------ Abstraction refinement Options
% 6.78/1.48  
% 6.78/1.48  --abstr_ref                             []
% 6.78/1.48  --abstr_ref_prep                        false
% 6.78/1.48  --abstr_ref_until_sat                   false
% 6.78/1.48  --abstr_ref_sig_restrict                funpre
% 6.78/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 6.78/1.48  --abstr_ref_under                       []
% 6.78/1.48  
% 6.78/1.48  ------ SAT Options
% 6.78/1.48  
% 6.78/1.48  --sat_mode                              false
% 6.78/1.48  --sat_fm_restart_options                ""
% 6.78/1.48  --sat_gr_def                            false
% 6.78/1.48  --sat_epr_types                         true
% 6.78/1.48  --sat_non_cyclic_types                  false
% 6.78/1.48  --sat_finite_models                     false
% 6.78/1.48  --sat_fm_lemmas                         false
% 6.78/1.48  --sat_fm_prep                           false
% 6.78/1.48  --sat_fm_uc_incr                        true
% 6.78/1.48  --sat_out_model                         small
% 6.78/1.48  --sat_out_clauses                       false
% 6.78/1.48  
% 6.78/1.48  ------ QBF Options
% 6.78/1.48  
% 6.78/1.48  --qbf_mode                              false
% 6.78/1.48  --qbf_elim_univ                         false
% 6.78/1.48  --qbf_dom_inst                          none
% 6.78/1.48  --qbf_dom_pre_inst                      false
% 6.78/1.48  --qbf_sk_in                             false
% 6.78/1.48  --qbf_pred_elim                         true
% 6.78/1.48  --qbf_split                             512
% 6.78/1.48  
% 6.78/1.48  ------ BMC1 Options
% 6.78/1.48  
% 6.78/1.48  --bmc1_incremental                      false
% 6.78/1.48  --bmc1_axioms                           reachable_all
% 6.78/1.48  --bmc1_min_bound                        0
% 6.78/1.48  --bmc1_max_bound                        -1
% 6.78/1.48  --bmc1_max_bound_default                -1
% 6.78/1.48  --bmc1_symbol_reachability              true
% 6.78/1.48  --bmc1_property_lemmas                  false
% 6.78/1.48  --bmc1_k_induction                      false
% 6.78/1.48  --bmc1_non_equiv_states                 false
% 6.78/1.48  --bmc1_deadlock                         false
% 6.78/1.48  --bmc1_ucm                              false
% 6.78/1.48  --bmc1_add_unsat_core                   none
% 6.78/1.48  --bmc1_unsat_core_children              false
% 6.78/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 6.78/1.48  --bmc1_out_stat                         full
% 6.78/1.48  --bmc1_ground_init                      false
% 6.78/1.48  --bmc1_pre_inst_next_state              false
% 6.78/1.48  --bmc1_pre_inst_state                   false
% 6.78/1.48  --bmc1_pre_inst_reach_state             false
% 6.78/1.48  --bmc1_out_unsat_core                   false
% 6.78/1.48  --bmc1_aig_witness_out                  false
% 6.78/1.48  --bmc1_verbose                          false
% 6.78/1.48  --bmc1_dump_clauses_tptp                false
% 6.78/1.48  --bmc1_dump_unsat_core_tptp             false
% 6.78/1.48  --bmc1_dump_file                        -
% 6.78/1.48  --bmc1_ucm_expand_uc_limit              128
% 6.78/1.48  --bmc1_ucm_n_expand_iterations          6
% 6.78/1.48  --bmc1_ucm_extend_mode                  1
% 6.78/1.48  --bmc1_ucm_init_mode                    2
% 6.78/1.48  --bmc1_ucm_cone_mode                    none
% 6.78/1.48  --bmc1_ucm_reduced_relation_type        0
% 6.78/1.48  --bmc1_ucm_relax_model                  4
% 6.78/1.48  --bmc1_ucm_full_tr_after_sat            true
% 6.78/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 6.78/1.48  --bmc1_ucm_layered_model                none
% 6.78/1.48  --bmc1_ucm_max_lemma_size               10
% 6.78/1.48  
% 6.78/1.48  ------ AIG Options
% 6.78/1.48  
% 6.78/1.48  --aig_mode                              false
% 6.78/1.48  
% 6.78/1.48  ------ Instantiation Options
% 6.78/1.48  
% 6.78/1.48  --instantiation_flag                    true
% 6.78/1.48  --inst_sos_flag                         false
% 6.78/1.48  --inst_sos_phase                        true
% 6.78/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.78/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.78/1.48  --inst_lit_sel_side                     num_symb
% 6.78/1.48  --inst_solver_per_active                1400
% 6.78/1.48  --inst_solver_calls_frac                1.
% 6.78/1.48  --inst_passive_queue_type               priority_queues
% 6.78/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.78/1.48  --inst_passive_queues_freq              [25;2]
% 6.78/1.48  --inst_dismatching                      true
% 6.78/1.48  --inst_eager_unprocessed_to_passive     true
% 6.78/1.48  --inst_prop_sim_given                   true
% 6.78/1.48  --inst_prop_sim_new                     false
% 6.78/1.48  --inst_subs_new                         false
% 6.78/1.48  --inst_eq_res_simp                      false
% 6.78/1.48  --inst_subs_given                       false
% 6.78/1.48  --inst_orphan_elimination               true
% 6.78/1.48  --inst_learning_loop_flag               true
% 6.78/1.48  --inst_learning_start                   3000
% 6.78/1.48  --inst_learning_factor                  2
% 6.78/1.48  --inst_start_prop_sim_after_learn       3
% 6.78/1.48  --inst_sel_renew                        solver
% 6.78/1.48  --inst_lit_activity_flag                true
% 6.78/1.48  --inst_restr_to_given                   false
% 6.78/1.48  --inst_activity_threshold               500
% 6.78/1.48  --inst_out_proof                        true
% 6.78/1.48  
% 6.78/1.48  ------ Resolution Options
% 6.78/1.48  
% 6.78/1.48  --resolution_flag                       true
% 6.78/1.48  --res_lit_sel                           adaptive
% 6.78/1.48  --res_lit_sel_side                      none
% 6.78/1.48  --res_ordering                          kbo
% 6.78/1.48  --res_to_prop_solver                    active
% 6.78/1.48  --res_prop_simpl_new                    false
% 6.78/1.48  --res_prop_simpl_given                  true
% 6.78/1.48  --res_passive_queue_type                priority_queues
% 6.78/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.78/1.48  --res_passive_queues_freq               [15;5]
% 6.78/1.48  --res_forward_subs                      full
% 6.78/1.48  --res_backward_subs                     full
% 6.78/1.48  --res_forward_subs_resolution           true
% 6.78/1.48  --res_backward_subs_resolution          true
% 6.78/1.48  --res_orphan_elimination                true
% 6.78/1.48  --res_time_limit                        2.
% 6.78/1.48  --res_out_proof                         true
% 6.78/1.48  
% 6.78/1.48  ------ Superposition Options
% 6.78/1.48  
% 6.78/1.48  --superposition_flag                    true
% 6.78/1.48  --sup_passive_queue_type                priority_queues
% 6.78/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.78/1.48  --sup_passive_queues_freq               [8;1;4]
% 6.78/1.48  --demod_completeness_check              fast
% 6.78/1.48  --demod_use_ground                      true
% 6.78/1.48  --sup_to_prop_solver                    passive
% 6.78/1.48  --sup_prop_simpl_new                    true
% 6.78/1.48  --sup_prop_simpl_given                  true
% 6.78/1.48  --sup_fun_splitting                     false
% 6.78/1.48  --sup_smt_interval                      50000
% 6.78/1.48  
% 6.78/1.48  ------ Superposition Simplification Setup
% 6.78/1.48  
% 6.78/1.48  --sup_indices_passive                   []
% 6.78/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.78/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.78/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.78/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 6.78/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.78/1.48  --sup_full_bw                           [BwDemod]
% 6.78/1.48  --sup_immed_triv                        [TrivRules]
% 6.78/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.78/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.78/1.48  --sup_immed_bw_main                     []
% 6.78/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.78/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 6.78/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.78/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.78/1.48  
% 6.78/1.48  ------ Combination Options
% 6.78/1.48  
% 6.78/1.48  --comb_res_mult                         3
% 6.78/1.48  --comb_sup_mult                         2
% 6.78/1.48  --comb_inst_mult                        10
% 6.78/1.48  
% 6.78/1.48  ------ Debug Options
% 6.78/1.48  
% 6.78/1.48  --dbg_backtrace                         false
% 6.78/1.48  --dbg_dump_prop_clauses                 false
% 6.78/1.48  --dbg_dump_prop_clauses_file            -
% 6.78/1.48  --dbg_out_stat                          false
% 6.78/1.48  ------ Parsing...
% 6.78/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.78/1.48  
% 6.78/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 6.78/1.48  
% 6.78/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.78/1.48  
% 6.78/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.78/1.48  ------ Proving...
% 6.78/1.48  ------ Problem Properties 
% 6.78/1.48  
% 6.78/1.48  
% 6.78/1.48  clauses                                 21
% 6.78/1.48  conjectures                             2
% 6.78/1.48  EPR                                     3
% 6.78/1.48  Horn                                    16
% 6.78/1.48  unary                                   2
% 6.78/1.48  binary                                  16
% 6.78/1.48  lits                                    43
% 6.78/1.48  lits eq                                 4
% 6.78/1.48  fd_pure                                 0
% 6.78/1.48  fd_pseudo                               0
% 6.78/1.48  fd_cond                                 1
% 6.78/1.48  fd_pseudo_cond                          0
% 6.78/1.48  AC symbols                              0
% 6.78/1.48  
% 6.78/1.48  ------ Schedule dynamic 5 is on 
% 6.78/1.48  
% 6.78/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 6.78/1.48  
% 6.78/1.48  
% 6.78/1.48  ------ 
% 6.78/1.48  Current options:
% 6.78/1.48  ------ 
% 6.78/1.48  
% 6.78/1.48  ------ Input Options
% 6.78/1.48  
% 6.78/1.48  --out_options                           all
% 6.78/1.48  --tptp_safe_out                         true
% 6.78/1.48  --problem_path                          ""
% 6.78/1.48  --include_path                          ""
% 6.78/1.48  --clausifier                            res/vclausify_rel
% 6.78/1.48  --clausifier_options                    --mode clausify
% 6.78/1.48  --stdin                                 false
% 6.78/1.48  --stats_out                             all
% 6.78/1.48  
% 6.78/1.48  ------ General Options
% 6.78/1.48  
% 6.78/1.48  --fof                                   false
% 6.78/1.48  --time_out_real                         305.
% 6.78/1.48  --time_out_virtual                      -1.
% 6.78/1.48  --symbol_type_check                     false
% 6.78/1.48  --clausify_out                          false
% 6.78/1.48  --sig_cnt_out                           false
% 6.78/1.48  --trig_cnt_out                          false
% 6.78/1.48  --trig_cnt_out_tolerance                1.
% 6.78/1.48  --trig_cnt_out_sk_spl                   false
% 6.78/1.48  --abstr_cl_out                          false
% 6.78/1.48  
% 6.78/1.48  ------ Global Options
% 6.78/1.48  
% 6.78/1.48  --schedule                              default
% 6.78/1.48  --add_important_lit                     false
% 6.78/1.48  --prop_solver_per_cl                    1000
% 6.78/1.48  --min_unsat_core                        false
% 6.78/1.48  --soft_assumptions                      false
% 6.78/1.48  --soft_lemma_size                       3
% 6.78/1.48  --prop_impl_unit_size                   0
% 6.78/1.48  --prop_impl_unit                        []
% 6.78/1.48  --share_sel_clauses                     true
% 6.78/1.48  --reset_solvers                         false
% 6.78/1.48  --bc_imp_inh                            [conj_cone]
% 6.78/1.48  --conj_cone_tolerance                   3.
% 6.78/1.48  --extra_neg_conj                        none
% 6.78/1.48  --large_theory_mode                     true
% 6.78/1.48  --prolific_symb_bound                   200
% 6.78/1.48  --lt_threshold                          2000
% 6.78/1.48  --clause_weak_htbl                      true
% 6.78/1.48  --gc_record_bc_elim                     false
% 6.78/1.48  
% 6.78/1.48  ------ Preprocessing Options
% 6.78/1.48  
% 6.78/1.48  --preprocessing_flag                    true
% 6.78/1.48  --time_out_prep_mult                    0.1
% 6.78/1.48  --splitting_mode                        input
% 6.78/1.48  --splitting_grd                         true
% 6.78/1.48  --splitting_cvd                         false
% 6.78/1.48  --splitting_cvd_svl                     false
% 6.78/1.48  --splitting_nvd                         32
% 6.78/1.48  --sub_typing                            true
% 6.78/1.48  --prep_gs_sim                           true
% 6.78/1.48  --prep_unflatten                        true
% 6.78/1.48  --prep_res_sim                          true
% 6.78/1.48  --prep_upred                            true
% 6.78/1.48  --prep_sem_filter                       exhaustive
% 6.78/1.48  --prep_sem_filter_out                   false
% 6.78/1.48  --pred_elim                             true
% 6.78/1.48  --res_sim_input                         true
% 6.78/1.48  --eq_ax_congr_red                       true
% 6.78/1.48  --pure_diseq_elim                       true
% 6.78/1.48  --brand_transform                       false
% 6.78/1.48  --non_eq_to_eq                          false
% 6.78/1.48  --prep_def_merge                        true
% 6.78/1.48  --prep_def_merge_prop_impl              false
% 6.78/1.48  --prep_def_merge_mbd                    true
% 6.78/1.48  --prep_def_merge_tr_red                 false
% 6.78/1.48  --prep_def_merge_tr_cl                  false
% 6.78/1.48  --smt_preprocessing                     true
% 6.78/1.48  --smt_ac_axioms                         fast
% 6.78/1.48  --preprocessed_out                      false
% 6.78/1.48  --preprocessed_stats                    false
% 6.78/1.48  
% 6.78/1.48  ------ Abstraction refinement Options
% 6.78/1.48  
% 6.78/1.48  --abstr_ref                             []
% 6.78/1.48  --abstr_ref_prep                        false
% 6.78/1.48  --abstr_ref_until_sat                   false
% 6.78/1.48  --abstr_ref_sig_restrict                funpre
% 6.78/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 6.78/1.48  --abstr_ref_under                       []
% 6.78/1.48  
% 6.78/1.48  ------ SAT Options
% 6.78/1.48  
% 6.78/1.48  --sat_mode                              false
% 6.78/1.48  --sat_fm_restart_options                ""
% 6.78/1.48  --sat_gr_def                            false
% 6.78/1.48  --sat_epr_types                         true
% 6.78/1.48  --sat_non_cyclic_types                  false
% 6.78/1.48  --sat_finite_models                     false
% 6.78/1.48  --sat_fm_lemmas                         false
% 6.78/1.48  --sat_fm_prep                           false
% 6.78/1.48  --sat_fm_uc_incr                        true
% 6.78/1.48  --sat_out_model                         small
% 6.78/1.48  --sat_out_clauses                       false
% 6.78/1.48  
% 6.78/1.48  ------ QBF Options
% 6.78/1.48  
% 6.78/1.48  --qbf_mode                              false
% 6.78/1.48  --qbf_elim_univ                         false
% 6.78/1.48  --qbf_dom_inst                          none
% 6.78/1.48  --qbf_dom_pre_inst                      false
% 6.78/1.48  --qbf_sk_in                             false
% 6.78/1.48  --qbf_pred_elim                         true
% 6.78/1.48  --qbf_split                             512
% 6.78/1.48  
% 6.78/1.48  ------ BMC1 Options
% 6.78/1.48  
% 6.78/1.48  --bmc1_incremental                      false
% 6.78/1.48  --bmc1_axioms                           reachable_all
% 6.78/1.48  --bmc1_min_bound                        0
% 6.78/1.48  --bmc1_max_bound                        -1
% 6.78/1.48  --bmc1_max_bound_default                -1
% 6.78/1.48  --bmc1_symbol_reachability              true
% 6.78/1.48  --bmc1_property_lemmas                  false
% 6.78/1.48  --bmc1_k_induction                      false
% 6.78/1.48  --bmc1_non_equiv_states                 false
% 6.78/1.48  --bmc1_deadlock                         false
% 6.78/1.48  --bmc1_ucm                              false
% 6.78/1.48  --bmc1_add_unsat_core                   none
% 6.78/1.48  --bmc1_unsat_core_children              false
% 6.78/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 6.78/1.48  --bmc1_out_stat                         full
% 6.78/1.48  --bmc1_ground_init                      false
% 6.78/1.48  --bmc1_pre_inst_next_state              false
% 6.78/1.48  --bmc1_pre_inst_state                   false
% 6.78/1.48  --bmc1_pre_inst_reach_state             false
% 6.78/1.48  --bmc1_out_unsat_core                   false
% 6.78/1.48  --bmc1_aig_witness_out                  false
% 6.78/1.48  --bmc1_verbose                          false
% 6.78/1.48  --bmc1_dump_clauses_tptp                false
% 6.78/1.48  --bmc1_dump_unsat_core_tptp             false
% 6.78/1.48  --bmc1_dump_file                        -
% 6.78/1.48  --bmc1_ucm_expand_uc_limit              128
% 6.78/1.48  --bmc1_ucm_n_expand_iterations          6
% 6.78/1.48  --bmc1_ucm_extend_mode                  1
% 6.78/1.48  --bmc1_ucm_init_mode                    2
% 6.78/1.48  --bmc1_ucm_cone_mode                    none
% 6.78/1.48  --bmc1_ucm_reduced_relation_type        0
% 6.78/1.48  --bmc1_ucm_relax_model                  4
% 6.78/1.48  --bmc1_ucm_full_tr_after_sat            true
% 6.78/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 6.78/1.48  --bmc1_ucm_layered_model                none
% 6.78/1.48  --bmc1_ucm_max_lemma_size               10
% 6.78/1.48  
% 6.78/1.48  ------ AIG Options
% 6.78/1.48  
% 6.78/1.48  --aig_mode                              false
% 6.78/1.48  
% 6.78/1.48  ------ Instantiation Options
% 6.78/1.48  
% 6.78/1.48  --instantiation_flag                    true
% 6.78/1.48  --inst_sos_flag                         false
% 6.78/1.48  --inst_sos_phase                        true
% 6.78/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.78/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.78/1.48  --inst_lit_sel_side                     none
% 6.78/1.48  --inst_solver_per_active                1400
% 6.78/1.48  --inst_solver_calls_frac                1.
% 6.78/1.48  --inst_passive_queue_type               priority_queues
% 6.78/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.78/1.48  --inst_passive_queues_freq              [25;2]
% 6.78/1.48  --inst_dismatching                      true
% 6.78/1.48  --inst_eager_unprocessed_to_passive     true
% 6.78/1.48  --inst_prop_sim_given                   true
% 6.78/1.48  --inst_prop_sim_new                     false
% 6.78/1.48  --inst_subs_new                         false
% 6.78/1.48  --inst_eq_res_simp                      false
% 6.78/1.48  --inst_subs_given                       false
% 6.78/1.48  --inst_orphan_elimination               true
% 6.78/1.48  --inst_learning_loop_flag               true
% 6.78/1.48  --inst_learning_start                   3000
% 6.78/1.48  --inst_learning_factor                  2
% 6.78/1.48  --inst_start_prop_sim_after_learn       3
% 6.78/1.48  --inst_sel_renew                        solver
% 6.78/1.48  --inst_lit_activity_flag                true
% 6.78/1.48  --inst_restr_to_given                   false
% 6.78/1.48  --inst_activity_threshold               500
% 6.78/1.48  --inst_out_proof                        true
% 6.78/1.48  
% 6.78/1.48  ------ Resolution Options
% 6.78/1.48  
% 6.78/1.48  --resolution_flag                       false
% 6.78/1.48  --res_lit_sel                           adaptive
% 6.78/1.48  --res_lit_sel_side                      none
% 6.78/1.48  --res_ordering                          kbo
% 6.78/1.48  --res_to_prop_solver                    active
% 6.78/1.48  --res_prop_simpl_new                    false
% 6.78/1.48  --res_prop_simpl_given                  true
% 6.78/1.48  --res_passive_queue_type                priority_queues
% 6.78/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.78/1.48  --res_passive_queues_freq               [15;5]
% 6.78/1.48  --res_forward_subs                      full
% 6.78/1.48  --res_backward_subs                     full
% 6.78/1.48  --res_forward_subs_resolution           true
% 6.78/1.48  --res_backward_subs_resolution          true
% 6.78/1.48  --res_orphan_elimination                true
% 6.78/1.48  --res_time_limit                        2.
% 6.78/1.48  --res_out_proof                         true
% 6.78/1.48  
% 6.78/1.48  ------ Superposition Options
% 6.78/1.48  
% 6.78/1.48  --superposition_flag                    true
% 6.78/1.48  --sup_passive_queue_type                priority_queues
% 6.78/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.78/1.48  --sup_passive_queues_freq               [8;1;4]
% 6.78/1.48  --demod_completeness_check              fast
% 6.78/1.48  --demod_use_ground                      true
% 6.78/1.48  --sup_to_prop_solver                    passive
% 6.78/1.48  --sup_prop_simpl_new                    true
% 6.78/1.48  --sup_prop_simpl_given                  true
% 6.78/1.48  --sup_fun_splitting                     false
% 6.78/1.48  --sup_smt_interval                      50000
% 6.78/1.48  
% 6.78/1.48  ------ Superposition Simplification Setup
% 6.78/1.48  
% 6.78/1.48  --sup_indices_passive                   []
% 6.78/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.78/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.78/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.78/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 6.78/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.78/1.48  --sup_full_bw                           [BwDemod]
% 6.78/1.48  --sup_immed_triv                        [TrivRules]
% 6.78/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.78/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.78/1.48  --sup_immed_bw_main                     []
% 6.78/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.78/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 6.78/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.78/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.78/1.48  
% 6.78/1.48  ------ Combination Options
% 6.78/1.48  
% 6.78/1.48  --comb_res_mult                         3
% 6.78/1.48  --comb_sup_mult                         2
% 6.78/1.48  --comb_inst_mult                        10
% 6.78/1.48  
% 6.78/1.48  ------ Debug Options
% 6.78/1.48  
% 6.78/1.48  --dbg_backtrace                         false
% 6.78/1.48  --dbg_dump_prop_clauses                 false
% 6.78/1.48  --dbg_dump_prop_clauses_file            -
% 6.78/1.48  --dbg_out_stat                          false
% 6.78/1.48  
% 6.78/1.48  
% 6.78/1.48  
% 6.78/1.48  
% 6.78/1.48  ------ Proving...
% 6.78/1.48  
% 6.78/1.48  
% 6.78/1.48  % SZS status Theorem for theBenchmark.p
% 6.78/1.48  
% 6.78/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 6.78/1.48  
% 6.78/1.48  fof(f2,axiom,(
% 6.78/1.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 6.78/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.78/1.48  
% 6.78/1.48  fof(f12,plain,(
% 6.78/1.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 6.78/1.48    inference(rectify,[],[f2])).
% 6.78/1.48  
% 6.78/1.48  fof(f15,plain,(
% 6.78/1.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 6.78/1.48    inference(ennf_transformation,[],[f12])).
% 6.78/1.48  
% 6.78/1.48  fof(f24,plain,(
% 6.78/1.48    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 6.78/1.48    introduced(choice_axiom,[])).
% 6.78/1.48  
% 6.78/1.48  fof(f25,plain,(
% 6.78/1.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 6.78/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f24])).
% 6.78/1.48  
% 6.78/1.48  fof(f45,plain,(
% 6.78/1.48    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 6.78/1.48    inference(cnf_transformation,[],[f25])).
% 6.78/1.48  
% 6.78/1.48  fof(f5,axiom,(
% 6.78/1.48    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 6.78/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.78/1.48  
% 6.78/1.48  fof(f49,plain,(
% 6.78/1.48    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 6.78/1.48    inference(cnf_transformation,[],[f5])).
% 6.78/1.48  
% 6.78/1.48  fof(f9,axiom,(
% 6.78/1.48    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 6.78/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.78/1.48  
% 6.78/1.48  fof(f21,plain,(
% 6.78/1.48    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 6.78/1.48    inference(ennf_transformation,[],[f9])).
% 6.78/1.48  
% 6.78/1.48  fof(f22,plain,(
% 6.78/1.48    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 6.78/1.48    inference(flattening,[],[f21])).
% 6.78/1.48  
% 6.78/1.48  fof(f60,plain,(
% 6.78/1.48    ( ! [X2,X0,X1] : (r2_hidden(X1,k2_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 6.78/1.48    inference(cnf_transformation,[],[f22])).
% 6.78/1.48  
% 6.78/1.48  fof(f10,conjecture,(
% 6.78/1.48    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 6.78/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.78/1.48  
% 6.78/1.48  fof(f11,negated_conjecture,(
% 6.78/1.48    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 6.78/1.48    inference(negated_conjecture,[],[f10])).
% 6.78/1.48  
% 6.78/1.48  fof(f23,plain,(
% 6.78/1.48    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <~> r1_xboole_0(k2_relat_1(X1),X0)) & v1_relat_1(X1))),
% 6.78/1.48    inference(ennf_transformation,[],[f11])).
% 6.78/1.48  
% 6.78/1.48  fof(f38,plain,(
% 6.78/1.48    ? [X0,X1] : (((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0))) & v1_relat_1(X1))),
% 6.78/1.48    inference(nnf_transformation,[],[f23])).
% 6.78/1.48  
% 6.78/1.48  fof(f39,plain,(
% 6.78/1.48    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1))),
% 6.78/1.48    inference(flattening,[],[f38])).
% 6.78/1.48  
% 6.78/1.48  fof(f40,plain,(
% 6.78/1.48    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k2_relat_1(sK6),sK5) | k1_xboole_0 != k10_relat_1(sK6,sK5)) & (r1_xboole_0(k2_relat_1(sK6),sK5) | k1_xboole_0 = k10_relat_1(sK6,sK5)) & v1_relat_1(sK6))),
% 6.78/1.48    introduced(choice_axiom,[])).
% 6.78/1.48  
% 6.78/1.48  fof(f41,plain,(
% 6.78/1.48    (~r1_xboole_0(k2_relat_1(sK6),sK5) | k1_xboole_0 != k10_relat_1(sK6,sK5)) & (r1_xboole_0(k2_relat_1(sK6),sK5) | k1_xboole_0 = k10_relat_1(sK6,sK5)) & v1_relat_1(sK6)),
% 6.78/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f39,f40])).
% 6.78/1.48  
% 6.78/1.48  fof(f61,plain,(
% 6.78/1.48    v1_relat_1(sK6)),
% 6.78/1.48    inference(cnf_transformation,[],[f41])).
% 6.78/1.48  
% 6.78/1.48  fof(f8,axiom,(
% 6.78/1.48    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 6.78/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.78/1.48  
% 6.78/1.48  fof(f20,plain,(
% 6.78/1.48    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 6.78/1.48    inference(ennf_transformation,[],[f8])).
% 6.78/1.48  
% 6.78/1.48  fof(f34,plain,(
% 6.78/1.48    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 6.78/1.48    inference(nnf_transformation,[],[f20])).
% 6.78/1.48  
% 6.78/1.48  fof(f35,plain,(
% 6.78/1.48    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 6.78/1.48    inference(rectify,[],[f34])).
% 6.78/1.48  
% 6.78/1.48  fof(f36,plain,(
% 6.78/1.48    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK4(X0,X1,X2)),X2) & r2_hidden(sK4(X0,X1,X2),k2_relat_1(X2))))),
% 6.78/1.48    introduced(choice_axiom,[])).
% 6.78/1.48  
% 6.78/1.48  fof(f37,plain,(
% 6.78/1.48    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK4(X0,X1,X2)),X2) & r2_hidden(sK4(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 6.78/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f36])).
% 6.78/1.48  
% 6.78/1.48  fof(f58,plain,(
% 6.78/1.48    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,k10_relat_1(X2,X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 6.78/1.48    inference(cnf_transformation,[],[f37])).
% 6.78/1.48  
% 6.78/1.48  fof(f6,axiom,(
% 6.78/1.48    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 6.78/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.78/1.48  
% 6.78/1.48  fof(f18,plain,(
% 6.78/1.48    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 6.78/1.48    inference(ennf_transformation,[],[f6])).
% 6.78/1.48  
% 6.78/1.48  fof(f30,plain,(
% 6.78/1.48    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 6.78/1.48    inference(nnf_transformation,[],[f18])).
% 6.78/1.48  
% 6.78/1.48  fof(f31,plain,(
% 6.78/1.48    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 6.78/1.48    inference(rectify,[],[f30])).
% 6.78/1.48  
% 6.78/1.48  fof(f32,plain,(
% 6.78/1.48    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2) & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2))))),
% 6.78/1.48    introduced(choice_axiom,[])).
% 6.78/1.48  
% 6.78/1.48  fof(f33,plain,(
% 6.78/1.48    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2) & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 6.78/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f32])).
% 6.78/1.48  
% 6.78/1.48  fof(f51,plain,(
% 6.78/1.48    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 6.78/1.48    inference(cnf_transformation,[],[f33])).
% 6.78/1.48  
% 6.78/1.48  fof(f50,plain,(
% 6.78/1.48    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2)) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 6.78/1.48    inference(cnf_transformation,[],[f33])).
% 6.78/1.48  
% 6.78/1.48  fof(f1,axiom,(
% 6.78/1.48    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 6.78/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.78/1.48  
% 6.78/1.48  fof(f14,plain,(
% 6.78/1.48    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 6.78/1.48    inference(ennf_transformation,[],[f1])).
% 6.78/1.48  
% 6.78/1.48  fof(f42,plain,(
% 6.78/1.48    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 6.78/1.48    inference(cnf_transformation,[],[f14])).
% 6.78/1.48  
% 6.78/1.48  fof(f62,plain,(
% 6.78/1.48    r1_xboole_0(k2_relat_1(sK6),sK5) | k1_xboole_0 = k10_relat_1(sK6,sK5)),
% 6.78/1.48    inference(cnf_transformation,[],[f41])).
% 6.78/1.48  
% 6.78/1.48  fof(f63,plain,(
% 6.78/1.48    ~r1_xboole_0(k2_relat_1(sK6),sK5) | k1_xboole_0 != k10_relat_1(sK6,sK5)),
% 6.78/1.48    inference(cnf_transformation,[],[f41])).
% 6.78/1.48  
% 6.78/1.48  fof(f4,axiom,(
% 6.78/1.48    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 6.78/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.78/1.48  
% 6.78/1.48  fof(f17,plain,(
% 6.78/1.48    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 6.78/1.48    inference(ennf_transformation,[],[f4])).
% 6.78/1.48  
% 6.78/1.48  fof(f28,plain,(
% 6.78/1.48    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 6.78/1.48    introduced(choice_axiom,[])).
% 6.78/1.48  
% 6.78/1.48  fof(f29,plain,(
% 6.78/1.48    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 6.78/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f28])).
% 6.78/1.48  
% 6.78/1.48  fof(f48,plain,(
% 6.78/1.48    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 6.78/1.48    inference(cnf_transformation,[],[f29])).
% 6.78/1.48  
% 6.78/1.48  fof(f55,plain,(
% 6.78/1.48    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),k2_relat_1(X2)) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 6.78/1.48    inference(cnf_transformation,[],[f37])).
% 6.78/1.48  
% 6.78/1.48  fof(f57,plain,(
% 6.78/1.48    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 6.78/1.48    inference(cnf_transformation,[],[f37])).
% 6.78/1.48  
% 6.78/1.48  fof(f43,plain,(
% 6.78/1.48    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 6.78/1.48    inference(cnf_transformation,[],[f25])).
% 6.78/1.48  
% 6.78/1.48  fof(f44,plain,(
% 6.78/1.48    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 6.78/1.48    inference(cnf_transformation,[],[f25])).
% 6.78/1.48  
% 6.78/1.48  fof(f7,axiom,(
% 6.78/1.48    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 6.78/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.78/1.48  
% 6.78/1.48  fof(f19,plain,(
% 6.78/1.48    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 6.78/1.48    inference(ennf_transformation,[],[f7])).
% 6.78/1.48  
% 6.78/1.48  fof(f54,plain,(
% 6.78/1.48    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 6.78/1.48    inference(cnf_transformation,[],[f19])).
% 6.78/1.48  
% 6.78/1.48  cnf(c_668,plain,
% 6.78/1.48      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 6.78/1.48      theory(equality) ).
% 6.78/1.48  
% 6.78/1.48  cnf(c_3331,plain,
% 6.78/1.48      ( r1_xboole_0(X0,X1)
% 6.78/1.48      | ~ r1_xboole_0(k1_xboole_0,X2)
% 6.78/1.48      | X1 != X2
% 6.78/1.48      | X0 != k1_xboole_0 ),
% 6.78/1.48      inference(instantiation,[status(thm)],[c_668]) ).
% 6.78/1.48  
% 6.78/1.48  cnf(c_10238,plain,
% 6.78/1.48      ( r1_xboole_0(k10_relat_1(sK6,sK5),X0)
% 6.78/1.48      | ~ r1_xboole_0(k1_xboole_0,X1)
% 6.78/1.48      | X0 != X1
% 6.78/1.48      | k10_relat_1(sK6,sK5) != k1_xboole_0 ),
% 6.78/1.48      inference(instantiation,[status(thm)],[c_3331]) ).
% 6.78/1.48  
% 6.78/1.48  cnf(c_14856,plain,
% 6.78/1.48      ( r1_xboole_0(k10_relat_1(sK6,sK5),k1_relat_1(sK6))
% 6.78/1.48      | ~ r1_xboole_0(k1_xboole_0,X0)
% 6.78/1.48      | k10_relat_1(sK6,sK5) != k1_xboole_0
% 6.78/1.48      | k1_relat_1(sK6) != X0 ),
% 6.78/1.48      inference(instantiation,[status(thm)],[c_10238]) ).
% 6.78/1.48  
% 6.78/1.48  cnf(c_30611,plain,
% 6.78/1.48      ( r1_xboole_0(k10_relat_1(sK6,sK5),k1_relat_1(sK6))
% 6.78/1.48      | ~ r1_xboole_0(k1_xboole_0,k1_relat_1(sK6))
% 6.78/1.48      | k10_relat_1(sK6,sK5) != k1_xboole_0
% 6.78/1.48      | k1_relat_1(sK6) != k1_relat_1(sK6) ),
% 6.78/1.48      inference(instantiation,[status(thm)],[c_14856]) ).
% 6.78/1.48  
% 6.78/1.48  cnf(c_1,plain,
% 6.78/1.48      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 6.78/1.48      inference(cnf_transformation,[],[f45]) ).
% 6.78/1.48  
% 6.78/1.48  cnf(c_5889,plain,
% 6.78/1.48      ( ~ r2_hidden(sK3(sK0(k2_relat_1(sK6),sK5),k1_relat_1(sK6),sK6),X0)
% 6.78/1.48      | ~ r2_hidden(sK3(sK0(k2_relat_1(sK6),sK5),k1_relat_1(sK6),sK6),k1_relat_1(sK6))
% 6.78/1.48      | ~ r1_xboole_0(X0,k1_relat_1(sK6)) ),
% 6.78/1.48      inference(instantiation,[status(thm)],[c_1]) ).
% 6.78/1.48  
% 6.78/1.48  cnf(c_14855,plain,
% 6.78/1.48      ( ~ r2_hidden(sK3(sK0(k2_relat_1(sK6),sK5),k1_relat_1(sK6),sK6),k10_relat_1(sK6,sK5))
% 6.78/1.48      | ~ r2_hidden(sK3(sK0(k2_relat_1(sK6),sK5),k1_relat_1(sK6),sK6),k1_relat_1(sK6))
% 6.78/1.48      | ~ r1_xboole_0(k10_relat_1(sK6,sK5),k1_relat_1(sK6)) ),
% 6.78/1.48      inference(instantiation,[status(thm)],[c_5889]) ).
% 6.78/1.48  
% 6.78/1.48  cnf(c_7,plain,
% 6.78/1.48      ( r1_xboole_0(X0,k1_xboole_0) ),
% 6.78/1.48      inference(cnf_transformation,[],[f49]) ).
% 6.78/1.48  
% 6.78/1.48  cnf(c_7700,plain,
% 6.78/1.48      ( r1_xboole_0(k1_relat_1(sK6),k1_xboole_0) ),
% 6.78/1.48      inference(instantiation,[status(thm)],[c_7]) ).
% 6.78/1.48  
% 6.78/1.48  cnf(c_17,plain,
% 6.78/1.48      ( r2_hidden(X0,k2_relat_1(X1))
% 6.78/1.48      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 6.78/1.48      | ~ v1_relat_1(X1) ),
% 6.78/1.48      inference(cnf_transformation,[],[f60]) ).
% 6.78/1.48  
% 6.78/1.48  cnf(c_21,negated_conjecture,
% 6.78/1.48      ( v1_relat_1(sK6) ),
% 6.78/1.48      inference(cnf_transformation,[],[f61]) ).
% 6.78/1.48  
% 6.78/1.48  cnf(c_350,plain,
% 6.78/1.48      ( r2_hidden(X0,k2_relat_1(X1))
% 6.78/1.48      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 6.78/1.48      | sK6 != X1 ),
% 6.78/1.48      inference(resolution_lifted,[status(thm)],[c_17,c_21]) ).
% 6.78/1.48  
% 6.78/1.48  cnf(c_351,plain,
% 6.78/1.48      ( r2_hidden(X0,k2_relat_1(sK6))
% 6.78/1.48      | ~ r2_hidden(k4_tarski(X1,X0),sK6) ),
% 6.78/1.48      inference(unflattening,[status(thm)],[c_350]) ).
% 6.78/1.48  
% 6.78/1.48  cnf(c_13,plain,
% 6.78/1.48      ( ~ r2_hidden(X0,X1)
% 6.78/1.48      | r2_hidden(X2,k10_relat_1(X3,X1))
% 6.78/1.48      | ~ r2_hidden(X0,k2_relat_1(X3))
% 6.78/1.48      | ~ r2_hidden(k4_tarski(X2,X0),X3)
% 6.78/1.48      | ~ v1_relat_1(X3) ),
% 6.78/1.48      inference(cnf_transformation,[],[f58]) ).
% 6.78/1.48  
% 6.78/1.48  cnf(c_298,plain,
% 6.78/1.48      ( ~ r2_hidden(X0,X1)
% 6.78/1.48      | r2_hidden(X2,k10_relat_1(X3,X1))
% 6.78/1.48      | ~ r2_hidden(X0,k2_relat_1(X3))
% 6.78/1.48      | ~ r2_hidden(k4_tarski(X2,X0),X3)
% 6.78/1.48      | sK6 != X3 ),
% 6.78/1.48      inference(resolution_lifted,[status(thm)],[c_13,c_21]) ).
% 6.78/1.48  
% 6.78/1.48  cnf(c_299,plain,
% 6.78/1.48      ( ~ r2_hidden(X0,X1)
% 6.78/1.48      | r2_hidden(X2,k10_relat_1(sK6,X1))
% 6.78/1.48      | ~ r2_hidden(X0,k2_relat_1(sK6))
% 6.78/1.48      | ~ r2_hidden(k4_tarski(X2,X0),sK6) ),
% 6.78/1.48      inference(unflattening,[status(thm)],[c_298]) ).
% 6.78/1.48  
% 6.78/1.48  cnf(c_360,plain,
% 6.78/1.48      ( ~ r2_hidden(X0,X1)
% 6.78/1.48      | r2_hidden(X2,k10_relat_1(sK6,X1))
% 6.78/1.48      | ~ r2_hidden(k4_tarski(X2,X0),sK6) ),
% 6.78/1.48      inference(backward_subsumption_resolution,
% 6.78/1.48                [status(thm)],
% 6.78/1.48                [c_351,c_299]) ).
% 6.78/1.48  
% 6.78/1.48  cnf(c_1386,plain,
% 6.78/1.48      ( r2_hidden(X0,k10_relat_1(sK6,sK5))
% 6.78/1.48      | ~ r2_hidden(k4_tarski(X0,sK0(k2_relat_1(sK6),sK5)),sK6)
% 6.78/1.48      | ~ r2_hidden(sK0(k2_relat_1(sK6),sK5),sK5) ),
% 6.78/1.48      inference(instantiation,[status(thm)],[c_360]) ).
% 6.78/1.48  
% 6.78/1.48  cnf(c_5881,plain,
% 6.78/1.48      ( r2_hidden(sK3(sK0(k2_relat_1(sK6),sK5),k1_relat_1(sK6),sK6),k10_relat_1(sK6,sK5))
% 6.78/1.48      | ~ r2_hidden(k4_tarski(sK3(sK0(k2_relat_1(sK6),sK5),k1_relat_1(sK6),sK6),sK0(k2_relat_1(sK6),sK5)),sK6)
% 6.78/1.48      | ~ r2_hidden(sK0(k2_relat_1(sK6),sK5),sK5) ),
% 6.78/1.48      inference(instantiation,[status(thm)],[c_1386]) ).
% 6.78/1.48  
% 6.78/1.48  cnf(c_10,plain,
% 6.78/1.48      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 6.78/1.48      | r2_hidden(k4_tarski(sK3(X0,X2,X1),X0),X1)
% 6.78/1.48      | ~ v1_relat_1(X1) ),
% 6.78/1.48      inference(cnf_transformation,[],[f51]) ).
% 6.78/1.48  
% 6.78/1.48  cnf(c_414,plain,
% 6.78/1.48      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 6.78/1.48      | r2_hidden(k4_tarski(sK3(X0,X2,X1),X0),X1)
% 6.78/1.48      | sK6 != X1 ),
% 6.78/1.48      inference(resolution_lifted,[status(thm)],[c_10,c_21]) ).
% 6.78/1.48  
% 6.78/1.48  cnf(c_415,plain,
% 6.78/1.48      ( ~ r2_hidden(X0,k9_relat_1(sK6,X1))
% 6.78/1.48      | r2_hidden(k4_tarski(sK3(X0,X1,sK6),X0),sK6) ),
% 6.78/1.48      inference(unflattening,[status(thm)],[c_414]) ).
% 6.78/1.48  
% 6.78/1.48  cnf(c_3515,plain,
% 6.78/1.48      ( r2_hidden(k4_tarski(sK3(sK0(k2_relat_1(sK6),sK5),k1_relat_1(sK6),sK6),sK0(k2_relat_1(sK6),sK5)),sK6)
% 6.78/1.48      | ~ r2_hidden(sK0(k2_relat_1(sK6),sK5),k9_relat_1(sK6,k1_relat_1(sK6))) ),
% 6.78/1.48      inference(instantiation,[status(thm)],[c_415]) ).
% 6.78/1.48  
% 6.78/1.48  cnf(c_11,plain,
% 6.78/1.48      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 6.78/1.48      | r2_hidden(sK3(X0,X2,X1),k1_relat_1(X1))
% 6.78/1.48      | ~ v1_relat_1(X1) ),
% 6.78/1.48      inference(cnf_transformation,[],[f50]) ).
% 6.78/1.48  
% 6.78/1.48  cnf(c_402,plain,
% 6.78/1.48      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 6.78/1.48      | r2_hidden(sK3(X0,X2,X1),k1_relat_1(X1))
% 6.78/1.48      | sK6 != X1 ),
% 6.78/1.48      inference(resolution_lifted,[status(thm)],[c_11,c_21]) ).
% 6.78/1.48  
% 6.78/1.48  cnf(c_403,plain,
% 6.78/1.48      ( ~ r2_hidden(X0,k9_relat_1(sK6,X1))
% 6.78/1.48      | r2_hidden(sK3(X0,X1,sK6),k1_relat_1(sK6)) ),
% 6.78/1.48      inference(unflattening,[status(thm)],[c_402]) ).
% 6.78/1.48  
% 6.78/1.48  cnf(c_3516,plain,
% 6.78/1.48      ( r2_hidden(sK3(sK0(k2_relat_1(sK6),sK5),k1_relat_1(sK6),sK6),k1_relat_1(sK6))
% 6.78/1.48      | ~ r2_hidden(sK0(k2_relat_1(sK6),sK5),k9_relat_1(sK6,k1_relat_1(sK6))) ),
% 6.78/1.48      inference(instantiation,[status(thm)],[c_403]) ).
% 6.78/1.48  
% 6.78/1.48  cnf(c_0,plain,
% 6.78/1.48      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 6.78/1.48      inference(cnf_transformation,[],[f42]) ).
% 6.78/1.48  
% 6.78/1.48  cnf(c_2000,plain,
% 6.78/1.48      ( ~ r1_xboole_0(X0,k1_xboole_0) | r1_xboole_0(k1_xboole_0,X0) ),
% 6.78/1.48      inference(instantiation,[status(thm)],[c_0]) ).
% 6.78/1.48  
% 6.78/1.48  cnf(c_3343,plain,
% 6.78/1.48      ( ~ r1_xboole_0(k1_relat_1(sK6),k1_xboole_0)
% 6.78/1.48      | r1_xboole_0(k1_xboole_0,k1_relat_1(sK6)) ),
% 6.78/1.48      inference(instantiation,[status(thm)],[c_2000]) ).
% 6.78/1.48  
% 6.78/1.48  cnf(c_20,negated_conjecture,
% 6.78/1.48      ( r1_xboole_0(k2_relat_1(sK6),sK5)
% 6.78/1.48      | k1_xboole_0 = k10_relat_1(sK6,sK5) ),
% 6.78/1.48      inference(cnf_transformation,[],[f62]) ).
% 6.78/1.48  
% 6.78/1.48  cnf(c_1151,plain,
% 6.78/1.48      ( k1_xboole_0 = k10_relat_1(sK6,sK5)
% 6.78/1.48      | r1_xboole_0(k2_relat_1(sK6),sK5) = iProver_top ),
% 6.78/1.48      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 6.78/1.48  
% 6.78/1.48  cnf(c_1160,plain,
% 6.78/1.48      ( r1_xboole_0(X0,X1) != iProver_top
% 6.78/1.48      | r1_xboole_0(X1,X0) = iProver_top ),
% 6.78/1.48      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 6.78/1.48  
% 6.78/1.48  cnf(c_1575,plain,
% 6.78/1.48      ( k10_relat_1(sK6,sK5) = k1_xboole_0
% 6.78/1.48      | r1_xboole_0(sK5,k2_relat_1(sK6)) = iProver_top ),
% 6.78/1.48      inference(superposition,[status(thm)],[c_1151,c_1160]) ).
% 6.78/1.48  
% 6.78/1.48  cnf(c_1728,plain,
% 6.78/1.48      ( k10_relat_1(sK6,sK5) = k1_xboole_0
% 6.78/1.48      | r1_xboole_0(k2_relat_1(sK6),sK5) = iProver_top ),
% 6.78/1.48      inference(superposition,[status(thm)],[c_1575,c_1160]) ).
% 6.78/1.48  
% 6.78/1.48  cnf(c_19,negated_conjecture,
% 6.78/1.48      ( ~ r1_xboole_0(k2_relat_1(sK6),sK5)
% 6.78/1.48      | k1_xboole_0 != k10_relat_1(sK6,sK5) ),
% 6.78/1.48      inference(cnf_transformation,[],[f63]) ).
% 6.78/1.48  
% 6.78/1.48  cnf(c_24,plain,
% 6.78/1.48      ( k1_xboole_0 != k10_relat_1(sK6,sK5)
% 6.78/1.48      | r1_xboole_0(k2_relat_1(sK6),sK5) != iProver_top ),
% 6.78/1.48      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 6.78/1.48  
% 6.78/1.48  cnf(c_6,plain,
% 6.78/1.48      ( r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0 ),
% 6.78/1.48      inference(cnf_transformation,[],[f48]) ).
% 6.78/1.48  
% 6.78/1.48  cnf(c_1322,plain,
% 6.78/1.48      ( r2_hidden(sK2(k10_relat_1(sK6,sK5)),k10_relat_1(sK6,sK5))
% 6.78/1.48      | k1_xboole_0 = k10_relat_1(sK6,sK5) ),
% 6.78/1.48      inference(instantiation,[status(thm)],[c_6]) ).
% 6.78/1.48  
% 6.78/1.48  cnf(c_16,plain,
% 6.78/1.48      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 6.78/1.48      | r2_hidden(sK4(X0,X2,X1),k2_relat_1(X1))
% 6.78/1.48      | ~ v1_relat_1(X1) ),
% 6.78/1.48      inference(cnf_transformation,[],[f55]) ).
% 6.78/1.48  
% 6.78/1.48  cnf(c_366,plain,
% 6.78/1.48      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 6.78/1.48      | r2_hidden(sK4(X0,X2,X1),k2_relat_1(X1))
% 6.78/1.48      | sK6 != X1 ),
% 6.78/1.48      inference(resolution_lifted,[status(thm)],[c_16,c_21]) ).
% 6.78/1.48  
% 6.78/1.48  cnf(c_367,plain,
% 6.78/1.48      ( ~ r2_hidden(X0,k10_relat_1(sK6,X1))
% 6.78/1.48      | r2_hidden(sK4(X0,X1,sK6),k2_relat_1(sK6)) ),
% 6.78/1.48      inference(unflattening,[status(thm)],[c_366]) ).
% 6.78/1.48  
% 6.78/1.48  cnf(c_1355,plain,
% 6.78/1.48      ( r2_hidden(sK4(sK2(k10_relat_1(sK6,sK5)),sK5,sK6),k2_relat_1(sK6))
% 6.78/1.48      | ~ r2_hidden(sK2(k10_relat_1(sK6,sK5)),k10_relat_1(sK6,sK5)) ),
% 6.78/1.48      inference(instantiation,[status(thm)],[c_367]) ).
% 6.78/1.48  
% 6.78/1.48  cnf(c_14,plain,
% 6.78/1.48      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 6.78/1.48      | r2_hidden(sK4(X0,X2,X1),X2)
% 6.78/1.48      | ~ v1_relat_1(X1) ),
% 6.78/1.48      inference(cnf_transformation,[],[f57]) ).
% 6.78/1.48  
% 6.78/1.48  cnf(c_390,plain,
% 6.78/1.48      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 6.78/1.48      | r2_hidden(sK4(X0,X2,X1),X2)
% 6.78/1.48      | sK6 != X1 ),
% 6.78/1.48      inference(resolution_lifted,[status(thm)],[c_14,c_21]) ).
% 6.78/1.48  
% 6.78/1.48  cnf(c_391,plain,
% 6.78/1.48      ( ~ r2_hidden(X0,k10_relat_1(sK6,X1))
% 6.78/1.48      | r2_hidden(sK4(X0,X1,sK6),X1) ),
% 6.78/1.48      inference(unflattening,[status(thm)],[c_390]) ).
% 6.78/1.48  
% 6.78/1.48  cnf(c_1353,plain,
% 6.78/1.48      ( r2_hidden(sK4(sK2(k10_relat_1(sK6,sK5)),sK5,sK6),sK5)
% 6.78/1.48      | ~ r2_hidden(sK2(k10_relat_1(sK6,sK5)),k10_relat_1(sK6,sK5)) ),
% 6.78/1.48      inference(instantiation,[status(thm)],[c_391]) ).
% 6.78/1.48  
% 6.78/1.48  cnf(c_1729,plain,
% 6.78/1.48      ( r1_xboole_0(k2_relat_1(sK6),sK5)
% 6.78/1.48      | k10_relat_1(sK6,sK5) = k1_xboole_0 ),
% 6.78/1.48      inference(predicate_to_equality_rev,[status(thm)],[c_1728]) ).
% 6.78/1.48  
% 6.78/1.48  cnf(c_1495,plain,
% 6.78/1.48      ( ~ r2_hidden(sK4(sK2(k10_relat_1(sK6,sK5)),sK5,sK6),X0)
% 6.78/1.48      | ~ r2_hidden(sK4(sK2(k10_relat_1(sK6,sK5)),sK5,sK6),sK5)
% 6.78/1.48      | ~ r1_xboole_0(X0,sK5) ),
% 6.78/1.48      inference(instantiation,[status(thm)],[c_1]) ).
% 6.78/1.48  
% 6.78/1.48  cnf(c_2128,plain,
% 6.78/1.48      ( ~ r2_hidden(sK4(sK2(k10_relat_1(sK6,sK5)),sK5,sK6),k2_relat_1(sK6))
% 6.78/1.48      | ~ r2_hidden(sK4(sK2(k10_relat_1(sK6,sK5)),sK5,sK6),sK5)
% 6.78/1.48      | ~ r1_xboole_0(k2_relat_1(sK6),sK5) ),
% 6.78/1.48      inference(instantiation,[status(thm)],[c_1495]) ).
% 6.78/1.48  
% 6.78/1.48  cnf(c_3055,plain,
% 6.78/1.48      ( k10_relat_1(sK6,sK5) = k1_xboole_0 ),
% 6.78/1.48      inference(global_propositional_subsumption,
% 6.78/1.48                [status(thm)],
% 6.78/1.48                [c_1728,c_24,c_1322,c_1355,c_1353,c_1729,c_2128]) ).
% 6.78/1.48  
% 6.78/1.48  cnf(c_1152,plain,
% 6.78/1.48      ( k1_xboole_0 != k10_relat_1(sK6,sK5)
% 6.78/1.48      | r1_xboole_0(k2_relat_1(sK6),sK5) != iProver_top ),
% 6.78/1.48      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 6.78/1.48  
% 6.78/1.48  cnf(c_3059,plain,
% 6.78/1.48      ( k1_xboole_0 != k1_xboole_0
% 6.78/1.48      | r1_xboole_0(k2_relat_1(sK6),sK5) != iProver_top ),
% 6.78/1.48      inference(demodulation,[status(thm)],[c_3055,c_1152]) ).
% 6.78/1.48  
% 6.78/1.48  cnf(c_3060,plain,
% 6.78/1.48      ( r1_xboole_0(k2_relat_1(sK6),sK5) != iProver_top ),
% 6.78/1.48      inference(equality_resolution_simp,[status(thm)],[c_3059]) ).
% 6.78/1.48  
% 6.78/1.48  cnf(c_666,plain,( X0 = X0 ),theory(equality) ).
% 6.78/1.48  
% 6.78/1.48  cnf(c_1961,plain,
% 6.78/1.48      ( sK0(k2_relat_1(sK6),sK5) = sK0(k2_relat_1(sK6),sK5) ),
% 6.78/1.48      inference(instantiation,[status(thm)],[c_666]) ).
% 6.78/1.48  
% 6.78/1.48  cnf(c_669,plain,
% 6.78/1.48      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 6.78/1.48      theory(equality) ).
% 6.78/1.48  
% 6.78/1.48  cnf(c_1404,plain,
% 6.78/1.48      ( r2_hidden(X0,X1)
% 6.78/1.48      | ~ r2_hidden(sK0(k2_relat_1(sK6),sK5),k2_relat_1(sK6))
% 6.78/1.48      | X0 != sK0(k2_relat_1(sK6),sK5)
% 6.78/1.48      | X1 != k2_relat_1(sK6) ),
% 6.78/1.48      inference(instantiation,[status(thm)],[c_669]) ).
% 6.78/1.48  
% 6.78/1.48  cnf(c_1738,plain,
% 6.78/1.48      ( r2_hidden(X0,k9_relat_1(sK6,k1_relat_1(sK6)))
% 6.78/1.48      | ~ r2_hidden(sK0(k2_relat_1(sK6),sK5),k2_relat_1(sK6))
% 6.78/1.48      | X0 != sK0(k2_relat_1(sK6),sK5)
% 6.78/1.48      | k9_relat_1(sK6,k1_relat_1(sK6)) != k2_relat_1(sK6) ),
% 6.78/1.48      inference(instantiation,[status(thm)],[c_1404]) ).
% 6.78/1.48  
% 6.78/1.48  cnf(c_1960,plain,
% 6.78/1.48      ( r2_hidden(sK0(k2_relat_1(sK6),sK5),k9_relat_1(sK6,k1_relat_1(sK6)))
% 6.78/1.48      | ~ r2_hidden(sK0(k2_relat_1(sK6),sK5),k2_relat_1(sK6))
% 6.78/1.48      | k9_relat_1(sK6,k1_relat_1(sK6)) != k2_relat_1(sK6)
% 6.78/1.48      | sK0(k2_relat_1(sK6),sK5) != sK0(k2_relat_1(sK6),sK5) ),
% 6.78/1.48      inference(instantiation,[status(thm)],[c_1738]) ).
% 6.78/1.48  
% 6.78/1.48  cnf(c_3,plain,
% 6.78/1.48      ( r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1) ),
% 6.78/1.48      inference(cnf_transformation,[],[f43]) ).
% 6.78/1.48  
% 6.78/1.48  cnf(c_1305,plain,
% 6.78/1.48      ( r2_hidden(sK0(k2_relat_1(sK6),sK5),k2_relat_1(sK6))
% 6.78/1.48      | r1_xboole_0(k2_relat_1(sK6),sK5) ),
% 6.78/1.48      inference(instantiation,[status(thm)],[c_3]) ).
% 6.78/1.48  
% 6.78/1.48  cnf(c_2,plain,
% 6.78/1.48      ( r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1) ),
% 6.78/1.48      inference(cnf_transformation,[],[f44]) ).
% 6.78/1.48  
% 6.78/1.48  cnf(c_1296,plain,
% 6.78/1.48      ( r2_hidden(sK0(k2_relat_1(sK6),sK5),sK5)
% 6.78/1.48      | r1_xboole_0(k2_relat_1(sK6),sK5) ),
% 6.78/1.48      inference(instantiation,[status(thm)],[c_2]) ).
% 6.78/1.48  
% 6.78/1.48  cnf(c_687,plain,
% 6.78/1.48      ( sK6 = sK6 ),
% 6.78/1.48      inference(instantiation,[status(thm)],[c_666]) ).
% 6.78/1.48  
% 6.78/1.48  cnf(c_672,plain,
% 6.78/1.48      ( X0 != X1 | k1_relat_1(X0) = k1_relat_1(X1) ),
% 6.78/1.48      theory(equality) ).
% 6.78/1.48  
% 6.78/1.48  cnf(c_681,plain,
% 6.78/1.48      ( k1_relat_1(sK6) = k1_relat_1(sK6) | sK6 != sK6 ),
% 6.78/1.48      inference(instantiation,[status(thm)],[c_672]) ).
% 6.78/1.48  
% 6.78/1.48  cnf(c_12,plain,
% 6.78/1.48      ( ~ v1_relat_1(X0)
% 6.78/1.48      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 6.78/1.48      inference(cnf_transformation,[],[f54]) ).
% 6.78/1.48  
% 6.78/1.48  cnf(c_44,plain,
% 6.78/1.48      ( ~ v1_relat_1(sK6)
% 6.78/1.48      | k9_relat_1(sK6,k1_relat_1(sK6)) = k2_relat_1(sK6) ),
% 6.78/1.48      inference(instantiation,[status(thm)],[c_12]) ).
% 6.78/1.48  
% 6.78/1.48  cnf(c_23,plain,
% 6.78/1.48      ( k1_xboole_0 = k10_relat_1(sK6,sK5)
% 6.78/1.48      | r1_xboole_0(k2_relat_1(sK6),sK5) = iProver_top ),
% 6.78/1.48      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 6.78/1.48  
% 6.78/1.48  cnf(contradiction,plain,
% 6.78/1.48      ( $false ),
% 6.78/1.48      inference(minisat,
% 6.78/1.48                [status(thm)],
% 6.78/1.48                [c_30611,c_14855,c_7700,c_5881,c_3515,c_3516,c_3343,
% 6.78/1.48                 c_3060,c_3055,c_1961,c_1960,c_1305,c_1296,c_687,c_681,
% 6.78/1.48                 c_44,c_19,c_23,c_21]) ).
% 6.78/1.48  
% 6.78/1.48  
% 6.78/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 6.78/1.48  
% 6.78/1.48  ------                               Statistics
% 6.78/1.48  
% 6.78/1.48  ------ General
% 6.78/1.48  
% 6.78/1.48  abstr_ref_over_cycles:                  0
% 6.78/1.48  abstr_ref_under_cycles:                 0
% 6.78/1.48  gc_basic_clause_elim:                   0
% 6.78/1.48  forced_gc_time:                         0
% 6.78/1.48  parsing_time:                           0.009
% 6.78/1.48  unif_index_cands_time:                  0.
% 6.78/1.48  unif_index_add_time:                    0.
% 6.78/1.48  orderings_time:                         0.
% 6.78/1.48  out_proof_time:                         0.008
% 6.78/1.48  total_time:                             0.654
% 6.78/1.48  num_of_symbols:                         48
% 6.78/1.48  num_of_terms:                           23971
% 6.78/1.48  
% 6.78/1.48  ------ Preprocessing
% 6.78/1.48  
% 6.78/1.48  num_of_splits:                          0
% 6.78/1.48  num_of_split_atoms:                     0
% 6.78/1.48  num_of_reused_defs:                     0
% 6.78/1.48  num_eq_ax_congr_red:                    37
% 6.78/1.48  num_of_sem_filtered_clauses:            1
% 6.78/1.48  num_of_subtypes:                        0
% 6.78/1.48  monotx_restored_types:                  0
% 6.78/1.48  sat_num_of_epr_types:                   0
% 6.78/1.48  sat_num_of_non_cyclic_types:            0
% 6.78/1.48  sat_guarded_non_collapsed_types:        0
% 6.78/1.48  num_pure_diseq_elim:                    0
% 6.78/1.48  simp_replaced_by:                       0
% 6.78/1.48  res_preprocessed:                       108
% 6.78/1.48  prep_upred:                             0
% 6.78/1.48  prep_unflattend:                        11
% 6.78/1.48  smt_new_axioms:                         0
% 6.78/1.48  pred_elim_cands:                        2
% 6.78/1.48  pred_elim:                              1
% 6.78/1.48  pred_elim_cl:                           1
% 6.78/1.48  pred_elim_cycles:                       3
% 6.78/1.48  merged_defs:                            8
% 6.78/1.48  merged_defs_ncl:                        0
% 6.78/1.48  bin_hyper_res:                          8
% 6.78/1.48  prep_cycles:                            4
% 6.78/1.48  pred_elim_time:                         0.003
% 6.78/1.48  splitting_time:                         0.
% 6.78/1.48  sem_filter_time:                        0.
% 6.78/1.48  monotx_time:                            0.
% 6.78/1.48  subtype_inf_time:                       0.
% 6.78/1.48  
% 6.78/1.48  ------ Problem properties
% 6.78/1.48  
% 6.78/1.48  clauses:                                21
% 6.78/1.48  conjectures:                            2
% 6.78/1.48  epr:                                    3
% 6.78/1.48  horn:                                   16
% 6.78/1.48  ground:                                 3
% 6.78/1.48  unary:                                  2
% 6.78/1.48  binary:                                 16
% 6.78/1.48  lits:                                   43
% 6.78/1.48  lits_eq:                                4
% 6.78/1.48  fd_pure:                                0
% 6.78/1.48  fd_pseudo:                              0
% 6.78/1.48  fd_cond:                                1
% 6.78/1.48  fd_pseudo_cond:                         0
% 6.78/1.48  ac_symbols:                             0
% 6.78/1.48  
% 6.78/1.48  ------ Propositional Solver
% 6.78/1.48  
% 6.78/1.48  prop_solver_calls:                      32
% 6.78/1.48  prop_fast_solver_calls:                 1040
% 6.78/1.48  smt_solver_calls:                       0
% 6.78/1.48  smt_fast_solver_calls:                  0
% 6.78/1.48  prop_num_of_clauses:                    11897
% 6.78/1.48  prop_preprocess_simplified:             20800
% 6.78/1.48  prop_fo_subsumed:                       3
% 6.78/1.48  prop_solver_time:                       0.
% 6.78/1.48  smt_solver_time:                        0.
% 6.78/1.48  smt_fast_solver_time:                   0.
% 6.78/1.48  prop_fast_solver_time:                  0.
% 6.78/1.48  prop_unsat_core_time:                   0.
% 6.78/1.48  
% 6.78/1.48  ------ QBF
% 6.78/1.48  
% 6.78/1.48  qbf_q_res:                              0
% 6.78/1.48  qbf_num_tautologies:                    0
% 6.78/1.48  qbf_prep_cycles:                        0
% 6.78/1.48  
% 6.78/1.48  ------ BMC1
% 6.78/1.48  
% 6.78/1.48  bmc1_current_bound:                     -1
% 6.78/1.48  bmc1_last_solved_bound:                 -1
% 6.78/1.48  bmc1_unsat_core_size:                   -1
% 6.78/1.48  bmc1_unsat_core_parents_size:           -1
% 6.78/1.48  bmc1_merge_next_fun:                    0
% 6.78/1.48  bmc1_unsat_core_clauses_time:           0.
% 6.78/1.48  
% 6.78/1.48  ------ Instantiation
% 6.78/1.48  
% 6.78/1.48  inst_num_of_clauses:                    2689
% 6.78/1.48  inst_num_in_passive:                    1192
% 6.78/1.48  inst_num_in_active:                     1068
% 6.78/1.48  inst_num_in_unprocessed:                430
% 6.78/1.48  inst_num_of_loops:                      1239
% 6.78/1.48  inst_num_of_learning_restarts:          0
% 6.78/1.48  inst_num_moves_active_passive:          165
% 6.78/1.48  inst_lit_activity:                      0
% 6.78/1.48  inst_lit_activity_moves:                0
% 6.78/1.48  inst_num_tautologies:                   0
% 6.78/1.48  inst_num_prop_implied:                  0
% 6.78/1.48  inst_num_existing_simplified:           0
% 6.78/1.48  inst_num_eq_res_simplified:             0
% 6.78/1.48  inst_num_child_elim:                    0
% 6.78/1.48  inst_num_of_dismatching_blockings:      2119
% 6.78/1.48  inst_num_of_non_proper_insts:           2826
% 6.78/1.48  inst_num_of_duplicates:                 0
% 6.78/1.48  inst_inst_num_from_inst_to_res:         0
% 6.78/1.48  inst_dismatching_checking_time:         0.
% 6.78/1.48  
% 6.78/1.48  ------ Resolution
% 6.78/1.48  
% 6.78/1.48  res_num_of_clauses:                     0
% 6.78/1.48  res_num_in_passive:                     0
% 6.78/1.48  res_num_in_active:                      0
% 6.78/1.48  res_num_of_loops:                       112
% 6.78/1.48  res_forward_subset_subsumed:            135
% 6.78/1.48  res_backward_subset_subsumed:           6
% 6.78/1.48  res_forward_subsumed:                   0
% 6.78/1.48  res_backward_subsumed:                  0
% 6.78/1.48  res_forward_subsumption_resolution:     0
% 6.78/1.48  res_backward_subsumption_resolution:    2
% 6.78/1.48  res_clause_to_clause_subsumption:       4657
% 6.78/1.48  res_orphan_elimination:                 0
% 6.78/1.48  res_tautology_del:                      206
% 6.78/1.48  res_num_eq_res_simplified:              0
% 6.78/1.48  res_num_sel_changes:                    0
% 6.78/1.48  res_moves_from_active_to_pass:          0
% 6.78/1.48  
% 6.78/1.48  ------ Superposition
% 6.78/1.48  
% 6.78/1.48  sup_time_total:                         0.
% 6.78/1.48  sup_time_generating:                    0.
% 6.78/1.48  sup_time_sim_full:                      0.
% 6.78/1.48  sup_time_sim_immed:                     0.
% 6.78/1.48  
% 6.78/1.48  sup_num_of_clauses:                     896
% 6.78/1.48  sup_num_in_active:                      237
% 6.78/1.48  sup_num_in_passive:                     659
% 6.78/1.48  sup_num_of_loops:                       246
% 6.78/1.48  sup_fw_superposition:                   1361
% 6.78/1.48  sup_bw_superposition:                   407
% 6.78/1.48  sup_immediate_simplified:               382
% 6.78/1.48  sup_given_eliminated:                   6
% 6.78/1.48  comparisons_done:                       0
% 6.78/1.48  comparisons_avoided:                    0
% 6.78/1.48  
% 6.78/1.48  ------ Simplifications
% 6.78/1.48  
% 6.78/1.48  
% 6.78/1.48  sim_fw_subset_subsumed:                 104
% 6.78/1.48  sim_bw_subset_subsumed:                 11
% 6.78/1.48  sim_fw_subsumed:                        169
% 6.78/1.48  sim_bw_subsumed:                        0
% 6.78/1.48  sim_fw_subsumption_res:                 1
% 6.78/1.48  sim_bw_subsumption_res:                 0
% 6.78/1.48  sim_tautology_del:                      6
% 6.78/1.48  sim_eq_tautology_del:                   17
% 6.78/1.48  sim_eq_res_simp:                        1
% 6.78/1.48  sim_fw_demodulated:                     1
% 6.78/1.48  sim_bw_demodulated:                     20
% 6.78/1.48  sim_light_normalised:                   145
% 6.78/1.48  sim_joinable_taut:                      0
% 6.78/1.48  sim_joinable_simp:                      0
% 6.78/1.48  sim_ac_normalised:                      0
% 6.78/1.48  sim_smt_subsumption:                    0
% 6.78/1.48  
%------------------------------------------------------------------------------
