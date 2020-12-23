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
% DateTime   : Thu Dec  3 11:43:16 EST 2020

% Result     : Theorem 3.67s
% Output     : CNFRefutation 3.67s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 180 expanded)
%              Number of clauses        :   44 (  51 expanded)
%              Number of leaves         :   21 (  49 expanded)
%              Depth                    :   14
%              Number of atoms          :  315 ( 660 expanded)
%              Number of equality atoms :   54 (  57 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k3_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f18])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f8,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
             => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
     => ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(sK8))
        & r1_tarski(X0,sK8)
        & v1_relat_1(sK8) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
            & r1_tarski(X0,X1)
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(sK7),k3_relat_1(X1))
          & r1_tarski(sK7,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ~ r1_tarski(k3_relat_1(sK7),k3_relat_1(sK8))
    & r1_tarski(sK7,sK8)
    & v1_relat_1(sK8)
    & v1_relat_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f17,f35,f34])).

fof(f55,plain,(
    r1_tarski(sK7,sK8) ),
    inference(cnf_transformation,[],[f36])).

fof(f54,plain,(
    v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f36])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f26,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK2(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK1(X0,X1),X3),X0)
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK1(X0,X1),X4),X0)
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK1(X0,X1),X3),X0)
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f23,f26,f25,f24])).

fof(f42,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f60,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f42])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f28])).

fof(f32,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK5(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0)
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK4(X0,X1)),X0)
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0)
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0)
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK6(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f29,f32,f31,f30])).

fof(f46,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f62,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK6(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f46])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f40,f41])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f50,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f58,plain,(
    ! [X0] :
      ( k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f50,f41])).

fof(f56,plain,(
    ~ r1_tarski(k3_relat_1(sK7),k3_relat_1(sK8)) ),
    inference(cnf_transformation,[],[f36])).

fof(f53,plain,(
    v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_14,plain,
    ( r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_16,negated_conjecture,
    ( r1_tarski(sK7,sK8) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_724,plain,
    ( r2_hidden(X0,sK8)
    | ~ r2_hidden(X0,sK7) ),
    inference(resolution,[status(thm)],[c_2,c_16])).

cnf(c_1510,plain,
    ( r2_hidden(X0,k3_relat_1(sK8))
    | ~ r2_hidden(k4_tarski(X0,X1),sK7)
    | ~ v1_relat_1(sK8) ),
    inference(resolution,[status(thm)],[c_14,c_724])).

cnf(c_17,negated_conjecture,
    ( v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1513,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK7)
    | r2_hidden(X0,k3_relat_1(sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1510,c_17])).

cnf(c_1514,plain,
    ( r2_hidden(X0,k3_relat_1(sK8))
    | ~ r2_hidden(k4_tarski(X0,X1),sK7) ),
    inference(renaming,[status(thm)],[c_1513])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,sK3(X1,X0)),X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2444,plain,
    ( r2_hidden(X0,k3_relat_1(sK8))
    | ~ r2_hidden(X0,k1_relat_1(sK7)) ),
    inference(resolution,[status(thm)],[c_1514,c_7])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_2720,plain,
    ( ~ r2_hidden(sK0(X0,k3_relat_1(sK8)),k1_relat_1(sK7))
    | r1_tarski(X0,k3_relat_1(sK8)) ),
    inference(resolution,[status(thm)],[c_2444,c_0])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_5438,plain,
    ( r1_tarski(k1_relat_1(sK7),k3_relat_1(sK8)) ),
    inference(resolution,[status(thm)],[c_2720,c_1])).

cnf(c_13,plain,
    ( r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1356,plain,
    ( r2_hidden(X0,k3_relat_1(sK8))
    | ~ r2_hidden(k4_tarski(X1,X0),sK7)
    | ~ v1_relat_1(sK8) ),
    inference(resolution,[status(thm)],[c_13,c_724])).

cnf(c_1361,plain,
    ( ~ r2_hidden(k4_tarski(X1,X0),sK7)
    | r2_hidden(X0,k3_relat_1(sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1356,c_17])).

cnf(c_1362,plain,
    ( r2_hidden(X0,k3_relat_1(sK8))
    | ~ r2_hidden(k4_tarski(X1,X0),sK7) ),
    inference(renaming,[status(thm)],[c_1361])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(k4_tarski(sK6(X1,X0),X0),X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2435,plain,
    ( r2_hidden(X0,k3_relat_1(sK8))
    | ~ r2_hidden(X0,k2_relat_1(sK7)) ),
    inference(resolution,[status(thm)],[c_1362,c_11])).

cnf(c_2696,plain,
    ( ~ r2_hidden(sK0(X0,k3_relat_1(sK8)),k2_relat_1(sK7))
    | r1_tarski(X0,k3_relat_1(sK8)) ),
    inference(resolution,[status(thm)],[c_2435,c_0])).

cnf(c_5242,plain,
    ( r1_tarski(k2_relat_1(sK7),k3_relat_1(sK8)) ),
    inference(resolution,[status(thm)],[c_2696,c_1])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1878,plain,
    ( ~ r1_tarski(k2_relat_1(sK7),X0)
    | ~ r1_tarski(k1_relat_1(sK7),X0)
    | r1_tarski(k3_tarski(k2_tarski(k1_relat_1(sK7),k2_relat_1(sK7))),X0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3481,plain,
    ( ~ r1_tarski(k2_relat_1(sK7),k3_relat_1(sK8))
    | ~ r1_tarski(k1_relat_1(sK7),k3_relat_1(sK8))
    | r1_tarski(k3_tarski(k2_tarski(k1_relat_1(sK7),k2_relat_1(sK7))),k3_relat_1(sK8)) ),
    inference(instantiation,[status(thm)],[c_1878])).

cnf(c_179,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_675,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_relat_1(sK7),k3_relat_1(sK8))
    | k3_relat_1(sK8) != X1
    | k3_relat_1(sK7) != X0 ),
    inference(instantiation,[status(thm)],[c_179])).

cnf(c_1613,plain,
    ( r1_tarski(k3_relat_1(sK7),k3_relat_1(sK8))
    | ~ r1_tarski(k3_tarski(k2_tarski(k1_relat_1(sK7),k2_relat_1(sK7))),X0)
    | k3_relat_1(sK8) != X0
    | k3_relat_1(sK7) != k3_tarski(k2_tarski(k1_relat_1(sK7),k2_relat_1(sK7))) ),
    inference(instantiation,[status(thm)],[c_675])).

cnf(c_3155,plain,
    ( r1_tarski(k3_relat_1(sK7),k3_relat_1(sK8))
    | ~ r1_tarski(k3_tarski(k2_tarski(k1_relat_1(sK7),k2_relat_1(sK7))),k3_relat_1(sK8))
    | k3_relat_1(sK8) != k3_relat_1(sK8)
    | k3_relat_1(sK7) != k3_tarski(k2_tarski(k1_relat_1(sK7),k2_relat_1(sK7))) ),
    inference(instantiation,[status(thm)],[c_1613])).

cnf(c_177,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1080,plain,
    ( k3_relat_1(sK8) = k3_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_177])).

cnf(c_178,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_750,plain,
    ( X0 != X1
    | k3_relat_1(sK7) != X1
    | k3_relat_1(sK7) = X0 ),
    inference(instantiation,[status(thm)],[c_178])).

cnf(c_814,plain,
    ( X0 != k3_relat_1(X1)
    | k3_relat_1(sK7) = X0
    | k3_relat_1(sK7) != k3_relat_1(X1) ),
    inference(instantiation,[status(thm)],[c_750])).

cnf(c_1002,plain,
    ( k3_relat_1(sK7) != k3_relat_1(X0)
    | k3_relat_1(sK7) = k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0)))
    | k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))) != k3_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_814])).

cnf(c_1003,plain,
    ( k3_relat_1(sK7) != k3_relat_1(sK7)
    | k3_relat_1(sK7) = k3_tarski(k2_tarski(k1_relat_1(sK7),k2_relat_1(sK7)))
    | k3_tarski(k2_tarski(k1_relat_1(sK7),k2_relat_1(sK7))) != k3_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_1002])).

cnf(c_194,plain,
    ( sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_177])).

cnf(c_184,plain,
    ( X0 != X1
    | k3_relat_1(X0) = k3_relat_1(X1) ),
    theory(equality)).

cnf(c_191,plain,
    ( k3_relat_1(sK7) = k3_relat_1(sK7)
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_184])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_28,plain,
    ( ~ v1_relat_1(sK7)
    | k3_tarski(k2_tarski(k1_relat_1(sK7),k2_relat_1(sK7))) = k3_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_15,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(sK7),k3_relat_1(sK8)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_18,negated_conjecture,
    ( v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f53])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5438,c_5242,c_3481,c_3155,c_1080,c_1003,c_194,c_191,c_28,c_15,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:05:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.67/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.67/1.00  
% 3.67/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.67/1.00  
% 3.67/1.00  ------  iProver source info
% 3.67/1.00  
% 3.67/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.67/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.67/1.00  git: non_committed_changes: false
% 3.67/1.00  git: last_make_outside_of_git: false
% 3.67/1.00  
% 3.67/1.00  ------ 
% 3.67/1.00  
% 3.67/1.00  ------ Input Options
% 3.67/1.00  
% 3.67/1.00  --out_options                           all
% 3.67/1.00  --tptp_safe_out                         true
% 3.67/1.00  --problem_path                          ""
% 3.67/1.00  --include_path                          ""
% 3.67/1.00  --clausifier                            res/vclausify_rel
% 3.67/1.00  --clausifier_options                    --mode clausify
% 3.67/1.00  --stdin                                 false
% 3.67/1.00  --stats_out                             sel
% 3.67/1.00  
% 3.67/1.00  ------ General Options
% 3.67/1.00  
% 3.67/1.00  --fof                                   false
% 3.67/1.00  --time_out_real                         604.99
% 3.67/1.00  --time_out_virtual                      -1.
% 3.67/1.00  --symbol_type_check                     false
% 3.67/1.00  --clausify_out                          false
% 3.67/1.00  --sig_cnt_out                           false
% 3.67/1.00  --trig_cnt_out                          false
% 3.67/1.00  --trig_cnt_out_tolerance                1.
% 3.67/1.00  --trig_cnt_out_sk_spl                   false
% 3.67/1.00  --abstr_cl_out                          false
% 3.67/1.00  
% 3.67/1.00  ------ Global Options
% 3.67/1.00  
% 3.67/1.00  --schedule                              none
% 3.67/1.00  --add_important_lit                     false
% 3.67/1.00  --prop_solver_per_cl                    1000
% 3.67/1.00  --min_unsat_core                        false
% 3.67/1.00  --soft_assumptions                      false
% 3.67/1.00  --soft_lemma_size                       3
% 3.67/1.00  --prop_impl_unit_size                   0
% 3.67/1.00  --prop_impl_unit                        []
% 3.67/1.00  --share_sel_clauses                     true
% 3.67/1.00  --reset_solvers                         false
% 3.67/1.00  --bc_imp_inh                            [conj_cone]
% 3.67/1.00  --conj_cone_tolerance                   3.
% 3.67/1.00  --extra_neg_conj                        none
% 3.67/1.00  --large_theory_mode                     true
% 3.67/1.00  --prolific_symb_bound                   200
% 3.67/1.00  --lt_threshold                          2000
% 3.67/1.00  --clause_weak_htbl                      true
% 3.67/1.00  --gc_record_bc_elim                     false
% 3.67/1.00  
% 3.67/1.00  ------ Preprocessing Options
% 3.67/1.00  
% 3.67/1.00  --preprocessing_flag                    true
% 3.67/1.00  --time_out_prep_mult                    0.1
% 3.67/1.00  --splitting_mode                        input
% 3.67/1.00  --splitting_grd                         true
% 3.67/1.00  --splitting_cvd                         false
% 3.67/1.00  --splitting_cvd_svl                     false
% 3.67/1.00  --splitting_nvd                         32
% 3.67/1.00  --sub_typing                            true
% 3.67/1.00  --prep_gs_sim                           false
% 3.67/1.00  --prep_unflatten                        true
% 3.67/1.00  --prep_res_sim                          true
% 3.67/1.00  --prep_upred                            true
% 3.67/1.00  --prep_sem_filter                       exhaustive
% 3.67/1.00  --prep_sem_filter_out                   false
% 3.67/1.00  --pred_elim                             false
% 3.67/1.00  --res_sim_input                         true
% 3.67/1.00  --eq_ax_congr_red                       true
% 3.67/1.00  --pure_diseq_elim                       true
% 3.67/1.00  --brand_transform                       false
% 3.67/1.00  --non_eq_to_eq                          false
% 3.67/1.00  --prep_def_merge                        true
% 3.67/1.00  --prep_def_merge_prop_impl              false
% 3.67/1.00  --prep_def_merge_mbd                    true
% 3.67/1.00  --prep_def_merge_tr_red                 false
% 3.67/1.00  --prep_def_merge_tr_cl                  false
% 3.67/1.00  --smt_preprocessing                     true
% 3.67/1.00  --smt_ac_axioms                         fast
% 3.67/1.00  --preprocessed_out                      false
% 3.67/1.00  --preprocessed_stats                    false
% 3.67/1.00  
% 3.67/1.00  ------ Abstraction refinement Options
% 3.67/1.00  
% 3.67/1.00  --abstr_ref                             []
% 3.67/1.00  --abstr_ref_prep                        false
% 3.67/1.00  --abstr_ref_until_sat                   false
% 3.67/1.00  --abstr_ref_sig_restrict                funpre
% 3.67/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.67/1.00  --abstr_ref_under                       []
% 3.67/1.00  
% 3.67/1.00  ------ SAT Options
% 3.67/1.00  
% 3.67/1.00  --sat_mode                              false
% 3.67/1.00  --sat_fm_restart_options                ""
% 3.67/1.00  --sat_gr_def                            false
% 3.67/1.00  --sat_epr_types                         true
% 3.67/1.00  --sat_non_cyclic_types                  false
% 3.67/1.00  --sat_finite_models                     false
% 3.67/1.00  --sat_fm_lemmas                         false
% 3.67/1.00  --sat_fm_prep                           false
% 3.67/1.00  --sat_fm_uc_incr                        true
% 3.67/1.00  --sat_out_model                         small
% 3.67/1.00  --sat_out_clauses                       false
% 3.67/1.00  
% 3.67/1.00  ------ QBF Options
% 3.67/1.00  
% 3.67/1.00  --qbf_mode                              false
% 3.67/1.00  --qbf_elim_univ                         false
% 3.67/1.00  --qbf_dom_inst                          none
% 3.67/1.00  --qbf_dom_pre_inst                      false
% 3.67/1.00  --qbf_sk_in                             false
% 3.67/1.00  --qbf_pred_elim                         true
% 3.67/1.00  --qbf_split                             512
% 3.67/1.00  
% 3.67/1.00  ------ BMC1 Options
% 3.67/1.00  
% 3.67/1.00  --bmc1_incremental                      false
% 3.67/1.00  --bmc1_axioms                           reachable_all
% 3.67/1.00  --bmc1_min_bound                        0
% 3.67/1.00  --bmc1_max_bound                        -1
% 3.67/1.00  --bmc1_max_bound_default                -1
% 3.67/1.00  --bmc1_symbol_reachability              true
% 3.67/1.00  --bmc1_property_lemmas                  false
% 3.67/1.00  --bmc1_k_induction                      false
% 3.67/1.00  --bmc1_non_equiv_states                 false
% 3.67/1.00  --bmc1_deadlock                         false
% 3.67/1.00  --bmc1_ucm                              false
% 3.67/1.00  --bmc1_add_unsat_core                   none
% 3.67/1.00  --bmc1_unsat_core_children              false
% 3.67/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.67/1.00  --bmc1_out_stat                         full
% 3.67/1.00  --bmc1_ground_init                      false
% 3.67/1.00  --bmc1_pre_inst_next_state              false
% 3.67/1.00  --bmc1_pre_inst_state                   false
% 3.67/1.00  --bmc1_pre_inst_reach_state             false
% 3.67/1.00  --bmc1_out_unsat_core                   false
% 3.67/1.00  --bmc1_aig_witness_out                  false
% 3.67/1.00  --bmc1_verbose                          false
% 3.67/1.00  --bmc1_dump_clauses_tptp                false
% 3.67/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.67/1.00  --bmc1_dump_file                        -
% 3.67/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.67/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.67/1.00  --bmc1_ucm_extend_mode                  1
% 3.67/1.00  --bmc1_ucm_init_mode                    2
% 3.67/1.00  --bmc1_ucm_cone_mode                    none
% 3.67/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.67/1.00  --bmc1_ucm_relax_model                  4
% 3.67/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.67/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.67/1.00  --bmc1_ucm_layered_model                none
% 3.67/1.00  --bmc1_ucm_max_lemma_size               10
% 3.67/1.00  
% 3.67/1.00  ------ AIG Options
% 3.67/1.00  
% 3.67/1.00  --aig_mode                              false
% 3.67/1.00  
% 3.67/1.00  ------ Instantiation Options
% 3.67/1.00  
% 3.67/1.00  --instantiation_flag                    true
% 3.67/1.00  --inst_sos_flag                         false
% 3.67/1.00  --inst_sos_phase                        true
% 3.67/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.67/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.67/1.00  --inst_lit_sel_side                     num_symb
% 3.67/1.00  --inst_solver_per_active                1400
% 3.67/1.00  --inst_solver_calls_frac                1.
% 3.67/1.00  --inst_passive_queue_type               priority_queues
% 3.67/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.67/1.00  --inst_passive_queues_freq              [25;2]
% 3.67/1.00  --inst_dismatching                      true
% 3.67/1.00  --inst_eager_unprocessed_to_passive     true
% 3.67/1.00  --inst_prop_sim_given                   true
% 3.67/1.00  --inst_prop_sim_new                     false
% 3.67/1.00  --inst_subs_new                         false
% 3.67/1.00  --inst_eq_res_simp                      false
% 3.67/1.00  --inst_subs_given                       false
% 3.67/1.00  --inst_orphan_elimination               true
% 3.67/1.00  --inst_learning_loop_flag               true
% 3.67/1.00  --inst_learning_start                   3000
% 3.67/1.00  --inst_learning_factor                  2
% 3.67/1.00  --inst_start_prop_sim_after_learn       3
% 3.67/1.00  --inst_sel_renew                        solver
% 3.67/1.00  --inst_lit_activity_flag                true
% 3.67/1.00  --inst_restr_to_given                   false
% 3.67/1.00  --inst_activity_threshold               500
% 3.67/1.00  --inst_out_proof                        true
% 3.67/1.00  
% 3.67/1.00  ------ Resolution Options
% 3.67/1.00  
% 3.67/1.00  --resolution_flag                       true
% 3.67/1.00  --res_lit_sel                           adaptive
% 3.67/1.00  --res_lit_sel_side                      none
% 3.67/1.00  --res_ordering                          kbo
% 3.67/1.00  --res_to_prop_solver                    active
% 3.67/1.00  --res_prop_simpl_new                    false
% 3.67/1.00  --res_prop_simpl_given                  true
% 3.67/1.00  --res_passive_queue_type                priority_queues
% 3.67/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.67/1.00  --res_passive_queues_freq               [15;5]
% 3.67/1.00  --res_forward_subs                      full
% 3.67/1.00  --res_backward_subs                     full
% 3.67/1.00  --res_forward_subs_resolution           true
% 3.67/1.00  --res_backward_subs_resolution          true
% 3.67/1.00  --res_orphan_elimination                true
% 3.67/1.00  --res_time_limit                        2.
% 3.67/1.00  --res_out_proof                         true
% 3.67/1.00  
% 3.67/1.00  ------ Superposition Options
% 3.67/1.00  
% 3.67/1.00  --superposition_flag                    true
% 3.67/1.00  --sup_passive_queue_type                priority_queues
% 3.67/1.00  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.67/1.00  --sup_passive_queues_freq               [1;4]
% 3.67/1.00  --demod_completeness_check              fast
% 3.67/1.00  --demod_use_ground                      true
% 3.67/1.00  --sup_to_prop_solver                    passive
% 3.67/1.00  --sup_prop_simpl_new                    true
% 3.67/1.00  --sup_prop_simpl_given                  true
% 3.67/1.00  --sup_fun_splitting                     false
% 3.67/1.00  --sup_smt_interval                      50000
% 3.67/1.00  
% 3.67/1.00  ------ Superposition Simplification Setup
% 3.67/1.00  
% 3.67/1.00  --sup_indices_passive                   []
% 3.67/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.67/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.67/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.67/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.67/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.67/1.00  --sup_full_bw                           [BwDemod]
% 3.67/1.00  --sup_immed_triv                        [TrivRules]
% 3.67/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.67/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.67/1.00  --sup_immed_bw_main                     []
% 3.67/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.67/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.67/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.67/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.67/1.00  
% 3.67/1.00  ------ Combination Options
% 3.67/1.00  
% 3.67/1.00  --comb_res_mult                         3
% 3.67/1.00  --comb_sup_mult                         2
% 3.67/1.00  --comb_inst_mult                        10
% 3.67/1.00  
% 3.67/1.00  ------ Debug Options
% 3.67/1.00  
% 3.67/1.00  --dbg_backtrace                         false
% 3.67/1.00  --dbg_dump_prop_clauses                 false
% 3.67/1.00  --dbg_dump_prop_clauses_file            -
% 3.67/1.00  --dbg_out_stat                          false
% 3.67/1.00  ------ Parsing...
% 3.67/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.67/1.00  
% 3.67/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.67/1.00  
% 3.67/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.67/1.00  
% 3.67/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.67/1.00  ------ Proving...
% 3.67/1.00  ------ Problem Properties 
% 3.67/1.00  
% 3.67/1.00  
% 3.67/1.00  clauses                                 19
% 3.67/1.00  conjectures                             4
% 3.67/1.00  EPR                                     4
% 3.67/1.00  Horn                                    16
% 3.67/1.00  unary                                   4
% 3.67/1.00  binary                                  7
% 3.67/1.00  lits                                    42
% 3.67/1.00  lits eq                                 5
% 3.67/1.00  fd_pure                                 0
% 3.67/1.00  fd_pseudo                               0
% 3.67/1.00  fd_cond                                 0
% 3.67/1.00  fd_pseudo_cond                          4
% 3.67/1.00  AC symbols                              0
% 3.67/1.00  
% 3.67/1.00  ------ Input Options Time Limit: Unbounded
% 3.67/1.00  
% 3.67/1.00  
% 3.67/1.00  ------ 
% 3.67/1.00  Current options:
% 3.67/1.00  ------ 
% 3.67/1.00  
% 3.67/1.00  ------ Input Options
% 3.67/1.00  
% 3.67/1.00  --out_options                           all
% 3.67/1.00  --tptp_safe_out                         true
% 3.67/1.00  --problem_path                          ""
% 3.67/1.00  --include_path                          ""
% 3.67/1.00  --clausifier                            res/vclausify_rel
% 3.67/1.00  --clausifier_options                    --mode clausify
% 3.67/1.00  --stdin                                 false
% 3.67/1.00  --stats_out                             sel
% 3.67/1.00  
% 3.67/1.00  ------ General Options
% 3.67/1.00  
% 3.67/1.00  --fof                                   false
% 3.67/1.00  --time_out_real                         604.99
% 3.67/1.00  --time_out_virtual                      -1.
% 3.67/1.00  --symbol_type_check                     false
% 3.67/1.00  --clausify_out                          false
% 3.67/1.00  --sig_cnt_out                           false
% 3.67/1.00  --trig_cnt_out                          false
% 3.67/1.00  --trig_cnt_out_tolerance                1.
% 3.67/1.00  --trig_cnt_out_sk_spl                   false
% 3.67/1.00  --abstr_cl_out                          false
% 3.67/1.00  
% 3.67/1.00  ------ Global Options
% 3.67/1.00  
% 3.67/1.00  --schedule                              none
% 3.67/1.00  --add_important_lit                     false
% 3.67/1.00  --prop_solver_per_cl                    1000
% 3.67/1.00  --min_unsat_core                        false
% 3.67/1.00  --soft_assumptions                      false
% 3.67/1.00  --soft_lemma_size                       3
% 3.67/1.00  --prop_impl_unit_size                   0
% 3.67/1.00  --prop_impl_unit                        []
% 3.67/1.00  --share_sel_clauses                     true
% 3.67/1.00  --reset_solvers                         false
% 3.67/1.00  --bc_imp_inh                            [conj_cone]
% 3.67/1.00  --conj_cone_tolerance                   3.
% 3.67/1.00  --extra_neg_conj                        none
% 3.67/1.00  --large_theory_mode                     true
% 3.67/1.00  --prolific_symb_bound                   200
% 3.67/1.00  --lt_threshold                          2000
% 3.67/1.00  --clause_weak_htbl                      true
% 3.67/1.00  --gc_record_bc_elim                     false
% 3.67/1.00  
% 3.67/1.00  ------ Preprocessing Options
% 3.67/1.00  
% 3.67/1.00  --preprocessing_flag                    true
% 3.67/1.00  --time_out_prep_mult                    0.1
% 3.67/1.00  --splitting_mode                        input
% 3.67/1.00  --splitting_grd                         true
% 3.67/1.00  --splitting_cvd                         false
% 3.67/1.00  --splitting_cvd_svl                     false
% 3.67/1.00  --splitting_nvd                         32
% 3.67/1.00  --sub_typing                            true
% 3.67/1.00  --prep_gs_sim                           false
% 3.67/1.00  --prep_unflatten                        true
% 3.67/1.00  --prep_res_sim                          true
% 3.67/1.00  --prep_upred                            true
% 3.67/1.00  --prep_sem_filter                       exhaustive
% 3.67/1.00  --prep_sem_filter_out                   false
% 3.67/1.00  --pred_elim                             false
% 3.67/1.00  --res_sim_input                         true
% 3.67/1.00  --eq_ax_congr_red                       true
% 3.67/1.00  --pure_diseq_elim                       true
% 3.67/1.00  --brand_transform                       false
% 3.67/1.00  --non_eq_to_eq                          false
% 3.67/1.00  --prep_def_merge                        true
% 3.67/1.00  --prep_def_merge_prop_impl              false
% 3.67/1.00  --prep_def_merge_mbd                    true
% 3.67/1.00  --prep_def_merge_tr_red                 false
% 3.67/1.00  --prep_def_merge_tr_cl                  false
% 3.67/1.00  --smt_preprocessing                     true
% 3.67/1.00  --smt_ac_axioms                         fast
% 3.67/1.00  --preprocessed_out                      false
% 3.67/1.00  --preprocessed_stats                    false
% 3.67/1.00  
% 3.67/1.00  ------ Abstraction refinement Options
% 3.67/1.00  
% 3.67/1.00  --abstr_ref                             []
% 3.67/1.00  --abstr_ref_prep                        false
% 3.67/1.00  --abstr_ref_until_sat                   false
% 3.67/1.00  --abstr_ref_sig_restrict                funpre
% 3.67/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.67/1.00  --abstr_ref_under                       []
% 3.67/1.00  
% 3.67/1.00  ------ SAT Options
% 3.67/1.00  
% 3.67/1.00  --sat_mode                              false
% 3.67/1.00  --sat_fm_restart_options                ""
% 3.67/1.00  --sat_gr_def                            false
% 3.67/1.00  --sat_epr_types                         true
% 3.67/1.00  --sat_non_cyclic_types                  false
% 3.67/1.00  --sat_finite_models                     false
% 3.67/1.00  --sat_fm_lemmas                         false
% 3.67/1.00  --sat_fm_prep                           false
% 3.67/1.00  --sat_fm_uc_incr                        true
% 3.67/1.00  --sat_out_model                         small
% 3.67/1.00  --sat_out_clauses                       false
% 3.67/1.00  
% 3.67/1.00  ------ QBF Options
% 3.67/1.00  
% 3.67/1.00  --qbf_mode                              false
% 3.67/1.00  --qbf_elim_univ                         false
% 3.67/1.00  --qbf_dom_inst                          none
% 3.67/1.00  --qbf_dom_pre_inst                      false
% 3.67/1.00  --qbf_sk_in                             false
% 3.67/1.00  --qbf_pred_elim                         true
% 3.67/1.00  --qbf_split                             512
% 3.67/1.00  
% 3.67/1.00  ------ BMC1 Options
% 3.67/1.00  
% 3.67/1.00  --bmc1_incremental                      false
% 3.67/1.00  --bmc1_axioms                           reachable_all
% 3.67/1.00  --bmc1_min_bound                        0
% 3.67/1.00  --bmc1_max_bound                        -1
% 3.67/1.00  --bmc1_max_bound_default                -1
% 3.67/1.00  --bmc1_symbol_reachability              true
% 3.67/1.00  --bmc1_property_lemmas                  false
% 3.67/1.00  --bmc1_k_induction                      false
% 3.67/1.00  --bmc1_non_equiv_states                 false
% 3.67/1.00  --bmc1_deadlock                         false
% 3.67/1.00  --bmc1_ucm                              false
% 3.67/1.00  --bmc1_add_unsat_core                   none
% 3.67/1.00  --bmc1_unsat_core_children              false
% 3.67/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.67/1.00  --bmc1_out_stat                         full
% 3.67/1.00  --bmc1_ground_init                      false
% 3.67/1.00  --bmc1_pre_inst_next_state              false
% 3.67/1.00  --bmc1_pre_inst_state                   false
% 3.67/1.00  --bmc1_pre_inst_reach_state             false
% 3.67/1.00  --bmc1_out_unsat_core                   false
% 3.67/1.00  --bmc1_aig_witness_out                  false
% 3.67/1.00  --bmc1_verbose                          false
% 3.67/1.00  --bmc1_dump_clauses_tptp                false
% 3.67/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.67/1.00  --bmc1_dump_file                        -
% 3.67/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.67/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.67/1.00  --bmc1_ucm_extend_mode                  1
% 3.67/1.00  --bmc1_ucm_init_mode                    2
% 3.67/1.00  --bmc1_ucm_cone_mode                    none
% 3.67/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.67/1.00  --bmc1_ucm_relax_model                  4
% 3.67/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.67/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.67/1.00  --bmc1_ucm_layered_model                none
% 3.67/1.00  --bmc1_ucm_max_lemma_size               10
% 3.67/1.00  
% 3.67/1.00  ------ AIG Options
% 3.67/1.00  
% 3.67/1.00  --aig_mode                              false
% 3.67/1.00  
% 3.67/1.00  ------ Instantiation Options
% 3.67/1.00  
% 3.67/1.00  --instantiation_flag                    true
% 3.67/1.00  --inst_sos_flag                         false
% 3.67/1.00  --inst_sos_phase                        true
% 3.67/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.67/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.67/1.00  --inst_lit_sel_side                     num_symb
% 3.67/1.00  --inst_solver_per_active                1400
% 3.67/1.00  --inst_solver_calls_frac                1.
% 3.67/1.00  --inst_passive_queue_type               priority_queues
% 3.67/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.67/1.00  --inst_passive_queues_freq              [25;2]
% 3.67/1.00  --inst_dismatching                      true
% 3.67/1.00  --inst_eager_unprocessed_to_passive     true
% 3.67/1.00  --inst_prop_sim_given                   true
% 3.67/1.00  --inst_prop_sim_new                     false
% 3.67/1.00  --inst_subs_new                         false
% 3.67/1.00  --inst_eq_res_simp                      false
% 3.67/1.00  --inst_subs_given                       false
% 3.67/1.00  --inst_orphan_elimination               true
% 3.67/1.00  --inst_learning_loop_flag               true
% 3.67/1.00  --inst_learning_start                   3000
% 3.67/1.00  --inst_learning_factor                  2
% 3.67/1.00  --inst_start_prop_sim_after_learn       3
% 3.67/1.00  --inst_sel_renew                        solver
% 3.67/1.00  --inst_lit_activity_flag                true
% 3.67/1.00  --inst_restr_to_given                   false
% 3.67/1.00  --inst_activity_threshold               500
% 3.67/1.00  --inst_out_proof                        true
% 3.67/1.00  
% 3.67/1.00  ------ Resolution Options
% 3.67/1.00  
% 3.67/1.00  --resolution_flag                       true
% 3.67/1.00  --res_lit_sel                           adaptive
% 3.67/1.00  --res_lit_sel_side                      none
% 3.67/1.00  --res_ordering                          kbo
% 3.67/1.00  --res_to_prop_solver                    active
% 3.67/1.00  --res_prop_simpl_new                    false
% 3.67/1.00  --res_prop_simpl_given                  true
% 3.67/1.00  --res_passive_queue_type                priority_queues
% 3.67/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.67/1.00  --res_passive_queues_freq               [15;5]
% 3.67/1.00  --res_forward_subs                      full
% 3.67/1.00  --res_backward_subs                     full
% 3.67/1.00  --res_forward_subs_resolution           true
% 3.67/1.00  --res_backward_subs_resolution          true
% 3.67/1.00  --res_orphan_elimination                true
% 3.67/1.00  --res_time_limit                        2.
% 3.67/1.00  --res_out_proof                         true
% 3.67/1.00  
% 3.67/1.00  ------ Superposition Options
% 3.67/1.00  
% 3.67/1.00  --superposition_flag                    true
% 3.67/1.00  --sup_passive_queue_type                priority_queues
% 3.67/1.00  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.67/1.00  --sup_passive_queues_freq               [1;4]
% 3.67/1.00  --demod_completeness_check              fast
% 3.67/1.00  --demod_use_ground                      true
% 3.67/1.00  --sup_to_prop_solver                    passive
% 3.67/1.00  --sup_prop_simpl_new                    true
% 3.67/1.00  --sup_prop_simpl_given                  true
% 3.67/1.00  --sup_fun_splitting                     false
% 3.67/1.00  --sup_smt_interval                      50000
% 3.67/1.00  
% 3.67/1.00  ------ Superposition Simplification Setup
% 3.67/1.00  
% 3.67/1.00  --sup_indices_passive                   []
% 3.67/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.67/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.67/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.67/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.67/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.67/1.00  --sup_full_bw                           [BwDemod]
% 3.67/1.00  --sup_immed_triv                        [TrivRules]
% 3.67/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.67/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.67/1.00  --sup_immed_bw_main                     []
% 3.67/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.67/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.67/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.67/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.67/1.00  
% 3.67/1.00  ------ Combination Options
% 3.67/1.00  
% 3.67/1.00  --comb_res_mult                         3
% 3.67/1.00  --comb_sup_mult                         2
% 3.67/1.00  --comb_inst_mult                        10
% 3.67/1.00  
% 3.67/1.00  ------ Debug Options
% 3.67/1.00  
% 3.67/1.00  --dbg_backtrace                         false
% 3.67/1.00  --dbg_dump_prop_clauses                 false
% 3.67/1.00  --dbg_dump_prop_clauses_file            -
% 3.67/1.00  --dbg_out_stat                          false
% 3.67/1.00  
% 3.67/1.00  
% 3.67/1.00  
% 3.67/1.00  
% 3.67/1.00  ------ Proving...
% 3.67/1.00  
% 3.67/1.00  
% 3.67/1.00  % SZS status Theorem for theBenchmark.p
% 3.67/1.00  
% 3.67/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.67/1.00  
% 3.67/1.00  fof(f7,axiom,(
% 3.67/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)))))),
% 3.67/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/1.00  
% 3.67/1.00  fof(f14,plain,(
% 3.67/1.00    ! [X0,X1,X2] : (((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 3.67/1.00    inference(ennf_transformation,[],[f7])).
% 3.67/1.00  
% 3.67/1.00  fof(f15,plain,(
% 3.67/1.00    ! [X0,X1,X2] : ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 3.67/1.00    inference(flattening,[],[f14])).
% 3.67/1.00  
% 3.67/1.00  fof(f51,plain,(
% 3.67/1.00    ( ! [X2,X0,X1] : (r2_hidden(X0,k3_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 3.67/1.00    inference(cnf_transformation,[],[f15])).
% 3.67/1.00  
% 3.67/1.00  fof(f1,axiom,(
% 3.67/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.67/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/1.00  
% 3.67/1.00  fof(f10,plain,(
% 3.67/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.67/1.00    inference(ennf_transformation,[],[f1])).
% 3.67/1.00  
% 3.67/1.00  fof(f18,plain,(
% 3.67/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.67/1.00    inference(nnf_transformation,[],[f10])).
% 3.67/1.00  
% 3.67/1.00  fof(f19,plain,(
% 3.67/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.67/1.00    inference(rectify,[],[f18])).
% 3.67/1.00  
% 3.67/1.00  fof(f20,plain,(
% 3.67/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.67/1.00    introduced(choice_axiom,[])).
% 3.67/1.00  
% 3.67/1.00  fof(f21,plain,(
% 3.67/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.67/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).
% 3.67/1.00  
% 3.67/1.00  fof(f37,plain,(
% 3.67/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.67/1.00    inference(cnf_transformation,[],[f21])).
% 3.67/1.00  
% 3.67/1.00  fof(f8,conjecture,(
% 3.67/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 3.67/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/1.00  
% 3.67/1.00  fof(f9,negated_conjecture,(
% 3.67/1.00    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 3.67/1.00    inference(negated_conjecture,[],[f8])).
% 3.67/1.00  
% 3.67/1.00  fof(f16,plain,(
% 3.67/1.00    ? [X0] : (? [X1] : ((~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 3.67/1.00    inference(ennf_transformation,[],[f9])).
% 3.67/1.00  
% 3.67/1.00  fof(f17,plain,(
% 3.67/1.00    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 3.67/1.00    inference(flattening,[],[f16])).
% 3.67/1.00  
% 3.67/1.00  fof(f35,plain,(
% 3.67/1.00    ( ! [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) => (~r1_tarski(k3_relat_1(X0),k3_relat_1(sK8)) & r1_tarski(X0,sK8) & v1_relat_1(sK8))) )),
% 3.67/1.00    introduced(choice_axiom,[])).
% 3.67/1.00  
% 3.67/1.00  fof(f34,plain,(
% 3.67/1.00    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k3_relat_1(sK7),k3_relat_1(X1)) & r1_tarski(sK7,X1) & v1_relat_1(X1)) & v1_relat_1(sK7))),
% 3.67/1.00    introduced(choice_axiom,[])).
% 3.67/1.00  
% 3.67/1.00  fof(f36,plain,(
% 3.67/1.00    (~r1_tarski(k3_relat_1(sK7),k3_relat_1(sK8)) & r1_tarski(sK7,sK8) & v1_relat_1(sK8)) & v1_relat_1(sK7)),
% 3.67/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f17,f35,f34])).
% 3.67/1.00  
% 3.67/1.00  fof(f55,plain,(
% 3.67/1.00    r1_tarski(sK7,sK8)),
% 3.67/1.00    inference(cnf_transformation,[],[f36])).
% 3.67/1.00  
% 3.67/1.00  fof(f54,plain,(
% 3.67/1.00    v1_relat_1(sK8)),
% 3.67/1.00    inference(cnf_transformation,[],[f36])).
% 3.67/1.00  
% 3.67/1.00  fof(f4,axiom,(
% 3.67/1.00    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 3.67/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/1.00  
% 3.67/1.00  fof(f22,plain,(
% 3.67/1.00    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 3.67/1.00    inference(nnf_transformation,[],[f4])).
% 3.67/1.00  
% 3.67/1.00  fof(f23,plain,(
% 3.67/1.00    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 3.67/1.00    inference(rectify,[],[f22])).
% 3.67/1.00  
% 3.67/1.00  fof(f26,plain,(
% 3.67/1.00    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0))),
% 3.67/1.00    introduced(choice_axiom,[])).
% 3.67/1.00  
% 3.67/1.00  fof(f25,plain,(
% 3.67/1.00    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) => r2_hidden(k4_tarski(X2,sK2(X0,X1)),X0))) )),
% 3.67/1.00    introduced(choice_axiom,[])).
% 3.67/1.00  
% 3.67/1.00  fof(f24,plain,(
% 3.67/1.00    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK1(X0,X1),X3),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK1(X0,X1),X4),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 3.67/1.00    introduced(choice_axiom,[])).
% 3.67/1.00  
% 3.67/1.00  fof(f27,plain,(
% 3.67/1.00    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK1(X0,X1),X3),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 3.67/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f23,f26,f25,f24])).
% 3.67/1.00  
% 3.67/1.00  fof(f42,plain,(
% 3.67/1.00    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 3.67/1.00    inference(cnf_transformation,[],[f27])).
% 3.67/1.00  
% 3.67/1.00  fof(f60,plain,(
% 3.67/1.00    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 3.67/1.00    inference(equality_resolution,[],[f42])).
% 3.67/1.00  
% 3.67/1.00  fof(f39,plain,(
% 3.67/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.67/1.00    inference(cnf_transformation,[],[f21])).
% 3.67/1.00  
% 3.67/1.00  fof(f38,plain,(
% 3.67/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.67/1.00    inference(cnf_transformation,[],[f21])).
% 3.67/1.00  
% 3.67/1.00  fof(f52,plain,(
% 3.67/1.00    ( ! [X2,X0,X1] : (r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 3.67/1.00    inference(cnf_transformation,[],[f15])).
% 3.67/1.00  
% 3.67/1.00  fof(f5,axiom,(
% 3.67/1.00    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 3.67/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/1.00  
% 3.67/1.00  fof(f28,plain,(
% 3.67/1.00    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 3.67/1.00    inference(nnf_transformation,[],[f5])).
% 3.67/1.00  
% 3.67/1.00  fof(f29,plain,(
% 3.67/1.00    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 3.67/1.00    inference(rectify,[],[f28])).
% 3.67/1.00  
% 3.67/1.00  fof(f32,plain,(
% 3.67/1.00    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK6(X0,X5),X5),X0))),
% 3.67/1.00    introduced(choice_axiom,[])).
% 3.67/1.00  
% 3.67/1.00  fof(f31,plain,(
% 3.67/1.00    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) => r2_hidden(k4_tarski(sK5(X0,X1),X2),X0))) )),
% 3.67/1.00    introduced(choice_axiom,[])).
% 3.67/1.00  
% 3.67/1.00  fof(f30,plain,(
% 3.67/1.00    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK4(X0,X1)),X0) | r2_hidden(sK4(X0,X1),X1))))),
% 3.67/1.00    introduced(choice_axiom,[])).
% 3.67/1.00  
% 3.67/1.00  fof(f33,plain,(
% 3.67/1.00    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 3.67/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f29,f32,f31,f30])).
% 3.67/1.00  
% 3.67/1.00  fof(f46,plain,(
% 3.67/1.00    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 3.67/1.00    inference(cnf_transformation,[],[f33])).
% 3.67/1.00  
% 3.67/1.00  fof(f62,plain,(
% 3.67/1.00    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 3.67/1.00    inference(equality_resolution,[],[f46])).
% 3.67/1.00  
% 3.67/1.00  fof(f2,axiom,(
% 3.67/1.00    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 3.67/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/1.00  
% 3.67/1.00  fof(f11,plain,(
% 3.67/1.00    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 3.67/1.00    inference(ennf_transformation,[],[f2])).
% 3.67/1.00  
% 3.67/1.00  fof(f12,plain,(
% 3.67/1.00    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 3.67/1.00    inference(flattening,[],[f11])).
% 3.67/1.00  
% 3.67/1.00  fof(f40,plain,(
% 3.67/1.00    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 3.67/1.00    inference(cnf_transformation,[],[f12])).
% 3.67/1.00  
% 3.67/1.00  fof(f3,axiom,(
% 3.67/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.67/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/1.00  
% 3.67/1.00  fof(f41,plain,(
% 3.67/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.67/1.00    inference(cnf_transformation,[],[f3])).
% 3.67/1.00  
% 3.67/1.00  fof(f57,plain,(
% 3.67/1.00    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 3.67/1.00    inference(definition_unfolding,[],[f40,f41])).
% 3.67/1.00  
% 3.67/1.00  fof(f6,axiom,(
% 3.67/1.00    ! [X0] : (v1_relat_1(X0) => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0))),
% 3.67/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/1.00  
% 3.67/1.00  fof(f13,plain,(
% 3.67/1.00    ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0))),
% 3.67/1.00    inference(ennf_transformation,[],[f6])).
% 3.67/1.00  
% 3.67/1.00  fof(f50,plain,(
% 3.67/1.00    ( ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.67/1.00    inference(cnf_transformation,[],[f13])).
% 3.67/1.00  
% 3.67/1.00  fof(f58,plain,(
% 3.67/1.00    ( ! [X0] : (k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.67/1.00    inference(definition_unfolding,[],[f50,f41])).
% 3.67/1.00  
% 3.67/1.00  fof(f56,plain,(
% 3.67/1.00    ~r1_tarski(k3_relat_1(sK7),k3_relat_1(sK8))),
% 3.67/1.00    inference(cnf_transformation,[],[f36])).
% 3.67/1.00  
% 3.67/1.00  fof(f53,plain,(
% 3.67/1.00    v1_relat_1(sK7)),
% 3.67/1.00    inference(cnf_transformation,[],[f36])).
% 3.67/1.00  
% 3.67/1.00  cnf(c_14,plain,
% 3.67/1.00      ( r2_hidden(X0,k3_relat_1(X1))
% 3.67/1.00      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 3.67/1.00      | ~ v1_relat_1(X1) ),
% 3.67/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_2,plain,
% 3.67/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.67/1.00      inference(cnf_transformation,[],[f37]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_16,negated_conjecture,
% 3.67/1.00      ( r1_tarski(sK7,sK8) ),
% 3.67/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_724,plain,
% 3.67/1.00      ( r2_hidden(X0,sK8) | ~ r2_hidden(X0,sK7) ),
% 3.67/1.00      inference(resolution,[status(thm)],[c_2,c_16]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_1510,plain,
% 3.67/1.00      ( r2_hidden(X0,k3_relat_1(sK8))
% 3.67/1.00      | ~ r2_hidden(k4_tarski(X0,X1),sK7)
% 3.67/1.00      | ~ v1_relat_1(sK8) ),
% 3.67/1.00      inference(resolution,[status(thm)],[c_14,c_724]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_17,negated_conjecture,
% 3.67/1.00      ( v1_relat_1(sK8) ),
% 3.67/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_1513,plain,
% 3.67/1.00      ( ~ r2_hidden(k4_tarski(X0,X1),sK7)
% 3.67/1.00      | r2_hidden(X0,k3_relat_1(sK8)) ),
% 3.67/1.00      inference(global_propositional_subsumption,
% 3.67/1.00                [status(thm)],
% 3.67/1.00                [c_1510,c_17]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_1514,plain,
% 3.67/1.00      ( r2_hidden(X0,k3_relat_1(sK8))
% 3.67/1.00      | ~ r2_hidden(k4_tarski(X0,X1),sK7) ),
% 3.67/1.00      inference(renaming,[status(thm)],[c_1513]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_7,plain,
% 3.67/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.67/1.00      | r2_hidden(k4_tarski(X0,sK3(X1,X0)),X1) ),
% 3.67/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_2444,plain,
% 3.67/1.00      ( r2_hidden(X0,k3_relat_1(sK8)) | ~ r2_hidden(X0,k1_relat_1(sK7)) ),
% 3.67/1.00      inference(resolution,[status(thm)],[c_1514,c_7]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_0,plain,
% 3.67/1.00      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.67/1.00      inference(cnf_transformation,[],[f39]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_2720,plain,
% 3.67/1.00      ( ~ r2_hidden(sK0(X0,k3_relat_1(sK8)),k1_relat_1(sK7))
% 3.67/1.00      | r1_tarski(X0,k3_relat_1(sK8)) ),
% 3.67/1.00      inference(resolution,[status(thm)],[c_2444,c_0]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_1,plain,
% 3.67/1.00      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.67/1.00      inference(cnf_transformation,[],[f38]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_5438,plain,
% 3.67/1.00      ( r1_tarski(k1_relat_1(sK7),k3_relat_1(sK8)) ),
% 3.67/1.00      inference(resolution,[status(thm)],[c_2720,c_1]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_13,plain,
% 3.67/1.00      ( r2_hidden(X0,k3_relat_1(X1))
% 3.67/1.00      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 3.67/1.00      | ~ v1_relat_1(X1) ),
% 3.67/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_1356,plain,
% 3.67/1.00      ( r2_hidden(X0,k3_relat_1(sK8))
% 3.67/1.00      | ~ r2_hidden(k4_tarski(X1,X0),sK7)
% 3.67/1.00      | ~ v1_relat_1(sK8) ),
% 3.67/1.00      inference(resolution,[status(thm)],[c_13,c_724]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_1361,plain,
% 3.67/1.00      ( ~ r2_hidden(k4_tarski(X1,X0),sK7)
% 3.67/1.00      | r2_hidden(X0,k3_relat_1(sK8)) ),
% 3.67/1.00      inference(global_propositional_subsumption,
% 3.67/1.00                [status(thm)],
% 3.67/1.00                [c_1356,c_17]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_1362,plain,
% 3.67/1.00      ( r2_hidden(X0,k3_relat_1(sK8))
% 3.67/1.00      | ~ r2_hidden(k4_tarski(X1,X0),sK7) ),
% 3.67/1.00      inference(renaming,[status(thm)],[c_1361]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_11,plain,
% 3.67/1.00      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 3.67/1.00      | r2_hidden(k4_tarski(sK6(X1,X0),X0),X1) ),
% 3.67/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_2435,plain,
% 3.67/1.00      ( r2_hidden(X0,k3_relat_1(sK8)) | ~ r2_hidden(X0,k2_relat_1(sK7)) ),
% 3.67/1.00      inference(resolution,[status(thm)],[c_1362,c_11]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_2696,plain,
% 3.67/1.00      ( ~ r2_hidden(sK0(X0,k3_relat_1(sK8)),k2_relat_1(sK7))
% 3.67/1.00      | r1_tarski(X0,k3_relat_1(sK8)) ),
% 3.67/1.00      inference(resolution,[status(thm)],[c_2435,c_0]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_5242,plain,
% 3.67/1.00      ( r1_tarski(k2_relat_1(sK7),k3_relat_1(sK8)) ),
% 3.67/1.00      inference(resolution,[status(thm)],[c_2696,c_1]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_3,plain,
% 3.67/1.00      ( ~ r1_tarski(X0,X1)
% 3.67/1.00      | ~ r1_tarski(X2,X1)
% 3.67/1.00      | r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) ),
% 3.67/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_1878,plain,
% 3.67/1.00      ( ~ r1_tarski(k2_relat_1(sK7),X0)
% 3.67/1.00      | ~ r1_tarski(k1_relat_1(sK7),X0)
% 3.67/1.00      | r1_tarski(k3_tarski(k2_tarski(k1_relat_1(sK7),k2_relat_1(sK7))),X0) ),
% 3.67/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_3481,plain,
% 3.67/1.00      ( ~ r1_tarski(k2_relat_1(sK7),k3_relat_1(sK8))
% 3.67/1.00      | ~ r1_tarski(k1_relat_1(sK7),k3_relat_1(sK8))
% 3.67/1.00      | r1_tarski(k3_tarski(k2_tarski(k1_relat_1(sK7),k2_relat_1(sK7))),k3_relat_1(sK8)) ),
% 3.67/1.00      inference(instantiation,[status(thm)],[c_1878]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_179,plain,
% 3.67/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.67/1.00      theory(equality) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_675,plain,
% 3.67/1.00      ( ~ r1_tarski(X0,X1)
% 3.67/1.00      | r1_tarski(k3_relat_1(sK7),k3_relat_1(sK8))
% 3.67/1.00      | k3_relat_1(sK8) != X1
% 3.67/1.00      | k3_relat_1(sK7) != X0 ),
% 3.67/1.00      inference(instantiation,[status(thm)],[c_179]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_1613,plain,
% 3.67/1.00      ( r1_tarski(k3_relat_1(sK7),k3_relat_1(sK8))
% 3.67/1.00      | ~ r1_tarski(k3_tarski(k2_tarski(k1_relat_1(sK7),k2_relat_1(sK7))),X0)
% 3.67/1.00      | k3_relat_1(sK8) != X0
% 3.67/1.00      | k3_relat_1(sK7) != k3_tarski(k2_tarski(k1_relat_1(sK7),k2_relat_1(sK7))) ),
% 3.67/1.00      inference(instantiation,[status(thm)],[c_675]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_3155,plain,
% 3.67/1.00      ( r1_tarski(k3_relat_1(sK7),k3_relat_1(sK8))
% 3.67/1.00      | ~ r1_tarski(k3_tarski(k2_tarski(k1_relat_1(sK7),k2_relat_1(sK7))),k3_relat_1(sK8))
% 3.67/1.00      | k3_relat_1(sK8) != k3_relat_1(sK8)
% 3.67/1.00      | k3_relat_1(sK7) != k3_tarski(k2_tarski(k1_relat_1(sK7),k2_relat_1(sK7))) ),
% 3.67/1.00      inference(instantiation,[status(thm)],[c_1613]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_177,plain,( X0 = X0 ),theory(equality) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_1080,plain,
% 3.67/1.00      ( k3_relat_1(sK8) = k3_relat_1(sK8) ),
% 3.67/1.00      inference(instantiation,[status(thm)],[c_177]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_178,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_750,plain,
% 3.67/1.00      ( X0 != X1 | k3_relat_1(sK7) != X1 | k3_relat_1(sK7) = X0 ),
% 3.67/1.00      inference(instantiation,[status(thm)],[c_178]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_814,plain,
% 3.67/1.00      ( X0 != k3_relat_1(X1)
% 3.67/1.00      | k3_relat_1(sK7) = X0
% 3.67/1.00      | k3_relat_1(sK7) != k3_relat_1(X1) ),
% 3.67/1.00      inference(instantiation,[status(thm)],[c_750]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_1002,plain,
% 3.67/1.00      ( k3_relat_1(sK7) != k3_relat_1(X0)
% 3.67/1.00      | k3_relat_1(sK7) = k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0)))
% 3.67/1.00      | k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))) != k3_relat_1(X0) ),
% 3.67/1.00      inference(instantiation,[status(thm)],[c_814]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_1003,plain,
% 3.67/1.00      ( k3_relat_1(sK7) != k3_relat_1(sK7)
% 3.67/1.00      | k3_relat_1(sK7) = k3_tarski(k2_tarski(k1_relat_1(sK7),k2_relat_1(sK7)))
% 3.67/1.00      | k3_tarski(k2_tarski(k1_relat_1(sK7),k2_relat_1(sK7))) != k3_relat_1(sK7) ),
% 3.67/1.00      inference(instantiation,[status(thm)],[c_1002]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_194,plain,
% 3.67/1.00      ( sK7 = sK7 ),
% 3.67/1.00      inference(instantiation,[status(thm)],[c_177]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_184,plain,
% 3.67/1.00      ( X0 != X1 | k3_relat_1(X0) = k3_relat_1(X1) ),
% 3.67/1.00      theory(equality) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_191,plain,
% 3.67/1.00      ( k3_relat_1(sK7) = k3_relat_1(sK7) | sK7 != sK7 ),
% 3.67/1.00      inference(instantiation,[status(thm)],[c_184]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_12,plain,
% 3.67/1.00      ( ~ v1_relat_1(X0)
% 3.67/1.00      | k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) ),
% 3.67/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_28,plain,
% 3.67/1.00      ( ~ v1_relat_1(sK7)
% 3.67/1.00      | k3_tarski(k2_tarski(k1_relat_1(sK7),k2_relat_1(sK7))) = k3_relat_1(sK7) ),
% 3.67/1.00      inference(instantiation,[status(thm)],[c_12]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_15,negated_conjecture,
% 3.67/1.00      ( ~ r1_tarski(k3_relat_1(sK7),k3_relat_1(sK8)) ),
% 3.67/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_18,negated_conjecture,
% 3.67/1.00      ( v1_relat_1(sK7) ),
% 3.67/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(contradiction,plain,
% 3.67/1.00      ( $false ),
% 3.67/1.00      inference(minisat,
% 3.67/1.00                [status(thm)],
% 3.67/1.00                [c_5438,c_5242,c_3481,c_3155,c_1080,c_1003,c_194,c_191,
% 3.67/1.00                 c_28,c_15,c_18]) ).
% 3.67/1.00  
% 3.67/1.00  
% 3.67/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.67/1.00  
% 3.67/1.00  ------                               Statistics
% 3.67/1.00  
% 3.67/1.00  ------ Selected
% 3.67/1.00  
% 3.67/1.00  total_time:                             0.218
% 3.67/1.00  
%------------------------------------------------------------------------------
