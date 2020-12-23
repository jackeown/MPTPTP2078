%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:44:47 EST 2020

% Result     : Theorem 3.17s
% Output     : CNFRefutation 3.17s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 255 expanded)
%              Number of clauses        :   52 (  89 expanded)
%              Number of leaves         :   16 (  49 expanded)
%              Depth                    :   21
%              Number of atoms          :  320 ( 765 expanded)
%              Number of equality atoms :  128 ( 327 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k7_relat_1(X1,X0)
        <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f28,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <~> r1_xboole_0(k1_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f41,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k7_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k7_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f42,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k7_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k7_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f41])).

fof(f43,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 = k7_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k1_relat_1(sK3),sK2)
        | k1_xboole_0 != k7_relat_1(sK3,sK2) )
      & ( r1_xboole_0(k1_relat_1(sK3),sK2)
        | k1_xboole_0 = k7_relat_1(sK3,sK2) )
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ( ~ r1_xboole_0(k1_relat_1(sK3),sK2)
      | k1_xboole_0 != k7_relat_1(sK3,sK2) )
    & ( r1_xboole_0(k1_relat_1(sK3),sK2)
      | k1_xboole_0 = k7_relat_1(sK3,sK2) )
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f42,f43])).

fof(f77,plain,
    ( r1_xboole_0(k1_relat_1(sK3),sK2)
    | k1_xboole_0 = k7_relat_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f76,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f75,f59])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f84,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f57,f59])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f72,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f16,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f16])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f33])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f36])).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f89,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f48])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f38])).

fof(f56,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f78,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK3),sK2)
    | k1_xboole_0 != k7_relat_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_17,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_906,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_15,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_174,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(prop_impl,[status(thm)],[c_15])).

cnf(c_25,negated_conjecture,
    ( r1_xboole_0(k1_relat_1(sK3),sK2)
    | k1_xboole_0 = k7_relat_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_178,plain,
    ( r1_xboole_0(k1_relat_1(sK3),sK2)
    | k1_xboole_0 = k7_relat_1(sK3,sK2) ),
    inference(prop_impl,[status(thm)],[c_25])).

cnf(c_311,plain,
    ( k7_relat_1(sK3,sK2) = k1_xboole_0
    | k4_xboole_0(X0,X1) = X0
    | k1_relat_1(sK3) != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_174,c_178])).

cnf(c_312,plain,
    ( k7_relat_1(sK3,sK2) = k1_xboole_0
    | k4_xboole_0(k1_relat_1(sK3),sK2) = k1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_311])).

cnf(c_383,plain,
    ( k7_relat_1(sK3,sK2) = k1_xboole_0
    | k4_xboole_0(k1_relat_1(sK3),sK2) = k1_relat_1(sK3) ),
    inference(prop_impl,[status(thm)],[c_312])).

cnf(c_26,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_901,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_23,plain,
    ( ~ v1_relat_1(X0)
    | k4_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_902,plain,
    ( k4_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1382,plain,
    ( k4_xboole_0(k1_relat_1(sK3),k4_xboole_0(k1_relat_1(sK3),X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_901,c_902])).

cnf(c_1602,plain,
    ( k7_relat_1(sK3,sK2) = k1_xboole_0
    | k4_xboole_0(k1_relat_1(sK3),k1_relat_1(sK3)) = k1_relat_1(k7_relat_1(sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_383,c_1382])).

cnf(c_12,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_13,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_918,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_12,c_13])).

cnf(c_1610,plain,
    ( k7_relat_1(sK3,sK2) = k1_xboole_0
    | k1_relat_1(k7_relat_1(sK3,sK2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1602,c_918])).

cnf(c_21,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_904,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3117,plain,
    ( k7_relat_1(sK3,sK2) = k1_xboole_0
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1610,c_904])).

cnf(c_9112,plain,
    ( k7_relat_1(sK3,sK2) = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_906,c_3117])).

cnf(c_27,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_9192,plain,
    ( k7_relat_1(sK3,sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9112,c_27])).

cnf(c_1608,plain,
    ( k1_relat_1(k7_relat_1(sK3,k4_xboole_0(k1_relat_1(sK3),X0))) = k4_xboole_0(k1_relat_1(sK3),k1_relat_1(k7_relat_1(sK3,X0))) ),
    inference(superposition,[status(thm)],[c_1382,c_1382])).

cnf(c_9227,plain,
    ( k1_relat_1(k7_relat_1(sK3,k4_xboole_0(k1_relat_1(sK3),sK2))) = k4_xboole_0(k1_relat_1(sK3),k1_relat_1(k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_9192,c_1608])).

cnf(c_19,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_9256,plain,
    ( k1_relat_1(k7_relat_1(sK3,k4_xboole_0(k1_relat_1(sK3),sK2))) = k4_xboole_0(k1_relat_1(sK3),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_9227,c_19])).

cnf(c_9257,plain,
    ( k1_relat_1(k7_relat_1(sK3,k4_xboole_0(k1_relat_1(sK3),sK2))) = k1_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_9256,c_13])).

cnf(c_22,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_903,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_9548,plain,
    ( r1_tarski(k1_relat_1(sK3),k4_xboole_0(k1_relat_1(sK3),sK2)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_9257,c_903])).

cnf(c_8,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1330,plain,
    ( ~ r2_hidden(sK0(k4_xboole_0(k1_relat_1(sK3),sK2),k1_relat_1(sK3)),k4_xboole_0(k1_relat_1(sK3),sK2))
    | r2_hidden(sK0(k4_xboole_0(k1_relat_1(sK3),sK2),k1_relat_1(sK3)),k1_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1331,plain,
    ( r2_hidden(sK0(k4_xboole_0(k1_relat_1(sK3),sK2),k1_relat_1(sK3)),k4_xboole_0(k1_relat_1(sK3),sK2)) != iProver_top
    | r2_hidden(sK0(k4_xboole_0(k1_relat_1(sK3),sK2),k1_relat_1(sK3)),k1_relat_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1330])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1050,plain,
    ( ~ r2_hidden(sK0(k4_xboole_0(k1_relat_1(sK3),sK2),k1_relat_1(sK3)),k1_relat_1(sK3))
    | r1_tarski(k4_xboole_0(k1_relat_1(sK3),sK2),k1_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1054,plain,
    ( r2_hidden(sK0(k4_xboole_0(k1_relat_1(sK3),sK2),k1_relat_1(sK3)),k1_relat_1(sK3)) != iProver_top
    | r1_tarski(k4_xboole_0(k1_relat_1(sK3),sK2),k1_relat_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1050])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1051,plain,
    ( r2_hidden(sK0(k4_xboole_0(k1_relat_1(sK3),sK2),k1_relat_1(sK3)),k4_xboole_0(k1_relat_1(sK3),sK2))
    | r1_tarski(k4_xboole_0(k1_relat_1(sK3),sK2),k1_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1052,plain,
    ( r2_hidden(sK0(k4_xboole_0(k1_relat_1(sK3),sK2),k1_relat_1(sK3)),k4_xboole_0(k1_relat_1(sK3),sK2)) = iProver_top
    | r1_tarski(k4_xboole_0(k1_relat_1(sK3),sK2),k1_relat_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1051])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_948,plain,
    ( ~ r1_tarski(k4_xboole_0(k1_relat_1(sK3),sK2),k1_relat_1(sK3))
    | ~ r1_tarski(k1_relat_1(sK3),k4_xboole_0(k1_relat_1(sK3),sK2))
    | k4_xboole_0(k1_relat_1(sK3),sK2) = k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_949,plain,
    ( k4_xboole_0(k1_relat_1(sK3),sK2) = k1_relat_1(sK3)
    | r1_tarski(k4_xboole_0(k1_relat_1(sK3),sK2),k1_relat_1(sK3)) != iProver_top
    | r1_tarski(k1_relat_1(sK3),k4_xboole_0(k1_relat_1(sK3),sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_948])).

cnf(c_14,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_172,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(prop_impl,[status(thm)],[c_14])).

cnf(c_24,negated_conjecture,
    ( ~ r1_xboole_0(k1_relat_1(sK3),sK2)
    | k1_xboole_0 != k7_relat_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_176,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK3),sK2)
    | k1_xboole_0 != k7_relat_1(sK3,sK2) ),
    inference(prop_impl,[status(thm)],[c_24])).

cnf(c_303,plain,
    ( k7_relat_1(sK3,sK2) != k1_xboole_0
    | k4_xboole_0(X0,X1) != X0
    | k1_relat_1(sK3) != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_172,c_176])).

cnf(c_304,plain,
    ( k7_relat_1(sK3,sK2) != k1_xboole_0
    | k4_xboole_0(k1_relat_1(sK3),sK2) != k1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_303])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9548,c_9112,c_1331,c_1054,c_1052,c_949,c_304,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:56:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.17/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.17/0.99  
% 3.17/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.17/0.99  
% 3.17/0.99  ------  iProver source info
% 3.17/0.99  
% 3.17/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.17/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.17/0.99  git: non_committed_changes: false
% 3.17/0.99  git: last_make_outside_of_git: false
% 3.17/0.99  
% 3.17/0.99  ------ 
% 3.17/0.99  
% 3.17/0.99  ------ Input Options
% 3.17/0.99  
% 3.17/0.99  --out_options                           all
% 3.17/0.99  --tptp_safe_out                         true
% 3.17/0.99  --problem_path                          ""
% 3.17/0.99  --include_path                          ""
% 3.17/0.99  --clausifier                            res/vclausify_rel
% 3.17/0.99  --clausifier_options                    ""
% 3.17/0.99  --stdin                                 false
% 3.17/0.99  --stats_out                             all
% 3.17/0.99  
% 3.17/0.99  ------ General Options
% 3.17/0.99  
% 3.17/0.99  --fof                                   false
% 3.17/0.99  --time_out_real                         305.
% 3.17/0.99  --time_out_virtual                      -1.
% 3.17/0.99  --symbol_type_check                     false
% 3.17/0.99  --clausify_out                          false
% 3.17/0.99  --sig_cnt_out                           false
% 3.17/1.00  --trig_cnt_out                          false
% 3.17/1.00  --trig_cnt_out_tolerance                1.
% 3.17/1.00  --trig_cnt_out_sk_spl                   false
% 3.17/1.00  --abstr_cl_out                          false
% 3.17/1.00  
% 3.17/1.00  ------ Global Options
% 3.17/1.00  
% 3.17/1.00  --schedule                              default
% 3.17/1.00  --add_important_lit                     false
% 3.17/1.00  --prop_solver_per_cl                    1000
% 3.17/1.00  --min_unsat_core                        false
% 3.17/1.00  --soft_assumptions                      false
% 3.17/1.00  --soft_lemma_size                       3
% 3.17/1.00  --prop_impl_unit_size                   0
% 3.17/1.00  --prop_impl_unit                        []
% 3.17/1.00  --share_sel_clauses                     true
% 3.17/1.00  --reset_solvers                         false
% 3.17/1.00  --bc_imp_inh                            [conj_cone]
% 3.17/1.00  --conj_cone_tolerance                   3.
% 3.17/1.00  --extra_neg_conj                        none
% 3.17/1.00  --large_theory_mode                     true
% 3.17/1.00  --prolific_symb_bound                   200
% 3.17/1.00  --lt_threshold                          2000
% 3.17/1.00  --clause_weak_htbl                      true
% 3.17/1.00  --gc_record_bc_elim                     false
% 3.17/1.00  
% 3.17/1.00  ------ Preprocessing Options
% 3.17/1.00  
% 3.17/1.00  --preprocessing_flag                    true
% 3.17/1.00  --time_out_prep_mult                    0.1
% 3.17/1.00  --splitting_mode                        input
% 3.17/1.00  --splitting_grd                         true
% 3.17/1.00  --splitting_cvd                         false
% 3.17/1.00  --splitting_cvd_svl                     false
% 3.17/1.00  --splitting_nvd                         32
% 3.17/1.00  --sub_typing                            true
% 3.17/1.00  --prep_gs_sim                           true
% 3.17/1.00  --prep_unflatten                        true
% 3.17/1.00  --prep_res_sim                          true
% 3.17/1.00  --prep_upred                            true
% 3.17/1.00  --prep_sem_filter                       exhaustive
% 3.17/1.00  --prep_sem_filter_out                   false
% 3.17/1.00  --pred_elim                             true
% 3.17/1.00  --res_sim_input                         true
% 3.17/1.00  --eq_ax_congr_red                       true
% 3.17/1.00  --pure_diseq_elim                       true
% 3.17/1.00  --brand_transform                       false
% 3.17/1.00  --non_eq_to_eq                          false
% 3.17/1.00  --prep_def_merge                        true
% 3.17/1.00  --prep_def_merge_prop_impl              false
% 3.17/1.00  --prep_def_merge_mbd                    true
% 3.17/1.00  --prep_def_merge_tr_red                 false
% 3.17/1.00  --prep_def_merge_tr_cl                  false
% 3.17/1.00  --smt_preprocessing                     true
% 3.17/1.00  --smt_ac_axioms                         fast
% 3.17/1.00  --preprocessed_out                      false
% 3.17/1.00  --preprocessed_stats                    false
% 3.17/1.00  
% 3.17/1.00  ------ Abstraction refinement Options
% 3.17/1.00  
% 3.17/1.00  --abstr_ref                             []
% 3.17/1.00  --abstr_ref_prep                        false
% 3.17/1.00  --abstr_ref_until_sat                   false
% 3.17/1.00  --abstr_ref_sig_restrict                funpre
% 3.17/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.17/1.00  --abstr_ref_under                       []
% 3.17/1.00  
% 3.17/1.00  ------ SAT Options
% 3.17/1.00  
% 3.17/1.00  --sat_mode                              false
% 3.17/1.00  --sat_fm_restart_options                ""
% 3.17/1.00  --sat_gr_def                            false
% 3.17/1.00  --sat_epr_types                         true
% 3.17/1.00  --sat_non_cyclic_types                  false
% 3.17/1.00  --sat_finite_models                     false
% 3.17/1.00  --sat_fm_lemmas                         false
% 3.17/1.00  --sat_fm_prep                           false
% 3.17/1.00  --sat_fm_uc_incr                        true
% 3.17/1.00  --sat_out_model                         small
% 3.17/1.00  --sat_out_clauses                       false
% 3.17/1.00  
% 3.17/1.00  ------ QBF Options
% 3.17/1.00  
% 3.17/1.00  --qbf_mode                              false
% 3.17/1.00  --qbf_elim_univ                         false
% 3.17/1.00  --qbf_dom_inst                          none
% 3.17/1.00  --qbf_dom_pre_inst                      false
% 3.17/1.00  --qbf_sk_in                             false
% 3.17/1.00  --qbf_pred_elim                         true
% 3.17/1.00  --qbf_split                             512
% 3.17/1.00  
% 3.17/1.00  ------ BMC1 Options
% 3.17/1.00  
% 3.17/1.00  --bmc1_incremental                      false
% 3.17/1.00  --bmc1_axioms                           reachable_all
% 3.17/1.00  --bmc1_min_bound                        0
% 3.17/1.00  --bmc1_max_bound                        -1
% 3.17/1.00  --bmc1_max_bound_default                -1
% 3.17/1.00  --bmc1_symbol_reachability              true
% 3.17/1.00  --bmc1_property_lemmas                  false
% 3.17/1.00  --bmc1_k_induction                      false
% 3.17/1.00  --bmc1_non_equiv_states                 false
% 3.17/1.00  --bmc1_deadlock                         false
% 3.17/1.00  --bmc1_ucm                              false
% 3.17/1.00  --bmc1_add_unsat_core                   none
% 3.17/1.00  --bmc1_unsat_core_children              false
% 3.17/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.17/1.00  --bmc1_out_stat                         full
% 3.17/1.00  --bmc1_ground_init                      false
% 3.17/1.00  --bmc1_pre_inst_next_state              false
% 3.17/1.00  --bmc1_pre_inst_state                   false
% 3.17/1.00  --bmc1_pre_inst_reach_state             false
% 3.17/1.00  --bmc1_out_unsat_core                   false
% 3.17/1.00  --bmc1_aig_witness_out                  false
% 3.17/1.00  --bmc1_verbose                          false
% 3.17/1.00  --bmc1_dump_clauses_tptp                false
% 3.17/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.17/1.00  --bmc1_dump_file                        -
% 3.17/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.17/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.17/1.00  --bmc1_ucm_extend_mode                  1
% 3.17/1.00  --bmc1_ucm_init_mode                    2
% 3.17/1.00  --bmc1_ucm_cone_mode                    none
% 3.17/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.17/1.00  --bmc1_ucm_relax_model                  4
% 3.17/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.17/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.17/1.00  --bmc1_ucm_layered_model                none
% 3.17/1.00  --bmc1_ucm_max_lemma_size               10
% 3.17/1.00  
% 3.17/1.00  ------ AIG Options
% 3.17/1.00  
% 3.17/1.00  --aig_mode                              false
% 3.17/1.00  
% 3.17/1.00  ------ Instantiation Options
% 3.17/1.00  
% 3.17/1.00  --instantiation_flag                    true
% 3.17/1.00  --inst_sos_flag                         true
% 3.17/1.00  --inst_sos_phase                        true
% 3.17/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.17/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.17/1.00  --inst_lit_sel_side                     num_symb
% 3.17/1.00  --inst_solver_per_active                1400
% 3.17/1.00  --inst_solver_calls_frac                1.
% 3.17/1.00  --inst_passive_queue_type               priority_queues
% 3.17/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.17/1.00  --inst_passive_queues_freq              [25;2]
% 3.17/1.00  --inst_dismatching                      true
% 3.17/1.00  --inst_eager_unprocessed_to_passive     true
% 3.17/1.00  --inst_prop_sim_given                   true
% 3.17/1.00  --inst_prop_sim_new                     false
% 3.17/1.00  --inst_subs_new                         false
% 3.17/1.00  --inst_eq_res_simp                      false
% 3.17/1.00  --inst_subs_given                       false
% 3.17/1.00  --inst_orphan_elimination               true
% 3.17/1.00  --inst_learning_loop_flag               true
% 3.17/1.00  --inst_learning_start                   3000
% 3.17/1.00  --inst_learning_factor                  2
% 3.17/1.00  --inst_start_prop_sim_after_learn       3
% 3.17/1.00  --inst_sel_renew                        solver
% 3.17/1.00  --inst_lit_activity_flag                true
% 3.17/1.00  --inst_restr_to_given                   false
% 3.17/1.00  --inst_activity_threshold               500
% 3.17/1.00  --inst_out_proof                        true
% 3.17/1.00  
% 3.17/1.00  ------ Resolution Options
% 3.17/1.00  
% 3.17/1.00  --resolution_flag                       true
% 3.17/1.00  --res_lit_sel                           adaptive
% 3.17/1.00  --res_lit_sel_side                      none
% 3.17/1.00  --res_ordering                          kbo
% 3.17/1.00  --res_to_prop_solver                    active
% 3.17/1.00  --res_prop_simpl_new                    false
% 3.17/1.00  --res_prop_simpl_given                  true
% 3.17/1.00  --res_passive_queue_type                priority_queues
% 3.17/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.17/1.00  --res_passive_queues_freq               [15;5]
% 3.17/1.00  --res_forward_subs                      full
% 3.17/1.00  --res_backward_subs                     full
% 3.17/1.00  --res_forward_subs_resolution           true
% 3.17/1.00  --res_backward_subs_resolution          true
% 3.17/1.00  --res_orphan_elimination                true
% 3.17/1.00  --res_time_limit                        2.
% 3.17/1.00  --res_out_proof                         true
% 3.17/1.00  
% 3.17/1.00  ------ Superposition Options
% 3.17/1.00  
% 3.17/1.00  --superposition_flag                    true
% 3.17/1.00  --sup_passive_queue_type                priority_queues
% 3.17/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.17/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.17/1.00  --demod_completeness_check              fast
% 3.17/1.00  --demod_use_ground                      true
% 3.17/1.00  --sup_to_prop_solver                    passive
% 3.17/1.00  --sup_prop_simpl_new                    true
% 3.17/1.00  --sup_prop_simpl_given                  true
% 3.17/1.00  --sup_fun_splitting                     true
% 3.17/1.00  --sup_smt_interval                      50000
% 3.17/1.00  
% 3.17/1.00  ------ Superposition Simplification Setup
% 3.17/1.00  
% 3.17/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.17/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.17/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.17/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.17/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.17/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.17/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.17/1.00  --sup_immed_triv                        [TrivRules]
% 3.17/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.17/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.17/1.00  --sup_immed_bw_main                     []
% 3.17/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.17/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.17/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.17/1.00  --sup_input_bw                          []
% 3.17/1.00  
% 3.17/1.00  ------ Combination Options
% 3.17/1.00  
% 3.17/1.00  --comb_res_mult                         3
% 3.17/1.00  --comb_sup_mult                         2
% 3.17/1.00  --comb_inst_mult                        10
% 3.17/1.00  
% 3.17/1.00  ------ Debug Options
% 3.17/1.00  
% 3.17/1.00  --dbg_backtrace                         false
% 3.17/1.00  --dbg_dump_prop_clauses                 false
% 3.17/1.00  --dbg_dump_prop_clauses_file            -
% 3.17/1.00  --dbg_out_stat                          false
% 3.17/1.00  ------ Parsing...
% 3.17/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.17/1.00  
% 3.17/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.17/1.00  
% 3.17/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.17/1.00  
% 3.17/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.17/1.00  ------ Proving...
% 3.17/1.00  ------ Problem Properties 
% 3.17/1.00  
% 3.17/1.00  
% 3.17/1.00  clauses                                 24
% 3.17/1.00  conjectures                             1
% 3.17/1.00  EPR                                     4
% 3.17/1.00  Horn                                    18
% 3.17/1.00  unary                                   7
% 3.17/1.00  binary                                  9
% 3.17/1.00  lits                                    50
% 3.17/1.00  lits eq                                 18
% 3.17/1.00  fd_pure                                 0
% 3.17/1.00  fd_pseudo                               0
% 3.17/1.00  fd_cond                                 2
% 3.17/1.00  fd_pseudo_cond                          4
% 3.17/1.00  AC symbols                              0
% 3.17/1.00  
% 3.17/1.00  ------ Schedule dynamic 5 is on 
% 3.17/1.00  
% 3.17/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.17/1.00  
% 3.17/1.00  
% 3.17/1.00  ------ 
% 3.17/1.00  Current options:
% 3.17/1.00  ------ 
% 3.17/1.00  
% 3.17/1.00  ------ Input Options
% 3.17/1.00  
% 3.17/1.00  --out_options                           all
% 3.17/1.00  --tptp_safe_out                         true
% 3.17/1.00  --problem_path                          ""
% 3.17/1.00  --include_path                          ""
% 3.17/1.00  --clausifier                            res/vclausify_rel
% 3.17/1.00  --clausifier_options                    ""
% 3.17/1.00  --stdin                                 false
% 3.17/1.00  --stats_out                             all
% 3.17/1.00  
% 3.17/1.00  ------ General Options
% 3.17/1.00  
% 3.17/1.00  --fof                                   false
% 3.17/1.00  --time_out_real                         305.
% 3.17/1.00  --time_out_virtual                      -1.
% 3.17/1.00  --symbol_type_check                     false
% 3.17/1.00  --clausify_out                          false
% 3.17/1.00  --sig_cnt_out                           false
% 3.17/1.00  --trig_cnt_out                          false
% 3.17/1.00  --trig_cnt_out_tolerance                1.
% 3.17/1.00  --trig_cnt_out_sk_spl                   false
% 3.17/1.00  --abstr_cl_out                          false
% 3.17/1.00  
% 3.17/1.00  ------ Global Options
% 3.17/1.00  
% 3.17/1.00  --schedule                              default
% 3.17/1.00  --add_important_lit                     false
% 3.17/1.00  --prop_solver_per_cl                    1000
% 3.17/1.00  --min_unsat_core                        false
% 3.17/1.00  --soft_assumptions                      false
% 3.17/1.00  --soft_lemma_size                       3
% 3.17/1.00  --prop_impl_unit_size                   0
% 3.17/1.00  --prop_impl_unit                        []
% 3.17/1.00  --share_sel_clauses                     true
% 3.17/1.00  --reset_solvers                         false
% 3.17/1.00  --bc_imp_inh                            [conj_cone]
% 3.17/1.00  --conj_cone_tolerance                   3.
% 3.17/1.00  --extra_neg_conj                        none
% 3.17/1.00  --large_theory_mode                     true
% 3.17/1.00  --prolific_symb_bound                   200
% 3.17/1.00  --lt_threshold                          2000
% 3.17/1.00  --clause_weak_htbl                      true
% 3.17/1.00  --gc_record_bc_elim                     false
% 3.17/1.00  
% 3.17/1.00  ------ Preprocessing Options
% 3.17/1.00  
% 3.17/1.00  --preprocessing_flag                    true
% 3.17/1.00  --time_out_prep_mult                    0.1
% 3.17/1.00  --splitting_mode                        input
% 3.17/1.00  --splitting_grd                         true
% 3.17/1.00  --splitting_cvd                         false
% 3.17/1.00  --splitting_cvd_svl                     false
% 3.17/1.00  --splitting_nvd                         32
% 3.17/1.00  --sub_typing                            true
% 3.17/1.00  --prep_gs_sim                           true
% 3.17/1.00  --prep_unflatten                        true
% 3.17/1.00  --prep_res_sim                          true
% 3.17/1.00  --prep_upred                            true
% 3.17/1.00  --prep_sem_filter                       exhaustive
% 3.17/1.00  --prep_sem_filter_out                   false
% 3.17/1.00  --pred_elim                             true
% 3.17/1.00  --res_sim_input                         true
% 3.17/1.00  --eq_ax_congr_red                       true
% 3.17/1.00  --pure_diseq_elim                       true
% 3.17/1.00  --brand_transform                       false
% 3.17/1.00  --non_eq_to_eq                          false
% 3.17/1.00  --prep_def_merge                        true
% 3.17/1.00  --prep_def_merge_prop_impl              false
% 3.17/1.00  --prep_def_merge_mbd                    true
% 3.17/1.00  --prep_def_merge_tr_red                 false
% 3.17/1.00  --prep_def_merge_tr_cl                  false
% 3.17/1.00  --smt_preprocessing                     true
% 3.17/1.00  --smt_ac_axioms                         fast
% 3.17/1.00  --preprocessed_out                      false
% 3.17/1.00  --preprocessed_stats                    false
% 3.17/1.00  
% 3.17/1.00  ------ Abstraction refinement Options
% 3.17/1.00  
% 3.17/1.00  --abstr_ref                             []
% 3.17/1.00  --abstr_ref_prep                        false
% 3.17/1.00  --abstr_ref_until_sat                   false
% 3.17/1.00  --abstr_ref_sig_restrict                funpre
% 3.17/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.17/1.00  --abstr_ref_under                       []
% 3.17/1.00  
% 3.17/1.00  ------ SAT Options
% 3.17/1.00  
% 3.17/1.00  --sat_mode                              false
% 3.17/1.00  --sat_fm_restart_options                ""
% 3.17/1.00  --sat_gr_def                            false
% 3.17/1.00  --sat_epr_types                         true
% 3.17/1.00  --sat_non_cyclic_types                  false
% 3.17/1.00  --sat_finite_models                     false
% 3.17/1.00  --sat_fm_lemmas                         false
% 3.17/1.00  --sat_fm_prep                           false
% 3.17/1.00  --sat_fm_uc_incr                        true
% 3.17/1.00  --sat_out_model                         small
% 3.17/1.00  --sat_out_clauses                       false
% 3.17/1.00  
% 3.17/1.00  ------ QBF Options
% 3.17/1.00  
% 3.17/1.00  --qbf_mode                              false
% 3.17/1.00  --qbf_elim_univ                         false
% 3.17/1.00  --qbf_dom_inst                          none
% 3.17/1.00  --qbf_dom_pre_inst                      false
% 3.17/1.00  --qbf_sk_in                             false
% 3.17/1.00  --qbf_pred_elim                         true
% 3.17/1.00  --qbf_split                             512
% 3.17/1.00  
% 3.17/1.00  ------ BMC1 Options
% 3.17/1.00  
% 3.17/1.00  --bmc1_incremental                      false
% 3.17/1.00  --bmc1_axioms                           reachable_all
% 3.17/1.00  --bmc1_min_bound                        0
% 3.17/1.00  --bmc1_max_bound                        -1
% 3.17/1.00  --bmc1_max_bound_default                -1
% 3.17/1.00  --bmc1_symbol_reachability              true
% 3.17/1.00  --bmc1_property_lemmas                  false
% 3.17/1.00  --bmc1_k_induction                      false
% 3.17/1.00  --bmc1_non_equiv_states                 false
% 3.17/1.00  --bmc1_deadlock                         false
% 3.17/1.00  --bmc1_ucm                              false
% 3.17/1.00  --bmc1_add_unsat_core                   none
% 3.17/1.00  --bmc1_unsat_core_children              false
% 3.17/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.17/1.00  --bmc1_out_stat                         full
% 3.17/1.00  --bmc1_ground_init                      false
% 3.17/1.00  --bmc1_pre_inst_next_state              false
% 3.17/1.00  --bmc1_pre_inst_state                   false
% 3.17/1.00  --bmc1_pre_inst_reach_state             false
% 3.17/1.00  --bmc1_out_unsat_core                   false
% 3.17/1.00  --bmc1_aig_witness_out                  false
% 3.17/1.00  --bmc1_verbose                          false
% 3.17/1.00  --bmc1_dump_clauses_tptp                false
% 3.17/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.17/1.00  --bmc1_dump_file                        -
% 3.17/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.17/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.17/1.00  --bmc1_ucm_extend_mode                  1
% 3.17/1.00  --bmc1_ucm_init_mode                    2
% 3.17/1.00  --bmc1_ucm_cone_mode                    none
% 3.17/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.17/1.00  --bmc1_ucm_relax_model                  4
% 3.17/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.17/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.17/1.00  --bmc1_ucm_layered_model                none
% 3.17/1.00  --bmc1_ucm_max_lemma_size               10
% 3.17/1.00  
% 3.17/1.00  ------ AIG Options
% 3.17/1.00  
% 3.17/1.00  --aig_mode                              false
% 3.17/1.00  
% 3.17/1.00  ------ Instantiation Options
% 3.17/1.00  
% 3.17/1.00  --instantiation_flag                    true
% 3.17/1.00  --inst_sos_flag                         true
% 3.17/1.00  --inst_sos_phase                        true
% 3.17/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.17/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.17/1.00  --inst_lit_sel_side                     none
% 3.17/1.00  --inst_solver_per_active                1400
% 3.17/1.00  --inst_solver_calls_frac                1.
% 3.17/1.00  --inst_passive_queue_type               priority_queues
% 3.17/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.17/1.00  --inst_passive_queues_freq              [25;2]
% 3.17/1.00  --inst_dismatching                      true
% 3.17/1.00  --inst_eager_unprocessed_to_passive     true
% 3.17/1.00  --inst_prop_sim_given                   true
% 3.17/1.00  --inst_prop_sim_new                     false
% 3.17/1.00  --inst_subs_new                         false
% 3.17/1.00  --inst_eq_res_simp                      false
% 3.17/1.00  --inst_subs_given                       false
% 3.17/1.00  --inst_orphan_elimination               true
% 3.17/1.00  --inst_learning_loop_flag               true
% 3.17/1.00  --inst_learning_start                   3000
% 3.17/1.00  --inst_learning_factor                  2
% 3.17/1.00  --inst_start_prop_sim_after_learn       3
% 3.17/1.00  --inst_sel_renew                        solver
% 3.17/1.00  --inst_lit_activity_flag                true
% 3.17/1.00  --inst_restr_to_given                   false
% 3.17/1.00  --inst_activity_threshold               500
% 3.17/1.00  --inst_out_proof                        true
% 3.17/1.00  
% 3.17/1.00  ------ Resolution Options
% 3.17/1.00  
% 3.17/1.00  --resolution_flag                       false
% 3.17/1.00  --res_lit_sel                           adaptive
% 3.17/1.00  --res_lit_sel_side                      none
% 3.17/1.00  --res_ordering                          kbo
% 3.17/1.00  --res_to_prop_solver                    active
% 3.17/1.00  --res_prop_simpl_new                    false
% 3.17/1.00  --res_prop_simpl_given                  true
% 3.17/1.00  --res_passive_queue_type                priority_queues
% 3.17/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.17/1.00  --res_passive_queues_freq               [15;5]
% 3.17/1.00  --res_forward_subs                      full
% 3.17/1.00  --res_backward_subs                     full
% 3.17/1.00  --res_forward_subs_resolution           true
% 3.17/1.00  --res_backward_subs_resolution          true
% 3.17/1.00  --res_orphan_elimination                true
% 3.17/1.00  --res_time_limit                        2.
% 3.17/1.00  --res_out_proof                         true
% 3.17/1.00  
% 3.17/1.00  ------ Superposition Options
% 3.17/1.00  
% 3.17/1.00  --superposition_flag                    true
% 3.17/1.00  --sup_passive_queue_type                priority_queues
% 3.17/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.17/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.17/1.00  --demod_completeness_check              fast
% 3.17/1.00  --demod_use_ground                      true
% 3.17/1.00  --sup_to_prop_solver                    passive
% 3.17/1.00  --sup_prop_simpl_new                    true
% 3.17/1.00  --sup_prop_simpl_given                  true
% 3.17/1.00  --sup_fun_splitting                     true
% 3.17/1.00  --sup_smt_interval                      50000
% 3.17/1.00  
% 3.17/1.00  ------ Superposition Simplification Setup
% 3.17/1.00  
% 3.17/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.17/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.17/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.17/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.17/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.17/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.17/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.17/1.00  --sup_immed_triv                        [TrivRules]
% 3.17/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.17/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.17/1.00  --sup_immed_bw_main                     []
% 3.17/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.17/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.17/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.17/1.00  --sup_input_bw                          []
% 3.17/1.00  
% 3.17/1.00  ------ Combination Options
% 3.17/1.00  
% 3.17/1.00  --comb_res_mult                         3
% 3.17/1.00  --comb_sup_mult                         2
% 3.17/1.00  --comb_inst_mult                        10
% 3.17/1.00  
% 3.17/1.00  ------ Debug Options
% 3.17/1.00  
% 3.17/1.00  --dbg_backtrace                         false
% 3.17/1.00  --dbg_dump_prop_clauses                 false
% 3.17/1.00  --dbg_dump_prop_clauses_file            -
% 3.17/1.00  --dbg_out_stat                          false
% 3.17/1.00  
% 3.17/1.00  
% 3.17/1.00  
% 3.17/1.00  
% 3.17/1.00  ------ Proving...
% 3.17/1.00  
% 3.17/1.00  
% 3.17/1.00  % SZS status Theorem for theBenchmark.p
% 3.17/1.00  
% 3.17/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.17/1.00  
% 3.17/1.00  fof(f15,axiom,(
% 3.17/1.00    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 3.17/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.17/1.00  
% 3.17/1.00  fof(f23,plain,(
% 3.17/1.00    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 3.17/1.00    inference(ennf_transformation,[],[f15])).
% 3.17/1.00  
% 3.17/1.00  fof(f69,plain,(
% 3.17/1.00    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 3.17/1.00    inference(cnf_transformation,[],[f23])).
% 3.17/1.00  
% 3.17/1.00  fof(f7,axiom,(
% 3.17/1.00    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 3.17/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.17/1.00  
% 3.17/1.00  fof(f40,plain,(
% 3.17/1.00    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 3.17/1.00    inference(nnf_transformation,[],[f7])).
% 3.17/1.00  
% 3.17/1.00  fof(f60,plain,(
% 3.17/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 3.17/1.00    inference(cnf_transformation,[],[f40])).
% 3.17/1.00  
% 3.17/1.00  fof(f20,conjecture,(
% 3.17/1.00    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 3.17/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.17/1.00  
% 3.17/1.00  fof(f21,negated_conjecture,(
% 3.17/1.00    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 3.17/1.00    inference(negated_conjecture,[],[f20])).
% 3.17/1.00  
% 3.17/1.00  fof(f28,plain,(
% 3.17/1.00    ? [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <~> r1_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 3.17/1.00    inference(ennf_transformation,[],[f21])).
% 3.17/1.00  
% 3.17/1.00  fof(f41,plain,(
% 3.17/1.00    ? [X0,X1] : (((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0))) & v1_relat_1(X1))),
% 3.17/1.00    inference(nnf_transformation,[],[f28])).
% 3.17/1.00  
% 3.17/1.00  fof(f42,plain,(
% 3.17/1.00    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0)) & v1_relat_1(X1))),
% 3.17/1.00    inference(flattening,[],[f41])).
% 3.17/1.00  
% 3.17/1.00  fof(f43,plain,(
% 3.17/1.00    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k1_relat_1(sK3),sK2) | k1_xboole_0 != k7_relat_1(sK3,sK2)) & (r1_xboole_0(k1_relat_1(sK3),sK2) | k1_xboole_0 = k7_relat_1(sK3,sK2)) & v1_relat_1(sK3))),
% 3.17/1.00    introduced(choice_axiom,[])).
% 3.17/1.00  
% 3.17/1.00  fof(f44,plain,(
% 3.17/1.00    (~r1_xboole_0(k1_relat_1(sK3),sK2) | k1_xboole_0 != k7_relat_1(sK3,sK2)) & (r1_xboole_0(k1_relat_1(sK3),sK2) | k1_xboole_0 = k7_relat_1(sK3,sK2)) & v1_relat_1(sK3)),
% 3.17/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f42,f43])).
% 3.17/1.00  
% 3.17/1.00  fof(f77,plain,(
% 3.17/1.00    r1_xboole_0(k1_relat_1(sK3),sK2) | k1_xboole_0 = k7_relat_1(sK3,sK2)),
% 3.17/1.00    inference(cnf_transformation,[],[f44])).
% 3.17/1.00  
% 3.17/1.00  fof(f76,plain,(
% 3.17/1.00    v1_relat_1(sK3)),
% 3.17/1.00    inference(cnf_transformation,[],[f44])).
% 3.17/1.00  
% 3.17/1.00  fof(f19,axiom,(
% 3.17/1.00    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)))),
% 3.17/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.17/1.00  
% 3.17/1.00  fof(f27,plain,(
% 3.17/1.00    ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 3.17/1.00    inference(ennf_transformation,[],[f19])).
% 3.17/1.00  
% 3.17/1.00  fof(f75,plain,(
% 3.17/1.00    ( ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 3.17/1.00    inference(cnf_transformation,[],[f27])).
% 3.17/1.00  
% 3.17/1.00  fof(f6,axiom,(
% 3.17/1.00    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 3.17/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.17/1.00  
% 3.17/1.00  fof(f59,plain,(
% 3.17/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 3.17/1.00    inference(cnf_transformation,[],[f6])).
% 3.17/1.00  
% 3.17/1.00  fof(f86,plain,(
% 3.17/1.00    ( ! [X0,X1] : (k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 3.17/1.00    inference(definition_unfolding,[],[f75,f59])).
% 3.17/1.00  
% 3.17/1.00  fof(f4,axiom,(
% 3.17/1.00    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 3.17/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.17/1.00  
% 3.17/1.00  fof(f57,plain,(
% 3.17/1.00    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 3.17/1.00    inference(cnf_transformation,[],[f4])).
% 3.17/1.00  
% 3.17/1.00  fof(f84,plain,(
% 3.17/1.00    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0) )),
% 3.17/1.00    inference(definition_unfolding,[],[f57,f59])).
% 3.17/1.00  
% 3.17/1.00  fof(f5,axiom,(
% 3.17/1.00    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.17/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.17/1.00  
% 3.17/1.00  fof(f58,plain,(
% 3.17/1.00    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.17/1.00    inference(cnf_transformation,[],[f5])).
% 3.17/1.00  
% 3.17/1.00  fof(f17,axiom,(
% 3.17/1.00    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 3.17/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.17/1.00  
% 3.17/1.00  fof(f24,plain,(
% 3.17/1.00    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.17/1.00    inference(ennf_transformation,[],[f17])).
% 3.17/1.00  
% 3.17/1.00  fof(f25,plain,(
% 3.17/1.00    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.17/1.00    inference(flattening,[],[f24])).
% 3.17/1.00  
% 3.17/1.00  fof(f72,plain,(
% 3.17/1.00    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.17/1.00    inference(cnf_transformation,[],[f25])).
% 3.17/1.00  
% 3.17/1.00  fof(f16,axiom,(
% 3.17/1.00    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.17/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.17/1.00  
% 3.17/1.00  fof(f70,plain,(
% 3.17/1.00    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.17/1.00    inference(cnf_transformation,[],[f16])).
% 3.17/1.00  
% 3.17/1.00  fof(f18,axiom,(
% 3.17/1.00    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 3.17/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.17/1.00  
% 3.17/1.00  fof(f26,plain,(
% 3.17/1.00    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 3.17/1.00    inference(ennf_transformation,[],[f18])).
% 3.17/1.00  
% 3.17/1.00  fof(f74,plain,(
% 3.17/1.00    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 3.17/1.00    inference(cnf_transformation,[],[f26])).
% 3.17/1.00  
% 3.17/1.00  fof(f2,axiom,(
% 3.17/1.00    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.17/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.17/1.00  
% 3.17/1.00  fof(f33,plain,(
% 3.17/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.17/1.00    inference(nnf_transformation,[],[f2])).
% 3.17/1.00  
% 3.17/1.00  fof(f34,plain,(
% 3.17/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.17/1.00    inference(flattening,[],[f33])).
% 3.17/1.00  
% 3.17/1.00  fof(f35,plain,(
% 3.17/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.17/1.00    inference(rectify,[],[f34])).
% 3.17/1.00  
% 3.17/1.00  fof(f36,plain,(
% 3.17/1.00    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.17/1.00    introduced(choice_axiom,[])).
% 3.17/1.00  
% 3.17/1.00  fof(f37,plain,(
% 3.17/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.17/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f36])).
% 3.17/1.00  
% 3.17/1.00  fof(f48,plain,(
% 3.17/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.17/1.00    inference(cnf_transformation,[],[f37])).
% 3.17/1.00  
% 3.17/1.00  fof(f89,plain,(
% 3.17/1.00    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 3.17/1.00    inference(equality_resolution,[],[f48])).
% 3.17/1.00  
% 3.17/1.00  fof(f1,axiom,(
% 3.17/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.17/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.17/1.00  
% 3.17/1.00  fof(f22,plain,(
% 3.17/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.17/1.00    inference(ennf_transformation,[],[f1])).
% 3.17/1.00  
% 3.17/1.00  fof(f29,plain,(
% 3.17/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.17/1.00    inference(nnf_transformation,[],[f22])).
% 3.17/1.00  
% 3.17/1.00  fof(f30,plain,(
% 3.17/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.17/1.00    inference(rectify,[],[f29])).
% 3.17/1.00  
% 3.17/1.00  fof(f31,plain,(
% 3.17/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.17/1.00    introduced(choice_axiom,[])).
% 3.17/1.00  
% 3.17/1.00  fof(f32,plain,(
% 3.17/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.17/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).
% 3.17/1.00  
% 3.17/1.00  fof(f47,plain,(
% 3.17/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.17/1.00    inference(cnf_transformation,[],[f32])).
% 3.17/1.00  
% 3.17/1.00  fof(f46,plain,(
% 3.17/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.17/1.00    inference(cnf_transformation,[],[f32])).
% 3.17/1.00  
% 3.17/1.00  fof(f3,axiom,(
% 3.17/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.17/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.17/1.00  
% 3.17/1.00  fof(f38,plain,(
% 3.17/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.17/1.00    inference(nnf_transformation,[],[f3])).
% 3.17/1.00  
% 3.17/1.00  fof(f39,plain,(
% 3.17/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.17/1.00    inference(flattening,[],[f38])).
% 3.17/1.00  
% 3.17/1.00  fof(f56,plain,(
% 3.17/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.17/1.00    inference(cnf_transformation,[],[f39])).
% 3.17/1.00  
% 3.17/1.00  fof(f61,plain,(
% 3.17/1.00    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 3.17/1.00    inference(cnf_transformation,[],[f40])).
% 3.17/1.00  
% 3.17/1.00  fof(f78,plain,(
% 3.17/1.00    ~r1_xboole_0(k1_relat_1(sK3),sK2) | k1_xboole_0 != k7_relat_1(sK3,sK2)),
% 3.17/1.00    inference(cnf_transformation,[],[f44])).
% 3.17/1.00  
% 3.17/1.00  cnf(c_17,plain,
% 3.17/1.00      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 3.17/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_906,plain,
% 3.17/1.00      ( v1_relat_1(X0) != iProver_top
% 3.17/1.00      | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
% 3.17/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_15,plain,
% 3.17/1.00      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 3.17/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_174,plain,
% 3.17/1.00      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 3.17/1.00      inference(prop_impl,[status(thm)],[c_15]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_25,negated_conjecture,
% 3.17/1.00      ( r1_xboole_0(k1_relat_1(sK3),sK2)
% 3.17/1.00      | k1_xboole_0 = k7_relat_1(sK3,sK2) ),
% 3.17/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_178,plain,
% 3.17/1.00      ( r1_xboole_0(k1_relat_1(sK3),sK2)
% 3.17/1.00      | k1_xboole_0 = k7_relat_1(sK3,sK2) ),
% 3.17/1.00      inference(prop_impl,[status(thm)],[c_25]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_311,plain,
% 3.17/1.00      ( k7_relat_1(sK3,sK2) = k1_xboole_0
% 3.17/1.00      | k4_xboole_0(X0,X1) = X0
% 3.17/1.00      | k1_relat_1(sK3) != X0
% 3.17/1.00      | sK2 != X1 ),
% 3.17/1.00      inference(resolution_lifted,[status(thm)],[c_174,c_178]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_312,plain,
% 3.17/1.00      ( k7_relat_1(sK3,sK2) = k1_xboole_0
% 3.17/1.00      | k4_xboole_0(k1_relat_1(sK3),sK2) = k1_relat_1(sK3) ),
% 3.17/1.00      inference(unflattening,[status(thm)],[c_311]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_383,plain,
% 3.17/1.00      ( k7_relat_1(sK3,sK2) = k1_xboole_0
% 3.17/1.00      | k4_xboole_0(k1_relat_1(sK3),sK2) = k1_relat_1(sK3) ),
% 3.17/1.00      inference(prop_impl,[status(thm)],[c_312]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_26,negated_conjecture,
% 3.17/1.00      ( v1_relat_1(sK3) ),
% 3.17/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_901,plain,
% 3.17/1.00      ( v1_relat_1(sK3) = iProver_top ),
% 3.17/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_23,plain,
% 3.17/1.00      ( ~ v1_relat_1(X0)
% 3.17/1.00      | k4_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
% 3.17/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_902,plain,
% 3.17/1.00      ( k4_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1))
% 3.17/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.17/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_1382,plain,
% 3.17/1.00      ( k4_xboole_0(k1_relat_1(sK3),k4_xboole_0(k1_relat_1(sK3),X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
% 3.17/1.00      inference(superposition,[status(thm)],[c_901,c_902]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_1602,plain,
% 3.17/1.00      ( k7_relat_1(sK3,sK2) = k1_xboole_0
% 3.17/1.00      | k4_xboole_0(k1_relat_1(sK3),k1_relat_1(sK3)) = k1_relat_1(k7_relat_1(sK3,sK2)) ),
% 3.17/1.00      inference(superposition,[status(thm)],[c_383,c_1382]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_12,plain,
% 3.17/1.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 3.17/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_13,plain,
% 3.17/1.00      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.17/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_918,plain,
% 3.17/1.00      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.17/1.00      inference(light_normalisation,[status(thm)],[c_12,c_13]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_1610,plain,
% 3.17/1.00      ( k7_relat_1(sK3,sK2) = k1_xboole_0
% 3.17/1.00      | k1_relat_1(k7_relat_1(sK3,sK2)) = k1_xboole_0 ),
% 3.17/1.00      inference(demodulation,[status(thm)],[c_1602,c_918]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_21,plain,
% 3.17/1.00      ( ~ v1_relat_1(X0)
% 3.17/1.00      | k1_relat_1(X0) != k1_xboole_0
% 3.17/1.00      | k1_xboole_0 = X0 ),
% 3.17/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_904,plain,
% 3.17/1.00      ( k1_relat_1(X0) != k1_xboole_0
% 3.17/1.00      | k1_xboole_0 = X0
% 3.17/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.17/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_3117,plain,
% 3.17/1.00      ( k7_relat_1(sK3,sK2) = k1_xboole_0
% 3.17/1.00      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.17/1.00      inference(superposition,[status(thm)],[c_1610,c_904]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_9112,plain,
% 3.17/1.00      ( k7_relat_1(sK3,sK2) = k1_xboole_0
% 3.17/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.17/1.00      inference(superposition,[status(thm)],[c_906,c_3117]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_27,plain,
% 3.17/1.00      ( v1_relat_1(sK3) = iProver_top ),
% 3.17/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_9192,plain,
% 3.17/1.00      ( k7_relat_1(sK3,sK2) = k1_xboole_0 ),
% 3.17/1.00      inference(global_propositional_subsumption,
% 3.17/1.00                [status(thm)],
% 3.17/1.00                [c_9112,c_27]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_1608,plain,
% 3.17/1.00      ( k1_relat_1(k7_relat_1(sK3,k4_xboole_0(k1_relat_1(sK3),X0))) = k4_xboole_0(k1_relat_1(sK3),k1_relat_1(k7_relat_1(sK3,X0))) ),
% 3.17/1.00      inference(superposition,[status(thm)],[c_1382,c_1382]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_9227,plain,
% 3.17/1.00      ( k1_relat_1(k7_relat_1(sK3,k4_xboole_0(k1_relat_1(sK3),sK2))) = k4_xboole_0(k1_relat_1(sK3),k1_relat_1(k1_xboole_0)) ),
% 3.17/1.00      inference(superposition,[status(thm)],[c_9192,c_1608]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_19,plain,
% 3.17/1.00      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.17/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_9256,plain,
% 3.17/1.00      ( k1_relat_1(k7_relat_1(sK3,k4_xboole_0(k1_relat_1(sK3),sK2))) = k4_xboole_0(k1_relat_1(sK3),k1_xboole_0) ),
% 3.17/1.00      inference(light_normalisation,[status(thm)],[c_9227,c_19]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_9257,plain,
% 3.17/1.00      ( k1_relat_1(k7_relat_1(sK3,k4_xboole_0(k1_relat_1(sK3),sK2))) = k1_relat_1(sK3) ),
% 3.17/1.00      inference(demodulation,[status(thm)],[c_9256,c_13]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_22,plain,
% 3.17/1.00      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 3.17/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_903,plain,
% 3.17/1.00      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
% 3.17/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.17/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_9548,plain,
% 3.17/1.00      ( r1_tarski(k1_relat_1(sK3),k4_xboole_0(k1_relat_1(sK3),sK2)) = iProver_top
% 3.17/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.17/1.00      inference(superposition,[status(thm)],[c_9257,c_903]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_8,plain,
% 3.17/1.00      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 3.17/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_1330,plain,
% 3.17/1.00      ( ~ r2_hidden(sK0(k4_xboole_0(k1_relat_1(sK3),sK2),k1_relat_1(sK3)),k4_xboole_0(k1_relat_1(sK3),sK2))
% 3.17/1.00      | r2_hidden(sK0(k4_xboole_0(k1_relat_1(sK3),sK2),k1_relat_1(sK3)),k1_relat_1(sK3)) ),
% 3.17/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_1331,plain,
% 3.17/1.00      ( r2_hidden(sK0(k4_xboole_0(k1_relat_1(sK3),sK2),k1_relat_1(sK3)),k4_xboole_0(k1_relat_1(sK3),sK2)) != iProver_top
% 3.17/1.00      | r2_hidden(sK0(k4_xboole_0(k1_relat_1(sK3),sK2),k1_relat_1(sK3)),k1_relat_1(sK3)) = iProver_top ),
% 3.17/1.00      inference(predicate_to_equality,[status(thm)],[c_1330]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_0,plain,
% 3.17/1.00      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.17/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_1050,plain,
% 3.17/1.00      ( ~ r2_hidden(sK0(k4_xboole_0(k1_relat_1(sK3),sK2),k1_relat_1(sK3)),k1_relat_1(sK3))
% 3.17/1.00      | r1_tarski(k4_xboole_0(k1_relat_1(sK3),sK2),k1_relat_1(sK3)) ),
% 3.17/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_1054,plain,
% 3.17/1.00      ( r2_hidden(sK0(k4_xboole_0(k1_relat_1(sK3),sK2),k1_relat_1(sK3)),k1_relat_1(sK3)) != iProver_top
% 3.17/1.00      | r1_tarski(k4_xboole_0(k1_relat_1(sK3),sK2),k1_relat_1(sK3)) = iProver_top ),
% 3.17/1.00      inference(predicate_to_equality,[status(thm)],[c_1050]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_1,plain,
% 3.17/1.00      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.17/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_1051,plain,
% 3.17/1.00      ( r2_hidden(sK0(k4_xboole_0(k1_relat_1(sK3),sK2),k1_relat_1(sK3)),k4_xboole_0(k1_relat_1(sK3),sK2))
% 3.17/1.00      | r1_tarski(k4_xboole_0(k1_relat_1(sK3),sK2),k1_relat_1(sK3)) ),
% 3.17/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_1052,plain,
% 3.17/1.00      ( r2_hidden(sK0(k4_xboole_0(k1_relat_1(sK3),sK2),k1_relat_1(sK3)),k4_xboole_0(k1_relat_1(sK3),sK2)) = iProver_top
% 3.17/1.00      | r1_tarski(k4_xboole_0(k1_relat_1(sK3),sK2),k1_relat_1(sK3)) = iProver_top ),
% 3.17/1.00      inference(predicate_to_equality,[status(thm)],[c_1051]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_9,plain,
% 3.17/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.17/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_948,plain,
% 3.17/1.00      ( ~ r1_tarski(k4_xboole_0(k1_relat_1(sK3),sK2),k1_relat_1(sK3))
% 3.17/1.00      | ~ r1_tarski(k1_relat_1(sK3),k4_xboole_0(k1_relat_1(sK3),sK2))
% 3.17/1.00      | k4_xboole_0(k1_relat_1(sK3),sK2) = k1_relat_1(sK3) ),
% 3.17/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_949,plain,
% 3.17/1.00      ( k4_xboole_0(k1_relat_1(sK3),sK2) = k1_relat_1(sK3)
% 3.17/1.00      | r1_tarski(k4_xboole_0(k1_relat_1(sK3),sK2),k1_relat_1(sK3)) != iProver_top
% 3.17/1.00      | r1_tarski(k1_relat_1(sK3),k4_xboole_0(k1_relat_1(sK3),sK2)) != iProver_top ),
% 3.17/1.00      inference(predicate_to_equality,[status(thm)],[c_948]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_14,plain,
% 3.17/1.00      ( r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0 ),
% 3.17/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_172,plain,
% 3.17/1.00      ( r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0 ),
% 3.17/1.00      inference(prop_impl,[status(thm)],[c_14]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_24,negated_conjecture,
% 3.17/1.00      ( ~ r1_xboole_0(k1_relat_1(sK3),sK2)
% 3.17/1.00      | k1_xboole_0 != k7_relat_1(sK3,sK2) ),
% 3.17/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_176,plain,
% 3.17/1.00      ( ~ r1_xboole_0(k1_relat_1(sK3),sK2)
% 3.17/1.00      | k1_xboole_0 != k7_relat_1(sK3,sK2) ),
% 3.17/1.00      inference(prop_impl,[status(thm)],[c_24]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_303,plain,
% 3.17/1.00      ( k7_relat_1(sK3,sK2) != k1_xboole_0
% 3.17/1.00      | k4_xboole_0(X0,X1) != X0
% 3.17/1.00      | k1_relat_1(sK3) != X0
% 3.17/1.00      | sK2 != X1 ),
% 3.17/1.00      inference(resolution_lifted,[status(thm)],[c_172,c_176]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_304,plain,
% 3.17/1.00      ( k7_relat_1(sK3,sK2) != k1_xboole_0
% 3.17/1.00      | k4_xboole_0(k1_relat_1(sK3),sK2) != k1_relat_1(sK3) ),
% 3.17/1.00      inference(unflattening,[status(thm)],[c_303]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(contradiction,plain,
% 3.17/1.00      ( $false ),
% 3.17/1.00      inference(minisat,
% 3.17/1.00                [status(thm)],
% 3.17/1.00                [c_9548,c_9112,c_1331,c_1054,c_1052,c_949,c_304,c_27]) ).
% 3.17/1.00  
% 3.17/1.00  
% 3.17/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.17/1.00  
% 3.17/1.00  ------                               Statistics
% 3.17/1.00  
% 3.17/1.00  ------ General
% 3.17/1.00  
% 3.17/1.00  abstr_ref_over_cycles:                  0
% 3.17/1.00  abstr_ref_under_cycles:                 0
% 3.17/1.00  gc_basic_clause_elim:                   0
% 3.17/1.00  forced_gc_time:                         0
% 3.17/1.00  parsing_time:                           0.01
% 3.17/1.00  unif_index_cands_time:                  0.
% 3.17/1.00  unif_index_add_time:                    0.
% 3.17/1.00  orderings_time:                         0.
% 3.17/1.00  out_proof_time:                         0.012
% 3.17/1.00  total_time:                             0.36
% 3.17/1.00  num_of_symbols:                         46
% 3.17/1.00  num_of_terms:                           12642
% 3.17/1.00  
% 3.17/1.00  ------ Preprocessing
% 3.17/1.00  
% 3.17/1.00  num_of_splits:                          0
% 3.17/1.00  num_of_split_atoms:                     0
% 3.17/1.00  num_of_reused_defs:                     0
% 3.17/1.00  num_eq_ax_congr_red:                    42
% 3.17/1.00  num_of_sem_filtered_clauses:            1
% 3.17/1.00  num_of_subtypes:                        0
% 3.17/1.00  monotx_restored_types:                  0
% 3.17/1.00  sat_num_of_epr_types:                   0
% 3.17/1.00  sat_num_of_non_cyclic_types:            0
% 3.17/1.00  sat_guarded_non_collapsed_types:        0
% 3.17/1.00  num_pure_diseq_elim:                    0
% 3.17/1.00  simp_replaced_by:                       0
% 3.17/1.00  res_preprocessed:                       119
% 3.17/1.00  prep_upred:                             0
% 3.17/1.00  prep_unflattend:                        4
% 3.17/1.00  smt_new_axioms:                         0
% 3.17/1.00  pred_elim_cands:                        3
% 3.17/1.00  pred_elim:                              1
% 3.17/1.00  pred_elim_cl:                           2
% 3.17/1.00  pred_elim_cycles:                       3
% 3.17/1.00  merged_defs:                            10
% 3.17/1.00  merged_defs_ncl:                        0
% 3.17/1.00  bin_hyper_res:                          10
% 3.17/1.00  prep_cycles:                            4
% 3.17/1.00  pred_elim_time:                         0.001
% 3.17/1.00  splitting_time:                         0.
% 3.17/1.00  sem_filter_time:                        0.
% 3.17/1.00  monotx_time:                            0.001
% 3.17/1.00  subtype_inf_time:                       0.
% 3.17/1.00  
% 3.17/1.00  ------ Problem properties
% 3.17/1.00  
% 3.17/1.00  clauses:                                24
% 3.17/1.00  conjectures:                            1
% 3.17/1.00  epr:                                    4
% 3.17/1.00  horn:                                   18
% 3.17/1.00  ground:                                 5
% 3.17/1.00  unary:                                  7
% 3.17/1.00  binary:                                 9
% 3.17/1.00  lits:                                   50
% 3.17/1.00  lits_eq:                                18
% 3.17/1.00  fd_pure:                                0
% 3.17/1.00  fd_pseudo:                              0
% 3.17/1.00  fd_cond:                                2
% 3.17/1.00  fd_pseudo_cond:                         4
% 3.17/1.00  ac_symbols:                             0
% 3.17/1.00  
% 3.17/1.00  ------ Propositional Solver
% 3.17/1.00  
% 3.17/1.00  prop_solver_calls:                      34
% 3.17/1.00  prop_fast_solver_calls:                 787
% 3.17/1.00  smt_solver_calls:                       0
% 3.17/1.00  smt_fast_solver_calls:                  0
% 3.17/1.00  prop_num_of_clauses:                    4233
% 3.17/1.00  prop_preprocess_simplified:             6226
% 3.17/1.00  prop_fo_subsumed:                       10
% 3.17/1.00  prop_solver_time:                       0.
% 3.17/1.00  smt_solver_time:                        0.
% 3.17/1.00  smt_fast_solver_time:                   0.
% 3.17/1.00  prop_fast_solver_time:                  0.
% 3.17/1.00  prop_unsat_core_time:                   0.
% 3.17/1.00  
% 3.17/1.00  ------ QBF
% 3.17/1.00  
% 3.17/1.00  qbf_q_res:                              0
% 3.17/1.00  qbf_num_tautologies:                    0
% 3.17/1.00  qbf_prep_cycles:                        0
% 3.17/1.00  
% 3.17/1.00  ------ BMC1
% 3.17/1.00  
% 3.17/1.00  bmc1_current_bound:                     -1
% 3.17/1.00  bmc1_last_solved_bound:                 -1
% 3.17/1.00  bmc1_unsat_core_size:                   -1
% 3.17/1.00  bmc1_unsat_core_parents_size:           -1
% 3.17/1.00  bmc1_merge_next_fun:                    0
% 3.17/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.17/1.00  
% 3.17/1.00  ------ Instantiation
% 3.17/1.00  
% 3.17/1.00  inst_num_of_clauses:                    715
% 3.17/1.00  inst_num_in_passive:                    248
% 3.17/1.00  inst_num_in_active:                     410
% 3.17/1.00  inst_num_in_unprocessed:                57
% 3.17/1.00  inst_num_of_loops:                      630
% 3.17/1.00  inst_num_of_learning_restarts:          0
% 3.17/1.00  inst_num_moves_active_passive:          213
% 3.17/1.00  inst_lit_activity:                      0
% 3.17/1.00  inst_lit_activity_moves:                0
% 3.17/1.00  inst_num_tautologies:                   0
% 3.17/1.00  inst_num_prop_implied:                  0
% 3.17/1.00  inst_num_existing_simplified:           0
% 3.17/1.00  inst_num_eq_res_simplified:             0
% 3.17/1.00  inst_num_child_elim:                    0
% 3.17/1.00  inst_num_of_dismatching_blockings:      379
% 3.17/1.00  inst_num_of_non_proper_insts:           1070
% 3.17/1.00  inst_num_of_duplicates:                 0
% 3.17/1.00  inst_inst_num_from_inst_to_res:         0
% 3.17/1.00  inst_dismatching_checking_time:         0.
% 3.17/1.00  
% 3.17/1.00  ------ Resolution
% 3.17/1.00  
% 3.17/1.00  res_num_of_clauses:                     0
% 3.17/1.00  res_num_in_passive:                     0
% 3.17/1.00  res_num_in_active:                      0
% 3.17/1.00  res_num_of_loops:                       123
% 3.17/1.00  res_forward_subset_subsumed:            83
% 3.17/1.00  res_backward_subset_subsumed:           0
% 3.17/1.00  res_forward_subsumed:                   0
% 3.17/1.00  res_backward_subsumed:                  0
% 3.17/1.00  res_forward_subsumption_resolution:     0
% 3.17/1.00  res_backward_subsumption_resolution:    0
% 3.17/1.00  res_clause_to_clause_subsumption:       1882
% 3.17/1.00  res_orphan_elimination:                 0
% 3.17/1.00  res_tautology_del:                      133
% 3.17/1.00  res_num_eq_res_simplified:              0
% 3.17/1.00  res_num_sel_changes:                    0
% 3.17/1.00  res_moves_from_active_to_pass:          0
% 3.17/1.00  
% 3.17/1.00  ------ Superposition
% 3.17/1.00  
% 3.17/1.00  sup_time_total:                         0.
% 3.17/1.00  sup_time_generating:                    0.
% 3.17/1.00  sup_time_sim_full:                      0.
% 3.17/1.00  sup_time_sim_immed:                     0.
% 3.17/1.00  
% 3.17/1.00  sup_num_of_clauses:                     311
% 3.17/1.00  sup_num_in_active:                      84
% 3.17/1.00  sup_num_in_passive:                     227
% 3.17/1.00  sup_num_of_loops:                       124
% 3.17/1.00  sup_fw_superposition:                   864
% 3.17/1.00  sup_bw_superposition:                   725
% 3.17/1.00  sup_immediate_simplified:               607
% 3.17/1.00  sup_given_eliminated:                   1
% 3.17/1.00  comparisons_done:                       0
% 3.17/1.00  comparisons_avoided:                    60
% 3.17/1.00  
% 3.17/1.00  ------ Simplifications
% 3.17/1.00  
% 3.17/1.00  
% 3.17/1.00  sim_fw_subset_subsumed:                 58
% 3.17/1.00  sim_bw_subset_subsumed:                 372
% 3.17/1.00  sim_fw_subsumed:                        143
% 3.17/1.00  sim_bw_subsumed:                        1
% 3.17/1.00  sim_fw_subsumption_res:                 0
% 3.17/1.00  sim_bw_subsumption_res:                 0
% 3.17/1.00  sim_tautology_del:                      66
% 3.17/1.00  sim_eq_tautology_del:                   98
% 3.17/1.00  sim_eq_res_simp:                        3
% 3.17/1.00  sim_fw_demodulated:                     366
% 3.17/1.00  sim_bw_demodulated:                     14
% 3.17/1.00  sim_light_normalised:                   354
% 3.17/1.00  sim_joinable_taut:                      0
% 3.17/1.00  sim_joinable_simp:                      0
% 3.17/1.00  sim_ac_normalised:                      0
% 3.17/1.00  sim_smt_subsumption:                    0
% 3.17/1.00  
%------------------------------------------------------------------------------
