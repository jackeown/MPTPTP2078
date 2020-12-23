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
% DateTime   : Thu Dec  3 11:43:09 EST 2020

% Result     : Theorem 0.90s
% Output     : CNFRefutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 104 expanded)
%              Number of clauses        :   23 (  29 expanded)
%              Number of leaves         :   13 (  24 expanded)
%              Depth                    :   11
%              Number of atoms          :  257 ( 457 expanded)
%              Number of equality atoms :   53 (  70 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(k4_tarski(X0,X1),X2)
         => ( r2_hidden(X1,k3_relat_1(X2))
            & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,k3_relat_1(X2))
        | ~ r2_hidden(X0,k3_relat_1(X2)) )
      & r2_hidden(k4_tarski(X0,X1),X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,k3_relat_1(X2))
        | ~ r2_hidden(X0,k3_relat_1(X2)) )
      & r2_hidden(k4_tarski(X0,X1),X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f27,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(X1,k3_relat_1(X2))
          | ~ r2_hidden(X0,k3_relat_1(X2)) )
        & r2_hidden(k4_tarski(X0,X1),X2)
        & v1_relat_1(X2) )
   => ( ( ~ r2_hidden(sK8,k3_relat_1(sK9))
        | ~ r2_hidden(sK7,k3_relat_1(sK9)) )
      & r2_hidden(k4_tarski(sK7,sK8),sK9)
      & v1_relat_1(sK9) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ( ~ r2_hidden(sK8,k3_relat_1(sK9))
      | ~ r2_hidden(sK7,k3_relat_1(sK9)) )
    & r2_hidden(k4_tarski(sK7,sK8),sK9)
    & v1_relat_1(sK9) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f9,f27])).

fof(f45,plain,(
    r2_hidden(k4_tarski(sK7,sK8),sK9) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f16,plain,(
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
    inference(rectify,[],[f15])).

fof(f19,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK2(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
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

fof(f20,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f16,f19,f18,f17])).

fof(f36,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f50,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f43,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f44,plain,(
    v1_relat_1(sK9) ),
    inference(cnf_transformation,[],[f28])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f10])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f11])).

fof(f13,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & ~ r2_hidden(sK0(X0,X1,X2),X0) )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( r2_hidden(sK0(X0,X1,X2),X1)
          | r2_hidden(sK0(X0,X1,X2),X0)
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & ~ r2_hidden(sK0(X0,X1,X2),X0) )
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( r2_hidden(sK0(X0,X1,X2),X1)
            | r2_hidden(sK0(X0,X1,X2),X0)
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f13])).

fof(f30,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f48,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f30])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f25,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK5(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
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

fof(f26,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f22,f25,f24,f23])).

fof(f40,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f52,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f31,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f47,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f31])).

fof(f46,plain,
    ( ~ r2_hidden(sK8,k3_relat_1(sK9))
    | ~ r2_hidden(sK7,k3_relat_1(sK9)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_16,negated_conjecture,
    ( r2_hidden(k4_tarski(sK7,sK8),sK9) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_590,plain,
    ( r2_hidden(k4_tarski(sK7,sK8),sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_8,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_597,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1421,plain,
    ( r2_hidden(sK7,k1_relat_1(sK9)) = iProver_top ),
    inference(superposition,[status(thm)],[c_590,c_597])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_17,negated_conjecture,
    ( v1_relat_1(sK9) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_204,plain,
    ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_17])).

cnf(c_205,plain,
    ( k2_xboole_0(k1_relat_1(sK9),k2_relat_1(sK9)) = k3_relat_1(sK9) ),
    inference(unflattening,[status(thm)],[c_204])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_601,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k2_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_749,plain,
    ( r2_hidden(X0,k3_relat_1(sK9)) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_205,c_601])).

cnf(c_1957,plain,
    ( r2_hidden(sK7,k3_relat_1(sK9)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1421,c_749])).

cnf(c_12,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_593,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1099,plain,
    ( r2_hidden(sK8,k2_relat_1(sK9)) = iProver_top ),
    inference(superposition,[status(thm)],[c_590,c_593])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_602,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k2_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_837,plain,
    ( r2_hidden(X0,k3_relat_1(sK9)) = iProver_top
    | r2_hidden(X0,k2_relat_1(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_205,c_602])).

cnf(c_1826,plain,
    ( r2_hidden(sK8,k3_relat_1(sK9)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1099,c_837])).

cnf(c_15,negated_conjecture,
    ( ~ r2_hidden(sK7,k3_relat_1(sK9))
    | ~ r2_hidden(sK8,k3_relat_1(sK9)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_20,plain,
    ( r2_hidden(sK7,k3_relat_1(sK9)) != iProver_top
    | r2_hidden(sK8,k3_relat_1(sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1957,c_1826,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.08  % Command    : iproveropt_run.sh %d %s
% 0.06/0.26  % Computer   : n002.cluster.edu
% 0.06/0.26  % Model      : x86_64 x86_64
% 0.06/0.26  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.06/0.26  % Memory     : 8042.1875MB
% 0.06/0.26  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.06/0.26  % CPULimit   : 60
% 0.06/0.26  % WCLimit    : 600
% 0.06/0.26  % DateTime   : Tue Dec  1 09:59:21 EST 2020
% 0.06/0.26  % CPUTime    : 
% 0.06/0.26  % Running in FOF mode
% 0.90/0.84  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.90/0.84  
% 0.90/0.84  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.90/0.84  
% 0.90/0.84  ------  iProver source info
% 0.90/0.84  
% 0.90/0.84  git: date: 2020-06-30 10:37:57 +0100
% 0.90/0.84  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.90/0.84  git: non_committed_changes: false
% 0.90/0.84  git: last_make_outside_of_git: false
% 0.90/0.84  
% 0.90/0.84  ------ 
% 0.90/0.84  
% 0.90/0.84  ------ Input Options
% 0.90/0.84  
% 0.90/0.84  --out_options                           all
% 0.90/0.84  --tptp_safe_out                         true
% 0.90/0.84  --problem_path                          ""
% 0.90/0.84  --include_path                          ""
% 0.90/0.84  --clausifier                            res/vclausify_rel
% 0.90/0.84  --clausifier_options                    --mode clausify
% 0.90/0.84  --stdin                                 false
% 0.90/0.84  --stats_out                             all
% 0.90/0.84  
% 0.90/0.84  ------ General Options
% 0.90/0.84  
% 0.90/0.84  --fof                                   false
% 0.90/0.84  --time_out_real                         305.
% 0.90/0.84  --time_out_virtual                      -1.
% 0.90/0.84  --symbol_type_check                     false
% 0.90/0.84  --clausify_out                          false
% 0.90/0.84  --sig_cnt_out                           false
% 0.90/0.84  --trig_cnt_out                          false
% 0.90/0.84  --trig_cnt_out_tolerance                1.
% 0.90/0.84  --trig_cnt_out_sk_spl                   false
% 0.90/0.84  --abstr_cl_out                          false
% 0.90/0.84  
% 0.90/0.84  ------ Global Options
% 0.90/0.84  
% 0.90/0.84  --schedule                              default
% 0.90/0.84  --add_important_lit                     false
% 0.90/0.84  --prop_solver_per_cl                    1000
% 0.90/0.84  --min_unsat_core                        false
% 0.90/0.84  --soft_assumptions                      false
% 0.90/0.84  --soft_lemma_size                       3
% 0.90/0.84  --prop_impl_unit_size                   0
% 0.90/0.84  --prop_impl_unit                        []
% 0.90/0.84  --share_sel_clauses                     true
% 0.90/0.84  --reset_solvers                         false
% 0.90/0.84  --bc_imp_inh                            [conj_cone]
% 0.90/0.84  --conj_cone_tolerance                   3.
% 0.90/0.84  --extra_neg_conj                        none
% 0.90/0.84  --large_theory_mode                     true
% 0.90/0.84  --prolific_symb_bound                   200
% 0.90/0.84  --lt_threshold                          2000
% 0.90/0.84  --clause_weak_htbl                      true
% 0.90/0.84  --gc_record_bc_elim                     false
% 0.90/0.84  
% 0.90/0.84  ------ Preprocessing Options
% 0.90/0.84  
% 0.90/0.84  --preprocessing_flag                    true
% 0.90/0.84  --time_out_prep_mult                    0.1
% 0.90/0.84  --splitting_mode                        input
% 0.90/0.84  --splitting_grd                         true
% 0.90/0.84  --splitting_cvd                         false
% 0.90/0.84  --splitting_cvd_svl                     false
% 0.90/0.84  --splitting_nvd                         32
% 0.90/0.84  --sub_typing                            true
% 0.90/0.84  --prep_gs_sim                           true
% 0.90/0.84  --prep_unflatten                        true
% 0.90/0.84  --prep_res_sim                          true
% 0.90/0.84  --prep_upred                            true
% 0.90/0.84  --prep_sem_filter                       exhaustive
% 0.90/0.84  --prep_sem_filter_out                   false
% 0.90/0.84  --pred_elim                             true
% 0.90/0.84  --res_sim_input                         true
% 0.90/0.84  --eq_ax_congr_red                       true
% 0.90/0.84  --pure_diseq_elim                       true
% 0.90/0.84  --brand_transform                       false
% 0.90/0.84  --non_eq_to_eq                          false
% 0.90/0.84  --prep_def_merge                        true
% 0.90/0.84  --prep_def_merge_prop_impl              false
% 0.90/0.84  --prep_def_merge_mbd                    true
% 0.90/0.84  --prep_def_merge_tr_red                 false
% 0.90/0.84  --prep_def_merge_tr_cl                  false
% 0.90/0.84  --smt_preprocessing                     true
% 0.90/0.84  --smt_ac_axioms                         fast
% 0.90/0.84  --preprocessed_out                      false
% 0.90/0.84  --preprocessed_stats                    false
% 0.90/0.84  
% 0.90/0.84  ------ Abstraction refinement Options
% 0.90/0.84  
% 0.90/0.84  --abstr_ref                             []
% 0.90/0.84  --abstr_ref_prep                        false
% 0.90/0.84  --abstr_ref_until_sat                   false
% 0.90/0.84  --abstr_ref_sig_restrict                funpre
% 0.90/0.84  --abstr_ref_af_restrict_to_split_sk     false
% 0.90/0.84  --abstr_ref_under                       []
% 0.90/0.84  
% 0.90/0.84  ------ SAT Options
% 0.90/0.84  
% 0.90/0.84  --sat_mode                              false
% 0.90/0.84  --sat_fm_restart_options                ""
% 0.90/0.84  --sat_gr_def                            false
% 0.90/0.84  --sat_epr_types                         true
% 0.90/0.84  --sat_non_cyclic_types                  false
% 0.90/0.84  --sat_finite_models                     false
% 0.90/0.84  --sat_fm_lemmas                         false
% 0.90/0.84  --sat_fm_prep                           false
% 0.90/0.84  --sat_fm_uc_incr                        true
% 0.90/0.84  --sat_out_model                         small
% 0.90/0.84  --sat_out_clauses                       false
% 0.90/0.84  
% 0.90/0.84  ------ QBF Options
% 0.90/0.84  
% 0.90/0.84  --qbf_mode                              false
% 0.90/0.84  --qbf_elim_univ                         false
% 0.90/0.84  --qbf_dom_inst                          none
% 0.90/0.84  --qbf_dom_pre_inst                      false
% 0.90/0.84  --qbf_sk_in                             false
% 0.90/0.84  --qbf_pred_elim                         true
% 0.90/0.84  --qbf_split                             512
% 0.90/0.84  
% 0.90/0.84  ------ BMC1 Options
% 0.90/0.84  
% 0.90/0.84  --bmc1_incremental                      false
% 0.90/0.84  --bmc1_axioms                           reachable_all
% 0.90/0.84  --bmc1_min_bound                        0
% 0.90/0.84  --bmc1_max_bound                        -1
% 0.90/0.84  --bmc1_max_bound_default                -1
% 0.90/0.84  --bmc1_symbol_reachability              true
% 0.90/0.84  --bmc1_property_lemmas                  false
% 0.90/0.84  --bmc1_k_induction                      false
% 0.90/0.84  --bmc1_non_equiv_states                 false
% 0.90/0.84  --bmc1_deadlock                         false
% 0.90/0.84  --bmc1_ucm                              false
% 0.90/0.84  --bmc1_add_unsat_core                   none
% 0.90/0.84  --bmc1_unsat_core_children              false
% 0.90/0.84  --bmc1_unsat_core_extrapolate_axioms    false
% 0.90/0.84  --bmc1_out_stat                         full
% 0.90/0.84  --bmc1_ground_init                      false
% 0.90/0.84  --bmc1_pre_inst_next_state              false
% 0.90/0.84  --bmc1_pre_inst_state                   false
% 0.90/0.84  --bmc1_pre_inst_reach_state             false
% 0.90/0.84  --bmc1_out_unsat_core                   false
% 0.90/0.84  --bmc1_aig_witness_out                  false
% 0.90/0.84  --bmc1_verbose                          false
% 0.90/0.84  --bmc1_dump_clauses_tptp                false
% 0.90/0.84  --bmc1_dump_unsat_core_tptp             false
% 0.90/0.84  --bmc1_dump_file                        -
% 0.90/0.84  --bmc1_ucm_expand_uc_limit              128
% 0.90/0.84  --bmc1_ucm_n_expand_iterations          6
% 0.90/0.84  --bmc1_ucm_extend_mode                  1
% 0.90/0.84  --bmc1_ucm_init_mode                    2
% 0.90/0.84  --bmc1_ucm_cone_mode                    none
% 0.90/0.84  --bmc1_ucm_reduced_relation_type        0
% 0.90/0.84  --bmc1_ucm_relax_model                  4
% 0.90/0.84  --bmc1_ucm_full_tr_after_sat            true
% 0.90/0.84  --bmc1_ucm_expand_neg_assumptions       false
% 0.90/0.84  --bmc1_ucm_layered_model                none
% 0.90/0.84  --bmc1_ucm_max_lemma_size               10
% 0.90/0.84  
% 0.90/0.84  ------ AIG Options
% 0.90/0.84  
% 0.90/0.84  --aig_mode                              false
% 0.90/0.84  
% 0.90/0.84  ------ Instantiation Options
% 0.90/0.84  
% 0.90/0.84  --instantiation_flag                    true
% 0.90/0.84  --inst_sos_flag                         false
% 0.90/0.84  --inst_sos_phase                        true
% 0.90/0.84  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.90/0.84  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.90/0.84  --inst_lit_sel_side                     num_symb
% 0.90/0.84  --inst_solver_per_active                1400
% 0.90/0.84  --inst_solver_calls_frac                1.
% 0.90/0.84  --inst_passive_queue_type               priority_queues
% 0.90/0.84  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.90/0.84  --inst_passive_queues_freq              [25;2]
% 0.90/0.84  --inst_dismatching                      true
% 0.90/0.84  --inst_eager_unprocessed_to_passive     true
% 0.90/0.84  --inst_prop_sim_given                   true
% 0.90/0.84  --inst_prop_sim_new                     false
% 0.90/0.84  --inst_subs_new                         false
% 0.90/0.84  --inst_eq_res_simp                      false
% 0.90/0.84  --inst_subs_given                       false
% 0.90/0.84  --inst_orphan_elimination               true
% 0.90/0.84  --inst_learning_loop_flag               true
% 0.90/0.84  --inst_learning_start                   3000
% 0.90/0.84  --inst_learning_factor                  2
% 0.90/0.84  --inst_start_prop_sim_after_learn       3
% 0.90/0.84  --inst_sel_renew                        solver
% 0.90/0.84  --inst_lit_activity_flag                true
% 0.90/0.84  --inst_restr_to_given                   false
% 0.90/0.84  --inst_activity_threshold               500
% 0.90/0.84  --inst_out_proof                        true
% 0.90/0.84  
% 0.90/0.84  ------ Resolution Options
% 0.90/0.84  
% 0.90/0.84  --resolution_flag                       true
% 0.90/0.84  --res_lit_sel                           adaptive
% 0.90/0.84  --res_lit_sel_side                      none
% 0.90/0.84  --res_ordering                          kbo
% 0.90/0.84  --res_to_prop_solver                    active
% 0.90/0.84  --res_prop_simpl_new                    false
% 0.90/0.84  --res_prop_simpl_given                  true
% 0.90/0.84  --res_passive_queue_type                priority_queues
% 0.90/0.84  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.90/0.84  --res_passive_queues_freq               [15;5]
% 0.90/0.84  --res_forward_subs                      full
% 0.90/0.84  --res_backward_subs                     full
% 0.90/0.84  --res_forward_subs_resolution           true
% 0.90/0.84  --res_backward_subs_resolution          true
% 0.90/0.84  --res_orphan_elimination                true
% 0.90/0.84  --res_time_limit                        2.
% 0.90/0.84  --res_out_proof                         true
% 0.90/0.84  
% 0.90/0.84  ------ Superposition Options
% 0.90/0.84  
% 0.90/0.84  --superposition_flag                    true
% 0.90/0.84  --sup_passive_queue_type                priority_queues
% 0.90/0.84  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.90/0.84  --sup_passive_queues_freq               [8;1;4]
% 0.90/0.84  --demod_completeness_check              fast
% 0.90/0.84  --demod_use_ground                      true
% 0.90/0.84  --sup_to_prop_solver                    passive
% 0.90/0.84  --sup_prop_simpl_new                    true
% 0.90/0.84  --sup_prop_simpl_given                  true
% 0.90/0.84  --sup_fun_splitting                     false
% 0.90/0.84  --sup_smt_interval                      50000
% 0.90/0.84  
% 0.90/0.84  ------ Superposition Simplification Setup
% 0.90/0.84  
% 0.90/0.84  --sup_indices_passive                   []
% 0.90/0.84  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.90/0.84  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.90/0.84  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.90/0.84  --sup_full_triv                         [TrivRules;PropSubs]
% 0.90/0.84  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.90/0.84  --sup_full_bw                           [BwDemod]
% 0.90/0.84  --sup_immed_triv                        [TrivRules]
% 0.90/0.84  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.90/0.84  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.90/0.84  --sup_immed_bw_main                     []
% 0.90/0.84  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.90/0.84  --sup_input_triv                        [Unflattening;TrivRules]
% 0.90/0.84  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.90/0.84  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.90/0.84  
% 0.90/0.84  ------ Combination Options
% 0.90/0.84  
% 0.90/0.84  --comb_res_mult                         3
% 0.90/0.84  --comb_sup_mult                         2
% 0.90/0.84  --comb_inst_mult                        10
% 0.90/0.84  
% 0.90/0.84  ------ Debug Options
% 0.90/0.84  
% 0.90/0.84  --dbg_backtrace                         false
% 0.90/0.84  --dbg_dump_prop_clauses                 false
% 0.90/0.84  --dbg_dump_prop_clauses_file            -
% 0.90/0.84  --dbg_out_stat                          false
% 0.90/0.84  ------ Parsing...
% 0.90/0.84  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.90/0.84  
% 0.90/0.84  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 0.90/0.84  
% 0.90/0.84  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.90/0.84  
% 0.90/0.84  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.90/0.84  ------ Proving...
% 0.90/0.84  ------ Problem Properties 
% 0.90/0.84  
% 0.90/0.84  
% 0.90/0.84  clauses                                 17
% 0.90/0.84  conjectures                             2
% 0.90/0.84  EPR                                     0
% 0.90/0.84  Horn                                    13
% 0.90/0.84  unary                                   2
% 0.90/0.84  binary                                  7
% 0.90/0.84  lits                                    41
% 0.90/0.84  lits eq                                 8
% 0.90/0.84  fd_pure                                 0
% 0.90/0.84  fd_pseudo                               0
% 0.90/0.84  fd_cond                                 0
% 0.90/0.84  fd_pseudo_cond                          7
% 0.90/0.84  AC symbols                              0
% 0.90/0.84  
% 0.90/0.84  ------ Schedule dynamic 5 is on 
% 0.90/0.84  
% 0.90/0.84  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.90/0.84  
% 0.90/0.84  
% 0.90/0.84  ------ 
% 0.90/0.84  Current options:
% 0.90/0.84  ------ 
% 0.90/0.84  
% 0.90/0.84  ------ Input Options
% 0.90/0.84  
% 0.90/0.84  --out_options                           all
% 0.90/0.84  --tptp_safe_out                         true
% 0.90/0.84  --problem_path                          ""
% 0.90/0.84  --include_path                          ""
% 0.90/0.84  --clausifier                            res/vclausify_rel
% 0.90/0.84  --clausifier_options                    --mode clausify
% 0.90/0.84  --stdin                                 false
% 0.90/0.84  --stats_out                             all
% 0.90/0.84  
% 0.90/0.84  ------ General Options
% 0.90/0.84  
% 0.90/0.84  --fof                                   false
% 0.90/0.84  --time_out_real                         305.
% 0.90/0.84  --time_out_virtual                      -1.
% 0.90/0.84  --symbol_type_check                     false
% 0.90/0.84  --clausify_out                          false
% 0.90/0.84  --sig_cnt_out                           false
% 0.90/0.84  --trig_cnt_out                          false
% 0.90/0.84  --trig_cnt_out_tolerance                1.
% 0.90/0.84  --trig_cnt_out_sk_spl                   false
% 0.90/0.84  --abstr_cl_out                          false
% 0.90/0.84  
% 0.90/0.84  ------ Global Options
% 0.90/0.84  
% 0.90/0.84  --schedule                              default
% 0.90/0.84  --add_important_lit                     false
% 0.90/0.84  --prop_solver_per_cl                    1000
% 0.90/0.84  --min_unsat_core                        false
% 0.90/0.84  --soft_assumptions                      false
% 0.90/0.84  --soft_lemma_size                       3
% 0.90/0.84  --prop_impl_unit_size                   0
% 0.90/0.84  --prop_impl_unit                        []
% 0.90/0.84  --share_sel_clauses                     true
% 0.90/0.84  --reset_solvers                         false
% 0.90/0.84  --bc_imp_inh                            [conj_cone]
% 0.90/0.84  --conj_cone_tolerance                   3.
% 0.90/0.84  --extra_neg_conj                        none
% 0.90/0.84  --large_theory_mode                     true
% 0.90/0.84  --prolific_symb_bound                   200
% 0.90/0.84  --lt_threshold                          2000
% 0.90/0.84  --clause_weak_htbl                      true
% 0.90/0.84  --gc_record_bc_elim                     false
% 0.90/0.84  
% 0.90/0.84  ------ Preprocessing Options
% 0.90/0.84  
% 0.90/0.84  --preprocessing_flag                    true
% 0.90/0.84  --time_out_prep_mult                    0.1
% 0.90/0.84  --splitting_mode                        input
% 0.90/0.84  --splitting_grd                         true
% 0.90/0.84  --splitting_cvd                         false
% 0.90/0.84  --splitting_cvd_svl                     false
% 0.90/0.84  --splitting_nvd                         32
% 0.90/0.84  --sub_typing                            true
% 0.90/0.84  --prep_gs_sim                           true
% 0.90/0.84  --prep_unflatten                        true
% 0.90/0.84  --prep_res_sim                          true
% 0.90/0.84  --prep_upred                            true
% 0.90/0.84  --prep_sem_filter                       exhaustive
% 0.90/0.84  --prep_sem_filter_out                   false
% 0.90/0.84  --pred_elim                             true
% 0.90/0.84  --res_sim_input                         true
% 0.90/0.84  --eq_ax_congr_red                       true
% 0.90/0.84  --pure_diseq_elim                       true
% 0.90/0.84  --brand_transform                       false
% 0.90/0.84  --non_eq_to_eq                          false
% 0.90/0.84  --prep_def_merge                        true
% 0.90/0.84  --prep_def_merge_prop_impl              false
% 0.90/0.84  --prep_def_merge_mbd                    true
% 0.90/0.84  --prep_def_merge_tr_red                 false
% 0.90/0.84  --prep_def_merge_tr_cl                  false
% 0.90/0.84  --smt_preprocessing                     true
% 0.90/0.84  --smt_ac_axioms                         fast
% 0.90/0.84  --preprocessed_out                      false
% 0.90/0.84  --preprocessed_stats                    false
% 0.90/0.84  
% 0.90/0.84  ------ Abstraction refinement Options
% 0.90/0.84  
% 0.90/0.84  --abstr_ref                             []
% 0.90/0.84  --abstr_ref_prep                        false
% 0.90/0.84  --abstr_ref_until_sat                   false
% 0.90/0.84  --abstr_ref_sig_restrict                funpre
% 0.90/0.84  --abstr_ref_af_restrict_to_split_sk     false
% 0.90/0.84  --abstr_ref_under                       []
% 0.90/0.84  
% 0.90/0.84  ------ SAT Options
% 0.90/0.84  
% 0.90/0.84  --sat_mode                              false
% 0.90/0.84  --sat_fm_restart_options                ""
% 0.90/0.84  --sat_gr_def                            false
% 0.90/0.84  --sat_epr_types                         true
% 0.90/0.84  --sat_non_cyclic_types                  false
% 0.90/0.84  --sat_finite_models                     false
% 0.90/0.84  --sat_fm_lemmas                         false
% 0.90/0.84  --sat_fm_prep                           false
% 0.90/0.84  --sat_fm_uc_incr                        true
% 0.90/0.84  --sat_out_model                         small
% 0.90/0.84  --sat_out_clauses                       false
% 0.90/0.84  
% 0.90/0.84  ------ QBF Options
% 0.90/0.84  
% 0.90/0.84  --qbf_mode                              false
% 0.90/0.84  --qbf_elim_univ                         false
% 0.90/0.84  --qbf_dom_inst                          none
% 0.90/0.84  --qbf_dom_pre_inst                      false
% 0.90/0.84  --qbf_sk_in                             false
% 0.90/0.84  --qbf_pred_elim                         true
% 0.90/0.84  --qbf_split                             512
% 0.90/0.84  
% 0.90/0.84  ------ BMC1 Options
% 0.90/0.84  
% 0.90/0.84  --bmc1_incremental                      false
% 0.90/0.84  --bmc1_axioms                           reachable_all
% 0.90/0.84  --bmc1_min_bound                        0
% 0.90/0.84  --bmc1_max_bound                        -1
% 0.90/0.84  --bmc1_max_bound_default                -1
% 0.90/0.84  --bmc1_symbol_reachability              true
% 0.90/0.84  --bmc1_property_lemmas                  false
% 0.90/0.84  --bmc1_k_induction                      false
% 0.90/0.84  --bmc1_non_equiv_states                 false
% 0.90/0.84  --bmc1_deadlock                         false
% 0.90/0.84  --bmc1_ucm                              false
% 0.90/0.84  --bmc1_add_unsat_core                   none
% 0.90/0.84  --bmc1_unsat_core_children              false
% 0.90/0.84  --bmc1_unsat_core_extrapolate_axioms    false
% 0.90/0.84  --bmc1_out_stat                         full
% 0.90/0.84  --bmc1_ground_init                      false
% 0.90/0.84  --bmc1_pre_inst_next_state              false
% 0.90/0.84  --bmc1_pre_inst_state                   false
% 0.90/0.84  --bmc1_pre_inst_reach_state             false
% 0.90/0.84  --bmc1_out_unsat_core                   false
% 0.90/0.84  --bmc1_aig_witness_out                  false
% 0.90/0.84  --bmc1_verbose                          false
% 0.90/0.84  --bmc1_dump_clauses_tptp                false
% 0.90/0.84  --bmc1_dump_unsat_core_tptp             false
% 0.90/0.84  --bmc1_dump_file                        -
% 0.90/0.84  --bmc1_ucm_expand_uc_limit              128
% 0.90/0.84  --bmc1_ucm_n_expand_iterations          6
% 0.90/0.84  --bmc1_ucm_extend_mode                  1
% 0.90/0.84  --bmc1_ucm_init_mode                    2
% 0.90/0.84  --bmc1_ucm_cone_mode                    none
% 0.90/0.84  --bmc1_ucm_reduced_relation_type        0
% 0.90/0.84  --bmc1_ucm_relax_model                  4
% 0.90/0.84  --bmc1_ucm_full_tr_after_sat            true
% 0.90/0.84  --bmc1_ucm_expand_neg_assumptions       false
% 0.90/0.84  --bmc1_ucm_layered_model                none
% 0.90/0.84  --bmc1_ucm_max_lemma_size               10
% 0.90/0.84  
% 0.90/0.84  ------ AIG Options
% 0.90/0.84  
% 0.90/0.84  --aig_mode                              false
% 0.90/0.84  
% 0.90/0.84  ------ Instantiation Options
% 0.90/0.84  
% 0.90/0.84  --instantiation_flag                    true
% 0.90/0.84  --inst_sos_flag                         false
% 0.90/0.84  --inst_sos_phase                        true
% 0.90/0.84  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.90/0.84  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.90/0.84  --inst_lit_sel_side                     none
% 0.90/0.84  --inst_solver_per_active                1400
% 0.90/0.84  --inst_solver_calls_frac                1.
% 0.90/0.84  --inst_passive_queue_type               priority_queues
% 0.90/0.84  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.90/0.84  --inst_passive_queues_freq              [25;2]
% 0.90/0.84  --inst_dismatching                      true
% 0.90/0.84  --inst_eager_unprocessed_to_passive     true
% 0.90/0.84  --inst_prop_sim_given                   true
% 0.90/0.84  --inst_prop_sim_new                     false
% 0.90/0.84  --inst_subs_new                         false
% 0.90/0.84  --inst_eq_res_simp                      false
% 0.90/0.84  --inst_subs_given                       false
% 0.90/0.84  --inst_orphan_elimination               true
% 0.90/0.84  --inst_learning_loop_flag               true
% 0.90/0.84  --inst_learning_start                   3000
% 0.90/0.84  --inst_learning_factor                  2
% 0.90/0.84  --inst_start_prop_sim_after_learn       3
% 0.90/0.84  --inst_sel_renew                        solver
% 0.90/0.84  --inst_lit_activity_flag                true
% 0.90/0.84  --inst_restr_to_given                   false
% 0.90/0.84  --inst_activity_threshold               500
% 0.90/0.84  --inst_out_proof                        true
% 0.90/0.84  
% 0.90/0.84  ------ Resolution Options
% 0.90/0.84  
% 0.90/0.84  --resolution_flag                       false
% 0.90/0.84  --res_lit_sel                           adaptive
% 0.90/0.84  --res_lit_sel_side                      none
% 0.90/0.84  --res_ordering                          kbo
% 0.90/0.84  --res_to_prop_solver                    active
% 0.90/0.84  --res_prop_simpl_new                    false
% 0.90/0.84  --res_prop_simpl_given                  true
% 0.90/0.84  --res_passive_queue_type                priority_queues
% 0.90/0.84  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.90/0.84  --res_passive_queues_freq               [15;5]
% 0.90/0.84  --res_forward_subs                      full
% 0.90/0.84  --res_backward_subs                     full
% 0.90/0.84  --res_forward_subs_resolution           true
% 0.90/0.84  --res_backward_subs_resolution          true
% 0.90/0.84  --res_orphan_elimination                true
% 0.90/0.84  --res_time_limit                        2.
% 0.90/0.84  --res_out_proof                         true
% 0.90/0.84  
% 0.90/0.84  ------ Superposition Options
% 0.90/0.84  
% 0.90/0.84  --superposition_flag                    true
% 0.90/0.84  --sup_passive_queue_type                priority_queues
% 0.90/0.84  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.90/0.84  --sup_passive_queues_freq               [8;1;4]
% 0.90/0.84  --demod_completeness_check              fast
% 0.90/0.84  --demod_use_ground                      true
% 0.90/0.84  --sup_to_prop_solver                    passive
% 0.90/0.84  --sup_prop_simpl_new                    true
% 0.90/0.84  --sup_prop_simpl_given                  true
% 0.90/0.84  --sup_fun_splitting                     false
% 0.90/0.84  --sup_smt_interval                      50000
% 0.90/0.84  
% 0.90/0.84  ------ Superposition Simplification Setup
% 0.90/0.84  
% 0.90/0.84  --sup_indices_passive                   []
% 0.90/0.84  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.90/0.84  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.90/0.84  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.90/0.84  --sup_full_triv                         [TrivRules;PropSubs]
% 0.90/0.84  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.90/0.84  --sup_full_bw                           [BwDemod]
% 0.90/0.84  --sup_immed_triv                        [TrivRules]
% 0.90/0.84  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.90/0.84  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.90/0.84  --sup_immed_bw_main                     []
% 0.90/0.84  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.90/0.84  --sup_input_triv                        [Unflattening;TrivRules]
% 0.90/0.84  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.90/0.84  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.90/0.84  
% 0.90/0.84  ------ Combination Options
% 0.90/0.84  
% 0.90/0.84  --comb_res_mult                         3
% 0.90/0.84  --comb_sup_mult                         2
% 0.90/0.84  --comb_inst_mult                        10
% 0.90/0.84  
% 0.90/0.84  ------ Debug Options
% 0.90/0.84  
% 0.90/0.84  --dbg_backtrace                         false
% 0.90/0.84  --dbg_dump_prop_clauses                 false
% 0.90/0.84  --dbg_dump_prop_clauses_file            -
% 0.90/0.84  --dbg_out_stat                          false
% 0.90/0.84  
% 0.90/0.84  
% 0.90/0.84  
% 0.90/0.84  
% 0.90/0.84  ------ Proving...
% 0.90/0.84  
% 0.90/0.84  
% 0.90/0.84  % SZS status Theorem for theBenchmark.p
% 0.90/0.84  
% 0.90/0.84  % SZS output start CNFRefutation for theBenchmark.p
% 0.90/0.84  
% 0.90/0.84  fof(f5,conjecture,(
% 0.90/0.84    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)))))),
% 0.90/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.90/0.84  
% 0.90/0.84  fof(f6,negated_conjecture,(
% 0.90/0.84    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)))))),
% 0.90/0.84    inference(negated_conjecture,[],[f5])).
% 0.90/0.84  
% 0.90/0.84  fof(f8,plain,(
% 0.90/0.84    ? [X0,X1,X2] : (((~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2))) & r2_hidden(k4_tarski(X0,X1),X2)) & v1_relat_1(X2))),
% 0.90/0.84    inference(ennf_transformation,[],[f6])).
% 0.90/0.84  
% 0.90/0.84  fof(f9,plain,(
% 0.90/0.84    ? [X0,X1,X2] : ((~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2))) & r2_hidden(k4_tarski(X0,X1),X2) & v1_relat_1(X2))),
% 0.90/0.84    inference(flattening,[],[f8])).
% 0.90/0.84  
% 0.90/0.84  fof(f27,plain,(
% 0.90/0.84    ? [X0,X1,X2] : ((~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2))) & r2_hidden(k4_tarski(X0,X1),X2) & v1_relat_1(X2)) => ((~r2_hidden(sK8,k3_relat_1(sK9)) | ~r2_hidden(sK7,k3_relat_1(sK9))) & r2_hidden(k4_tarski(sK7,sK8),sK9) & v1_relat_1(sK9))),
% 0.90/0.84    introduced(choice_axiom,[])).
% 0.90/0.84  
% 0.90/0.84  fof(f28,plain,(
% 0.90/0.84    (~r2_hidden(sK8,k3_relat_1(sK9)) | ~r2_hidden(sK7,k3_relat_1(sK9))) & r2_hidden(k4_tarski(sK7,sK8),sK9) & v1_relat_1(sK9)),
% 0.90/0.84    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f9,f27])).
% 0.90/0.84  
% 0.90/0.84  fof(f45,plain,(
% 0.90/0.84    r2_hidden(k4_tarski(sK7,sK8),sK9)),
% 0.90/0.84    inference(cnf_transformation,[],[f28])).
% 0.90/0.84  
% 0.90/0.84  fof(f2,axiom,(
% 0.90/0.84    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.90/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.90/0.84  
% 0.90/0.84  fof(f15,plain,(
% 0.90/0.84    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 0.90/0.84    inference(nnf_transformation,[],[f2])).
% 0.90/0.84  
% 0.90/0.84  fof(f16,plain,(
% 0.90/0.84    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.90/0.84    inference(rectify,[],[f15])).
% 0.90/0.84  
% 0.90/0.84  fof(f19,plain,(
% 0.90/0.84    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0))),
% 0.90/0.84    introduced(choice_axiom,[])).
% 0.90/0.84  
% 0.90/0.84  fof(f18,plain,(
% 0.90/0.84    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) => r2_hidden(k4_tarski(X2,sK2(X0,X1)),X0))) )),
% 0.90/0.84    introduced(choice_axiom,[])).
% 0.90/0.84  
% 0.90/0.84  fof(f17,plain,(
% 0.90/0.84    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK1(X0,X1),X3),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK1(X0,X1),X4),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 0.90/0.84    introduced(choice_axiom,[])).
% 0.90/0.84  
% 0.90/0.84  fof(f20,plain,(
% 0.90/0.84    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK1(X0,X1),X3),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.90/0.84    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f16,f19,f18,f17])).
% 0.90/0.84  
% 0.90/0.84  fof(f36,plain,(
% 0.90/0.84    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 0.90/0.84    inference(cnf_transformation,[],[f20])).
% 0.90/0.84  
% 0.90/0.84  fof(f50,plain,(
% 0.90/0.84    ( ! [X6,X0,X5] : (r2_hidden(X5,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X5,X6),X0)) )),
% 0.90/0.84    inference(equality_resolution,[],[f36])).
% 0.90/0.84  
% 0.90/0.84  fof(f4,axiom,(
% 0.90/0.84    ! [X0] : (v1_relat_1(X0) => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0))),
% 0.90/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.90/0.84  
% 0.90/0.84  fof(f7,plain,(
% 0.90/0.84    ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0))),
% 0.90/0.84    inference(ennf_transformation,[],[f4])).
% 0.90/0.84  
% 0.90/0.84  fof(f43,plain,(
% 0.90/0.84    ( ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.90/0.84    inference(cnf_transformation,[],[f7])).
% 0.90/0.84  
% 0.90/0.84  fof(f44,plain,(
% 0.90/0.84    v1_relat_1(sK9)),
% 0.90/0.84    inference(cnf_transformation,[],[f28])).
% 0.90/0.84  
% 0.90/0.84  fof(f1,axiom,(
% 0.90/0.84    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.90/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.90/0.84  
% 0.90/0.84  fof(f10,plain,(
% 0.90/0.84    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.90/0.84    inference(nnf_transformation,[],[f1])).
% 0.90/0.84  
% 0.90/0.84  fof(f11,plain,(
% 0.90/0.84    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.90/0.84    inference(flattening,[],[f10])).
% 0.90/0.84  
% 0.90/0.84  fof(f12,plain,(
% 0.90/0.84    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.90/0.84    inference(rectify,[],[f11])).
% 0.90/0.84  
% 0.90/0.84  fof(f13,plain,(
% 0.90/0.84    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 0.90/0.84    introduced(choice_axiom,[])).
% 0.90/0.84  
% 0.90/0.84  fof(f14,plain,(
% 0.90/0.84    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.90/0.84    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f13])).
% 0.90/0.84  
% 0.90/0.84  fof(f30,plain,(
% 0.90/0.84    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 0.90/0.84    inference(cnf_transformation,[],[f14])).
% 0.90/0.84  
% 0.90/0.84  fof(f48,plain,(
% 0.90/0.84    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 0.90/0.84    inference(equality_resolution,[],[f30])).
% 0.90/0.84  
% 0.90/0.84  fof(f3,axiom,(
% 0.90/0.84    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.90/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.90/0.84  
% 0.90/0.84  fof(f21,plain,(
% 0.90/0.84    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 0.90/0.84    inference(nnf_transformation,[],[f3])).
% 0.90/0.84  
% 0.90/0.84  fof(f22,plain,(
% 0.90/0.84    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.90/0.84    inference(rectify,[],[f21])).
% 0.90/0.84  
% 0.90/0.84  fof(f25,plain,(
% 0.90/0.84    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK6(X0,X5),X5),X0))),
% 0.90/0.84    introduced(choice_axiom,[])).
% 0.90/0.84  
% 0.90/0.84  fof(f24,plain,(
% 0.90/0.84    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) => r2_hidden(k4_tarski(sK5(X0,X1),X2),X0))) )),
% 0.90/0.84    introduced(choice_axiom,[])).
% 0.90/0.84  
% 0.90/0.84  fof(f23,plain,(
% 0.90/0.84    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK4(X0,X1)),X0) | r2_hidden(sK4(X0,X1),X1))))),
% 0.90/0.84    introduced(choice_axiom,[])).
% 0.90/0.84  
% 0.90/0.84  fof(f26,plain,(
% 0.90/0.84    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.90/0.84    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f22,f25,f24,f23])).
% 0.90/0.84  
% 0.90/0.84  fof(f40,plain,(
% 0.90/0.84    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 0.90/0.84    inference(cnf_transformation,[],[f26])).
% 0.90/0.84  
% 0.90/0.84  fof(f52,plain,(
% 0.90/0.84    ( ! [X6,X0,X5] : (r2_hidden(X5,k2_relat_1(X0)) | ~r2_hidden(k4_tarski(X6,X5),X0)) )),
% 0.90/0.84    inference(equality_resolution,[],[f40])).
% 0.90/0.84  
% 0.90/0.84  fof(f31,plain,(
% 0.90/0.84    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 0.90/0.84    inference(cnf_transformation,[],[f14])).
% 0.90/0.84  
% 0.90/0.84  fof(f47,plain,(
% 0.90/0.84    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 0.90/0.84    inference(equality_resolution,[],[f31])).
% 0.90/0.84  
% 0.90/0.84  fof(f46,plain,(
% 0.90/0.84    ~r2_hidden(sK8,k3_relat_1(sK9)) | ~r2_hidden(sK7,k3_relat_1(sK9))),
% 0.90/0.84    inference(cnf_transformation,[],[f28])).
% 0.90/0.84  
% 0.90/0.84  cnf(c_16,negated_conjecture,
% 0.90/0.84      ( r2_hidden(k4_tarski(sK7,sK8),sK9) ),
% 0.90/0.84      inference(cnf_transformation,[],[f45]) ).
% 0.90/0.84  
% 0.90/0.84  cnf(c_590,plain,
% 0.90/0.84      ( r2_hidden(k4_tarski(sK7,sK8),sK9) = iProver_top ),
% 0.90/0.84      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 0.90/0.84  
% 0.90/0.84  cnf(c_8,plain,
% 0.90/0.84      ( r2_hidden(X0,k1_relat_1(X1)) | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
% 0.90/0.84      inference(cnf_transformation,[],[f50]) ).
% 0.90/0.84  
% 0.90/0.84  cnf(c_597,plain,
% 0.90/0.84      ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
% 0.90/0.84      | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top ),
% 0.90/0.84      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 0.90/0.84  
% 0.90/0.84  cnf(c_1421,plain,
% 0.90/0.84      ( r2_hidden(sK7,k1_relat_1(sK9)) = iProver_top ),
% 0.90/0.84      inference(superposition,[status(thm)],[c_590,c_597]) ).
% 0.90/0.84  
% 0.90/0.84  cnf(c_14,plain,
% 0.90/0.84      ( ~ v1_relat_1(X0)
% 0.90/0.84      | k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ),
% 0.90/0.84      inference(cnf_transformation,[],[f43]) ).
% 0.90/0.84  
% 0.90/0.84  cnf(c_17,negated_conjecture,
% 0.90/0.84      ( v1_relat_1(sK9) ),
% 0.90/0.84      inference(cnf_transformation,[],[f44]) ).
% 0.90/0.84  
% 0.90/0.84  cnf(c_204,plain,
% 0.90/0.84      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
% 0.90/0.84      | sK9 != X0 ),
% 0.90/0.84      inference(resolution_lifted,[status(thm)],[c_14,c_17]) ).
% 0.90/0.84  
% 0.90/0.84  cnf(c_205,plain,
% 0.90/0.84      ( k2_xboole_0(k1_relat_1(sK9),k2_relat_1(sK9)) = k3_relat_1(sK9) ),
% 0.90/0.84      inference(unflattening,[status(thm)],[c_204]) ).
% 0.90/0.84  
% 0.90/0.84  cnf(c_4,plain,
% 0.90/0.84      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
% 0.90/0.84      inference(cnf_transformation,[],[f48]) ).
% 0.90/0.84  
% 0.90/0.84  cnf(c_601,plain,
% 0.90/0.84      ( r2_hidden(X0,X1) != iProver_top
% 0.90/0.84      | r2_hidden(X0,k2_xboole_0(X1,X2)) = iProver_top ),
% 0.90/0.84      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 0.90/0.84  
% 0.90/0.84  cnf(c_749,plain,
% 0.90/0.84      ( r2_hidden(X0,k3_relat_1(sK9)) = iProver_top
% 0.90/0.84      | r2_hidden(X0,k1_relat_1(sK9)) != iProver_top ),
% 0.90/0.84      inference(superposition,[status(thm)],[c_205,c_601]) ).
% 0.90/0.84  
% 0.90/0.84  cnf(c_1957,plain,
% 0.90/0.84      ( r2_hidden(sK7,k3_relat_1(sK9)) = iProver_top ),
% 0.90/0.84      inference(superposition,[status(thm)],[c_1421,c_749]) ).
% 0.90/0.84  
% 0.90/0.84  cnf(c_12,plain,
% 0.90/0.84      ( r2_hidden(X0,k2_relat_1(X1)) | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
% 0.90/0.84      inference(cnf_transformation,[],[f52]) ).
% 0.90/0.84  
% 0.90/0.84  cnf(c_593,plain,
% 0.90/0.84      ( r2_hidden(X0,k2_relat_1(X1)) = iProver_top
% 0.90/0.84      | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top ),
% 0.90/0.84      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 0.90/0.84  
% 0.90/0.84  cnf(c_1099,plain,
% 0.90/0.84      ( r2_hidden(sK8,k2_relat_1(sK9)) = iProver_top ),
% 0.90/0.84      inference(superposition,[status(thm)],[c_590,c_593]) ).
% 0.90/0.84  
% 0.90/0.84  cnf(c_3,plain,
% 0.90/0.84      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
% 0.90/0.84      inference(cnf_transformation,[],[f47]) ).
% 0.90/0.84  
% 0.90/0.84  cnf(c_602,plain,
% 0.90/0.84      ( r2_hidden(X0,X1) != iProver_top
% 0.90/0.84      | r2_hidden(X0,k2_xboole_0(X2,X1)) = iProver_top ),
% 0.90/0.84      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 0.90/0.84  
% 0.90/0.84  cnf(c_837,plain,
% 0.90/0.84      ( r2_hidden(X0,k3_relat_1(sK9)) = iProver_top
% 0.90/0.84      | r2_hidden(X0,k2_relat_1(sK9)) != iProver_top ),
% 0.90/0.84      inference(superposition,[status(thm)],[c_205,c_602]) ).
% 0.90/0.84  
% 0.90/0.84  cnf(c_1826,plain,
% 0.90/0.84      ( r2_hidden(sK8,k3_relat_1(sK9)) = iProver_top ),
% 0.90/0.84      inference(superposition,[status(thm)],[c_1099,c_837]) ).
% 0.90/0.84  
% 0.90/0.84  cnf(c_15,negated_conjecture,
% 0.90/0.84      ( ~ r2_hidden(sK7,k3_relat_1(sK9))
% 0.90/0.84      | ~ r2_hidden(sK8,k3_relat_1(sK9)) ),
% 0.90/0.84      inference(cnf_transformation,[],[f46]) ).
% 0.90/0.84  
% 0.90/0.84  cnf(c_20,plain,
% 0.90/0.84      ( r2_hidden(sK7,k3_relat_1(sK9)) != iProver_top
% 0.90/0.84      | r2_hidden(sK8,k3_relat_1(sK9)) != iProver_top ),
% 0.90/0.84      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 0.90/0.84  
% 0.90/0.84  cnf(contradiction,plain,
% 0.90/0.84      ( $false ),
% 0.90/0.84      inference(minisat,[status(thm)],[c_1957,c_1826,c_20]) ).
% 0.90/0.84  
% 0.90/0.84  
% 0.90/0.84  % SZS output end CNFRefutation for theBenchmark.p
% 0.90/0.84  
% 0.90/0.84  ------                               Statistics
% 0.90/0.84  
% 0.90/0.84  ------ General
% 0.90/0.84  
% 0.90/0.84  abstr_ref_over_cycles:                  0
% 0.90/0.84  abstr_ref_under_cycles:                 0
% 0.90/0.84  gc_basic_clause_elim:                   0
% 0.90/0.84  forced_gc_time:                         0
% 0.90/0.84  parsing_time:                           0.007
% 0.90/0.84  unif_index_cands_time:                  0.
% 0.90/0.84  unif_index_add_time:                    0.
% 0.90/0.84  orderings_time:                         0.
% 0.90/0.84  out_proof_time:                         0.009
% 0.90/0.84  total_time:                             0.068
% 0.90/0.84  num_of_symbols:                         48
% 0.90/0.84  num_of_terms:                           2470
% 0.90/0.84  
% 0.90/0.84  ------ Preprocessing
% 0.90/0.84  
% 0.90/0.84  num_of_splits:                          0
% 0.90/0.84  num_of_split_atoms:                     0
% 0.90/0.84  num_of_reused_defs:                     0
% 0.90/0.84  num_eq_ax_congr_red:                    47
% 0.90/0.84  num_of_sem_filtered_clauses:            1
% 0.90/0.84  num_of_subtypes:                        0
% 0.90/0.84  monotx_restored_types:                  0
% 0.90/0.84  sat_num_of_epr_types:                   0
% 0.90/0.84  sat_num_of_non_cyclic_types:            0
% 0.90/0.84  sat_guarded_non_collapsed_types:        0
% 0.90/0.84  num_pure_diseq_elim:                    0
% 0.90/0.84  simp_replaced_by:                       0
% 0.90/0.84  res_preprocessed:                       86
% 0.90/0.84  prep_upred:                             0
% 0.90/0.84  prep_unflattend:                        1
% 0.90/0.84  smt_new_axioms:                         0
% 0.90/0.84  pred_elim_cands:                        1
% 0.90/0.84  pred_elim:                              1
% 0.90/0.84  pred_elim_cl:                           1
% 0.90/0.84  pred_elim_cycles:                       3
% 0.90/0.84  merged_defs:                            0
% 0.90/0.84  merged_defs_ncl:                        0
% 0.90/0.84  bin_hyper_res:                          0
% 0.90/0.84  prep_cycles:                            4
% 0.90/0.84  pred_elim_time:                         0.
% 0.90/0.84  splitting_time:                         0.
% 0.90/0.84  sem_filter_time:                        0.
% 0.90/0.84  monotx_time:                            0.
% 0.90/0.84  subtype_inf_time:                       0.
% 0.90/0.84  
% 0.90/0.84  ------ Problem properties
% 0.90/0.84  
% 0.90/0.84  clauses:                                17
% 0.90/0.84  conjectures:                            2
% 0.90/0.84  epr:                                    0
% 0.90/0.84  horn:                                   13
% 0.90/0.84  ground:                                 3
% 0.90/0.84  unary:                                  2
% 0.90/0.84  binary:                                 7
% 0.90/0.84  lits:                                   41
% 0.90/0.84  lits_eq:                                8
% 0.90/0.84  fd_pure:                                0
% 0.90/0.84  fd_pseudo:                              0
% 0.90/0.84  fd_cond:                                0
% 0.90/0.84  fd_pseudo_cond:                         7
% 0.90/0.84  ac_symbols:                             0
% 0.90/0.84  
% 0.90/0.84  ------ Propositional Solver
% 0.90/0.84  
% 0.90/0.84  prop_solver_calls:                      25
% 0.90/0.84  prop_fast_solver_calls:                 443
% 0.90/0.84  smt_solver_calls:                       0
% 0.90/0.84  smt_fast_solver_calls:                  0
% 0.90/0.84  prop_num_of_clauses:                    802
% 0.90/0.84  prop_preprocess_simplified:             3466
% 0.90/0.84  prop_fo_subsumed:                       0
% 0.90/0.84  prop_solver_time:                       0.
% 0.90/0.84  smt_solver_time:                        0.
% 0.90/0.84  smt_fast_solver_time:                   0.
% 0.90/0.84  prop_fast_solver_time:                  0.
% 0.90/0.84  prop_unsat_core_time:                   0.
% 0.90/0.84  
% 0.90/0.84  ------ QBF
% 0.90/0.84  
% 0.90/0.84  qbf_q_res:                              0
% 0.90/0.84  qbf_num_tautologies:                    0
% 0.90/0.84  qbf_prep_cycles:                        0
% 0.90/0.84  
% 0.90/0.84  ------ BMC1
% 0.90/0.84  
% 0.90/0.84  bmc1_current_bound:                     -1
% 0.90/0.84  bmc1_last_solved_bound:                 -1
% 0.90/0.84  bmc1_unsat_core_size:                   -1
% 0.90/0.84  bmc1_unsat_core_parents_size:           -1
% 0.90/0.84  bmc1_merge_next_fun:                    0
% 0.90/0.84  bmc1_unsat_core_clauses_time:           0.
% 0.90/0.84  
% 0.90/0.84  ------ Instantiation
% 0.90/0.84  
% 0.90/0.84  inst_num_of_clauses:                    222
% 0.90/0.84  inst_num_in_passive:                    54
% 0.90/0.84  inst_num_in_active:                     75
% 0.90/0.84  inst_num_in_unprocessed:                93
% 0.90/0.84  inst_num_of_loops:                      80
% 0.90/0.84  inst_num_of_learning_restarts:          0
% 0.90/0.84  inst_num_moves_active_passive:          4
% 0.90/0.84  inst_lit_activity:                      0
% 0.90/0.84  inst_lit_activity_moves:                0
% 0.90/0.84  inst_num_tautologies:                   0
% 0.90/0.84  inst_num_prop_implied:                  0
% 0.90/0.84  inst_num_existing_simplified:           0
% 0.90/0.84  inst_num_eq_res_simplified:             0
% 0.90/0.84  inst_num_child_elim:                    0
% 0.90/0.84  inst_num_of_dismatching_blockings:      25
% 0.90/0.84  inst_num_of_non_proper_insts:           122
% 0.90/0.84  inst_num_of_duplicates:                 0
% 0.90/0.84  inst_inst_num_from_inst_to_res:         0
% 0.90/0.84  inst_dismatching_checking_time:         0.
% 0.90/0.84  
% 0.90/0.84  ------ Resolution
% 0.90/0.84  
% 0.90/0.84  res_num_of_clauses:                     0
% 0.90/0.84  res_num_in_passive:                     0
% 0.90/0.84  res_num_in_active:                      0
% 0.90/0.84  res_num_of_loops:                       90
% 0.90/0.84  res_forward_subset_subsumed:            2
% 0.90/0.84  res_backward_subset_subsumed:           0
% 0.90/0.84  res_forward_subsumed:                   0
% 0.90/0.84  res_backward_subsumed:                  0
% 0.90/0.84  res_forward_subsumption_resolution:     0
% 0.90/0.84  res_backward_subsumption_resolution:    0
% 0.90/0.84  res_clause_to_clause_subsumption:       72
% 0.90/0.84  res_orphan_elimination:                 0
% 0.90/0.84  res_tautology_del:                      2
% 0.90/0.84  res_num_eq_res_simplified:              0
% 0.90/0.84  res_num_sel_changes:                    0
% 0.90/0.84  res_moves_from_active_to_pass:          0
% 0.90/0.84  
% 0.90/0.84  ------ Superposition
% 0.90/0.84  
% 0.90/0.84  sup_time_total:                         0.
% 0.90/0.84  sup_time_generating:                    0.
% 0.90/0.84  sup_time_sim_full:                      0.
% 0.90/0.84  sup_time_sim_immed:                     0.
% 0.90/0.84  
% 0.90/0.84  sup_num_of_clauses:                     41
% 0.90/0.84  sup_num_in_active:                      15
% 0.90/0.84  sup_num_in_passive:                     26
% 0.90/0.84  sup_num_of_loops:                       14
% 0.90/0.84  sup_fw_superposition:                   14
% 0.90/0.84  sup_bw_superposition:                   14
% 0.90/0.84  sup_immediate_simplified:               0
% 0.90/0.84  sup_given_eliminated:                   0
% 0.90/0.84  comparisons_done:                       0
% 0.90/0.84  comparisons_avoided:                    0
% 0.90/0.84  
% 0.90/0.84  ------ Simplifications
% 0.90/0.84  
% 0.90/0.84  
% 0.90/0.84  sim_fw_subset_subsumed:                 0
% 0.90/0.84  sim_bw_subset_subsumed:                 0
% 0.90/0.84  sim_fw_subsumed:                        0
% 0.90/0.84  sim_bw_subsumed:                        0
% 0.90/0.84  sim_fw_subsumption_res:                 0
% 0.90/0.84  sim_bw_subsumption_res:                 0
% 0.90/0.84  sim_tautology_del:                      3
% 0.90/0.84  sim_eq_tautology_del:                   0
% 0.90/0.84  sim_eq_res_simp:                        0
% 0.90/0.84  sim_fw_demodulated:                     0
% 0.90/0.84  sim_bw_demodulated:                     0
% 0.90/0.84  sim_light_normalised:                   0
% 0.90/0.84  sim_joinable_taut:                      0
% 0.90/0.84  sim_joinable_simp:                      0
% 0.90/0.84  sim_ac_normalised:                      0
% 0.90/0.84  sim_smt_subsumption:                    0
% 0.90/0.84  
%------------------------------------------------------------------------------
