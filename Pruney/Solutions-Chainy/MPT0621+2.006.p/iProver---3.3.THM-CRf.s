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
% DateTime   : Thu Dec  3 11:49:21 EST 2020

% Result     : Theorem 3.00s
% Output     : CNFRefutation 3.00s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 238 expanded)
%              Number of clauses        :   51 (  88 expanded)
%              Number of leaves         :   15 (  58 expanded)
%              Depth                    :   19
%              Number of atoms          :  341 (1032 expanded)
%              Number of equality atoms :  157 ( 427 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f21])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f22])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f24])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f18,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f17])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).

fof(f36,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f6,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f37,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_xboole_0 = k1_funct_1(X1,X2) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_xboole_0 = k1_funct_1(X1,X2)
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ! [X2] :
            ( k1_xboole_0 = k1_funct_1(sK3(X0),X2)
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK3(X0)) = X0
        & v1_funct_1(sK3(X0))
        & v1_relat_1(sK3(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(sK3(X0),X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK3(X0)) = X0
      & v1_funct_1(sK3(X0))
      & v1_relat_1(sK3(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f29])).

fof(f51,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = k1_funct_1(sK3(X0),X2)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f50,plain,(
    ! [X0] : k1_relat_1(sK3(X0)) = X0 ),
    inference(cnf_transformation,[],[f30])).

fof(f8,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_funct_1(X1,X2) = np__1 )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = np__1
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_funct_1(X1,X2) = np__1
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ! [X2] :
            ( k1_funct_1(sK4(X0),X2) = np__1
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK4(X0)) = X0
        & v1_funct_1(sK4(X0))
        & v1_relat_1(sK4(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X2] :
          ( k1_funct_1(sK4(X0),X2) = np__1
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK4(X0)) = X0
      & v1_funct_1(sK4(X0))
      & v1_relat_1(sK4(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f14,f31])).

fof(f54,plain,(
    ! [X0] : k1_relat_1(sK4(X0)) = X0 ),
    inference(cnf_transformation,[],[f32])).

fof(f10,conjecture,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( ( k1_relat_1(X2) = X0
                  & k1_relat_1(X1) = X0 )
               => X1 = X2 ) ) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v1_relat_1(X2) )
               => ( ( k1_relat_1(X2) = X0
                    & k1_relat_1(X1) = X0 )
                 => X1 = X2 ) ) )
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f10])).

fof(f15,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != X0
              | k1_relat_1(X1) != X0
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f16,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != X0
              | k1_relat_1(X1) != X0
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    inference(flattening,[],[f15])).

fof(f33,plain,
    ( ? [X0] :
        ( k1_xboole_0 != X0
        & ! [X1] :
            ( ! [X2] :
                ( X1 = X2
                | k1_relat_1(X2) != X0
                | k1_relat_1(X1) != X0
                | ~ v1_funct_1(X2)
                | ~ v1_relat_1(X2) )
            | ~ v1_funct_1(X1)
            | ~ v1_relat_1(X1) ) )
   => ( k1_xboole_0 != sK5
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != sK5
              | k1_relat_1(X1) != sK5
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( k1_xboole_0 != sK5
    & ! [X1] :
        ( ! [X2] :
            ( X1 = X2
            | k1_relat_1(X2) != sK5
            | k1_relat_1(X1) != sK5
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) )
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f16,f33])).

fof(f57,plain,(
    ! [X2,X1] :
      ( X1 = X2
      | k1_relat_1(X2) != sK5
      | k1_relat_1(X1) != sK5
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f52,plain,(
    ! [X0] : v1_relat_1(sK4(X0)) ),
    inference(cnf_transformation,[],[f32])).

fof(f53,plain,(
    ! [X0] : v1_funct_1(sK4(X0)) ),
    inference(cnf_transformation,[],[f32])).

fof(f48,plain,(
    ! [X0] : v1_relat_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f30])).

fof(f49,plain,(
    ! [X0] : v1_funct_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f30])).

fof(f55,plain,(
    ! [X2,X0] :
      ( k1_funct_1(sK4(X0),X2) = np__1
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f58,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f34])).

fof(f9,axiom,(
    ~ v1_xboole_0(np__1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ~ v1_xboole_0(np__1) ),
    inference(cnf_transformation,[],[f9])).

cnf(c_4,plain,
    ( r2_hidden(sK1(X0,X1,X2),X1)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_595,plain,
    ( k3_xboole_0(X0,X1) = X2
    | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top
    | r2_hidden(sK1(X0,X1,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_9,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_239,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_9])).

cnf(c_240,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_239])).

cnf(c_579,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_240])).

cnf(c_2416,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = X1
    | r2_hidden(sK1(X0,k1_xboole_0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_595,c_579])).

cnf(c_12,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2466,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X1,k1_xboole_0,X0),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2416,c_12])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_220,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK0(X2),X2)
    | X1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_2])).

cnf(c_221,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK0(X1),X1) ),
    inference(unflattening,[status(thm)],[c_220])).

cnf(c_581,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(sK0(X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_221])).

cnf(c_3483,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2466,c_581])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_funct_1(sK3(X1),X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_588,plain,
    ( k1_funct_1(sK3(X0),X1) = k1_xboole_0
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3762,plain,
    ( k1_funct_1(sK3(X0),sK0(X0)) = k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(superposition,[status(thm)],[c_3483,c_588])).

cnf(c_14,plain,
    ( k1_relat_1(sK3(X0)) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_18,plain,
    ( k1_relat_1(sK4(X0)) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_23,negated_conjecture,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | X1 = X0
    | k1_relat_1(X0) != sK5
    | k1_relat_1(X1) != sK5 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_582,plain,
    ( X0 = X1
    | k1_relat_1(X0) != sK5
    | k1_relat_1(X1) != sK5
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_942,plain,
    ( sK4(X0) = X1
    | k1_relat_1(X1) != sK5
    | sK5 != X0
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(sK4(X0)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK4(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_18,c_582])).

cnf(c_20,plain,
    ( v1_relat_1(sK4(X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_28,plain,
    ( v1_relat_1(sK4(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_19,plain,
    ( v1_funct_1(sK4(X0)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_31,plain,
    ( v1_funct_1(sK4(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1280,plain,
    ( v1_funct_1(X1) != iProver_top
    | sK4(X0) = X1
    | k1_relat_1(X1) != sK5
    | sK5 != X0
    | v1_relat_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_942,c_28,c_31])).

cnf(c_1281,plain,
    ( sK4(X0) = X1
    | k1_relat_1(X1) != sK5
    | sK5 != X0
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_1280])).

cnf(c_1291,plain,
    ( sK4(X0) = sK3(X1)
    | sK5 != X1
    | sK5 != X0
    | v1_relat_1(sK3(X1)) != iProver_top
    | v1_funct_1(sK3(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_14,c_1281])).

cnf(c_1437,plain,
    ( sK3(X0) = sK4(sK5)
    | sK5 != X0
    | v1_relat_1(sK3(X0)) != iProver_top
    | v1_funct_1(sK3(X0)) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1291])).

cnf(c_16,plain,
    ( v1_relat_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_15,plain,
    ( v1_funct_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1438,plain,
    ( ~ v1_relat_1(sK3(X0))
    | ~ v1_funct_1(sK3(X0))
    | sK3(X0) = sK4(sK5)
    | sK5 != X0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1437])).

cnf(c_1538,plain,
    ( sK3(X0) = sK4(sK5)
    | sK5 != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1437,c_16,c_15,c_1438])).

cnf(c_1543,plain,
    ( sK4(sK5) = sK3(sK5) ),
    inference(equality_resolution,[status(thm)],[c_1538])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_funct_1(sK4(X1),X0) = np__1 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_585,plain,
    ( k1_funct_1(sK4(X0),X1) = np__1
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3763,plain,
    ( k1_funct_1(sK4(X0),sK0(X0)) = np__1
    | k1_xboole_0 = X0 ),
    inference(superposition,[status(thm)],[c_3483,c_585])).

cnf(c_4808,plain,
    ( k1_funct_1(sK3(sK5),sK0(sK5)) = np__1
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1543,c_3763])).

cnf(c_22,negated_conjecture,
    ( k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_261,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_277,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_261])).

cnf(c_262,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_767,plain,
    ( sK5 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_262])).

cnf(c_768,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_767])).

cnf(c_4953,plain,
    ( k1_funct_1(sK3(sK5),sK0(sK5)) = np__1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4808,c_22,c_277,c_768])).

cnf(c_4956,plain,
    ( sK5 = k1_xboole_0
    | np__1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3762,c_4953])).

cnf(c_21,plain,
    ( ~ v1_xboole_0(np__1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_248,plain,
    ( np__1 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_21])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4956,c_768,c_277,c_248,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:55:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.00/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.00/1.00  
% 3.00/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.00/1.00  
% 3.00/1.00  ------  iProver source info
% 3.00/1.00  
% 3.00/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.00/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.00/1.00  git: non_committed_changes: false
% 3.00/1.00  git: last_make_outside_of_git: false
% 3.00/1.00  
% 3.00/1.00  ------ 
% 3.00/1.00  
% 3.00/1.00  ------ Input Options
% 3.00/1.00  
% 3.00/1.00  --out_options                           all
% 3.00/1.00  --tptp_safe_out                         true
% 3.00/1.00  --problem_path                          ""
% 3.00/1.00  --include_path                          ""
% 3.00/1.00  --clausifier                            res/vclausify_rel
% 3.00/1.00  --clausifier_options                    --mode clausify
% 3.00/1.00  --stdin                                 false
% 3.00/1.00  --stats_out                             all
% 3.00/1.00  
% 3.00/1.00  ------ General Options
% 3.00/1.00  
% 3.00/1.00  --fof                                   false
% 3.00/1.00  --time_out_real                         305.
% 3.00/1.00  --time_out_virtual                      -1.
% 3.00/1.00  --symbol_type_check                     false
% 3.00/1.00  --clausify_out                          false
% 3.00/1.00  --sig_cnt_out                           false
% 3.00/1.00  --trig_cnt_out                          false
% 3.00/1.00  --trig_cnt_out_tolerance                1.
% 3.00/1.00  --trig_cnt_out_sk_spl                   false
% 3.00/1.00  --abstr_cl_out                          false
% 3.00/1.00  
% 3.00/1.00  ------ Global Options
% 3.00/1.00  
% 3.00/1.00  --schedule                              default
% 3.00/1.00  --add_important_lit                     false
% 3.00/1.00  --prop_solver_per_cl                    1000
% 3.00/1.00  --min_unsat_core                        false
% 3.00/1.00  --soft_assumptions                      false
% 3.00/1.00  --soft_lemma_size                       3
% 3.00/1.00  --prop_impl_unit_size                   0
% 3.00/1.00  --prop_impl_unit                        []
% 3.00/1.00  --share_sel_clauses                     true
% 3.00/1.00  --reset_solvers                         false
% 3.00/1.00  --bc_imp_inh                            [conj_cone]
% 3.00/1.00  --conj_cone_tolerance                   3.
% 3.00/1.00  --extra_neg_conj                        none
% 3.00/1.00  --large_theory_mode                     true
% 3.00/1.00  --prolific_symb_bound                   200
% 3.00/1.00  --lt_threshold                          2000
% 3.00/1.00  --clause_weak_htbl                      true
% 3.00/1.00  --gc_record_bc_elim                     false
% 3.00/1.00  
% 3.00/1.00  ------ Preprocessing Options
% 3.00/1.00  
% 3.00/1.00  --preprocessing_flag                    true
% 3.00/1.00  --time_out_prep_mult                    0.1
% 3.00/1.00  --splitting_mode                        input
% 3.00/1.00  --splitting_grd                         true
% 3.00/1.00  --splitting_cvd                         false
% 3.00/1.00  --splitting_cvd_svl                     false
% 3.00/1.00  --splitting_nvd                         32
% 3.00/1.00  --sub_typing                            true
% 3.00/1.00  --prep_gs_sim                           true
% 3.00/1.00  --prep_unflatten                        true
% 3.00/1.00  --prep_res_sim                          true
% 3.00/1.00  --prep_upred                            true
% 3.00/1.00  --prep_sem_filter                       exhaustive
% 3.00/1.00  --prep_sem_filter_out                   false
% 3.00/1.00  --pred_elim                             true
% 3.00/1.00  --res_sim_input                         true
% 3.00/1.00  --eq_ax_congr_red                       true
% 3.00/1.00  --pure_diseq_elim                       true
% 3.00/1.00  --brand_transform                       false
% 3.00/1.00  --non_eq_to_eq                          false
% 3.00/1.00  --prep_def_merge                        true
% 3.00/1.00  --prep_def_merge_prop_impl              false
% 3.00/1.00  --prep_def_merge_mbd                    true
% 3.00/1.00  --prep_def_merge_tr_red                 false
% 3.00/1.00  --prep_def_merge_tr_cl                  false
% 3.00/1.00  --smt_preprocessing                     true
% 3.00/1.00  --smt_ac_axioms                         fast
% 3.00/1.00  --preprocessed_out                      false
% 3.00/1.00  --preprocessed_stats                    false
% 3.00/1.00  
% 3.00/1.00  ------ Abstraction refinement Options
% 3.00/1.00  
% 3.00/1.00  --abstr_ref                             []
% 3.00/1.00  --abstr_ref_prep                        false
% 3.00/1.00  --abstr_ref_until_sat                   false
% 3.00/1.00  --abstr_ref_sig_restrict                funpre
% 3.00/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.00/1.00  --abstr_ref_under                       []
% 3.00/1.00  
% 3.00/1.00  ------ SAT Options
% 3.00/1.00  
% 3.00/1.00  --sat_mode                              false
% 3.00/1.00  --sat_fm_restart_options                ""
% 3.00/1.00  --sat_gr_def                            false
% 3.00/1.00  --sat_epr_types                         true
% 3.00/1.00  --sat_non_cyclic_types                  false
% 3.00/1.00  --sat_finite_models                     false
% 3.00/1.00  --sat_fm_lemmas                         false
% 3.00/1.00  --sat_fm_prep                           false
% 3.00/1.00  --sat_fm_uc_incr                        true
% 3.00/1.00  --sat_out_model                         small
% 3.00/1.00  --sat_out_clauses                       false
% 3.00/1.00  
% 3.00/1.00  ------ QBF Options
% 3.00/1.00  
% 3.00/1.00  --qbf_mode                              false
% 3.00/1.00  --qbf_elim_univ                         false
% 3.00/1.00  --qbf_dom_inst                          none
% 3.00/1.00  --qbf_dom_pre_inst                      false
% 3.00/1.00  --qbf_sk_in                             false
% 3.00/1.00  --qbf_pred_elim                         true
% 3.00/1.00  --qbf_split                             512
% 3.00/1.00  
% 3.00/1.00  ------ BMC1 Options
% 3.00/1.00  
% 3.00/1.00  --bmc1_incremental                      false
% 3.00/1.00  --bmc1_axioms                           reachable_all
% 3.00/1.00  --bmc1_min_bound                        0
% 3.00/1.00  --bmc1_max_bound                        -1
% 3.00/1.00  --bmc1_max_bound_default                -1
% 3.00/1.00  --bmc1_symbol_reachability              true
% 3.00/1.00  --bmc1_property_lemmas                  false
% 3.00/1.00  --bmc1_k_induction                      false
% 3.00/1.00  --bmc1_non_equiv_states                 false
% 3.00/1.00  --bmc1_deadlock                         false
% 3.00/1.00  --bmc1_ucm                              false
% 3.00/1.00  --bmc1_add_unsat_core                   none
% 3.00/1.00  --bmc1_unsat_core_children              false
% 3.00/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.00/1.00  --bmc1_out_stat                         full
% 3.00/1.00  --bmc1_ground_init                      false
% 3.00/1.00  --bmc1_pre_inst_next_state              false
% 3.00/1.00  --bmc1_pre_inst_state                   false
% 3.00/1.00  --bmc1_pre_inst_reach_state             false
% 3.00/1.00  --bmc1_out_unsat_core                   false
% 3.00/1.00  --bmc1_aig_witness_out                  false
% 3.00/1.00  --bmc1_verbose                          false
% 3.00/1.00  --bmc1_dump_clauses_tptp                false
% 3.00/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.00/1.00  --bmc1_dump_file                        -
% 3.00/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.00/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.00/1.00  --bmc1_ucm_extend_mode                  1
% 3.00/1.00  --bmc1_ucm_init_mode                    2
% 3.00/1.00  --bmc1_ucm_cone_mode                    none
% 3.00/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.00/1.00  --bmc1_ucm_relax_model                  4
% 3.00/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.00/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.00/1.00  --bmc1_ucm_layered_model                none
% 3.00/1.00  --bmc1_ucm_max_lemma_size               10
% 3.00/1.00  
% 3.00/1.00  ------ AIG Options
% 3.00/1.00  
% 3.00/1.00  --aig_mode                              false
% 3.00/1.00  
% 3.00/1.00  ------ Instantiation Options
% 3.00/1.00  
% 3.00/1.00  --instantiation_flag                    true
% 3.00/1.00  --inst_sos_flag                         false
% 3.00/1.00  --inst_sos_phase                        true
% 3.00/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.00/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.00/1.00  --inst_lit_sel_side                     num_symb
% 3.00/1.00  --inst_solver_per_active                1400
% 3.00/1.00  --inst_solver_calls_frac                1.
% 3.00/1.00  --inst_passive_queue_type               priority_queues
% 3.00/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.00/1.00  --inst_passive_queues_freq              [25;2]
% 3.00/1.00  --inst_dismatching                      true
% 3.00/1.00  --inst_eager_unprocessed_to_passive     true
% 3.00/1.00  --inst_prop_sim_given                   true
% 3.00/1.00  --inst_prop_sim_new                     false
% 3.00/1.00  --inst_subs_new                         false
% 3.00/1.00  --inst_eq_res_simp                      false
% 3.00/1.00  --inst_subs_given                       false
% 3.00/1.00  --inst_orphan_elimination               true
% 3.00/1.00  --inst_learning_loop_flag               true
% 3.00/1.00  --inst_learning_start                   3000
% 3.00/1.00  --inst_learning_factor                  2
% 3.00/1.00  --inst_start_prop_sim_after_learn       3
% 3.00/1.00  --inst_sel_renew                        solver
% 3.00/1.00  --inst_lit_activity_flag                true
% 3.00/1.00  --inst_restr_to_given                   false
% 3.00/1.00  --inst_activity_threshold               500
% 3.00/1.00  --inst_out_proof                        true
% 3.00/1.00  
% 3.00/1.00  ------ Resolution Options
% 3.00/1.00  
% 3.00/1.00  --resolution_flag                       true
% 3.00/1.00  --res_lit_sel                           adaptive
% 3.00/1.00  --res_lit_sel_side                      none
% 3.00/1.00  --res_ordering                          kbo
% 3.00/1.00  --res_to_prop_solver                    active
% 3.00/1.00  --res_prop_simpl_new                    false
% 3.00/1.00  --res_prop_simpl_given                  true
% 3.00/1.00  --res_passive_queue_type                priority_queues
% 3.00/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.00/1.00  --res_passive_queues_freq               [15;5]
% 3.00/1.00  --res_forward_subs                      full
% 3.00/1.00  --res_backward_subs                     full
% 3.00/1.00  --res_forward_subs_resolution           true
% 3.00/1.00  --res_backward_subs_resolution          true
% 3.00/1.00  --res_orphan_elimination                true
% 3.00/1.00  --res_time_limit                        2.
% 3.00/1.00  --res_out_proof                         true
% 3.00/1.00  
% 3.00/1.00  ------ Superposition Options
% 3.00/1.00  
% 3.00/1.00  --superposition_flag                    true
% 3.00/1.00  --sup_passive_queue_type                priority_queues
% 3.00/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.00/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.00/1.00  --demod_completeness_check              fast
% 3.00/1.00  --demod_use_ground                      true
% 3.00/1.00  --sup_to_prop_solver                    passive
% 3.00/1.00  --sup_prop_simpl_new                    true
% 3.00/1.00  --sup_prop_simpl_given                  true
% 3.00/1.00  --sup_fun_splitting                     false
% 3.00/1.00  --sup_smt_interval                      50000
% 3.00/1.00  
% 3.00/1.00  ------ Superposition Simplification Setup
% 3.00/1.00  
% 3.00/1.00  --sup_indices_passive                   []
% 3.00/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.00/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.00  --sup_full_bw                           [BwDemod]
% 3.00/1.00  --sup_immed_triv                        [TrivRules]
% 3.00/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.00/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.00  --sup_immed_bw_main                     []
% 3.00/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.00/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/1.00  
% 3.00/1.00  ------ Combination Options
% 3.00/1.00  
% 3.00/1.00  --comb_res_mult                         3
% 3.00/1.00  --comb_sup_mult                         2
% 3.00/1.00  --comb_inst_mult                        10
% 3.00/1.00  
% 3.00/1.00  ------ Debug Options
% 3.00/1.00  
% 3.00/1.00  --dbg_backtrace                         false
% 3.00/1.00  --dbg_dump_prop_clauses                 false
% 3.00/1.00  --dbg_dump_prop_clauses_file            -
% 3.00/1.00  --dbg_out_stat                          false
% 3.00/1.00  ------ Parsing...
% 3.00/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.00/1.00  
% 3.00/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e 
% 3.00/1.00  
% 3.00/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.00/1.00  
% 3.00/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.00/1.00  ------ Proving...
% 3.00/1.00  ------ Problem Properties 
% 3.00/1.00  
% 3.00/1.00  
% 3.00/1.00  clauses                                 24
% 3.00/1.00  conjectures                             2
% 3.00/1.00  EPR                                     3
% 3.00/1.00  Horn                                    21
% 3.00/1.00  unary                                   12
% 3.00/1.00  binary                                  5
% 3.00/1.00  lits                                    48
% 3.00/1.00  lits eq                                 16
% 3.00/1.00  fd_pure                                 0
% 3.00/1.00  fd_pseudo                               0
% 3.00/1.00  fd_cond                                 0
% 3.00/1.00  fd_pseudo_cond                          6
% 3.00/1.00  AC symbols                              0
% 3.00/1.00  
% 3.00/1.00  ------ Schedule dynamic 5 is on 
% 3.00/1.00  
% 3.00/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.00/1.00  
% 3.00/1.00  
% 3.00/1.00  ------ 
% 3.00/1.00  Current options:
% 3.00/1.00  ------ 
% 3.00/1.00  
% 3.00/1.00  ------ Input Options
% 3.00/1.00  
% 3.00/1.00  --out_options                           all
% 3.00/1.00  --tptp_safe_out                         true
% 3.00/1.00  --problem_path                          ""
% 3.00/1.00  --include_path                          ""
% 3.00/1.00  --clausifier                            res/vclausify_rel
% 3.00/1.00  --clausifier_options                    --mode clausify
% 3.00/1.00  --stdin                                 false
% 3.00/1.00  --stats_out                             all
% 3.00/1.00  
% 3.00/1.00  ------ General Options
% 3.00/1.00  
% 3.00/1.00  --fof                                   false
% 3.00/1.00  --time_out_real                         305.
% 3.00/1.00  --time_out_virtual                      -1.
% 3.00/1.00  --symbol_type_check                     false
% 3.00/1.00  --clausify_out                          false
% 3.00/1.00  --sig_cnt_out                           false
% 3.00/1.00  --trig_cnt_out                          false
% 3.00/1.00  --trig_cnt_out_tolerance                1.
% 3.00/1.00  --trig_cnt_out_sk_spl                   false
% 3.00/1.00  --abstr_cl_out                          false
% 3.00/1.00  
% 3.00/1.00  ------ Global Options
% 3.00/1.00  
% 3.00/1.00  --schedule                              default
% 3.00/1.00  --add_important_lit                     false
% 3.00/1.00  --prop_solver_per_cl                    1000
% 3.00/1.00  --min_unsat_core                        false
% 3.00/1.00  --soft_assumptions                      false
% 3.00/1.00  --soft_lemma_size                       3
% 3.00/1.00  --prop_impl_unit_size                   0
% 3.00/1.00  --prop_impl_unit                        []
% 3.00/1.00  --share_sel_clauses                     true
% 3.00/1.00  --reset_solvers                         false
% 3.00/1.00  --bc_imp_inh                            [conj_cone]
% 3.00/1.00  --conj_cone_tolerance                   3.
% 3.00/1.00  --extra_neg_conj                        none
% 3.00/1.00  --large_theory_mode                     true
% 3.00/1.00  --prolific_symb_bound                   200
% 3.00/1.00  --lt_threshold                          2000
% 3.00/1.00  --clause_weak_htbl                      true
% 3.00/1.00  --gc_record_bc_elim                     false
% 3.00/1.00  
% 3.00/1.00  ------ Preprocessing Options
% 3.00/1.00  
% 3.00/1.00  --preprocessing_flag                    true
% 3.00/1.00  --time_out_prep_mult                    0.1
% 3.00/1.00  --splitting_mode                        input
% 3.00/1.00  --splitting_grd                         true
% 3.00/1.00  --splitting_cvd                         false
% 3.00/1.00  --splitting_cvd_svl                     false
% 3.00/1.00  --splitting_nvd                         32
% 3.00/1.00  --sub_typing                            true
% 3.00/1.00  --prep_gs_sim                           true
% 3.00/1.00  --prep_unflatten                        true
% 3.00/1.00  --prep_res_sim                          true
% 3.00/1.00  --prep_upred                            true
% 3.00/1.00  --prep_sem_filter                       exhaustive
% 3.00/1.00  --prep_sem_filter_out                   false
% 3.00/1.00  --pred_elim                             true
% 3.00/1.00  --res_sim_input                         true
% 3.00/1.00  --eq_ax_congr_red                       true
% 3.00/1.00  --pure_diseq_elim                       true
% 3.00/1.00  --brand_transform                       false
% 3.00/1.00  --non_eq_to_eq                          false
% 3.00/1.00  --prep_def_merge                        true
% 3.00/1.00  --prep_def_merge_prop_impl              false
% 3.00/1.00  --prep_def_merge_mbd                    true
% 3.00/1.00  --prep_def_merge_tr_red                 false
% 3.00/1.00  --prep_def_merge_tr_cl                  false
% 3.00/1.00  --smt_preprocessing                     true
% 3.00/1.00  --smt_ac_axioms                         fast
% 3.00/1.00  --preprocessed_out                      false
% 3.00/1.00  --preprocessed_stats                    false
% 3.00/1.00  
% 3.00/1.00  ------ Abstraction refinement Options
% 3.00/1.00  
% 3.00/1.00  --abstr_ref                             []
% 3.00/1.00  --abstr_ref_prep                        false
% 3.00/1.00  --abstr_ref_until_sat                   false
% 3.00/1.00  --abstr_ref_sig_restrict                funpre
% 3.00/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.00/1.00  --abstr_ref_under                       []
% 3.00/1.00  
% 3.00/1.00  ------ SAT Options
% 3.00/1.00  
% 3.00/1.00  --sat_mode                              false
% 3.00/1.00  --sat_fm_restart_options                ""
% 3.00/1.00  --sat_gr_def                            false
% 3.00/1.00  --sat_epr_types                         true
% 3.00/1.00  --sat_non_cyclic_types                  false
% 3.00/1.00  --sat_finite_models                     false
% 3.00/1.00  --sat_fm_lemmas                         false
% 3.00/1.00  --sat_fm_prep                           false
% 3.00/1.00  --sat_fm_uc_incr                        true
% 3.00/1.00  --sat_out_model                         small
% 3.00/1.00  --sat_out_clauses                       false
% 3.00/1.00  
% 3.00/1.00  ------ QBF Options
% 3.00/1.00  
% 3.00/1.00  --qbf_mode                              false
% 3.00/1.00  --qbf_elim_univ                         false
% 3.00/1.00  --qbf_dom_inst                          none
% 3.00/1.00  --qbf_dom_pre_inst                      false
% 3.00/1.00  --qbf_sk_in                             false
% 3.00/1.00  --qbf_pred_elim                         true
% 3.00/1.00  --qbf_split                             512
% 3.00/1.00  
% 3.00/1.00  ------ BMC1 Options
% 3.00/1.00  
% 3.00/1.00  --bmc1_incremental                      false
% 3.00/1.00  --bmc1_axioms                           reachable_all
% 3.00/1.00  --bmc1_min_bound                        0
% 3.00/1.00  --bmc1_max_bound                        -1
% 3.00/1.00  --bmc1_max_bound_default                -1
% 3.00/1.00  --bmc1_symbol_reachability              true
% 3.00/1.00  --bmc1_property_lemmas                  false
% 3.00/1.00  --bmc1_k_induction                      false
% 3.00/1.00  --bmc1_non_equiv_states                 false
% 3.00/1.00  --bmc1_deadlock                         false
% 3.00/1.00  --bmc1_ucm                              false
% 3.00/1.00  --bmc1_add_unsat_core                   none
% 3.00/1.00  --bmc1_unsat_core_children              false
% 3.00/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.00/1.00  --bmc1_out_stat                         full
% 3.00/1.00  --bmc1_ground_init                      false
% 3.00/1.00  --bmc1_pre_inst_next_state              false
% 3.00/1.00  --bmc1_pre_inst_state                   false
% 3.00/1.00  --bmc1_pre_inst_reach_state             false
% 3.00/1.00  --bmc1_out_unsat_core                   false
% 3.00/1.00  --bmc1_aig_witness_out                  false
% 3.00/1.00  --bmc1_verbose                          false
% 3.00/1.00  --bmc1_dump_clauses_tptp                false
% 3.00/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.00/1.00  --bmc1_dump_file                        -
% 3.00/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.00/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.00/1.00  --bmc1_ucm_extend_mode                  1
% 3.00/1.00  --bmc1_ucm_init_mode                    2
% 3.00/1.00  --bmc1_ucm_cone_mode                    none
% 3.00/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.00/1.00  --bmc1_ucm_relax_model                  4
% 3.00/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.00/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.00/1.00  --bmc1_ucm_layered_model                none
% 3.00/1.00  --bmc1_ucm_max_lemma_size               10
% 3.00/1.00  
% 3.00/1.00  ------ AIG Options
% 3.00/1.00  
% 3.00/1.00  --aig_mode                              false
% 3.00/1.00  
% 3.00/1.00  ------ Instantiation Options
% 3.00/1.00  
% 3.00/1.00  --instantiation_flag                    true
% 3.00/1.00  --inst_sos_flag                         false
% 3.00/1.00  --inst_sos_phase                        true
% 3.00/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.00/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.00/1.00  --inst_lit_sel_side                     none
% 3.00/1.00  --inst_solver_per_active                1400
% 3.00/1.00  --inst_solver_calls_frac                1.
% 3.00/1.00  --inst_passive_queue_type               priority_queues
% 3.00/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.00/1.00  --inst_passive_queues_freq              [25;2]
% 3.00/1.00  --inst_dismatching                      true
% 3.00/1.00  --inst_eager_unprocessed_to_passive     true
% 3.00/1.00  --inst_prop_sim_given                   true
% 3.00/1.00  --inst_prop_sim_new                     false
% 3.00/1.00  --inst_subs_new                         false
% 3.00/1.00  --inst_eq_res_simp                      false
% 3.00/1.00  --inst_subs_given                       false
% 3.00/1.00  --inst_orphan_elimination               true
% 3.00/1.00  --inst_learning_loop_flag               true
% 3.00/1.00  --inst_learning_start                   3000
% 3.00/1.00  --inst_learning_factor                  2
% 3.00/1.00  --inst_start_prop_sim_after_learn       3
% 3.00/1.00  --inst_sel_renew                        solver
% 3.00/1.00  --inst_lit_activity_flag                true
% 3.00/1.00  --inst_restr_to_given                   false
% 3.00/1.00  --inst_activity_threshold               500
% 3.00/1.00  --inst_out_proof                        true
% 3.00/1.00  
% 3.00/1.00  ------ Resolution Options
% 3.00/1.00  
% 3.00/1.00  --resolution_flag                       false
% 3.00/1.00  --res_lit_sel                           adaptive
% 3.00/1.00  --res_lit_sel_side                      none
% 3.00/1.00  --res_ordering                          kbo
% 3.00/1.00  --res_to_prop_solver                    active
% 3.00/1.00  --res_prop_simpl_new                    false
% 3.00/1.00  --res_prop_simpl_given                  true
% 3.00/1.00  --res_passive_queue_type                priority_queues
% 3.00/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.00/1.00  --res_passive_queues_freq               [15;5]
% 3.00/1.00  --res_forward_subs                      full
% 3.00/1.00  --res_backward_subs                     full
% 3.00/1.00  --res_forward_subs_resolution           true
% 3.00/1.00  --res_backward_subs_resolution          true
% 3.00/1.00  --res_orphan_elimination                true
% 3.00/1.00  --res_time_limit                        2.
% 3.00/1.00  --res_out_proof                         true
% 3.00/1.00  
% 3.00/1.00  ------ Superposition Options
% 3.00/1.00  
% 3.00/1.00  --superposition_flag                    true
% 3.00/1.00  --sup_passive_queue_type                priority_queues
% 3.00/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.00/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.00/1.00  --demod_completeness_check              fast
% 3.00/1.00  --demod_use_ground                      true
% 3.00/1.00  --sup_to_prop_solver                    passive
% 3.00/1.00  --sup_prop_simpl_new                    true
% 3.00/1.00  --sup_prop_simpl_given                  true
% 3.00/1.00  --sup_fun_splitting                     false
% 3.00/1.00  --sup_smt_interval                      50000
% 3.00/1.00  
% 3.00/1.00  ------ Superposition Simplification Setup
% 3.00/1.00  
% 3.00/1.00  --sup_indices_passive                   []
% 3.00/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.00/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.00  --sup_full_bw                           [BwDemod]
% 3.00/1.00  --sup_immed_triv                        [TrivRules]
% 3.00/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.00/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.00  --sup_immed_bw_main                     []
% 3.00/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.00/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/1.00  
% 3.00/1.00  ------ Combination Options
% 3.00/1.00  
% 3.00/1.00  --comb_res_mult                         3
% 3.00/1.00  --comb_sup_mult                         2
% 3.00/1.00  --comb_inst_mult                        10
% 3.00/1.00  
% 3.00/1.00  ------ Debug Options
% 3.00/1.00  
% 3.00/1.00  --dbg_backtrace                         false
% 3.00/1.00  --dbg_dump_prop_clauses                 false
% 3.00/1.00  --dbg_dump_prop_clauses_file            -
% 3.00/1.00  --dbg_out_stat                          false
% 3.00/1.00  
% 3.00/1.00  
% 3.00/1.00  
% 3.00/1.00  
% 3.00/1.00  ------ Proving...
% 3.00/1.00  
% 3.00/1.00  
% 3.00/1.00  % SZS status Theorem for theBenchmark.p
% 3.00/1.00  
% 3.00/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.00/1.00  
% 3.00/1.00  fof(f3,axiom,(
% 3.00/1.00    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.00/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.00  
% 3.00/1.00  fof(f21,plain,(
% 3.00/1.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.00/1.00    inference(nnf_transformation,[],[f3])).
% 3.00/1.00  
% 3.00/1.00  fof(f22,plain,(
% 3.00/1.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.00/1.00    inference(flattening,[],[f21])).
% 3.00/1.00  
% 3.00/1.00  fof(f23,plain,(
% 3.00/1.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.00/1.00    inference(rectify,[],[f22])).
% 3.00/1.00  
% 3.00/1.00  fof(f24,plain,(
% 3.00/1.00    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.00/1.00    introduced(choice_axiom,[])).
% 3.00/1.00  
% 3.00/1.00  fof(f25,plain,(
% 3.00/1.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.00/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f24])).
% 3.00/1.00  
% 3.00/1.00  fof(f42,plain,(
% 3.00/1.00    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 3.00/1.00    inference(cnf_transformation,[],[f25])).
% 3.00/1.00  
% 3.00/1.00  fof(f2,axiom,(
% 3.00/1.00    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.00/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.00  
% 3.00/1.00  fof(f17,plain,(
% 3.00/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.00/1.00    inference(nnf_transformation,[],[f2])).
% 3.00/1.00  
% 3.00/1.00  fof(f18,plain,(
% 3.00/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.00/1.00    inference(rectify,[],[f17])).
% 3.00/1.00  
% 3.00/1.00  fof(f19,plain,(
% 3.00/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.00/1.00    introduced(choice_axiom,[])).
% 3.00/1.00  
% 3.00/1.00  fof(f20,plain,(
% 3.00/1.00    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.00/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).
% 3.00/1.00  
% 3.00/1.00  fof(f36,plain,(
% 3.00/1.00    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.00/1.00    inference(cnf_transformation,[],[f20])).
% 3.00/1.00  
% 3.00/1.00  fof(f4,axiom,(
% 3.00/1.00    v1_xboole_0(k1_xboole_0)),
% 3.00/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.00  
% 3.00/1.00  fof(f44,plain,(
% 3.00/1.00    v1_xboole_0(k1_xboole_0)),
% 3.00/1.00    inference(cnf_transformation,[],[f4])).
% 3.00/1.00  
% 3.00/1.00  fof(f6,axiom,(
% 3.00/1.00    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 3.00/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.00  
% 3.00/1.00  fof(f47,plain,(
% 3.00/1.00    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 3.00/1.00    inference(cnf_transformation,[],[f6])).
% 3.00/1.00  
% 3.00/1.00  fof(f37,plain,(
% 3.00/1.00    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 3.00/1.00    inference(cnf_transformation,[],[f20])).
% 3.00/1.00  
% 3.00/1.00  fof(f7,axiom,(
% 3.00/1.00    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_xboole_0 = k1_funct_1(X1,X2)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 3.00/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.00  
% 3.00/1.00  fof(f13,plain,(
% 3.00/1.00    ! [X0] : ? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 3.00/1.00    inference(ennf_transformation,[],[f7])).
% 3.00/1.00  
% 3.00/1.00  fof(f29,plain,(
% 3.00/1.00    ! [X0] : (? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1)) => (! [X2] : (k1_xboole_0 = k1_funct_1(sK3(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK3(X0)) = X0 & v1_funct_1(sK3(X0)) & v1_relat_1(sK3(X0))))),
% 3.00/1.00    introduced(choice_axiom,[])).
% 3.00/1.00  
% 3.00/1.00  fof(f30,plain,(
% 3.00/1.00    ! [X0] : (! [X2] : (k1_xboole_0 = k1_funct_1(sK3(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK3(X0)) = X0 & v1_funct_1(sK3(X0)) & v1_relat_1(sK3(X0)))),
% 3.00/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f29])).
% 3.00/1.00  
% 3.00/1.00  fof(f51,plain,(
% 3.00/1.00    ( ! [X2,X0] : (k1_xboole_0 = k1_funct_1(sK3(X0),X2) | ~r2_hidden(X2,X0)) )),
% 3.00/1.00    inference(cnf_transformation,[],[f30])).
% 3.00/1.00  
% 3.00/1.00  fof(f50,plain,(
% 3.00/1.00    ( ! [X0] : (k1_relat_1(sK3(X0)) = X0) )),
% 3.00/1.00    inference(cnf_transformation,[],[f30])).
% 3.00/1.00  
% 3.00/1.00  fof(f8,axiom,(
% 3.00/1.00    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = np__1) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 3.00/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.00  
% 3.00/1.00  fof(f14,plain,(
% 3.00/1.00    ! [X0] : ? [X1] : (! [X2] : (k1_funct_1(X1,X2) = np__1 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 3.00/1.00    inference(ennf_transformation,[],[f8])).
% 3.00/1.00  
% 3.00/1.00  fof(f31,plain,(
% 3.00/1.00    ! [X0] : (? [X1] : (! [X2] : (k1_funct_1(X1,X2) = np__1 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1)) => (! [X2] : (k1_funct_1(sK4(X0),X2) = np__1 | ~r2_hidden(X2,X0)) & k1_relat_1(sK4(X0)) = X0 & v1_funct_1(sK4(X0)) & v1_relat_1(sK4(X0))))),
% 3.00/1.00    introduced(choice_axiom,[])).
% 3.00/1.00  
% 3.00/1.00  fof(f32,plain,(
% 3.00/1.00    ! [X0] : (! [X2] : (k1_funct_1(sK4(X0),X2) = np__1 | ~r2_hidden(X2,X0)) & k1_relat_1(sK4(X0)) = X0 & v1_funct_1(sK4(X0)) & v1_relat_1(sK4(X0)))),
% 3.00/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f14,f31])).
% 3.00/1.00  
% 3.00/1.00  fof(f54,plain,(
% 3.00/1.00    ( ! [X0] : (k1_relat_1(sK4(X0)) = X0) )),
% 3.00/1.00    inference(cnf_transformation,[],[f32])).
% 3.00/1.00  
% 3.00/1.00  fof(f10,conjecture,(
% 3.00/1.00    ! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 3.00/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.00  
% 3.00/1.00  fof(f11,negated_conjecture,(
% 3.00/1.00    ~! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 3.00/1.00    inference(negated_conjecture,[],[f10])).
% 3.00/1.00  
% 3.00/1.00  fof(f15,plain,(
% 3.00/1.00    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : ((X1 = X2 | (k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))))),
% 3.00/1.00    inference(ennf_transformation,[],[f11])).
% 3.00/1.00  
% 3.00/1.00  fof(f16,plain,(
% 3.00/1.00    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.00/1.00    inference(flattening,[],[f15])).
% 3.00/1.00  
% 3.00/1.00  fof(f33,plain,(
% 3.00/1.00    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) => (k1_xboole_0 != sK5 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != sK5 | k1_relat_1(X1) != sK5 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.00/1.00    introduced(choice_axiom,[])).
% 3.00/1.00  
% 3.00/1.00  fof(f34,plain,(
% 3.00/1.00    k1_xboole_0 != sK5 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != sK5 | k1_relat_1(X1) != sK5 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.00/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f16,f33])).
% 3.00/1.00  
% 3.00/1.00  fof(f57,plain,(
% 3.00/1.00    ( ! [X2,X1] : (X1 = X2 | k1_relat_1(X2) != sK5 | k1_relat_1(X1) != sK5 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.00/1.00    inference(cnf_transformation,[],[f34])).
% 3.00/1.00  
% 3.00/1.00  fof(f52,plain,(
% 3.00/1.00    ( ! [X0] : (v1_relat_1(sK4(X0))) )),
% 3.00/1.00    inference(cnf_transformation,[],[f32])).
% 3.00/1.00  
% 3.00/1.00  fof(f53,plain,(
% 3.00/1.00    ( ! [X0] : (v1_funct_1(sK4(X0))) )),
% 3.00/1.00    inference(cnf_transformation,[],[f32])).
% 3.00/1.00  
% 3.00/1.00  fof(f48,plain,(
% 3.00/1.00    ( ! [X0] : (v1_relat_1(sK3(X0))) )),
% 3.00/1.00    inference(cnf_transformation,[],[f30])).
% 3.00/1.00  
% 3.00/1.00  fof(f49,plain,(
% 3.00/1.00    ( ! [X0] : (v1_funct_1(sK3(X0))) )),
% 3.00/1.00    inference(cnf_transformation,[],[f30])).
% 3.00/1.00  
% 3.00/1.00  fof(f55,plain,(
% 3.00/1.00    ( ! [X2,X0] : (k1_funct_1(sK4(X0),X2) = np__1 | ~r2_hidden(X2,X0)) )),
% 3.00/1.00    inference(cnf_transformation,[],[f32])).
% 3.00/1.00  
% 3.00/1.00  fof(f58,plain,(
% 3.00/1.00    k1_xboole_0 != sK5),
% 3.00/1.00    inference(cnf_transformation,[],[f34])).
% 3.00/1.00  
% 3.00/1.00  fof(f9,axiom,(
% 3.00/1.00    ~v1_xboole_0(np__1)),
% 3.00/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.00  
% 3.00/1.00  fof(f56,plain,(
% 3.00/1.00    ~v1_xboole_0(np__1)),
% 3.00/1.00    inference(cnf_transformation,[],[f9])).
% 3.00/1.00  
% 3.00/1.00  cnf(c_4,plain,
% 3.00/1.00      ( r2_hidden(sK1(X0,X1,X2),X1)
% 3.00/1.00      | r2_hidden(sK1(X0,X1,X2),X2)
% 3.00/1.00      | k3_xboole_0(X0,X1) = X2 ),
% 3.00/1.00      inference(cnf_transformation,[],[f42]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_595,plain,
% 3.00/1.00      ( k3_xboole_0(X0,X1) = X2
% 3.00/1.00      | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top
% 3.00/1.00      | r2_hidden(sK1(X0,X1,X2),X1) = iProver_top ),
% 3.00/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_2,plain,
% 3.00/1.00      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.00/1.00      inference(cnf_transformation,[],[f36]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_9,plain,
% 3.00/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 3.00/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_239,plain,
% 3.00/1.00      ( ~ r2_hidden(X0,X1) | k1_xboole_0 != X1 ),
% 3.00/1.00      inference(resolution_lifted,[status(thm)],[c_2,c_9]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_240,plain,
% 3.00/1.00      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 3.00/1.00      inference(unflattening,[status(thm)],[c_239]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_579,plain,
% 3.00/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.00/1.00      inference(predicate_to_equality,[status(thm)],[c_240]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_2416,plain,
% 3.00/1.00      ( k3_xboole_0(X0,k1_xboole_0) = X1
% 3.00/1.00      | r2_hidden(sK1(X0,k1_xboole_0,X1),X1) = iProver_top ),
% 3.00/1.00      inference(superposition,[status(thm)],[c_595,c_579]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_12,plain,
% 3.00/1.00      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.00/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_2466,plain,
% 3.00/1.00      ( k1_xboole_0 = X0
% 3.00/1.00      | r2_hidden(sK1(X1,k1_xboole_0,X0),X0) = iProver_top ),
% 3.00/1.00      inference(demodulation,[status(thm)],[c_2416,c_12]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_1,plain,
% 3.00/1.00      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.00/1.00      inference(cnf_transformation,[],[f37]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_220,plain,
% 3.00/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(sK0(X2),X2) | X1 != X2 ),
% 3.00/1.00      inference(resolution_lifted,[status(thm)],[c_1,c_2]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_221,plain,
% 3.00/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(sK0(X1),X1) ),
% 3.00/1.00      inference(unflattening,[status(thm)],[c_220]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_581,plain,
% 3.00/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.00/1.00      | r2_hidden(sK0(X1),X1) = iProver_top ),
% 3.00/1.00      inference(predicate_to_equality,[status(thm)],[c_221]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_3483,plain,
% 3.00/1.00      ( k1_xboole_0 = X0 | r2_hidden(sK0(X0),X0) = iProver_top ),
% 3.00/1.00      inference(superposition,[status(thm)],[c_2466,c_581]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_13,plain,
% 3.00/1.00      ( ~ r2_hidden(X0,X1) | k1_funct_1(sK3(X1),X0) = k1_xboole_0 ),
% 3.00/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_588,plain,
% 3.00/1.00      ( k1_funct_1(sK3(X0),X1) = k1_xboole_0
% 3.00/1.00      | r2_hidden(X1,X0) != iProver_top ),
% 3.00/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_3762,plain,
% 3.00/1.00      ( k1_funct_1(sK3(X0),sK0(X0)) = k1_xboole_0 | k1_xboole_0 = X0 ),
% 3.00/1.00      inference(superposition,[status(thm)],[c_3483,c_588]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_14,plain,
% 3.00/1.00      ( k1_relat_1(sK3(X0)) = X0 ),
% 3.00/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_18,plain,
% 3.00/1.00      ( k1_relat_1(sK4(X0)) = X0 ),
% 3.00/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_23,negated_conjecture,
% 3.00/1.00      ( ~ v1_relat_1(X0)
% 3.00/1.00      | ~ v1_relat_1(X1)
% 3.00/1.00      | ~ v1_funct_1(X0)
% 3.00/1.00      | ~ v1_funct_1(X1)
% 3.00/1.00      | X1 = X0
% 3.00/1.00      | k1_relat_1(X0) != sK5
% 3.00/1.00      | k1_relat_1(X1) != sK5 ),
% 3.00/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_582,plain,
% 3.00/1.00      ( X0 = X1
% 3.00/1.00      | k1_relat_1(X0) != sK5
% 3.00/1.00      | k1_relat_1(X1) != sK5
% 3.00/1.00      | v1_relat_1(X1) != iProver_top
% 3.00/1.00      | v1_relat_1(X0) != iProver_top
% 3.00/1.00      | v1_funct_1(X1) != iProver_top
% 3.00/1.00      | v1_funct_1(X0) != iProver_top ),
% 3.00/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_942,plain,
% 3.00/1.00      ( sK4(X0) = X1
% 3.00/1.00      | k1_relat_1(X1) != sK5
% 3.00/1.00      | sK5 != X0
% 3.00/1.00      | v1_relat_1(X1) != iProver_top
% 3.00/1.00      | v1_relat_1(sK4(X0)) != iProver_top
% 3.00/1.00      | v1_funct_1(X1) != iProver_top
% 3.00/1.00      | v1_funct_1(sK4(X0)) != iProver_top ),
% 3.00/1.00      inference(superposition,[status(thm)],[c_18,c_582]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_20,plain,
% 3.00/1.00      ( v1_relat_1(sK4(X0)) ),
% 3.00/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_28,plain,
% 3.00/1.00      ( v1_relat_1(sK4(X0)) = iProver_top ),
% 3.00/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_19,plain,
% 3.00/1.00      ( v1_funct_1(sK4(X0)) ),
% 3.00/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_31,plain,
% 3.00/1.00      ( v1_funct_1(sK4(X0)) = iProver_top ),
% 3.00/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_1280,plain,
% 3.00/1.00      ( v1_funct_1(X1) != iProver_top
% 3.00/1.00      | sK4(X0) = X1
% 3.00/1.00      | k1_relat_1(X1) != sK5
% 3.00/1.00      | sK5 != X0
% 3.00/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.00/1.00      inference(global_propositional_subsumption,
% 3.00/1.00                [status(thm)],
% 3.00/1.00                [c_942,c_28,c_31]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_1281,plain,
% 3.00/1.00      ( sK4(X0) = X1
% 3.00/1.00      | k1_relat_1(X1) != sK5
% 3.00/1.00      | sK5 != X0
% 3.00/1.00      | v1_relat_1(X1) != iProver_top
% 3.00/1.00      | v1_funct_1(X1) != iProver_top ),
% 3.00/1.00      inference(renaming,[status(thm)],[c_1280]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_1291,plain,
% 3.00/1.00      ( sK4(X0) = sK3(X1)
% 3.00/1.00      | sK5 != X1
% 3.00/1.00      | sK5 != X0
% 3.00/1.00      | v1_relat_1(sK3(X1)) != iProver_top
% 3.00/1.00      | v1_funct_1(sK3(X1)) != iProver_top ),
% 3.00/1.00      inference(superposition,[status(thm)],[c_14,c_1281]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_1437,plain,
% 3.00/1.00      ( sK3(X0) = sK4(sK5)
% 3.00/1.00      | sK5 != X0
% 3.00/1.00      | v1_relat_1(sK3(X0)) != iProver_top
% 3.00/1.00      | v1_funct_1(sK3(X0)) != iProver_top ),
% 3.00/1.00      inference(equality_resolution,[status(thm)],[c_1291]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_16,plain,
% 3.00/1.00      ( v1_relat_1(sK3(X0)) ),
% 3.00/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_15,plain,
% 3.00/1.00      ( v1_funct_1(sK3(X0)) ),
% 3.00/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_1438,plain,
% 3.00/1.00      ( ~ v1_relat_1(sK3(X0))
% 3.00/1.00      | ~ v1_funct_1(sK3(X0))
% 3.00/1.00      | sK3(X0) = sK4(sK5)
% 3.00/1.00      | sK5 != X0 ),
% 3.00/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1437]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_1538,plain,
% 3.00/1.00      ( sK3(X0) = sK4(sK5) | sK5 != X0 ),
% 3.00/1.00      inference(global_propositional_subsumption,
% 3.00/1.00                [status(thm)],
% 3.00/1.00                [c_1437,c_16,c_15,c_1438]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_1543,plain,
% 3.00/1.00      ( sK4(sK5) = sK3(sK5) ),
% 3.00/1.00      inference(equality_resolution,[status(thm)],[c_1538]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_17,plain,
% 3.00/1.00      ( ~ r2_hidden(X0,X1) | k1_funct_1(sK4(X1),X0) = np__1 ),
% 3.00/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_585,plain,
% 3.00/1.00      ( k1_funct_1(sK4(X0),X1) = np__1
% 3.00/1.00      | r2_hidden(X1,X0) != iProver_top ),
% 3.00/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_3763,plain,
% 3.00/1.00      ( k1_funct_1(sK4(X0),sK0(X0)) = np__1 | k1_xboole_0 = X0 ),
% 3.00/1.00      inference(superposition,[status(thm)],[c_3483,c_585]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_4808,plain,
% 3.00/1.00      ( k1_funct_1(sK3(sK5),sK0(sK5)) = np__1 | sK5 = k1_xboole_0 ),
% 3.00/1.00      inference(superposition,[status(thm)],[c_1543,c_3763]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_22,negated_conjecture,
% 3.00/1.00      ( k1_xboole_0 != sK5 ),
% 3.00/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_261,plain,( X0 = X0 ),theory(equality) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_277,plain,
% 3.00/1.00      ( k1_xboole_0 = k1_xboole_0 ),
% 3.00/1.00      inference(instantiation,[status(thm)],[c_261]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_262,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_767,plain,
% 3.00/1.00      ( sK5 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK5 ),
% 3.00/1.00      inference(instantiation,[status(thm)],[c_262]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_768,plain,
% 3.00/1.00      ( sK5 != k1_xboole_0
% 3.00/1.00      | k1_xboole_0 = sK5
% 3.00/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.00/1.00      inference(instantiation,[status(thm)],[c_767]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_4953,plain,
% 3.00/1.00      ( k1_funct_1(sK3(sK5),sK0(sK5)) = np__1 ),
% 3.00/1.00      inference(global_propositional_subsumption,
% 3.00/1.00                [status(thm)],
% 3.00/1.00                [c_4808,c_22,c_277,c_768]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_4956,plain,
% 3.00/1.00      ( sK5 = k1_xboole_0 | np__1 = k1_xboole_0 ),
% 3.00/1.00      inference(superposition,[status(thm)],[c_3762,c_4953]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_21,plain,
% 3.00/1.00      ( ~ v1_xboole_0(np__1) ),
% 3.00/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_248,plain,
% 3.00/1.00      ( np__1 != k1_xboole_0 ),
% 3.00/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_21]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(contradiction,plain,
% 3.00/1.00      ( $false ),
% 3.00/1.00      inference(minisat,[status(thm)],[c_4956,c_768,c_277,c_248,c_22]) ).
% 3.00/1.00  
% 3.00/1.00  
% 3.00/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.00/1.00  
% 3.00/1.00  ------                               Statistics
% 3.00/1.00  
% 3.00/1.00  ------ General
% 3.00/1.00  
% 3.00/1.00  abstr_ref_over_cycles:                  0
% 3.00/1.00  abstr_ref_under_cycles:                 0
% 3.00/1.00  gc_basic_clause_elim:                   0
% 3.00/1.00  forced_gc_time:                         0
% 3.00/1.00  parsing_time:                           0.013
% 3.00/1.00  unif_index_cands_time:                  0.
% 3.00/1.00  unif_index_add_time:                    0.
% 3.00/1.00  orderings_time:                         0.
% 3.00/1.00  out_proof_time:                         0.006
% 3.00/1.00  total_time:                             0.153
% 3.00/1.00  num_of_symbols:                         46
% 3.00/1.00  num_of_terms:                           4012
% 3.00/1.00  
% 3.00/1.00  ------ Preprocessing
% 3.00/1.00  
% 3.00/1.00  num_of_splits:                          0
% 3.00/1.00  num_of_split_atoms:                     0
% 3.00/1.00  num_of_reused_defs:                     0
% 3.00/1.00  num_eq_ax_congr_red:                    19
% 3.00/1.00  num_of_sem_filtered_clauses:            1
% 3.00/1.00  num_of_subtypes:                        0
% 3.00/1.00  monotx_restored_types:                  0
% 3.00/1.00  sat_num_of_epr_types:                   0
% 3.00/1.00  sat_num_of_non_cyclic_types:            0
% 3.00/1.00  sat_guarded_non_collapsed_types:        0
% 3.00/1.00  num_pure_diseq_elim:                    0
% 3.00/1.00  simp_replaced_by:                       0
% 3.00/1.00  res_preprocessed:                       91
% 3.00/1.00  prep_upred:                             0
% 3.00/1.00  prep_unflattend:                        3
% 3.00/1.00  smt_new_axioms:                         0
% 3.00/1.00  pred_elim_cands:                        4
% 3.00/1.00  pred_elim:                              1
% 3.00/1.00  pred_elim_cl:                           0
% 3.00/1.00  pred_elim_cycles:                       2
% 3.00/1.00  merged_defs:                            0
% 3.00/1.00  merged_defs_ncl:                        0
% 3.00/1.00  bin_hyper_res:                          0
% 3.00/1.00  prep_cycles:                            3
% 3.00/1.00  pred_elim_time:                         0.
% 3.00/1.00  splitting_time:                         0.
% 3.00/1.00  sem_filter_time:                        0.
% 3.00/1.00  monotx_time:                            0.
% 3.00/1.00  subtype_inf_time:                       0.
% 3.00/1.00  
% 3.00/1.00  ------ Problem properties
% 3.00/1.00  
% 3.00/1.00  clauses:                                24
% 3.00/1.00  conjectures:                            2
% 3.00/1.00  epr:                                    3
% 3.00/1.00  horn:                                   21
% 3.00/1.00  ground:                                 3
% 3.00/1.00  unary:                                  12
% 3.00/1.00  binary:                                 5
% 3.00/1.00  lits:                                   48
% 3.00/1.00  lits_eq:                                16
% 3.00/1.00  fd_pure:                                0
% 3.00/1.00  fd_pseudo:                              0
% 3.00/1.00  fd_cond:                                0
% 3.00/1.00  fd_pseudo_cond:                         6
% 3.00/1.00  ac_symbols:                             0
% 3.00/1.00  
% 3.00/1.00  ------ Propositional Solver
% 3.00/1.00  
% 3.00/1.00  prop_solver_calls:                      23
% 3.00/1.00  prop_fast_solver_calls:                 564
% 3.00/1.00  smt_solver_calls:                       0
% 3.00/1.00  smt_fast_solver_calls:                  0
% 3.00/1.00  prop_num_of_clauses:                    1764
% 3.00/1.00  prop_preprocess_simplified:             4702
% 3.00/1.00  prop_fo_subsumed:                       11
% 3.00/1.00  prop_solver_time:                       0.
% 3.00/1.00  smt_solver_time:                        0.
% 3.00/1.00  smt_fast_solver_time:                   0.
% 3.00/1.00  prop_fast_solver_time:                  0.
% 3.00/1.00  prop_unsat_core_time:                   0.
% 3.00/1.00  
% 3.00/1.00  ------ QBF
% 3.00/1.00  
% 3.00/1.00  qbf_q_res:                              0
% 3.00/1.00  qbf_num_tautologies:                    0
% 3.00/1.00  qbf_prep_cycles:                        0
% 3.00/1.00  
% 3.00/1.00  ------ BMC1
% 3.00/1.00  
% 3.00/1.00  bmc1_current_bound:                     -1
% 3.00/1.00  bmc1_last_solved_bound:                 -1
% 3.00/1.00  bmc1_unsat_core_size:                   -1
% 3.00/1.00  bmc1_unsat_core_parents_size:           -1
% 3.00/1.00  bmc1_merge_next_fun:                    0
% 3.00/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.00/1.00  
% 3.00/1.00  ------ Instantiation
% 3.00/1.00  
% 3.00/1.00  inst_num_of_clauses:                    476
% 3.00/1.00  inst_num_in_passive:                    58
% 3.00/1.00  inst_num_in_active:                     245
% 3.00/1.00  inst_num_in_unprocessed:                176
% 3.00/1.00  inst_num_of_loops:                      310
% 3.00/1.00  inst_num_of_learning_restarts:          0
% 3.00/1.00  inst_num_moves_active_passive:          63
% 3.00/1.00  inst_lit_activity:                      0
% 3.00/1.00  inst_lit_activity_moves:                0
% 3.00/1.00  inst_num_tautologies:                   0
% 3.00/1.00  inst_num_prop_implied:                  0
% 3.00/1.00  inst_num_existing_simplified:           0
% 3.00/1.00  inst_num_eq_res_simplified:             0
% 3.00/1.00  inst_num_child_elim:                    0
% 3.00/1.00  inst_num_of_dismatching_blockings:      104
% 3.00/1.00  inst_num_of_non_proper_insts:           358
% 3.00/1.00  inst_num_of_duplicates:                 0
% 3.00/1.00  inst_inst_num_from_inst_to_res:         0
% 3.00/1.00  inst_dismatching_checking_time:         0.
% 3.00/1.00  
% 3.00/1.00  ------ Resolution
% 3.00/1.00  
% 3.00/1.00  res_num_of_clauses:                     0
% 3.00/1.00  res_num_in_passive:                     0
% 3.00/1.00  res_num_in_active:                      0
% 3.00/1.00  res_num_of_loops:                       94
% 3.00/1.00  res_forward_subset_subsumed:            43
% 3.00/1.00  res_backward_subset_subsumed:           18
% 3.00/1.00  res_forward_subsumed:                   0
% 3.00/1.00  res_backward_subsumed:                  0
% 3.00/1.00  res_forward_subsumption_resolution:     0
% 3.00/1.00  res_backward_subsumption_resolution:    0
% 3.00/1.00  res_clause_to_clause_subsumption:       760
% 3.00/1.00  res_orphan_elimination:                 0
% 3.00/1.00  res_tautology_del:                      17
% 3.00/1.00  res_num_eq_res_simplified:              0
% 3.00/1.00  res_num_sel_changes:                    0
% 3.00/1.00  res_moves_from_active_to_pass:          0
% 3.00/1.00  
% 3.00/1.00  ------ Superposition
% 3.00/1.00  
% 3.00/1.00  sup_time_total:                         0.
% 3.00/1.00  sup_time_generating:                    0.
% 3.00/1.00  sup_time_sim_full:                      0.
% 3.00/1.00  sup_time_sim_immed:                     0.
% 3.00/1.00  
% 3.00/1.00  sup_num_of_clauses:                     198
% 3.00/1.00  sup_num_in_active:                      61
% 3.00/1.00  sup_num_in_passive:                     137
% 3.00/1.00  sup_num_of_loops:                       61
% 3.00/1.00  sup_fw_superposition:                   88
% 3.00/1.00  sup_bw_superposition:                   161
% 3.00/1.00  sup_immediate_simplified:               17
% 3.00/1.00  sup_given_eliminated:                   0
% 3.00/1.00  comparisons_done:                       0
% 3.00/1.00  comparisons_avoided:                    2
% 3.00/1.00  
% 3.00/1.00  ------ Simplifications
% 3.00/1.00  
% 3.00/1.00  
% 3.00/1.00  sim_fw_subset_subsumed:                 6
% 3.00/1.00  sim_bw_subset_subsumed:                 0
% 3.00/1.00  sim_fw_subsumed:                        12
% 3.00/1.00  sim_bw_subsumed:                        0
% 3.00/1.00  sim_fw_subsumption_res:                 2
% 3.00/1.00  sim_bw_subsumption_res:                 0
% 3.00/1.00  sim_tautology_del:                      11
% 3.00/1.00  sim_eq_tautology_del:                   9
% 3.00/1.00  sim_eq_res_simp:                        2
% 3.00/1.00  sim_fw_demodulated:                     3
% 3.00/1.00  sim_bw_demodulated:                     1
% 3.00/1.00  sim_light_normalised:                   1
% 3.00/1.00  sim_joinable_taut:                      0
% 3.00/1.00  sim_joinable_simp:                      0
% 3.00/1.00  sim_ac_normalised:                      0
% 3.00/1.00  sim_smt_subsumption:                    0
% 3.00/1.00  
%------------------------------------------------------------------------------
