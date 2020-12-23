%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:49:54 EST 2020

% Result     : Theorem 3.83s
% Output     : CNFRefutation 3.83s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 115 expanded)
%              Number of clauses        :   32 (  39 expanded)
%              Number of leaves         :   11 (  24 expanded)
%              Depth                    :   16
%              Number of atoms          :  280 ( 487 expanded)
%              Number of equality atoms :  115 ( 157 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
       => k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
         => k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(X2,X0) != k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)
      & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(X2,X0) != k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)
      & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f25,plain,
    ( ? [X0,X1,X2] :
        ( k1_funct_1(X2,X0) != k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)
        & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k1_funct_1(sK4,sK2) != k1_funct_1(k5_relat_1(k6_relat_1(sK3),sK4),sK2)
      & r2_hidden(sK2,k3_xboole_0(k1_relat_1(sK4),sK3))
      & v1_funct_1(sK4)
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( k1_funct_1(sK4,sK2) != k1_funct_1(k5_relat_1(k6_relat_1(sK3),sK4),sK2)
    & r2_hidden(sK2,k3_xboole_0(k1_relat_1(sK4),sK3))
    & v1_funct_1(sK4)
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f14,f25])).

fof(f43,plain,(
    r2_hidden(sK2,k3_xboole_0(k1_relat_1(sK4),sK3)) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f17,plain,(
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
    inference(rectify,[],[f16])).

fof(f18,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f18])).

fof(f28,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f46,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f28])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X2] :
                ( k1_funct_1(X1,X2) = X2
                | ~ r2_hidden(X2,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X2] :
                ( k1_funct_1(X1,X2) = X2
                | ~ r2_hidden(X2,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f21])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X1,X2) != X2
          & r2_hidden(X2,X0) )
     => ( k1_funct_1(X1,sK1(X0,X1)) != sK1(X0,X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( k1_funct_1(X1,sK1(X0,X1)) != sK1(X0,X1)
            & r2_hidden(sK1(X0,X1),X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f23])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | k6_relat_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f51,plain,(
    ! [X0] :
      ( k1_relat_1(k6_relat_1(X0)) = X0
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f36])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f8])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_funct_1(k6_relat_1(X1),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k6_relat_1(X1),X0) = X0
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k6_relat_1(X1),X0) = X0
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f44,plain,(
    k1_funct_1(sK4,sK2) != k1_funct_1(k5_relat_1(k6_relat_1(sK3),sK4),sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f42,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f26])).

fof(f41,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_15,negated_conjecture,
    ( r2_hidden(sK2,k3_xboole_0(k1_relat_1(sK4),sK3)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_499,plain,
    ( r2_hidden(sK2,k3_xboole_0(k1_relat_1(sK4),sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_507,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_974,plain,
    ( r2_hidden(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_499,c_507])).

cnf(c_12,plain,
    ( ~ v1_relat_1(k6_relat_1(X0))
    | ~ v1_funct_1(k6_relat_1(X0))
    | k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_7,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_6,plain,
    ( v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_130,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12,c_7,c_6])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_503,plain,
    ( k1_funct_1(k5_relat_1(X0,X1),X2) = k1_funct_1(X1,k1_funct_1(X0,X2))
    | r2_hidden(X2,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1892,plain,
    ( k1_funct_1(X0,k1_funct_1(k6_relat_1(X1),X2)) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X0),X2)
    | r2_hidden(X2,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_130,c_503])).

cnf(c_505,plain,
    ( v1_funct_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_504,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_16964,plain,
    ( k1_funct_1(k5_relat_1(k6_relat_1(X0),X1),X2) = k1_funct_1(X1,k1_funct_1(k6_relat_1(X0),X2))
    | r2_hidden(X2,X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1892,c_505,c_504])).

cnf(c_16976,plain,
    ( k1_funct_1(X0,k1_funct_1(k6_relat_1(sK3),sK2)) = k1_funct_1(k5_relat_1(k6_relat_1(sK3),X0),sK2)
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_974,c_16964])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_funct_1(k6_relat_1(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_500,plain,
    ( k1_funct_1(k6_relat_1(X0),X1) = X1
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2170,plain,
    ( k1_funct_1(k6_relat_1(sK3),sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_974,c_500])).

cnf(c_17345,plain,
    ( k1_funct_1(k5_relat_1(k6_relat_1(sK3),X0),sK2) = k1_funct_1(X0,sK2)
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_16976,c_2170])).

cnf(c_17488,plain,
    ( k1_funct_1(k5_relat_1(k6_relat_1(sK3),sK4),sK2) = k1_funct_1(sK4,sK2)
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_17345])).

cnf(c_238,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_739,plain,
    ( k1_funct_1(sK4,sK2) = k1_funct_1(sK4,sK2) ),
    inference(instantiation,[status(thm)],[c_238])).

cnf(c_239,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_658,plain,
    ( k1_funct_1(k5_relat_1(k6_relat_1(sK3),sK4),sK2) != X0
    | k1_funct_1(sK4,sK2) != X0
    | k1_funct_1(sK4,sK2) = k1_funct_1(k5_relat_1(k6_relat_1(sK3),sK4),sK2) ),
    inference(instantiation,[status(thm)],[c_239])).

cnf(c_738,plain,
    ( k1_funct_1(k5_relat_1(k6_relat_1(sK3),sK4),sK2) != k1_funct_1(sK4,sK2)
    | k1_funct_1(sK4,sK2) = k1_funct_1(k5_relat_1(k6_relat_1(sK3),sK4),sK2)
    | k1_funct_1(sK4,sK2) != k1_funct_1(sK4,sK2) ),
    inference(instantiation,[status(thm)],[c_658])).

cnf(c_14,negated_conjecture,
    ( k1_funct_1(sK4,sK2) != k1_funct_1(k5_relat_1(k6_relat_1(sK3),sK4),sK2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_16,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_19,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_17,negated_conjecture,
    ( v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_18,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_17488,c_739,c_738,c_14,c_19,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n025.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:42:50 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.83/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.83/0.98  
% 3.83/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.83/0.98  
% 3.83/0.98  ------  iProver source info
% 3.83/0.98  
% 3.83/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.83/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.83/0.98  git: non_committed_changes: false
% 3.83/0.98  git: last_make_outside_of_git: false
% 3.83/0.98  
% 3.83/0.98  ------ 
% 3.83/0.98  
% 3.83/0.98  ------ Input Options
% 3.83/0.98  
% 3.83/0.98  --out_options                           all
% 3.83/0.98  --tptp_safe_out                         true
% 3.83/0.98  --problem_path                          ""
% 3.83/0.98  --include_path                          ""
% 3.83/0.98  --clausifier                            res/vclausify_rel
% 3.83/0.98  --clausifier_options                    --mode clausify
% 3.83/0.98  --stdin                                 false
% 3.83/0.98  --stats_out                             sel
% 3.83/0.98  
% 3.83/0.98  ------ General Options
% 3.83/0.98  
% 3.83/0.98  --fof                                   false
% 3.83/0.98  --time_out_real                         604.99
% 3.83/0.98  --time_out_virtual                      -1.
% 3.83/0.98  --symbol_type_check                     false
% 3.83/0.98  --clausify_out                          false
% 3.83/0.98  --sig_cnt_out                           false
% 3.83/0.98  --trig_cnt_out                          false
% 3.83/0.98  --trig_cnt_out_tolerance                1.
% 3.83/0.98  --trig_cnt_out_sk_spl                   false
% 3.83/0.98  --abstr_cl_out                          false
% 3.83/0.98  
% 3.83/0.98  ------ Global Options
% 3.83/0.98  
% 3.83/0.98  --schedule                              none
% 3.83/0.98  --add_important_lit                     false
% 3.83/0.98  --prop_solver_per_cl                    1000
% 3.83/0.98  --min_unsat_core                        false
% 3.83/0.98  --soft_assumptions                      false
% 3.83/0.98  --soft_lemma_size                       3
% 3.83/0.98  --prop_impl_unit_size                   0
% 3.83/0.98  --prop_impl_unit                        []
% 3.83/0.98  --share_sel_clauses                     true
% 3.83/0.98  --reset_solvers                         false
% 3.83/0.98  --bc_imp_inh                            [conj_cone]
% 3.83/0.98  --conj_cone_tolerance                   3.
% 3.83/0.98  --extra_neg_conj                        none
% 3.83/0.98  --large_theory_mode                     true
% 3.83/0.98  --prolific_symb_bound                   200
% 3.83/0.98  --lt_threshold                          2000
% 3.83/0.98  --clause_weak_htbl                      true
% 3.83/0.98  --gc_record_bc_elim                     false
% 3.83/0.98  
% 3.83/0.98  ------ Preprocessing Options
% 3.83/0.98  
% 3.83/0.98  --preprocessing_flag                    true
% 3.83/0.98  --time_out_prep_mult                    0.1
% 3.83/0.98  --splitting_mode                        input
% 3.83/0.98  --splitting_grd                         true
% 3.83/0.98  --splitting_cvd                         false
% 3.83/0.98  --splitting_cvd_svl                     false
% 3.83/0.98  --splitting_nvd                         32
% 3.83/0.98  --sub_typing                            true
% 3.83/0.98  --prep_gs_sim                           false
% 3.83/0.98  --prep_unflatten                        true
% 3.83/0.98  --prep_res_sim                          true
% 3.83/0.98  --prep_upred                            true
% 3.83/0.98  --prep_sem_filter                       exhaustive
% 3.83/0.98  --prep_sem_filter_out                   false
% 3.83/0.98  --pred_elim                             false
% 3.83/0.98  --res_sim_input                         true
% 3.83/0.98  --eq_ax_congr_red                       true
% 3.83/0.98  --pure_diseq_elim                       true
% 3.83/0.98  --brand_transform                       false
% 3.83/0.98  --non_eq_to_eq                          false
% 3.83/0.98  --prep_def_merge                        true
% 3.83/0.98  --prep_def_merge_prop_impl              false
% 3.83/0.98  --prep_def_merge_mbd                    true
% 3.83/0.98  --prep_def_merge_tr_red                 false
% 3.83/0.98  --prep_def_merge_tr_cl                  false
% 3.83/0.98  --smt_preprocessing                     true
% 3.83/0.98  --smt_ac_axioms                         fast
% 3.83/0.98  --preprocessed_out                      false
% 3.83/0.98  --preprocessed_stats                    false
% 3.83/0.98  
% 3.83/0.98  ------ Abstraction refinement Options
% 3.83/0.98  
% 3.83/0.98  --abstr_ref                             []
% 3.83/0.98  --abstr_ref_prep                        false
% 3.83/0.98  --abstr_ref_until_sat                   false
% 3.83/0.98  --abstr_ref_sig_restrict                funpre
% 3.83/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.83/0.98  --abstr_ref_under                       []
% 3.83/0.98  
% 3.83/0.98  ------ SAT Options
% 3.83/0.98  
% 3.83/0.98  --sat_mode                              false
% 3.83/0.98  --sat_fm_restart_options                ""
% 3.83/0.98  --sat_gr_def                            false
% 3.83/0.98  --sat_epr_types                         true
% 3.83/0.98  --sat_non_cyclic_types                  false
% 3.83/0.98  --sat_finite_models                     false
% 3.83/0.98  --sat_fm_lemmas                         false
% 3.83/0.98  --sat_fm_prep                           false
% 3.83/0.98  --sat_fm_uc_incr                        true
% 3.83/0.98  --sat_out_model                         small
% 3.83/0.98  --sat_out_clauses                       false
% 3.83/0.98  
% 3.83/0.98  ------ QBF Options
% 3.83/0.98  
% 3.83/0.98  --qbf_mode                              false
% 3.83/0.98  --qbf_elim_univ                         false
% 3.83/0.98  --qbf_dom_inst                          none
% 3.83/0.98  --qbf_dom_pre_inst                      false
% 3.83/0.98  --qbf_sk_in                             false
% 3.83/0.98  --qbf_pred_elim                         true
% 3.83/0.98  --qbf_split                             512
% 3.83/0.98  
% 3.83/0.98  ------ BMC1 Options
% 3.83/0.98  
% 3.83/0.98  --bmc1_incremental                      false
% 3.83/0.98  --bmc1_axioms                           reachable_all
% 3.83/0.98  --bmc1_min_bound                        0
% 3.83/0.98  --bmc1_max_bound                        -1
% 3.83/0.98  --bmc1_max_bound_default                -1
% 3.83/0.98  --bmc1_symbol_reachability              true
% 3.83/0.98  --bmc1_property_lemmas                  false
% 3.83/0.98  --bmc1_k_induction                      false
% 3.83/0.98  --bmc1_non_equiv_states                 false
% 3.83/0.98  --bmc1_deadlock                         false
% 3.83/0.98  --bmc1_ucm                              false
% 3.83/0.98  --bmc1_add_unsat_core                   none
% 3.83/0.98  --bmc1_unsat_core_children              false
% 3.83/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.83/0.98  --bmc1_out_stat                         full
% 3.83/0.98  --bmc1_ground_init                      false
% 3.83/0.98  --bmc1_pre_inst_next_state              false
% 3.83/0.98  --bmc1_pre_inst_state                   false
% 3.83/0.98  --bmc1_pre_inst_reach_state             false
% 3.83/0.98  --bmc1_out_unsat_core                   false
% 3.83/0.98  --bmc1_aig_witness_out                  false
% 3.83/0.98  --bmc1_verbose                          false
% 3.83/0.98  --bmc1_dump_clauses_tptp                false
% 3.83/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.83/0.98  --bmc1_dump_file                        -
% 3.83/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.83/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.83/0.98  --bmc1_ucm_extend_mode                  1
% 3.83/0.98  --bmc1_ucm_init_mode                    2
% 3.83/0.98  --bmc1_ucm_cone_mode                    none
% 3.83/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.83/0.98  --bmc1_ucm_relax_model                  4
% 3.83/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.83/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.83/0.98  --bmc1_ucm_layered_model                none
% 3.83/0.98  --bmc1_ucm_max_lemma_size               10
% 3.83/0.98  
% 3.83/0.98  ------ AIG Options
% 3.83/0.98  
% 3.83/0.98  --aig_mode                              false
% 3.83/0.98  
% 3.83/0.98  ------ Instantiation Options
% 3.83/0.98  
% 3.83/0.98  --instantiation_flag                    true
% 3.83/0.98  --inst_sos_flag                         false
% 3.83/0.98  --inst_sos_phase                        true
% 3.83/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.83/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.83/0.98  --inst_lit_sel_side                     num_symb
% 3.83/0.98  --inst_solver_per_active                1400
% 3.83/0.98  --inst_solver_calls_frac                1.
% 3.83/0.98  --inst_passive_queue_type               priority_queues
% 3.83/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.83/0.98  --inst_passive_queues_freq              [25;2]
% 3.83/0.98  --inst_dismatching                      true
% 3.83/0.98  --inst_eager_unprocessed_to_passive     true
% 3.83/0.98  --inst_prop_sim_given                   true
% 3.83/0.98  --inst_prop_sim_new                     false
% 3.83/0.98  --inst_subs_new                         false
% 3.83/0.98  --inst_eq_res_simp                      false
% 3.83/0.98  --inst_subs_given                       false
% 3.83/0.98  --inst_orphan_elimination               true
% 3.83/0.98  --inst_learning_loop_flag               true
% 3.83/0.98  --inst_learning_start                   3000
% 3.83/0.98  --inst_learning_factor                  2
% 3.83/0.98  --inst_start_prop_sim_after_learn       3
% 3.83/0.98  --inst_sel_renew                        solver
% 3.83/0.98  --inst_lit_activity_flag                true
% 3.83/0.98  --inst_restr_to_given                   false
% 3.83/0.98  --inst_activity_threshold               500
% 3.83/0.98  --inst_out_proof                        true
% 3.83/0.98  
% 3.83/0.98  ------ Resolution Options
% 3.83/0.98  
% 3.83/0.98  --resolution_flag                       true
% 3.83/0.98  --res_lit_sel                           adaptive
% 3.83/0.98  --res_lit_sel_side                      none
% 3.83/0.98  --res_ordering                          kbo
% 3.83/0.98  --res_to_prop_solver                    active
% 3.83/0.98  --res_prop_simpl_new                    false
% 3.83/0.98  --res_prop_simpl_given                  true
% 3.83/0.98  --res_passive_queue_type                priority_queues
% 3.83/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.83/0.98  --res_passive_queues_freq               [15;5]
% 3.83/0.98  --res_forward_subs                      full
% 3.83/0.98  --res_backward_subs                     full
% 3.83/0.98  --res_forward_subs_resolution           true
% 3.83/0.98  --res_backward_subs_resolution          true
% 3.83/0.98  --res_orphan_elimination                true
% 3.83/0.98  --res_time_limit                        2.
% 3.83/0.98  --res_out_proof                         true
% 3.83/0.98  
% 3.83/0.98  ------ Superposition Options
% 3.83/0.98  
% 3.83/0.98  --superposition_flag                    true
% 3.83/0.98  --sup_passive_queue_type                priority_queues
% 3.83/0.98  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.83/0.98  --sup_passive_queues_freq               [1;4]
% 3.83/0.98  --demod_completeness_check              fast
% 3.83/0.98  --demod_use_ground                      true
% 3.83/0.98  --sup_to_prop_solver                    passive
% 3.83/0.98  --sup_prop_simpl_new                    true
% 3.83/0.98  --sup_prop_simpl_given                  true
% 3.83/0.98  --sup_fun_splitting                     false
% 3.83/0.98  --sup_smt_interval                      50000
% 3.83/0.98  
% 3.83/0.98  ------ Superposition Simplification Setup
% 3.83/0.98  
% 3.83/0.98  --sup_indices_passive                   []
% 3.83/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.83/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.83/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.83/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.83/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.83/0.98  --sup_full_bw                           [BwDemod]
% 3.83/0.98  --sup_immed_triv                        [TrivRules]
% 3.83/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.83/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.83/0.98  --sup_immed_bw_main                     []
% 3.83/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.83/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.83/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.83/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.83/0.98  
% 3.83/0.98  ------ Combination Options
% 3.83/0.98  
% 3.83/0.98  --comb_res_mult                         3
% 3.83/0.98  --comb_sup_mult                         2
% 3.83/0.98  --comb_inst_mult                        10
% 3.83/0.98  
% 3.83/0.98  ------ Debug Options
% 3.83/0.98  
% 3.83/0.98  --dbg_backtrace                         false
% 3.83/0.98  --dbg_dump_prop_clauses                 false
% 3.83/0.98  --dbg_dump_prop_clauses_file            -
% 3.83/0.98  --dbg_out_stat                          false
% 3.83/0.98  ------ Parsing...
% 3.83/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.83/0.98  
% 3.83/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.83/0.98  
% 3.83/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.83/0.98  
% 3.83/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.83/0.98  ------ Proving...
% 3.83/0.98  ------ Problem Properties 
% 3.83/0.98  
% 3.83/0.98  
% 3.83/0.98  clauses                                 17
% 3.83/0.98  conjectures                             4
% 3.83/0.98  EPR                                     2
% 3.83/0.98  Horn                                    14
% 3.83/0.98  unary                                   7
% 3.83/0.98  binary                                  3
% 3.83/0.98  lits                                    40
% 3.83/0.98  lits eq                                 10
% 3.83/0.98  fd_pure                                 0
% 3.83/0.98  fd_pseudo                               0
% 3.83/0.98  fd_cond                                 0
% 3.83/0.98  fd_pseudo_cond                          3
% 3.83/0.98  AC symbols                              0
% 3.83/0.98  
% 3.83/0.98  ------ Input Options Time Limit: Unbounded
% 3.83/0.98  
% 3.83/0.98  
% 3.83/0.98  ------ 
% 3.83/0.98  Current options:
% 3.83/0.98  ------ 
% 3.83/0.98  
% 3.83/0.98  ------ Input Options
% 3.83/0.98  
% 3.83/0.98  --out_options                           all
% 3.83/0.98  --tptp_safe_out                         true
% 3.83/0.98  --problem_path                          ""
% 3.83/0.98  --include_path                          ""
% 3.83/0.98  --clausifier                            res/vclausify_rel
% 3.83/0.98  --clausifier_options                    --mode clausify
% 3.83/0.98  --stdin                                 false
% 3.83/0.98  --stats_out                             sel
% 3.83/0.98  
% 3.83/0.98  ------ General Options
% 3.83/0.98  
% 3.83/0.98  --fof                                   false
% 3.83/0.98  --time_out_real                         604.99
% 3.83/0.98  --time_out_virtual                      -1.
% 3.83/0.98  --symbol_type_check                     false
% 3.83/0.98  --clausify_out                          false
% 3.83/0.98  --sig_cnt_out                           false
% 3.83/0.98  --trig_cnt_out                          false
% 3.83/0.98  --trig_cnt_out_tolerance                1.
% 3.83/0.98  --trig_cnt_out_sk_spl                   false
% 3.83/0.98  --abstr_cl_out                          false
% 3.83/0.98  
% 3.83/0.98  ------ Global Options
% 3.83/0.98  
% 3.83/0.98  --schedule                              none
% 3.83/0.98  --add_important_lit                     false
% 3.83/0.98  --prop_solver_per_cl                    1000
% 3.83/0.98  --min_unsat_core                        false
% 3.83/0.98  --soft_assumptions                      false
% 3.83/0.98  --soft_lemma_size                       3
% 3.83/0.98  --prop_impl_unit_size                   0
% 3.83/0.98  --prop_impl_unit                        []
% 3.83/0.98  --share_sel_clauses                     true
% 3.83/0.98  --reset_solvers                         false
% 3.83/0.98  --bc_imp_inh                            [conj_cone]
% 3.83/0.98  --conj_cone_tolerance                   3.
% 3.83/0.98  --extra_neg_conj                        none
% 3.83/0.98  --large_theory_mode                     true
% 3.83/0.98  --prolific_symb_bound                   200
% 3.83/0.98  --lt_threshold                          2000
% 3.83/0.98  --clause_weak_htbl                      true
% 3.83/0.98  --gc_record_bc_elim                     false
% 3.83/0.98  
% 3.83/0.98  ------ Preprocessing Options
% 3.83/0.98  
% 3.83/0.98  --preprocessing_flag                    true
% 3.83/0.98  --time_out_prep_mult                    0.1
% 3.83/0.98  --splitting_mode                        input
% 3.83/0.98  --splitting_grd                         true
% 3.83/0.98  --splitting_cvd                         false
% 3.83/0.98  --splitting_cvd_svl                     false
% 3.83/0.98  --splitting_nvd                         32
% 3.83/0.98  --sub_typing                            true
% 3.83/0.98  --prep_gs_sim                           false
% 3.83/0.98  --prep_unflatten                        true
% 3.83/0.98  --prep_res_sim                          true
% 3.83/0.98  --prep_upred                            true
% 3.83/0.98  --prep_sem_filter                       exhaustive
% 3.83/0.98  --prep_sem_filter_out                   false
% 3.83/0.98  --pred_elim                             false
% 3.83/0.98  --res_sim_input                         true
% 3.83/0.98  --eq_ax_congr_red                       true
% 3.83/0.98  --pure_diseq_elim                       true
% 3.83/0.98  --brand_transform                       false
% 3.83/0.98  --non_eq_to_eq                          false
% 3.83/0.98  --prep_def_merge                        true
% 3.83/0.98  --prep_def_merge_prop_impl              false
% 3.83/0.98  --prep_def_merge_mbd                    true
% 3.83/0.98  --prep_def_merge_tr_red                 false
% 3.83/0.98  --prep_def_merge_tr_cl                  false
% 3.83/0.98  --smt_preprocessing                     true
% 3.83/0.98  --smt_ac_axioms                         fast
% 3.83/0.98  --preprocessed_out                      false
% 3.83/0.98  --preprocessed_stats                    false
% 3.83/0.98  
% 3.83/0.98  ------ Abstraction refinement Options
% 3.83/0.98  
% 3.83/0.98  --abstr_ref                             []
% 3.83/0.98  --abstr_ref_prep                        false
% 3.83/0.98  --abstr_ref_until_sat                   false
% 3.83/0.98  --abstr_ref_sig_restrict                funpre
% 3.83/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.83/0.98  --abstr_ref_under                       []
% 3.83/0.98  
% 3.83/0.98  ------ SAT Options
% 3.83/0.98  
% 3.83/0.98  --sat_mode                              false
% 3.83/0.98  --sat_fm_restart_options                ""
% 3.83/0.98  --sat_gr_def                            false
% 3.83/0.98  --sat_epr_types                         true
% 3.83/0.98  --sat_non_cyclic_types                  false
% 3.83/0.98  --sat_finite_models                     false
% 3.83/0.98  --sat_fm_lemmas                         false
% 3.83/0.98  --sat_fm_prep                           false
% 3.83/0.98  --sat_fm_uc_incr                        true
% 3.83/0.98  --sat_out_model                         small
% 3.83/0.98  --sat_out_clauses                       false
% 3.83/0.98  
% 3.83/0.98  ------ QBF Options
% 3.83/0.98  
% 3.83/0.98  --qbf_mode                              false
% 3.83/0.98  --qbf_elim_univ                         false
% 3.83/0.98  --qbf_dom_inst                          none
% 3.83/0.98  --qbf_dom_pre_inst                      false
% 3.83/0.98  --qbf_sk_in                             false
% 3.83/0.98  --qbf_pred_elim                         true
% 3.83/0.98  --qbf_split                             512
% 3.83/0.98  
% 3.83/0.98  ------ BMC1 Options
% 3.83/0.98  
% 3.83/0.98  --bmc1_incremental                      false
% 3.83/0.98  --bmc1_axioms                           reachable_all
% 3.83/0.98  --bmc1_min_bound                        0
% 3.83/0.98  --bmc1_max_bound                        -1
% 3.83/0.98  --bmc1_max_bound_default                -1
% 3.83/0.98  --bmc1_symbol_reachability              true
% 3.83/0.98  --bmc1_property_lemmas                  false
% 3.83/0.98  --bmc1_k_induction                      false
% 3.83/0.98  --bmc1_non_equiv_states                 false
% 3.83/0.98  --bmc1_deadlock                         false
% 3.83/0.98  --bmc1_ucm                              false
% 3.83/0.98  --bmc1_add_unsat_core                   none
% 3.83/0.98  --bmc1_unsat_core_children              false
% 3.83/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.83/0.98  --bmc1_out_stat                         full
% 3.83/0.98  --bmc1_ground_init                      false
% 3.83/0.98  --bmc1_pre_inst_next_state              false
% 3.83/0.98  --bmc1_pre_inst_state                   false
% 3.83/0.98  --bmc1_pre_inst_reach_state             false
% 3.83/0.98  --bmc1_out_unsat_core                   false
% 3.83/0.98  --bmc1_aig_witness_out                  false
% 3.83/0.98  --bmc1_verbose                          false
% 3.83/0.98  --bmc1_dump_clauses_tptp                false
% 3.83/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.83/0.98  --bmc1_dump_file                        -
% 3.83/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.83/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.83/0.98  --bmc1_ucm_extend_mode                  1
% 3.83/0.98  --bmc1_ucm_init_mode                    2
% 3.83/0.98  --bmc1_ucm_cone_mode                    none
% 3.83/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.83/0.98  --bmc1_ucm_relax_model                  4
% 3.83/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.83/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.83/0.98  --bmc1_ucm_layered_model                none
% 3.83/0.98  --bmc1_ucm_max_lemma_size               10
% 3.83/0.98  
% 3.83/0.98  ------ AIG Options
% 3.83/0.98  
% 3.83/0.98  --aig_mode                              false
% 3.83/0.98  
% 3.83/0.98  ------ Instantiation Options
% 3.83/0.98  
% 3.83/0.98  --instantiation_flag                    true
% 3.83/0.98  --inst_sos_flag                         false
% 3.83/0.98  --inst_sos_phase                        true
% 3.83/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.83/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.83/0.98  --inst_lit_sel_side                     num_symb
% 3.83/0.98  --inst_solver_per_active                1400
% 3.83/0.98  --inst_solver_calls_frac                1.
% 3.83/0.98  --inst_passive_queue_type               priority_queues
% 3.83/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.83/0.98  --inst_passive_queues_freq              [25;2]
% 3.83/0.98  --inst_dismatching                      true
% 3.83/0.98  --inst_eager_unprocessed_to_passive     true
% 3.83/0.98  --inst_prop_sim_given                   true
% 3.83/0.98  --inst_prop_sim_new                     false
% 3.83/0.98  --inst_subs_new                         false
% 3.83/0.98  --inst_eq_res_simp                      false
% 3.83/0.98  --inst_subs_given                       false
% 3.83/0.98  --inst_orphan_elimination               true
% 3.83/0.98  --inst_learning_loop_flag               true
% 3.83/0.98  --inst_learning_start                   3000
% 3.83/0.98  --inst_learning_factor                  2
% 3.83/0.98  --inst_start_prop_sim_after_learn       3
% 3.83/0.98  --inst_sel_renew                        solver
% 3.83/0.98  --inst_lit_activity_flag                true
% 3.83/0.98  --inst_restr_to_given                   false
% 3.83/0.98  --inst_activity_threshold               500
% 3.83/0.98  --inst_out_proof                        true
% 3.83/0.98  
% 3.83/0.98  ------ Resolution Options
% 3.83/0.98  
% 3.83/0.98  --resolution_flag                       true
% 3.83/0.98  --res_lit_sel                           adaptive
% 3.83/0.98  --res_lit_sel_side                      none
% 3.83/0.98  --res_ordering                          kbo
% 3.83/0.98  --res_to_prop_solver                    active
% 3.83/0.98  --res_prop_simpl_new                    false
% 3.83/0.98  --res_prop_simpl_given                  true
% 3.83/0.98  --res_passive_queue_type                priority_queues
% 3.83/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.83/0.98  --res_passive_queues_freq               [15;5]
% 3.83/0.98  --res_forward_subs                      full
% 3.83/0.98  --res_backward_subs                     full
% 3.83/0.98  --res_forward_subs_resolution           true
% 3.83/0.98  --res_backward_subs_resolution          true
% 3.83/0.98  --res_orphan_elimination                true
% 3.83/0.98  --res_time_limit                        2.
% 3.83/0.98  --res_out_proof                         true
% 3.83/0.98  
% 3.83/0.98  ------ Superposition Options
% 3.83/0.98  
% 3.83/0.98  --superposition_flag                    true
% 3.83/0.98  --sup_passive_queue_type                priority_queues
% 3.83/0.98  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.83/0.98  --sup_passive_queues_freq               [1;4]
% 3.83/0.98  --demod_completeness_check              fast
% 3.83/0.98  --demod_use_ground                      true
% 3.83/0.98  --sup_to_prop_solver                    passive
% 3.83/0.98  --sup_prop_simpl_new                    true
% 3.83/0.98  --sup_prop_simpl_given                  true
% 3.83/0.98  --sup_fun_splitting                     false
% 3.83/0.98  --sup_smt_interval                      50000
% 3.83/0.98  
% 3.83/0.98  ------ Superposition Simplification Setup
% 3.83/0.98  
% 3.83/0.98  --sup_indices_passive                   []
% 3.83/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.83/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.83/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.83/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.83/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.83/0.98  --sup_full_bw                           [BwDemod]
% 3.83/0.98  --sup_immed_triv                        [TrivRules]
% 3.83/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.83/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.83/0.98  --sup_immed_bw_main                     []
% 3.83/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.83/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.83/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.83/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.83/0.98  
% 3.83/0.98  ------ Combination Options
% 3.83/0.98  
% 3.83/0.98  --comb_res_mult                         3
% 3.83/0.98  --comb_sup_mult                         2
% 3.83/0.98  --comb_inst_mult                        10
% 3.83/0.98  
% 3.83/0.98  ------ Debug Options
% 3.83/0.98  
% 3.83/0.98  --dbg_backtrace                         false
% 3.83/0.98  --dbg_dump_prop_clauses                 false
% 3.83/0.98  --dbg_dump_prop_clauses_file            -
% 3.83/0.98  --dbg_out_stat                          false
% 3.83/0.98  
% 3.83/0.98  
% 3.83/0.98  
% 3.83/0.98  
% 3.83/0.98  ------ Proving...
% 3.83/0.98  
% 3.83/0.98  
% 3.83/0.98  % SZS status Theorem for theBenchmark.p
% 3.83/0.98  
% 3.83/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.83/0.98  
% 3.83/0.98  fof(f6,conjecture,(
% 3.83/0.98    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) => k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)))),
% 3.83/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.98  
% 3.83/0.98  fof(f7,negated_conjecture,(
% 3.83/0.98    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) => k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)))),
% 3.83/0.98    inference(negated_conjecture,[],[f6])).
% 3.83/0.98  
% 3.83/0.98  fof(f13,plain,(
% 3.83/0.98    ? [X0,X1,X2] : ((k1_funct_1(X2,X0) != k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 3.83/0.98    inference(ennf_transformation,[],[f7])).
% 3.83/0.98  
% 3.83/0.98  fof(f14,plain,(
% 3.83/0.98    ? [X0,X1,X2] : (k1_funct_1(X2,X0) != k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 3.83/0.98    inference(flattening,[],[f13])).
% 3.83/0.98  
% 3.83/0.98  fof(f25,plain,(
% 3.83/0.98    ? [X0,X1,X2] : (k1_funct_1(X2,X0) != k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (k1_funct_1(sK4,sK2) != k1_funct_1(k5_relat_1(k6_relat_1(sK3),sK4),sK2) & r2_hidden(sK2,k3_xboole_0(k1_relat_1(sK4),sK3)) & v1_funct_1(sK4) & v1_relat_1(sK4))),
% 3.83/0.98    introduced(choice_axiom,[])).
% 3.83/0.98  
% 3.83/0.98  fof(f26,plain,(
% 3.83/0.98    k1_funct_1(sK4,sK2) != k1_funct_1(k5_relat_1(k6_relat_1(sK3),sK4),sK2) & r2_hidden(sK2,k3_xboole_0(k1_relat_1(sK4),sK3)) & v1_funct_1(sK4) & v1_relat_1(sK4)),
% 3.83/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f14,f25])).
% 3.83/0.98  
% 3.83/0.98  fof(f43,plain,(
% 3.83/0.98    r2_hidden(sK2,k3_xboole_0(k1_relat_1(sK4),sK3))),
% 3.83/0.98    inference(cnf_transformation,[],[f26])).
% 3.83/0.98  
% 3.83/0.98  fof(f1,axiom,(
% 3.83/0.98    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.83/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.98  
% 3.83/0.98  fof(f15,plain,(
% 3.83/0.98    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.83/0.98    inference(nnf_transformation,[],[f1])).
% 3.83/0.98  
% 3.83/0.98  fof(f16,plain,(
% 3.83/0.98    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.83/0.98    inference(flattening,[],[f15])).
% 3.83/0.98  
% 3.83/0.98  fof(f17,plain,(
% 3.83/0.98    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.83/0.98    inference(rectify,[],[f16])).
% 3.83/0.98  
% 3.83/0.98  fof(f18,plain,(
% 3.83/0.98    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.83/0.98    introduced(choice_axiom,[])).
% 3.83/0.98  
% 3.83/0.98  fof(f19,plain,(
% 3.83/0.98    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.83/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f18])).
% 3.83/0.98  
% 3.83/0.98  fof(f28,plain,(
% 3.83/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 3.83/0.98    inference(cnf_transformation,[],[f19])).
% 3.83/0.98  
% 3.83/0.98  fof(f46,plain,(
% 3.83/0.98    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 3.83/0.98    inference(equality_resolution,[],[f28])).
% 3.83/0.98  
% 3.83/0.98  fof(f4,axiom,(
% 3.83/0.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(X0) = X1 <=> (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = X2) & k1_relat_1(X1) = X0)))),
% 3.83/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.98  
% 3.83/0.98  fof(f10,plain,(
% 3.83/0.98    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.83/0.98    inference(ennf_transformation,[],[f4])).
% 3.83/0.98  
% 3.83/0.98  fof(f11,plain,(
% 3.83/0.98    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.83/0.98    inference(flattening,[],[f10])).
% 3.83/0.98  
% 3.83/0.98  fof(f20,plain,(
% 3.83/0.98    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0)) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.83/0.98    inference(nnf_transformation,[],[f11])).
% 3.83/0.98  
% 3.83/0.98  fof(f21,plain,(
% 3.83/0.98    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.83/0.98    inference(flattening,[],[f20])).
% 3.83/0.98  
% 3.83/0.98  fof(f22,plain,(
% 3.83/0.98    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.83/0.98    inference(rectify,[],[f21])).
% 3.83/0.98  
% 3.83/0.98  fof(f23,plain,(
% 3.83/0.98    ! [X1,X0] : (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) => (k1_funct_1(X1,sK1(X0,X1)) != sK1(X0,X1) & r2_hidden(sK1(X0,X1),X0)))),
% 3.83/0.98    introduced(choice_axiom,[])).
% 3.83/0.98  
% 3.83/0.98  fof(f24,plain,(
% 3.83/0.98    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (k1_funct_1(X1,sK1(X0,X1)) != sK1(X0,X1) & r2_hidden(sK1(X0,X1),X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.83/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f23])).
% 3.83/0.98  
% 3.83/0.98  fof(f36,plain,(
% 3.83/0.98    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | k6_relat_1(X0) != X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.83/0.98    inference(cnf_transformation,[],[f24])).
% 3.83/0.98  
% 3.83/0.98  fof(f51,plain,(
% 3.83/0.98    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0 | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 3.83/0.98    inference(equality_resolution,[],[f36])).
% 3.83/0.98  
% 3.83/0.98  fof(f2,axiom,(
% 3.83/0.98    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.83/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.98  
% 3.83/0.98  fof(f33,plain,(
% 3.83/0.98    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 3.83/0.98    inference(cnf_transformation,[],[f2])).
% 3.83/0.98  
% 3.83/0.98  fof(f34,plain,(
% 3.83/0.98    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 3.83/0.98    inference(cnf_transformation,[],[f2])).
% 3.83/0.98  
% 3.83/0.98  fof(f3,axiom,(
% 3.83/0.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0))))),
% 3.83/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.98  
% 3.83/0.98  fof(f8,plain,(
% 3.83/0.98    ! [X0,X1] : (! [X2] : ((k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.83/0.98    inference(ennf_transformation,[],[f3])).
% 3.83/0.98  
% 3.83/0.98  fof(f9,plain,(
% 3.83/0.98    ! [X0,X1] : (! [X2] : (k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.83/0.98    inference(flattening,[],[f8])).
% 3.83/0.98  
% 3.83/0.98  fof(f35,plain,(
% 3.83/0.98    ( ! [X2,X0,X1] : (k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.83/0.98    inference(cnf_transformation,[],[f9])).
% 3.83/0.98  
% 3.83/0.98  fof(f5,axiom,(
% 3.83/0.98    ! [X0,X1] : (r2_hidden(X0,X1) => k1_funct_1(k6_relat_1(X1),X0) = X0)),
% 3.83/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.98  
% 3.83/0.98  fof(f12,plain,(
% 3.83/0.98    ! [X0,X1] : (k1_funct_1(k6_relat_1(X1),X0) = X0 | ~r2_hidden(X0,X1))),
% 3.83/0.98    inference(ennf_transformation,[],[f5])).
% 3.83/0.98  
% 3.83/0.98  fof(f40,plain,(
% 3.83/0.98    ( ! [X0,X1] : (k1_funct_1(k6_relat_1(X1),X0) = X0 | ~r2_hidden(X0,X1)) )),
% 3.83/0.98    inference(cnf_transformation,[],[f12])).
% 3.83/0.98  
% 3.83/0.98  fof(f44,plain,(
% 3.83/0.98    k1_funct_1(sK4,sK2) != k1_funct_1(k5_relat_1(k6_relat_1(sK3),sK4),sK2)),
% 3.83/0.98    inference(cnf_transformation,[],[f26])).
% 3.83/0.98  
% 3.83/0.98  fof(f42,plain,(
% 3.83/0.98    v1_funct_1(sK4)),
% 3.83/0.98    inference(cnf_transformation,[],[f26])).
% 3.83/0.98  
% 3.83/0.98  fof(f41,plain,(
% 3.83/0.98    v1_relat_1(sK4)),
% 3.83/0.98    inference(cnf_transformation,[],[f26])).
% 3.83/0.98  
% 3.83/0.98  cnf(c_15,negated_conjecture,
% 3.83/0.98      ( r2_hidden(sK2,k3_xboole_0(k1_relat_1(sK4),sK3)) ),
% 3.83/0.98      inference(cnf_transformation,[],[f43]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_499,plain,
% 3.83/0.98      ( r2_hidden(sK2,k3_xboole_0(k1_relat_1(sK4),sK3)) = iProver_top ),
% 3.83/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_4,plain,
% 3.83/0.98      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
% 3.83/0.98      inference(cnf_transformation,[],[f46]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_507,plain,
% 3.83/0.98      ( r2_hidden(X0,X1) = iProver_top
% 3.83/0.98      | r2_hidden(X0,k3_xboole_0(X2,X1)) != iProver_top ),
% 3.83/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_974,plain,
% 3.83/0.98      ( r2_hidden(sK2,sK3) = iProver_top ),
% 3.83/0.98      inference(superposition,[status(thm)],[c_499,c_507]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_12,plain,
% 3.83/0.98      ( ~ v1_relat_1(k6_relat_1(X0))
% 3.83/0.98      | ~ v1_funct_1(k6_relat_1(X0))
% 3.83/0.98      | k1_relat_1(k6_relat_1(X0)) = X0 ),
% 3.83/0.98      inference(cnf_transformation,[],[f51]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_7,plain,
% 3.83/0.98      ( v1_relat_1(k6_relat_1(X0)) ),
% 3.83/0.98      inference(cnf_transformation,[],[f33]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_6,plain,
% 3.83/0.98      ( v1_funct_1(k6_relat_1(X0)) ),
% 3.83/0.98      inference(cnf_transformation,[],[f34]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_130,plain,
% 3.83/0.98      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 3.83/0.98      inference(global_propositional_subsumption,
% 3.83/0.98                [status(thm)],
% 3.83/0.98                [c_12,c_7,c_6]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_8,plain,
% 3.83/0.98      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.83/0.98      | ~ v1_relat_1(X2)
% 3.83/0.98      | ~ v1_relat_1(X1)
% 3.83/0.98      | ~ v1_funct_1(X2)
% 3.83/0.98      | ~ v1_funct_1(X1)
% 3.83/0.98      | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ),
% 3.83/0.98      inference(cnf_transformation,[],[f35]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_503,plain,
% 3.83/0.98      ( k1_funct_1(k5_relat_1(X0,X1),X2) = k1_funct_1(X1,k1_funct_1(X0,X2))
% 3.83/0.98      | r2_hidden(X2,k1_relat_1(X0)) != iProver_top
% 3.83/0.98      | v1_relat_1(X1) != iProver_top
% 3.83/0.98      | v1_relat_1(X0) != iProver_top
% 3.83/0.98      | v1_funct_1(X1) != iProver_top
% 3.83/0.98      | v1_funct_1(X0) != iProver_top ),
% 3.83/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_1892,plain,
% 3.83/0.98      ( k1_funct_1(X0,k1_funct_1(k6_relat_1(X1),X2)) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X0),X2)
% 3.83/0.98      | r2_hidden(X2,X1) != iProver_top
% 3.83/0.98      | v1_relat_1(X0) != iProver_top
% 3.83/0.98      | v1_relat_1(k6_relat_1(X1)) != iProver_top
% 3.83/0.98      | v1_funct_1(X0) != iProver_top
% 3.83/0.98      | v1_funct_1(k6_relat_1(X1)) != iProver_top ),
% 3.83/0.98      inference(superposition,[status(thm)],[c_130,c_503]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_505,plain,
% 3.83/0.98      ( v1_funct_1(k6_relat_1(X0)) = iProver_top ),
% 3.83/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_504,plain,
% 3.83/0.98      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 3.83/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_16964,plain,
% 3.83/0.98      ( k1_funct_1(k5_relat_1(k6_relat_1(X0),X1),X2) = k1_funct_1(X1,k1_funct_1(k6_relat_1(X0),X2))
% 3.83/0.98      | r2_hidden(X2,X0) != iProver_top
% 3.83/0.98      | v1_relat_1(X1) != iProver_top
% 3.83/0.98      | v1_funct_1(X1) != iProver_top ),
% 3.83/0.98      inference(forward_subsumption_resolution,
% 3.83/0.98                [status(thm)],
% 3.83/0.98                [c_1892,c_505,c_504]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_16976,plain,
% 3.83/0.98      ( k1_funct_1(X0,k1_funct_1(k6_relat_1(sK3),sK2)) = k1_funct_1(k5_relat_1(k6_relat_1(sK3),X0),sK2)
% 3.83/0.98      | v1_relat_1(X0) != iProver_top
% 3.83/0.98      | v1_funct_1(X0) != iProver_top ),
% 3.83/0.98      inference(superposition,[status(thm)],[c_974,c_16964]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_13,plain,
% 3.83/0.98      ( ~ r2_hidden(X0,X1) | k1_funct_1(k6_relat_1(X1),X0) = X0 ),
% 3.83/0.98      inference(cnf_transformation,[],[f40]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_500,plain,
% 3.83/0.98      ( k1_funct_1(k6_relat_1(X0),X1) = X1
% 3.83/0.98      | r2_hidden(X1,X0) != iProver_top ),
% 3.83/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_2170,plain,
% 3.83/0.98      ( k1_funct_1(k6_relat_1(sK3),sK2) = sK2 ),
% 3.83/0.98      inference(superposition,[status(thm)],[c_974,c_500]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_17345,plain,
% 3.83/0.98      ( k1_funct_1(k5_relat_1(k6_relat_1(sK3),X0),sK2) = k1_funct_1(X0,sK2)
% 3.83/0.98      | v1_relat_1(X0) != iProver_top
% 3.83/0.98      | v1_funct_1(X0) != iProver_top ),
% 3.83/0.98      inference(light_normalisation,[status(thm)],[c_16976,c_2170]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_17488,plain,
% 3.83/0.98      ( k1_funct_1(k5_relat_1(k6_relat_1(sK3),sK4),sK2) = k1_funct_1(sK4,sK2)
% 3.83/0.98      | v1_relat_1(sK4) != iProver_top
% 3.83/0.98      | v1_funct_1(sK4) != iProver_top ),
% 3.83/0.98      inference(instantiation,[status(thm)],[c_17345]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_238,plain,( X0 = X0 ),theory(equality) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_739,plain,
% 3.83/0.98      ( k1_funct_1(sK4,sK2) = k1_funct_1(sK4,sK2) ),
% 3.83/0.98      inference(instantiation,[status(thm)],[c_238]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_239,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_658,plain,
% 3.83/0.98      ( k1_funct_1(k5_relat_1(k6_relat_1(sK3),sK4),sK2) != X0
% 3.83/0.98      | k1_funct_1(sK4,sK2) != X0
% 3.83/0.98      | k1_funct_1(sK4,sK2) = k1_funct_1(k5_relat_1(k6_relat_1(sK3),sK4),sK2) ),
% 3.83/0.98      inference(instantiation,[status(thm)],[c_239]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_738,plain,
% 3.83/0.98      ( k1_funct_1(k5_relat_1(k6_relat_1(sK3),sK4),sK2) != k1_funct_1(sK4,sK2)
% 3.83/0.98      | k1_funct_1(sK4,sK2) = k1_funct_1(k5_relat_1(k6_relat_1(sK3),sK4),sK2)
% 3.83/0.98      | k1_funct_1(sK4,sK2) != k1_funct_1(sK4,sK2) ),
% 3.83/0.98      inference(instantiation,[status(thm)],[c_658]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_14,negated_conjecture,
% 3.83/0.98      ( k1_funct_1(sK4,sK2) != k1_funct_1(k5_relat_1(k6_relat_1(sK3),sK4),sK2) ),
% 3.83/0.98      inference(cnf_transformation,[],[f44]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_16,negated_conjecture,
% 3.83/0.98      ( v1_funct_1(sK4) ),
% 3.83/0.98      inference(cnf_transformation,[],[f42]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_19,plain,
% 3.83/0.98      ( v1_funct_1(sK4) = iProver_top ),
% 3.83/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_17,negated_conjecture,
% 3.83/0.98      ( v1_relat_1(sK4) ),
% 3.83/0.98      inference(cnf_transformation,[],[f41]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_18,plain,
% 3.83/0.98      ( v1_relat_1(sK4) = iProver_top ),
% 3.83/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(contradiction,plain,
% 3.83/0.98      ( $false ),
% 3.83/0.98      inference(minisat,
% 3.83/0.98                [status(thm)],
% 3.83/0.98                [c_17488,c_739,c_738,c_14,c_19,c_18]) ).
% 3.83/0.98  
% 3.83/0.98  
% 3.83/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.83/0.98  
% 3.83/0.98  ------                               Statistics
% 3.83/0.98  
% 3.83/0.98  ------ Selected
% 3.83/0.98  
% 3.83/0.98  total_time:                             0.475
% 3.83/0.98  
%------------------------------------------------------------------------------
