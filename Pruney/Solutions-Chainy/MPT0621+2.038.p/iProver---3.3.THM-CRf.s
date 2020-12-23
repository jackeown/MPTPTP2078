%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:49:27 EST 2020

% Result     : Theorem 2.60s
% Output     : CNFRefutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 640 expanded)
%              Number of clauses        :   48 ( 233 expanded)
%              Number of leaves         :   12 ( 154 expanded)
%              Depth                    :   21
%              Number of atoms          :  298 (2958 expanded)
%              Number of equality atoms :  173 (1437 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_xboole_0 = k1_funct_1(X1,X2) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_xboole_0 = k1_funct_1(X1,X2)
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ! [X2] :
            ( k1_xboole_0 = k1_funct_1(sK2(X0),X2)
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK2(X0)) = X0
        & v1_funct_1(sK2(X0))
        & v1_relat_1(sK2(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(sK2(X0),X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK2(X0)) = X0
      & v1_funct_1(sK2(X0))
      & v1_relat_1(sK2(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f11,f20])).

fof(f37,plain,(
    ! [X0] : k1_relat_1(sK2(X0)) = X0 ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X0)
         => k1_funct_1(X2,X3) = X1 )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k1_funct_1(X2,X3) = X1
              | ~ r2_hidden(X3,X0) )
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( ! [X3] :
            ( k1_funct_1(sK1(X0,X1),X3) = X1
            | ~ r2_hidden(X3,X0) )
        & k1_relat_1(sK1(X0,X1)) = X0
        & v1_funct_1(sK1(X0,X1))
        & v1_relat_1(sK1(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X3] :
          ( k1_funct_1(sK1(X0,X1),X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(sK1(X0,X1)) = X0
      & v1_funct_1(sK1(X0,X1))
      & v1_relat_1(sK1(X0,X1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f10,f18])).

fof(f33,plain,(
    ! [X0,X1] : k1_relat_1(sK1(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f6,conjecture,(
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

fof(f7,negated_conjecture,(
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
    inference(negated_conjecture,[],[f6])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f22,plain,
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
   => ( k1_xboole_0 != sK3
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != sK3
              | k1_relat_1(X1) != sK3
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( k1_xboole_0 != sK3
    & ! [X1] :
        ( ! [X2] :
            ( X1 = X2
            | k1_relat_1(X2) != sK3
            | k1_relat_1(X1) != sK3
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) )
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f22])).

fof(f39,plain,(
    ! [X2,X1] :
      ( X1 = X2
      | k1_relat_1(X2) != sK3
      | k1_relat_1(X1) != sK3
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f31,plain,(
    ! [X0,X1] : v1_relat_1(sK1(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f32,plain,(
    ! [X0,X1] : v1_funct_1(sK1(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f35,plain,(
    ! [X0] : v1_relat_1(sK2(X0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f36,plain,(
    ! [X0] : v1_funct_1(sK2(X0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f15,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK0(X0,X1),X1)
          | ~ r2_hidden(sK0(X0,X1),X0) )
        & ( r2_hidden(sK0(X0,X1),X1)
          | r2_hidden(sK0(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK0(X0,X1),X1)
          | ~ r2_hidden(sK0(X0,X1),X0) )
        & ( r2_hidden(sK0(X0,X1),X1)
          | r2_hidden(sK0(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).

fof(f28,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK0(X0,X1),X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f34,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(sK1(X0,X1),X3) = X1
      | ~ r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f40,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_12,plain,
    ( k1_relat_1(sK2(X0)) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_8,plain,
    ( k1_relat_1(sK1(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_16,negated_conjecture,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | X1 = X0
    | k1_relat_1(X0) != sK3
    | k1_relat_1(X1) != sK3 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_399,plain,
    ( X0 = X1
    | k1_relat_1(X0) != sK3
    | k1_relat_1(X1) != sK3
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_829,plain,
    ( sK1(X0,X1) = X2
    | k1_relat_1(X2) != sK3
    | sK3 != X0
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(sK1(X0,X1)) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_399])).

cnf(c_10,plain,
    ( v1_relat_1(sK1(X0,X1)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_30,plain,
    ( v1_relat_1(sK1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_9,plain,
    ( v1_funct_1(sK1(X0,X1)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_33,plain,
    ( v1_funct_1(sK1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_969,plain,
    ( v1_funct_1(X2) != iProver_top
    | sK1(X0,X1) = X2
    | k1_relat_1(X2) != sK3
    | sK3 != X0
    | v1_relat_1(X2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_829,c_30,c_33])).

cnf(c_970,plain,
    ( sK1(X0,X1) = X2
    | k1_relat_1(X2) != sK3
    | sK3 != X0
    | v1_relat_1(X2) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_969])).

cnf(c_981,plain,
    ( sK1(X0,X1) = sK2(X2)
    | sK3 != X2
    | sK3 != X0
    | v1_relat_1(sK2(X2)) != iProver_top
    | v1_funct_1(sK2(X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12,c_970])).

cnf(c_557,plain,
    ( sK2(X0) = X1
    | k1_relat_1(X1) != sK3
    | sK3 != X0
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(sK2(X0)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK2(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12,c_399])).

cnf(c_14,plain,
    ( v1_relat_1(sK2(X0)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_20,plain,
    ( v1_relat_1(sK2(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_13,plain,
    ( v1_funct_1(sK2(X0)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_23,plain,
    ( v1_funct_1(sK2(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_612,plain,
    ( v1_funct_1(X1) != iProver_top
    | sK2(X0) = X1
    | k1_relat_1(X1) != sK3
    | sK3 != X0
    | v1_relat_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_557,c_20,c_23])).

cnf(c_613,plain,
    ( sK2(X0) = X1
    | k1_relat_1(X1) != sK3
    | sK3 != X0
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_612])).

cnf(c_828,plain,
    ( sK1(X0,X1) = sK2(X2)
    | sK3 != X0
    | sK3 != X2
    | v1_relat_1(sK1(X0,X1)) != iProver_top
    | v1_funct_1(sK1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_613])).

cnf(c_854,plain,
    ( ~ v1_relat_1(sK1(X0,X1))
    | ~ v1_funct_1(sK1(X0,X1))
    | sK1(X0,X1) = sK2(X2)
    | sK3 != X0
    | sK3 != X2 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_828])).

cnf(c_1009,plain,
    ( sK1(X0,X1) = sK2(X2)
    | sK3 != X2
    | sK3 != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_981,c_10,c_9,c_854])).

cnf(c_1010,plain,
    ( sK1(X0,X1) = sK2(X2)
    | sK3 != X0
    | sK3 != X2 ),
    inference(renaming,[status(thm)],[c_1009])).

cnf(c_1015,plain,
    ( sK1(sK3,X0) = sK2(X1)
    | sK3 != X1 ),
    inference(equality_resolution,[status(thm)],[c_1010])).

cnf(c_1162,plain,
    ( sK1(sK3,X0) = sK2(sK3) ),
    inference(equality_resolution,[status(thm)],[c_1015])).

cnf(c_5,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r2_hidden(sK0(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_406,plain,
    ( X0 = X1
    | r2_hidden(sK0(X1,X0),X0) = iProver_top
    | r2_hidden(sK0(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_6,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k5_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_409,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1577,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_409])).

cnf(c_1702,plain,
    ( X0 = X1
    | r2_hidden(sK0(X0,X1),X1) = iProver_top
    | r2_hidden(sK0(X0,X1),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_406,c_1577])).

cnf(c_1706,plain,
    ( X0 = X1
    | r2_hidden(sK0(X1,X0),k1_xboole_0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1702,c_1577])).

cnf(c_1717,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(X0,k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_406,c_1706])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_funct_1(sK1(X1,X2),X0) = X2 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_405,plain,
    ( k1_funct_1(sK1(X0,X1),X2) = X1
    | r2_hidden(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1831,plain,
    ( k1_funct_1(sK1(X0,X1),sK0(X0,k1_xboole_0)) = X1
    | k1_xboole_0 = X0 ),
    inference(superposition,[status(thm)],[c_1717,c_405])).

cnf(c_2433,plain,
    ( k1_funct_1(sK2(sK3),sK0(sK3,k1_xboole_0)) = X0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1162,c_1831])).

cnf(c_15,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_158,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_173,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_158])).

cnf(c_159,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_547,plain,
    ( sK3 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_159])).

cnf(c_548,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_547])).

cnf(c_2488,plain,
    ( k1_funct_1(sK2(sK3),sK0(sK3,k1_xboole_0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2433,c_15,c_173,c_548])).

cnf(c_2494,plain,
    ( X0 = X1 ),
    inference(superposition,[status(thm)],[c_2488,c_2488])).

cnf(c_2803,plain,
    ( k1_xboole_0 != X0 ),
    inference(superposition,[status(thm)],[c_2494,c_15])).

cnf(c_2808,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2803,c_2494])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 17:48:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.60/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/0.99  
% 2.60/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.60/0.99  
% 2.60/0.99  ------  iProver source info
% 2.60/0.99  
% 2.60/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.60/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.60/0.99  git: non_committed_changes: false
% 2.60/0.99  git: last_make_outside_of_git: false
% 2.60/0.99  
% 2.60/0.99  ------ 
% 2.60/0.99  
% 2.60/0.99  ------ Input Options
% 2.60/0.99  
% 2.60/0.99  --out_options                           all
% 2.60/0.99  --tptp_safe_out                         true
% 2.60/0.99  --problem_path                          ""
% 2.60/0.99  --include_path                          ""
% 2.60/0.99  --clausifier                            res/vclausify_rel
% 2.60/0.99  --clausifier_options                    --mode clausify
% 2.60/0.99  --stdin                                 false
% 2.60/0.99  --stats_out                             all
% 2.60/0.99  
% 2.60/0.99  ------ General Options
% 2.60/0.99  
% 2.60/0.99  --fof                                   false
% 2.60/0.99  --time_out_real                         305.
% 2.60/0.99  --time_out_virtual                      -1.
% 2.60/0.99  --symbol_type_check                     false
% 2.60/0.99  --clausify_out                          false
% 2.60/0.99  --sig_cnt_out                           false
% 2.60/0.99  --trig_cnt_out                          false
% 2.60/0.99  --trig_cnt_out_tolerance                1.
% 2.60/0.99  --trig_cnt_out_sk_spl                   false
% 2.60/0.99  --abstr_cl_out                          false
% 2.60/0.99  
% 2.60/0.99  ------ Global Options
% 2.60/0.99  
% 2.60/0.99  --schedule                              default
% 2.60/0.99  --add_important_lit                     false
% 2.60/0.99  --prop_solver_per_cl                    1000
% 2.60/0.99  --min_unsat_core                        false
% 2.60/0.99  --soft_assumptions                      false
% 2.60/0.99  --soft_lemma_size                       3
% 2.60/0.99  --prop_impl_unit_size                   0
% 2.60/0.99  --prop_impl_unit                        []
% 2.60/0.99  --share_sel_clauses                     true
% 2.60/0.99  --reset_solvers                         false
% 2.60/0.99  --bc_imp_inh                            [conj_cone]
% 2.60/0.99  --conj_cone_tolerance                   3.
% 2.60/0.99  --extra_neg_conj                        none
% 2.60/0.99  --large_theory_mode                     true
% 2.60/0.99  --prolific_symb_bound                   200
% 2.60/0.99  --lt_threshold                          2000
% 2.60/0.99  --clause_weak_htbl                      true
% 2.60/0.99  --gc_record_bc_elim                     false
% 2.60/0.99  
% 2.60/0.99  ------ Preprocessing Options
% 2.60/0.99  
% 2.60/0.99  --preprocessing_flag                    true
% 2.60/0.99  --time_out_prep_mult                    0.1
% 2.60/0.99  --splitting_mode                        input
% 2.60/0.99  --splitting_grd                         true
% 2.60/0.99  --splitting_cvd                         false
% 2.60/0.99  --splitting_cvd_svl                     false
% 2.60/0.99  --splitting_nvd                         32
% 2.60/0.99  --sub_typing                            true
% 2.60/0.99  --prep_gs_sim                           true
% 2.60/0.99  --prep_unflatten                        true
% 2.60/0.99  --prep_res_sim                          true
% 2.60/0.99  --prep_upred                            true
% 2.60/0.99  --prep_sem_filter                       exhaustive
% 2.60/0.99  --prep_sem_filter_out                   false
% 2.60/0.99  --pred_elim                             true
% 2.60/0.99  --res_sim_input                         true
% 2.60/0.99  --eq_ax_congr_red                       true
% 2.60/0.99  --pure_diseq_elim                       true
% 2.60/0.99  --brand_transform                       false
% 2.60/0.99  --non_eq_to_eq                          false
% 2.60/0.99  --prep_def_merge                        true
% 2.60/0.99  --prep_def_merge_prop_impl              false
% 2.60/0.99  --prep_def_merge_mbd                    true
% 2.60/0.99  --prep_def_merge_tr_red                 false
% 2.60/0.99  --prep_def_merge_tr_cl                  false
% 2.60/0.99  --smt_preprocessing                     true
% 2.60/0.99  --smt_ac_axioms                         fast
% 2.60/0.99  --preprocessed_out                      false
% 2.60/0.99  --preprocessed_stats                    false
% 2.60/0.99  
% 2.60/0.99  ------ Abstraction refinement Options
% 2.60/0.99  
% 2.60/0.99  --abstr_ref                             []
% 2.60/0.99  --abstr_ref_prep                        false
% 2.60/0.99  --abstr_ref_until_sat                   false
% 2.60/0.99  --abstr_ref_sig_restrict                funpre
% 2.60/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.60/0.99  --abstr_ref_under                       []
% 2.60/0.99  
% 2.60/0.99  ------ SAT Options
% 2.60/0.99  
% 2.60/0.99  --sat_mode                              false
% 2.60/0.99  --sat_fm_restart_options                ""
% 2.60/0.99  --sat_gr_def                            false
% 2.60/0.99  --sat_epr_types                         true
% 2.60/0.99  --sat_non_cyclic_types                  false
% 2.60/0.99  --sat_finite_models                     false
% 2.60/0.99  --sat_fm_lemmas                         false
% 2.60/0.99  --sat_fm_prep                           false
% 2.60/0.99  --sat_fm_uc_incr                        true
% 2.60/0.99  --sat_out_model                         small
% 2.60/0.99  --sat_out_clauses                       false
% 2.60/0.99  
% 2.60/0.99  ------ QBF Options
% 2.60/0.99  
% 2.60/0.99  --qbf_mode                              false
% 2.60/0.99  --qbf_elim_univ                         false
% 2.60/0.99  --qbf_dom_inst                          none
% 2.60/0.99  --qbf_dom_pre_inst                      false
% 2.60/0.99  --qbf_sk_in                             false
% 2.60/0.99  --qbf_pred_elim                         true
% 2.60/0.99  --qbf_split                             512
% 2.60/0.99  
% 2.60/0.99  ------ BMC1 Options
% 2.60/0.99  
% 2.60/0.99  --bmc1_incremental                      false
% 2.60/0.99  --bmc1_axioms                           reachable_all
% 2.60/0.99  --bmc1_min_bound                        0
% 2.60/0.99  --bmc1_max_bound                        -1
% 2.60/0.99  --bmc1_max_bound_default                -1
% 2.60/0.99  --bmc1_symbol_reachability              true
% 2.60/0.99  --bmc1_property_lemmas                  false
% 2.60/0.99  --bmc1_k_induction                      false
% 2.60/0.99  --bmc1_non_equiv_states                 false
% 2.60/0.99  --bmc1_deadlock                         false
% 2.60/0.99  --bmc1_ucm                              false
% 2.60/0.99  --bmc1_add_unsat_core                   none
% 2.60/0.99  --bmc1_unsat_core_children              false
% 2.60/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.60/0.99  --bmc1_out_stat                         full
% 2.60/0.99  --bmc1_ground_init                      false
% 2.60/0.99  --bmc1_pre_inst_next_state              false
% 2.60/0.99  --bmc1_pre_inst_state                   false
% 2.60/0.99  --bmc1_pre_inst_reach_state             false
% 2.60/0.99  --bmc1_out_unsat_core                   false
% 2.60/0.99  --bmc1_aig_witness_out                  false
% 2.60/0.99  --bmc1_verbose                          false
% 2.60/0.99  --bmc1_dump_clauses_tptp                false
% 2.60/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.60/0.99  --bmc1_dump_file                        -
% 2.60/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.60/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.60/0.99  --bmc1_ucm_extend_mode                  1
% 2.60/0.99  --bmc1_ucm_init_mode                    2
% 2.60/0.99  --bmc1_ucm_cone_mode                    none
% 2.60/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.60/0.99  --bmc1_ucm_relax_model                  4
% 2.60/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.60/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.60/0.99  --bmc1_ucm_layered_model                none
% 2.60/0.99  --bmc1_ucm_max_lemma_size               10
% 2.60/0.99  
% 2.60/0.99  ------ AIG Options
% 2.60/0.99  
% 2.60/0.99  --aig_mode                              false
% 2.60/0.99  
% 2.60/0.99  ------ Instantiation Options
% 2.60/0.99  
% 2.60/0.99  --instantiation_flag                    true
% 2.60/0.99  --inst_sos_flag                         false
% 2.60/0.99  --inst_sos_phase                        true
% 2.60/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.60/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.60/0.99  --inst_lit_sel_side                     num_symb
% 2.60/0.99  --inst_solver_per_active                1400
% 2.60/0.99  --inst_solver_calls_frac                1.
% 2.60/0.99  --inst_passive_queue_type               priority_queues
% 2.60/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.60/0.99  --inst_passive_queues_freq              [25;2]
% 2.60/0.99  --inst_dismatching                      true
% 2.60/0.99  --inst_eager_unprocessed_to_passive     true
% 2.60/0.99  --inst_prop_sim_given                   true
% 2.60/0.99  --inst_prop_sim_new                     false
% 2.60/0.99  --inst_subs_new                         false
% 2.60/0.99  --inst_eq_res_simp                      false
% 2.60/0.99  --inst_subs_given                       false
% 2.60/0.99  --inst_orphan_elimination               true
% 2.60/0.99  --inst_learning_loop_flag               true
% 2.60/0.99  --inst_learning_start                   3000
% 2.60/0.99  --inst_learning_factor                  2
% 2.60/0.99  --inst_start_prop_sim_after_learn       3
% 2.60/0.99  --inst_sel_renew                        solver
% 2.60/0.99  --inst_lit_activity_flag                true
% 2.60/0.99  --inst_restr_to_given                   false
% 2.60/0.99  --inst_activity_threshold               500
% 2.60/0.99  --inst_out_proof                        true
% 2.60/0.99  
% 2.60/0.99  ------ Resolution Options
% 2.60/0.99  
% 2.60/0.99  --resolution_flag                       true
% 2.60/0.99  --res_lit_sel                           adaptive
% 2.60/0.99  --res_lit_sel_side                      none
% 2.60/0.99  --res_ordering                          kbo
% 2.60/0.99  --res_to_prop_solver                    active
% 2.60/0.99  --res_prop_simpl_new                    false
% 2.60/0.99  --res_prop_simpl_given                  true
% 2.60/0.99  --res_passive_queue_type                priority_queues
% 2.60/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.60/0.99  --res_passive_queues_freq               [15;5]
% 2.60/0.99  --res_forward_subs                      full
% 2.60/0.99  --res_backward_subs                     full
% 2.60/0.99  --res_forward_subs_resolution           true
% 2.60/0.99  --res_backward_subs_resolution          true
% 2.60/0.99  --res_orphan_elimination                true
% 2.60/0.99  --res_time_limit                        2.
% 2.60/0.99  --res_out_proof                         true
% 2.60/0.99  
% 2.60/0.99  ------ Superposition Options
% 2.60/0.99  
% 2.60/0.99  --superposition_flag                    true
% 2.60/0.99  --sup_passive_queue_type                priority_queues
% 2.60/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.60/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.60/0.99  --demod_completeness_check              fast
% 2.60/0.99  --demod_use_ground                      true
% 2.60/0.99  --sup_to_prop_solver                    passive
% 2.60/0.99  --sup_prop_simpl_new                    true
% 2.60/0.99  --sup_prop_simpl_given                  true
% 2.60/0.99  --sup_fun_splitting                     false
% 2.60/0.99  --sup_smt_interval                      50000
% 2.60/0.99  
% 2.60/0.99  ------ Superposition Simplification Setup
% 2.60/0.99  
% 2.60/0.99  --sup_indices_passive                   []
% 2.60/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.60/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.60/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.60/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.60/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.60/0.99  --sup_full_bw                           [BwDemod]
% 2.60/0.99  --sup_immed_triv                        [TrivRules]
% 2.60/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.60/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.60/0.99  --sup_immed_bw_main                     []
% 2.60/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.60/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.60/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.60/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.60/0.99  
% 2.60/0.99  ------ Combination Options
% 2.60/0.99  
% 2.60/0.99  --comb_res_mult                         3
% 2.60/0.99  --comb_sup_mult                         2
% 2.60/0.99  --comb_inst_mult                        10
% 2.60/0.99  
% 2.60/0.99  ------ Debug Options
% 2.60/0.99  
% 2.60/0.99  --dbg_backtrace                         false
% 2.60/0.99  --dbg_dump_prop_clauses                 false
% 2.60/0.99  --dbg_dump_prop_clauses_file            -
% 2.60/0.99  --dbg_out_stat                          false
% 2.60/0.99  ------ Parsing...
% 2.60/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.60/0.99  
% 2.60/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.60/0.99  
% 2.60/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.60/0.99  
% 2.60/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.60/0.99  ------ Proving...
% 2.60/0.99  ------ Problem Properties 
% 2.60/0.99  
% 2.60/0.99  
% 2.60/0.99  clauses                                 17
% 2.60/0.99  conjectures                             2
% 2.60/0.99  EPR                                     1
% 2.60/0.99  Horn                                    13
% 2.60/0.99  unary                                   8
% 2.60/0.99  binary                                  2
% 2.60/0.99  lits                                    37
% 2.60/0.99  lits eq                                 11
% 2.60/0.99  fd_pure                                 0
% 2.60/0.99  fd_pseudo                               0
% 2.60/0.99  fd_cond                                 0
% 2.60/0.99  fd_pseudo_cond                          3
% 2.60/0.99  AC symbols                              0
% 2.60/0.99  
% 2.60/0.99  ------ Schedule dynamic 5 is on 
% 2.60/0.99  
% 2.60/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.60/0.99  
% 2.60/0.99  
% 2.60/0.99  ------ 
% 2.60/0.99  Current options:
% 2.60/0.99  ------ 
% 2.60/0.99  
% 2.60/0.99  ------ Input Options
% 2.60/0.99  
% 2.60/0.99  --out_options                           all
% 2.60/0.99  --tptp_safe_out                         true
% 2.60/0.99  --problem_path                          ""
% 2.60/0.99  --include_path                          ""
% 2.60/0.99  --clausifier                            res/vclausify_rel
% 2.60/0.99  --clausifier_options                    --mode clausify
% 2.60/0.99  --stdin                                 false
% 2.60/0.99  --stats_out                             all
% 2.60/0.99  
% 2.60/0.99  ------ General Options
% 2.60/0.99  
% 2.60/0.99  --fof                                   false
% 2.60/0.99  --time_out_real                         305.
% 2.60/0.99  --time_out_virtual                      -1.
% 2.60/0.99  --symbol_type_check                     false
% 2.60/0.99  --clausify_out                          false
% 2.60/0.99  --sig_cnt_out                           false
% 2.60/0.99  --trig_cnt_out                          false
% 2.60/0.99  --trig_cnt_out_tolerance                1.
% 2.60/0.99  --trig_cnt_out_sk_spl                   false
% 2.60/0.99  --abstr_cl_out                          false
% 2.60/0.99  
% 2.60/0.99  ------ Global Options
% 2.60/0.99  
% 2.60/0.99  --schedule                              default
% 2.60/0.99  --add_important_lit                     false
% 2.60/0.99  --prop_solver_per_cl                    1000
% 2.60/0.99  --min_unsat_core                        false
% 2.60/0.99  --soft_assumptions                      false
% 2.60/0.99  --soft_lemma_size                       3
% 2.60/0.99  --prop_impl_unit_size                   0
% 2.60/0.99  --prop_impl_unit                        []
% 2.60/0.99  --share_sel_clauses                     true
% 2.60/0.99  --reset_solvers                         false
% 2.60/0.99  --bc_imp_inh                            [conj_cone]
% 2.60/0.99  --conj_cone_tolerance                   3.
% 2.60/0.99  --extra_neg_conj                        none
% 2.60/0.99  --large_theory_mode                     true
% 2.60/0.99  --prolific_symb_bound                   200
% 2.60/0.99  --lt_threshold                          2000
% 2.60/0.99  --clause_weak_htbl                      true
% 2.60/0.99  --gc_record_bc_elim                     false
% 2.60/0.99  
% 2.60/0.99  ------ Preprocessing Options
% 2.60/0.99  
% 2.60/0.99  --preprocessing_flag                    true
% 2.60/0.99  --time_out_prep_mult                    0.1
% 2.60/0.99  --splitting_mode                        input
% 2.60/0.99  --splitting_grd                         true
% 2.60/0.99  --splitting_cvd                         false
% 2.60/0.99  --splitting_cvd_svl                     false
% 2.60/0.99  --splitting_nvd                         32
% 2.60/0.99  --sub_typing                            true
% 2.60/0.99  --prep_gs_sim                           true
% 2.60/0.99  --prep_unflatten                        true
% 2.60/0.99  --prep_res_sim                          true
% 2.60/0.99  --prep_upred                            true
% 2.60/0.99  --prep_sem_filter                       exhaustive
% 2.60/0.99  --prep_sem_filter_out                   false
% 2.60/0.99  --pred_elim                             true
% 2.60/0.99  --res_sim_input                         true
% 2.60/0.99  --eq_ax_congr_red                       true
% 2.60/0.99  --pure_diseq_elim                       true
% 2.60/0.99  --brand_transform                       false
% 2.60/0.99  --non_eq_to_eq                          false
% 2.60/0.99  --prep_def_merge                        true
% 2.60/0.99  --prep_def_merge_prop_impl              false
% 2.60/0.99  --prep_def_merge_mbd                    true
% 2.60/0.99  --prep_def_merge_tr_red                 false
% 2.60/0.99  --prep_def_merge_tr_cl                  false
% 2.60/0.99  --smt_preprocessing                     true
% 2.60/0.99  --smt_ac_axioms                         fast
% 2.60/0.99  --preprocessed_out                      false
% 2.60/0.99  --preprocessed_stats                    false
% 2.60/0.99  
% 2.60/0.99  ------ Abstraction refinement Options
% 2.60/0.99  
% 2.60/0.99  --abstr_ref                             []
% 2.60/0.99  --abstr_ref_prep                        false
% 2.60/0.99  --abstr_ref_until_sat                   false
% 2.60/0.99  --abstr_ref_sig_restrict                funpre
% 2.60/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.60/0.99  --abstr_ref_under                       []
% 2.60/0.99  
% 2.60/0.99  ------ SAT Options
% 2.60/0.99  
% 2.60/0.99  --sat_mode                              false
% 2.60/0.99  --sat_fm_restart_options                ""
% 2.60/0.99  --sat_gr_def                            false
% 2.60/0.99  --sat_epr_types                         true
% 2.60/0.99  --sat_non_cyclic_types                  false
% 2.60/0.99  --sat_finite_models                     false
% 2.60/0.99  --sat_fm_lemmas                         false
% 2.60/0.99  --sat_fm_prep                           false
% 2.60/0.99  --sat_fm_uc_incr                        true
% 2.60/0.99  --sat_out_model                         small
% 2.60/0.99  --sat_out_clauses                       false
% 2.60/0.99  
% 2.60/0.99  ------ QBF Options
% 2.60/0.99  
% 2.60/0.99  --qbf_mode                              false
% 2.60/0.99  --qbf_elim_univ                         false
% 2.60/0.99  --qbf_dom_inst                          none
% 2.60/0.99  --qbf_dom_pre_inst                      false
% 2.60/0.99  --qbf_sk_in                             false
% 2.60/0.99  --qbf_pred_elim                         true
% 2.60/0.99  --qbf_split                             512
% 2.60/0.99  
% 2.60/0.99  ------ BMC1 Options
% 2.60/0.99  
% 2.60/0.99  --bmc1_incremental                      false
% 2.60/0.99  --bmc1_axioms                           reachable_all
% 2.60/0.99  --bmc1_min_bound                        0
% 2.60/0.99  --bmc1_max_bound                        -1
% 2.60/0.99  --bmc1_max_bound_default                -1
% 2.60/0.99  --bmc1_symbol_reachability              true
% 2.60/0.99  --bmc1_property_lemmas                  false
% 2.60/0.99  --bmc1_k_induction                      false
% 2.60/0.99  --bmc1_non_equiv_states                 false
% 2.60/0.99  --bmc1_deadlock                         false
% 2.60/0.99  --bmc1_ucm                              false
% 2.60/0.99  --bmc1_add_unsat_core                   none
% 2.60/0.99  --bmc1_unsat_core_children              false
% 2.60/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.60/0.99  --bmc1_out_stat                         full
% 2.60/0.99  --bmc1_ground_init                      false
% 2.60/0.99  --bmc1_pre_inst_next_state              false
% 2.60/0.99  --bmc1_pre_inst_state                   false
% 2.60/0.99  --bmc1_pre_inst_reach_state             false
% 2.60/0.99  --bmc1_out_unsat_core                   false
% 2.60/0.99  --bmc1_aig_witness_out                  false
% 2.60/0.99  --bmc1_verbose                          false
% 2.60/0.99  --bmc1_dump_clauses_tptp                false
% 2.60/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.60/0.99  --bmc1_dump_file                        -
% 2.60/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.60/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.60/0.99  --bmc1_ucm_extend_mode                  1
% 2.60/0.99  --bmc1_ucm_init_mode                    2
% 2.60/0.99  --bmc1_ucm_cone_mode                    none
% 2.60/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.60/0.99  --bmc1_ucm_relax_model                  4
% 2.60/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.60/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.60/0.99  --bmc1_ucm_layered_model                none
% 2.60/0.99  --bmc1_ucm_max_lemma_size               10
% 2.60/0.99  
% 2.60/0.99  ------ AIG Options
% 2.60/0.99  
% 2.60/0.99  --aig_mode                              false
% 2.60/0.99  
% 2.60/0.99  ------ Instantiation Options
% 2.60/0.99  
% 2.60/0.99  --instantiation_flag                    true
% 2.60/0.99  --inst_sos_flag                         false
% 2.60/0.99  --inst_sos_phase                        true
% 2.60/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.60/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.60/0.99  --inst_lit_sel_side                     none
% 2.60/0.99  --inst_solver_per_active                1400
% 2.60/0.99  --inst_solver_calls_frac                1.
% 2.60/0.99  --inst_passive_queue_type               priority_queues
% 2.60/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.60/0.99  --inst_passive_queues_freq              [25;2]
% 2.60/0.99  --inst_dismatching                      true
% 2.60/0.99  --inst_eager_unprocessed_to_passive     true
% 2.60/0.99  --inst_prop_sim_given                   true
% 2.60/0.99  --inst_prop_sim_new                     false
% 2.60/0.99  --inst_subs_new                         false
% 2.60/0.99  --inst_eq_res_simp                      false
% 2.60/0.99  --inst_subs_given                       false
% 2.60/0.99  --inst_orphan_elimination               true
% 2.60/0.99  --inst_learning_loop_flag               true
% 2.60/0.99  --inst_learning_start                   3000
% 2.60/0.99  --inst_learning_factor                  2
% 2.60/0.99  --inst_start_prop_sim_after_learn       3
% 2.60/0.99  --inst_sel_renew                        solver
% 2.60/0.99  --inst_lit_activity_flag                true
% 2.60/0.99  --inst_restr_to_given                   false
% 2.60/0.99  --inst_activity_threshold               500
% 2.60/0.99  --inst_out_proof                        true
% 2.60/0.99  
% 2.60/0.99  ------ Resolution Options
% 2.60/0.99  
% 2.60/0.99  --resolution_flag                       false
% 2.60/0.99  --res_lit_sel                           adaptive
% 2.60/0.99  --res_lit_sel_side                      none
% 2.60/0.99  --res_ordering                          kbo
% 2.60/0.99  --res_to_prop_solver                    active
% 2.60/0.99  --res_prop_simpl_new                    false
% 2.60/0.99  --res_prop_simpl_given                  true
% 2.60/0.99  --res_passive_queue_type                priority_queues
% 2.60/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.60/0.99  --res_passive_queues_freq               [15;5]
% 2.60/0.99  --res_forward_subs                      full
% 2.60/0.99  --res_backward_subs                     full
% 2.60/0.99  --res_forward_subs_resolution           true
% 2.60/0.99  --res_backward_subs_resolution          true
% 2.60/0.99  --res_orphan_elimination                true
% 2.60/0.99  --res_time_limit                        2.
% 2.60/0.99  --res_out_proof                         true
% 2.60/0.99  
% 2.60/0.99  ------ Superposition Options
% 2.60/0.99  
% 2.60/0.99  --superposition_flag                    true
% 2.60/0.99  --sup_passive_queue_type                priority_queues
% 2.60/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.60/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.60/0.99  --demod_completeness_check              fast
% 2.60/0.99  --demod_use_ground                      true
% 2.60/0.99  --sup_to_prop_solver                    passive
% 2.60/0.99  --sup_prop_simpl_new                    true
% 2.60/0.99  --sup_prop_simpl_given                  true
% 2.60/0.99  --sup_fun_splitting                     false
% 2.60/0.99  --sup_smt_interval                      50000
% 2.60/0.99  
% 2.60/0.99  ------ Superposition Simplification Setup
% 2.60/0.99  
% 2.60/0.99  --sup_indices_passive                   []
% 2.60/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.60/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.60/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.60/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.60/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.60/0.99  --sup_full_bw                           [BwDemod]
% 2.60/0.99  --sup_immed_triv                        [TrivRules]
% 2.60/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.60/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.60/0.99  --sup_immed_bw_main                     []
% 2.60/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.60/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.60/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.60/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.60/0.99  
% 2.60/0.99  ------ Combination Options
% 2.60/0.99  
% 2.60/0.99  --comb_res_mult                         3
% 2.60/0.99  --comb_sup_mult                         2
% 2.60/0.99  --comb_inst_mult                        10
% 2.60/0.99  
% 2.60/0.99  ------ Debug Options
% 2.60/0.99  
% 2.60/0.99  --dbg_backtrace                         false
% 2.60/0.99  --dbg_dump_prop_clauses                 false
% 2.60/0.99  --dbg_dump_prop_clauses_file            -
% 2.60/0.99  --dbg_out_stat                          false
% 2.60/0.99  
% 2.60/0.99  
% 2.60/0.99  
% 2.60/0.99  
% 2.60/0.99  ------ Proving...
% 2.60/0.99  
% 2.60/0.99  
% 2.60/0.99  % SZS status Theorem for theBenchmark.p
% 2.60/0.99  
% 2.60/0.99   Resolution empty clause
% 2.60/0.99  
% 2.60/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.60/0.99  
% 2.60/0.99  fof(f5,axiom,(
% 2.60/0.99    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_xboole_0 = k1_funct_1(X1,X2)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 2.60/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/0.99  
% 2.60/0.99  fof(f11,plain,(
% 2.60/0.99    ! [X0] : ? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 2.60/0.99    inference(ennf_transformation,[],[f5])).
% 2.60/0.99  
% 2.60/0.99  fof(f20,plain,(
% 2.60/0.99    ! [X0] : (? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1)) => (! [X2] : (k1_xboole_0 = k1_funct_1(sK2(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK2(X0)) = X0 & v1_funct_1(sK2(X0)) & v1_relat_1(sK2(X0))))),
% 2.60/0.99    introduced(choice_axiom,[])).
% 2.60/0.99  
% 2.60/0.99  fof(f21,plain,(
% 2.60/0.99    ! [X0] : (! [X2] : (k1_xboole_0 = k1_funct_1(sK2(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK2(X0)) = X0 & v1_funct_1(sK2(X0)) & v1_relat_1(sK2(X0)))),
% 2.60/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f11,f20])).
% 2.60/0.99  
% 2.60/0.99  fof(f37,plain,(
% 2.60/0.99    ( ! [X0] : (k1_relat_1(sK2(X0)) = X0) )),
% 2.60/0.99    inference(cnf_transformation,[],[f21])).
% 2.60/0.99  
% 2.60/0.99  fof(f4,axiom,(
% 2.60/0.99    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 2.60/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/0.99  
% 2.60/0.99  fof(f10,plain,(
% 2.60/0.99    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 2.60/0.99    inference(ennf_transformation,[],[f4])).
% 2.60/0.99  
% 2.60/0.99  fof(f18,plain,(
% 2.60/0.99    ! [X1,X0] : (? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (! [X3] : (k1_funct_1(sK1(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK1(X0,X1)) = X0 & v1_funct_1(sK1(X0,X1)) & v1_relat_1(sK1(X0,X1))))),
% 2.60/0.99    introduced(choice_axiom,[])).
% 2.60/0.99  
% 2.60/0.99  fof(f19,plain,(
% 2.60/0.99    ! [X0,X1] : (! [X3] : (k1_funct_1(sK1(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK1(X0,X1)) = X0 & v1_funct_1(sK1(X0,X1)) & v1_relat_1(sK1(X0,X1)))),
% 2.60/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f10,f18])).
% 2.60/0.99  
% 2.60/0.99  fof(f33,plain,(
% 2.60/0.99    ( ! [X0,X1] : (k1_relat_1(sK1(X0,X1)) = X0) )),
% 2.60/0.99    inference(cnf_transformation,[],[f19])).
% 2.60/0.99  
% 2.60/0.99  fof(f6,conjecture,(
% 2.60/0.99    ! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 2.60/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/0.99  
% 2.60/0.99  fof(f7,negated_conjecture,(
% 2.60/0.99    ~! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 2.60/0.99    inference(negated_conjecture,[],[f6])).
% 2.60/0.99  
% 2.60/0.99  fof(f12,plain,(
% 2.60/0.99    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : ((X1 = X2 | (k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))))),
% 2.60/0.99    inference(ennf_transformation,[],[f7])).
% 2.60/0.99  
% 2.60/0.99  fof(f13,plain,(
% 2.60/0.99    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.60/0.99    inference(flattening,[],[f12])).
% 2.60/0.99  
% 2.60/0.99  fof(f22,plain,(
% 2.60/0.99    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) => (k1_xboole_0 != sK3 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != sK3 | k1_relat_1(X1) != sK3 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.60/0.99    introduced(choice_axiom,[])).
% 2.60/0.99  
% 2.60/0.99  fof(f23,plain,(
% 2.60/0.99    k1_xboole_0 != sK3 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != sK3 | k1_relat_1(X1) != sK3 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.60/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f22])).
% 2.60/0.99  
% 2.60/0.99  fof(f39,plain,(
% 2.60/0.99    ( ! [X2,X1] : (X1 = X2 | k1_relat_1(X2) != sK3 | k1_relat_1(X1) != sK3 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.60/0.99    inference(cnf_transformation,[],[f23])).
% 2.60/0.99  
% 2.60/0.99  fof(f31,plain,(
% 2.60/0.99    ( ! [X0,X1] : (v1_relat_1(sK1(X0,X1))) )),
% 2.60/0.99    inference(cnf_transformation,[],[f19])).
% 2.60/0.99  
% 2.60/0.99  fof(f32,plain,(
% 2.60/0.99    ( ! [X0,X1] : (v1_funct_1(sK1(X0,X1))) )),
% 2.60/0.99    inference(cnf_transformation,[],[f19])).
% 2.60/0.99  
% 2.60/0.99  fof(f35,plain,(
% 2.60/0.99    ( ! [X0] : (v1_relat_1(sK2(X0))) )),
% 2.60/0.99    inference(cnf_transformation,[],[f21])).
% 2.60/0.99  
% 2.60/0.99  fof(f36,plain,(
% 2.60/0.99    ( ! [X0] : (v1_funct_1(sK2(X0))) )),
% 2.60/0.99    inference(cnf_transformation,[],[f21])).
% 2.60/0.99  
% 2.60/0.99  fof(f2,axiom,(
% 2.60/0.99    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 2.60/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/0.99  
% 2.60/0.99  fof(f9,plain,(
% 2.60/0.99    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 2.60/0.99    inference(ennf_transformation,[],[f2])).
% 2.60/0.99  
% 2.60/0.99  fof(f15,plain,(
% 2.60/0.99    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 2.60/0.99    inference(nnf_transformation,[],[f9])).
% 2.60/0.99  
% 2.60/0.99  fof(f16,plain,(
% 2.60/0.99    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) & (r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0))))),
% 2.60/0.99    introduced(choice_axiom,[])).
% 2.60/0.99  
% 2.60/0.99  fof(f17,plain,(
% 2.60/0.99    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) & (r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0))))),
% 2.60/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).
% 2.60/0.99  
% 2.60/0.99  fof(f28,plain,(
% 2.60/0.99    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.60/0.99    inference(cnf_transformation,[],[f17])).
% 2.60/0.99  
% 2.60/0.99  fof(f3,axiom,(
% 2.60/0.99    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.60/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/0.99  
% 2.60/0.99  fof(f30,plain,(
% 2.60/0.99    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.60/0.99    inference(cnf_transformation,[],[f3])).
% 2.60/0.99  
% 2.60/0.99  fof(f1,axiom,(
% 2.60/0.99    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 2.60/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/0.99  
% 2.60/0.99  fof(f8,plain,(
% 2.60/0.99    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 2.60/0.99    inference(ennf_transformation,[],[f1])).
% 2.60/0.99  
% 2.60/0.99  fof(f14,plain,(
% 2.60/0.99    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 2.60/0.99    inference(nnf_transformation,[],[f8])).
% 2.60/0.99  
% 2.60/0.99  fof(f25,plain,(
% 2.60/0.99    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 2.60/0.99    inference(cnf_transformation,[],[f14])).
% 2.60/0.99  
% 2.60/0.99  fof(f34,plain,(
% 2.60/0.99    ( ! [X0,X3,X1] : (k1_funct_1(sK1(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) )),
% 2.60/0.99    inference(cnf_transformation,[],[f19])).
% 2.60/0.99  
% 2.60/0.99  fof(f40,plain,(
% 2.60/0.99    k1_xboole_0 != sK3),
% 2.60/0.99    inference(cnf_transformation,[],[f23])).
% 2.60/0.99  
% 2.60/0.99  cnf(c_12,plain,
% 2.60/0.99      ( k1_relat_1(sK2(X0)) = X0 ),
% 2.60/0.99      inference(cnf_transformation,[],[f37]) ).
% 2.60/0.99  
% 2.60/0.99  cnf(c_8,plain,
% 2.60/0.99      ( k1_relat_1(sK1(X0,X1)) = X0 ),
% 2.60/0.99      inference(cnf_transformation,[],[f33]) ).
% 2.60/0.99  
% 2.60/0.99  cnf(c_16,negated_conjecture,
% 2.60/0.99      ( ~ v1_relat_1(X0)
% 2.60/0.99      | ~ v1_relat_1(X1)
% 2.60/0.99      | ~ v1_funct_1(X0)
% 2.60/0.99      | ~ v1_funct_1(X1)
% 2.60/0.99      | X1 = X0
% 2.60/0.99      | k1_relat_1(X0) != sK3
% 2.60/0.99      | k1_relat_1(X1) != sK3 ),
% 2.60/0.99      inference(cnf_transformation,[],[f39]) ).
% 2.60/0.99  
% 2.60/0.99  cnf(c_399,plain,
% 2.60/0.99      ( X0 = X1
% 2.60/0.99      | k1_relat_1(X0) != sK3
% 2.60/0.99      | k1_relat_1(X1) != sK3
% 2.60/0.99      | v1_relat_1(X1) != iProver_top
% 2.60/0.99      | v1_relat_1(X0) != iProver_top
% 2.60/0.99      | v1_funct_1(X1) != iProver_top
% 2.60/0.99      | v1_funct_1(X0) != iProver_top ),
% 2.60/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.60/0.99  
% 2.60/0.99  cnf(c_829,plain,
% 2.60/0.99      ( sK1(X0,X1) = X2
% 2.60/0.99      | k1_relat_1(X2) != sK3
% 2.60/0.99      | sK3 != X0
% 2.60/0.99      | v1_relat_1(X2) != iProver_top
% 2.60/0.99      | v1_relat_1(sK1(X0,X1)) != iProver_top
% 2.60/0.99      | v1_funct_1(X2) != iProver_top
% 2.60/0.99      | v1_funct_1(sK1(X0,X1)) != iProver_top ),
% 2.60/0.99      inference(superposition,[status(thm)],[c_8,c_399]) ).
% 2.60/0.99  
% 2.60/0.99  cnf(c_10,plain,
% 2.60/0.99      ( v1_relat_1(sK1(X0,X1)) ),
% 2.60/0.99      inference(cnf_transformation,[],[f31]) ).
% 2.60/0.99  
% 2.60/0.99  cnf(c_30,plain,
% 2.60/0.99      ( v1_relat_1(sK1(X0,X1)) = iProver_top ),
% 2.60/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.60/0.99  
% 2.60/0.99  cnf(c_9,plain,
% 2.60/0.99      ( v1_funct_1(sK1(X0,X1)) ),
% 2.60/0.99      inference(cnf_transformation,[],[f32]) ).
% 2.60/0.99  
% 2.60/0.99  cnf(c_33,plain,
% 2.60/0.99      ( v1_funct_1(sK1(X0,X1)) = iProver_top ),
% 2.60/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.60/0.99  
% 2.60/0.99  cnf(c_969,plain,
% 2.60/0.99      ( v1_funct_1(X2) != iProver_top
% 2.60/0.99      | sK1(X0,X1) = X2
% 2.60/0.99      | k1_relat_1(X2) != sK3
% 2.60/0.99      | sK3 != X0
% 2.60/0.99      | v1_relat_1(X2) != iProver_top ),
% 2.60/0.99      inference(global_propositional_subsumption,
% 2.60/0.99                [status(thm)],
% 2.60/0.99                [c_829,c_30,c_33]) ).
% 2.60/0.99  
% 2.60/0.99  cnf(c_970,plain,
% 2.60/0.99      ( sK1(X0,X1) = X2
% 2.60/0.99      | k1_relat_1(X2) != sK3
% 2.60/0.99      | sK3 != X0
% 2.60/0.99      | v1_relat_1(X2) != iProver_top
% 2.60/0.99      | v1_funct_1(X2) != iProver_top ),
% 2.60/0.99      inference(renaming,[status(thm)],[c_969]) ).
% 2.60/0.99  
% 2.60/0.99  cnf(c_981,plain,
% 2.60/0.99      ( sK1(X0,X1) = sK2(X2)
% 2.60/0.99      | sK3 != X2
% 2.60/0.99      | sK3 != X0
% 2.60/0.99      | v1_relat_1(sK2(X2)) != iProver_top
% 2.60/0.99      | v1_funct_1(sK2(X2)) != iProver_top ),
% 2.60/0.99      inference(superposition,[status(thm)],[c_12,c_970]) ).
% 2.60/0.99  
% 2.60/0.99  cnf(c_557,plain,
% 2.60/0.99      ( sK2(X0) = X1
% 2.60/0.99      | k1_relat_1(X1) != sK3
% 2.60/0.99      | sK3 != X0
% 2.60/0.99      | v1_relat_1(X1) != iProver_top
% 2.60/0.99      | v1_relat_1(sK2(X0)) != iProver_top
% 2.60/0.99      | v1_funct_1(X1) != iProver_top
% 2.60/0.99      | v1_funct_1(sK2(X0)) != iProver_top ),
% 2.60/0.99      inference(superposition,[status(thm)],[c_12,c_399]) ).
% 2.60/0.99  
% 2.60/0.99  cnf(c_14,plain,
% 2.60/0.99      ( v1_relat_1(sK2(X0)) ),
% 2.60/0.99      inference(cnf_transformation,[],[f35]) ).
% 2.60/0.99  
% 2.60/0.99  cnf(c_20,plain,
% 2.60/0.99      ( v1_relat_1(sK2(X0)) = iProver_top ),
% 2.60/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.60/0.99  
% 2.60/0.99  cnf(c_13,plain,
% 2.60/0.99      ( v1_funct_1(sK2(X0)) ),
% 2.60/0.99      inference(cnf_transformation,[],[f36]) ).
% 2.60/0.99  
% 2.60/0.99  cnf(c_23,plain,
% 2.60/0.99      ( v1_funct_1(sK2(X0)) = iProver_top ),
% 2.60/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.60/0.99  
% 2.60/0.99  cnf(c_612,plain,
% 2.60/0.99      ( v1_funct_1(X1) != iProver_top
% 2.60/0.99      | sK2(X0) = X1
% 2.60/0.99      | k1_relat_1(X1) != sK3
% 2.60/0.99      | sK3 != X0
% 2.60/0.99      | v1_relat_1(X1) != iProver_top ),
% 2.60/0.99      inference(global_propositional_subsumption,
% 2.60/0.99                [status(thm)],
% 2.60/0.99                [c_557,c_20,c_23]) ).
% 2.60/0.99  
% 2.60/0.99  cnf(c_613,plain,
% 2.60/0.99      ( sK2(X0) = X1
% 2.60/0.99      | k1_relat_1(X1) != sK3
% 2.60/0.99      | sK3 != X0
% 2.60/0.99      | v1_relat_1(X1) != iProver_top
% 2.60/0.99      | v1_funct_1(X1) != iProver_top ),
% 2.60/0.99      inference(renaming,[status(thm)],[c_612]) ).
% 2.60/0.99  
% 2.60/0.99  cnf(c_828,plain,
% 2.60/0.99      ( sK1(X0,X1) = sK2(X2)
% 2.60/0.99      | sK3 != X0
% 2.60/0.99      | sK3 != X2
% 2.60/0.99      | v1_relat_1(sK1(X0,X1)) != iProver_top
% 2.60/0.99      | v1_funct_1(sK1(X0,X1)) != iProver_top ),
% 2.60/0.99      inference(superposition,[status(thm)],[c_8,c_613]) ).
% 2.60/0.99  
% 2.60/0.99  cnf(c_854,plain,
% 2.60/0.99      ( ~ v1_relat_1(sK1(X0,X1))
% 2.60/0.99      | ~ v1_funct_1(sK1(X0,X1))
% 2.60/0.99      | sK1(X0,X1) = sK2(X2)
% 2.60/0.99      | sK3 != X0
% 2.60/0.99      | sK3 != X2 ),
% 2.60/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_828]) ).
% 2.60/0.99  
% 2.60/0.99  cnf(c_1009,plain,
% 2.60/0.99      ( sK1(X0,X1) = sK2(X2) | sK3 != X2 | sK3 != X0 ),
% 2.60/0.99      inference(global_propositional_subsumption,
% 2.60/0.99                [status(thm)],
% 2.60/0.99                [c_981,c_10,c_9,c_854]) ).
% 2.60/0.99  
% 2.60/0.99  cnf(c_1010,plain,
% 2.60/0.99      ( sK1(X0,X1) = sK2(X2) | sK3 != X0 | sK3 != X2 ),
% 2.60/0.99      inference(renaming,[status(thm)],[c_1009]) ).
% 2.60/0.99  
% 2.60/0.99  cnf(c_1015,plain,
% 2.60/0.99      ( sK1(sK3,X0) = sK2(X1) | sK3 != X1 ),
% 2.60/0.99      inference(equality_resolution,[status(thm)],[c_1010]) ).
% 2.60/0.99  
% 2.60/0.99  cnf(c_1162,plain,
% 2.60/0.99      ( sK1(sK3,X0) = sK2(sK3) ),
% 2.60/0.99      inference(equality_resolution,[status(thm)],[c_1015]) ).
% 2.60/0.99  
% 2.60/0.99  cnf(c_5,plain,
% 2.60/0.99      ( r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0) | X1 = X0 ),
% 2.60/0.99      inference(cnf_transformation,[],[f28]) ).
% 2.60/0.99  
% 2.60/0.99  cnf(c_406,plain,
% 2.60/0.99      ( X0 = X1
% 2.60/0.99      | r2_hidden(sK0(X1,X0),X0) = iProver_top
% 2.60/0.99      | r2_hidden(sK0(X1,X0),X1) = iProver_top ),
% 2.60/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.60/0.99  
% 2.60/0.99  cnf(c_6,plain,
% 2.60/0.99      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 2.60/0.99      inference(cnf_transformation,[],[f30]) ).
% 2.60/0.99  
% 2.60/0.99  cnf(c_2,plain,
% 2.60/0.99      ( ~ r2_hidden(X0,X1)
% 2.60/0.99      | ~ r2_hidden(X0,X2)
% 2.60/0.99      | ~ r2_hidden(X0,k5_xboole_0(X2,X1)) ),
% 2.60/0.99      inference(cnf_transformation,[],[f25]) ).
% 2.60/0.99  
% 2.60/0.99  cnf(c_409,plain,
% 2.60/0.99      ( r2_hidden(X0,X1) != iProver_top
% 2.60/0.99      | r2_hidden(X0,X2) != iProver_top
% 2.60/0.99      | r2_hidden(X0,k5_xboole_0(X2,X1)) != iProver_top ),
% 2.60/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.60/0.99  
% 2.60/0.99  cnf(c_1577,plain,
% 2.60/0.99      ( r2_hidden(X0,X1) != iProver_top
% 2.60/0.99      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.60/0.99      inference(superposition,[status(thm)],[c_6,c_409]) ).
% 2.60/0.99  
% 2.60/0.99  cnf(c_1702,plain,
% 2.60/0.99      ( X0 = X1
% 2.60/0.99      | r2_hidden(sK0(X0,X1),X1) = iProver_top
% 2.60/0.99      | r2_hidden(sK0(X0,X1),k1_xboole_0) != iProver_top ),
% 2.60/0.99      inference(superposition,[status(thm)],[c_406,c_1577]) ).
% 2.60/0.99  
% 2.60/0.99  cnf(c_1706,plain,
% 2.60/0.99      ( X0 = X1 | r2_hidden(sK0(X1,X0),k1_xboole_0) != iProver_top ),
% 2.60/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_1702,c_1577]) ).
% 2.60/0.99  
% 2.60/0.99  cnf(c_1717,plain,
% 2.60/0.99      ( k1_xboole_0 = X0 | r2_hidden(sK0(X0,k1_xboole_0),X0) = iProver_top ),
% 2.60/0.99      inference(superposition,[status(thm)],[c_406,c_1706]) ).
% 2.60/0.99  
% 2.60/0.99  cnf(c_7,plain,
% 2.60/0.99      ( ~ r2_hidden(X0,X1) | k1_funct_1(sK1(X1,X2),X0) = X2 ),
% 2.60/0.99      inference(cnf_transformation,[],[f34]) ).
% 2.60/0.99  
% 2.60/0.99  cnf(c_405,plain,
% 2.60/0.99      ( k1_funct_1(sK1(X0,X1),X2) = X1 | r2_hidden(X2,X0) != iProver_top ),
% 2.60/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.60/0.99  
% 2.60/0.99  cnf(c_1831,plain,
% 2.60/0.99      ( k1_funct_1(sK1(X0,X1),sK0(X0,k1_xboole_0)) = X1 | k1_xboole_0 = X0 ),
% 2.60/0.99      inference(superposition,[status(thm)],[c_1717,c_405]) ).
% 2.60/0.99  
% 2.60/0.99  cnf(c_2433,plain,
% 2.60/0.99      ( k1_funct_1(sK2(sK3),sK0(sK3,k1_xboole_0)) = X0 | sK3 = k1_xboole_0 ),
% 2.60/0.99      inference(superposition,[status(thm)],[c_1162,c_1831]) ).
% 2.60/0.99  
% 2.60/0.99  cnf(c_15,negated_conjecture,
% 2.60/0.99      ( k1_xboole_0 != sK3 ),
% 2.60/0.99      inference(cnf_transformation,[],[f40]) ).
% 2.60/0.99  
% 2.60/0.99  cnf(c_158,plain,( X0 = X0 ),theory(equality) ).
% 2.60/0.99  
% 2.60/0.99  cnf(c_173,plain,
% 2.60/0.99      ( k1_xboole_0 = k1_xboole_0 ),
% 2.60/0.99      inference(instantiation,[status(thm)],[c_158]) ).
% 2.60/0.99  
% 2.60/0.99  cnf(c_159,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.60/0.99  
% 2.60/0.99  cnf(c_547,plain,
% 2.60/0.99      ( sK3 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK3 ),
% 2.60/0.99      inference(instantiation,[status(thm)],[c_159]) ).
% 2.60/0.99  
% 2.60/0.99  cnf(c_548,plain,
% 2.60/0.99      ( sK3 != k1_xboole_0 | k1_xboole_0 = sK3 | k1_xboole_0 != k1_xboole_0 ),
% 2.60/0.99      inference(instantiation,[status(thm)],[c_547]) ).
% 2.60/0.99  
% 2.60/0.99  cnf(c_2488,plain,
% 2.60/0.99      ( k1_funct_1(sK2(sK3),sK0(sK3,k1_xboole_0)) = X0 ),
% 2.60/0.99      inference(global_propositional_subsumption,
% 2.60/0.99                [status(thm)],
% 2.60/0.99                [c_2433,c_15,c_173,c_548]) ).
% 2.60/0.99  
% 2.60/0.99  cnf(c_2494,plain,
% 2.60/0.99      ( X0 = X1 ),
% 2.60/0.99      inference(superposition,[status(thm)],[c_2488,c_2488]) ).
% 2.60/0.99  
% 2.60/0.99  cnf(c_2803,plain,
% 2.60/0.99      ( k1_xboole_0 != X0 ),
% 2.60/0.99      inference(superposition,[status(thm)],[c_2494,c_15]) ).
% 2.60/0.99  
% 2.60/0.99  cnf(c_2808,plain,
% 2.60/0.99      ( $false ),
% 2.60/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_2803,c_2494]) ).
% 2.60/0.99  
% 2.60/0.99  
% 2.60/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.60/0.99  
% 2.60/0.99  ------                               Statistics
% 2.60/0.99  
% 2.60/0.99  ------ General
% 2.60/0.99  
% 2.60/0.99  abstr_ref_over_cycles:                  0
% 2.60/0.99  abstr_ref_under_cycles:                 0
% 2.60/0.99  gc_basic_clause_elim:                   0
% 2.60/0.99  forced_gc_time:                         0
% 2.60/0.99  parsing_time:                           0.008
% 2.60/0.99  unif_index_cands_time:                  0.
% 2.60/0.99  unif_index_add_time:                    0.
% 2.60/0.99  orderings_time:                         0.
% 2.60/0.99  out_proof_time:                         0.012
% 2.60/0.99  total_time:                             0.112
% 2.60/0.99  num_of_symbols:                         42
% 2.60/0.99  num_of_terms:                           2278
% 2.60/0.99  
% 2.60/0.99  ------ Preprocessing
% 2.60/0.99  
% 2.60/0.99  num_of_splits:                          0
% 2.60/0.99  num_of_split_atoms:                     0
% 2.60/0.99  num_of_reused_defs:                     0
% 2.60/0.99  num_eq_ax_congr_red:                    14
% 2.60/0.99  num_of_sem_filtered_clauses:            1
% 2.60/0.99  num_of_subtypes:                        0
% 2.60/0.99  monotx_restored_types:                  0
% 2.60/0.99  sat_num_of_epr_types:                   0
% 2.60/0.99  sat_num_of_non_cyclic_types:            0
% 2.60/0.99  sat_guarded_non_collapsed_types:        0
% 2.60/0.99  num_pure_diseq_elim:                    0
% 2.60/0.99  simp_replaced_by:                       0
% 2.60/0.99  res_preprocessed:                       68
% 2.60/0.99  prep_upred:                             0
% 2.60/0.99  prep_unflattend:                        0
% 2.60/0.99  smt_new_axioms:                         0
% 2.60/0.99  pred_elim_cands:                        3
% 2.60/0.99  pred_elim:                              0
% 2.60/0.99  pred_elim_cl:                           0
% 2.60/0.99  pred_elim_cycles:                       1
% 2.60/0.99  merged_defs:                            0
% 2.60/0.99  merged_defs_ncl:                        0
% 2.60/0.99  bin_hyper_res:                          0
% 2.60/0.99  prep_cycles:                            3
% 2.60/0.99  pred_elim_time:                         0.
% 2.60/0.99  splitting_time:                         0.
% 2.60/0.99  sem_filter_time:                        0.
% 2.60/0.99  monotx_time:                            0.
% 2.60/0.99  subtype_inf_time:                       0.
% 2.60/0.99  
% 2.60/0.99  ------ Problem properties
% 2.60/0.99  
% 2.60/0.99  clauses:                                17
% 2.60/0.99  conjectures:                            2
% 2.60/0.99  epr:                                    1
% 2.60/0.99  horn:                                   13
% 2.60/0.99  ground:                                 1
% 2.60/0.99  unary:                                  8
% 2.60/0.99  binary:                                 2
% 2.60/0.99  lits:                                   37
% 2.60/0.99  lits_eq:                                11
% 2.60/0.99  fd_pure:                                0
% 2.60/0.99  fd_pseudo:                              0
% 2.60/0.99  fd_cond:                                0
% 2.60/0.99  fd_pseudo_cond:                         3
% 2.60/0.99  ac_symbols:                             0
% 2.60/0.99  
% 2.60/0.99  ------ Propositional Solver
% 2.60/0.99  
% 2.60/0.99  prop_solver_calls:                      24
% 2.60/0.99  prop_fast_solver_calls:                 432
% 2.60/0.99  smt_solver_calls:                       0
% 2.60/0.99  smt_fast_solver_calls:                  0
% 2.60/0.99  prop_num_of_clauses:                    885
% 2.60/0.99  prop_preprocess_simplified:             3027
% 2.60/0.99  prop_fo_subsumed:                       12
% 2.60/0.99  prop_solver_time:                       0.
% 2.60/0.99  smt_solver_time:                        0.
% 2.60/0.99  smt_fast_solver_time:                   0.
% 2.60/0.99  prop_fast_solver_time:                  0.
% 2.60/0.99  prop_unsat_core_time:                   0.
% 2.60/0.99  
% 2.60/0.99  ------ QBF
% 2.60/0.99  
% 2.60/0.99  qbf_q_res:                              0
% 2.60/0.99  qbf_num_tautologies:                    0
% 2.60/0.99  qbf_prep_cycles:                        0
% 2.60/0.99  
% 2.60/0.99  ------ BMC1
% 2.60/0.99  
% 2.60/0.99  bmc1_current_bound:                     -1
% 2.60/0.99  bmc1_last_solved_bound:                 -1
% 2.60/0.99  bmc1_unsat_core_size:                   -1
% 2.60/0.99  bmc1_unsat_core_parents_size:           -1
% 2.60/0.99  bmc1_merge_next_fun:                    0
% 2.60/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.60/0.99  
% 2.60/0.99  ------ Instantiation
% 2.60/0.99  
% 2.60/0.99  inst_num_of_clauses:                    269
% 2.60/0.99  inst_num_in_passive:                    118
% 2.60/0.99  inst_num_in_active:                     122
% 2.60/0.99  inst_num_in_unprocessed:                29
% 2.60/0.99  inst_num_of_loops:                      200
% 2.60/0.99  inst_num_of_learning_restarts:          0
% 2.60/0.99  inst_num_moves_active_passive:          75
% 2.60/0.99  inst_lit_activity:                      0
% 2.60/0.99  inst_lit_activity_moves:                0
% 2.60/0.99  inst_num_tautologies:                   0
% 2.60/0.99  inst_num_prop_implied:                  0
% 2.60/0.99  inst_num_existing_simplified:           0
% 2.60/0.99  inst_num_eq_res_simplified:             0
% 2.60/0.99  inst_num_child_elim:                    0
% 2.60/0.99  inst_num_of_dismatching_blockings:      116
% 2.60/0.99  inst_num_of_non_proper_insts:           241
% 2.60/0.99  inst_num_of_duplicates:                 0
% 2.60/0.99  inst_inst_num_from_inst_to_res:         0
% 2.60/0.99  inst_dismatching_checking_time:         0.
% 2.60/0.99  
% 2.60/0.99  ------ Resolution
% 2.60/0.99  
% 2.60/0.99  res_num_of_clauses:                     0
% 2.60/0.99  res_num_in_passive:                     0
% 2.60/0.99  res_num_in_active:                      0
% 2.60/0.99  res_num_of_loops:                       71
% 2.60/0.99  res_forward_subset_subsumed:            20
% 2.60/0.99  res_backward_subset_subsumed:           0
% 2.60/0.99  res_forward_subsumed:                   0
% 2.60/0.99  res_backward_subsumed:                  0
% 2.60/0.99  res_forward_subsumption_resolution:     0
% 2.60/0.99  res_backward_subsumption_resolution:    0
% 2.60/0.99  res_clause_to_clause_subsumption:       280
% 2.60/0.99  res_orphan_elimination:                 0
% 2.60/0.99  res_tautology_del:                      20
% 2.60/0.99  res_num_eq_res_simplified:              0
% 2.60/0.99  res_num_sel_changes:                    0
% 2.60/0.99  res_moves_from_active_to_pass:          0
% 2.60/0.99  
% 2.60/0.99  ------ Superposition
% 2.60/0.99  
% 2.60/0.99  sup_time_total:                         0.
% 2.60/0.99  sup_time_generating:                    0.
% 2.60/0.99  sup_time_sim_full:                      0.
% 2.60/0.99  sup_time_sim_immed:                     0.
% 2.60/0.99  
% 2.60/0.99  sup_num_of_clauses:                     30
% 2.60/0.99  sup_num_in_active:                      5
% 2.60/0.99  sup_num_in_passive:                     25
% 2.60/0.99  sup_num_of_loops:                       39
% 2.60/0.99  sup_fw_superposition:                   35
% 2.60/0.99  sup_bw_superposition:                   93
% 2.60/0.99  sup_immediate_simplified:               63
% 2.60/0.99  sup_given_eliminated:                   1
% 2.60/0.99  comparisons_done:                       0
% 2.60/0.99  comparisons_avoided:                    2
% 2.60/0.99  
% 2.60/0.99  ------ Simplifications
% 2.60/0.99  
% 2.60/0.99  
% 2.60/0.99  sim_fw_subset_subsumed:                 11
% 2.60/0.99  sim_bw_subset_subsumed:                 18
% 2.60/0.99  sim_fw_subsumed:                        59
% 2.60/0.99  sim_bw_subsumed:                        4
% 2.60/0.99  sim_fw_subsumption_res:                 15
% 2.60/0.99  sim_bw_subsumption_res:                 0
% 2.60/0.99  sim_tautology_del:                      12
% 2.60/0.99  sim_eq_tautology_del:                   6
% 2.60/0.99  sim_eq_res_simp:                        0
% 2.60/0.99  sim_fw_demodulated:                     3
% 2.60/0.99  sim_bw_demodulated:                     38
% 2.60/0.99  sim_light_normalised:                   6
% 2.60/0.99  sim_joinable_taut:                      0
% 2.60/0.99  sim_joinable_simp:                      0
% 2.60/0.99  sim_ac_normalised:                      0
% 2.60/0.99  sim_smt_subsumption:                    0
% 2.60/0.99  
%------------------------------------------------------------------------------
