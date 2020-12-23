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
% DateTime   : Thu Dec  3 11:49:26 EST 2020

% Result     : Theorem 3.68s
% Output     : CNFRefutation 3.68s
% Verified   : 
% Statistics : Number of formulae       :   98 (1318 expanded)
%              Number of clauses        :   65 ( 469 expanded)
%              Number of leaves         :   12 ( 323 expanded)
%              Depth                    :   25
%              Number of atoms          :  383 (6217 expanded)
%              Number of equality atoms :  256 (3289 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X0)
         => k1_funct_1(X2,X3) = X1 )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k1_funct_1(X2,X3) = X1
              | ~ r2_hidden(X3,X0) )
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( ! [X3] :
            ( k1_funct_1(sK3(X0,X1),X3) = X1
            | ~ r2_hidden(X3,X0) )
        & k1_relat_1(sK3(X0,X1)) = X0
        & v1_funct_1(sK3(X0,X1))
        & v1_relat_1(sK3(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X3] :
          ( k1_funct_1(sK3(X0,X1),X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(sK3(X0,X1)) = X0
      & v1_funct_1(sK3(X0,X1))
      & v1_relat_1(sK3(X0,X1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f11,f20])).

fof(f36,plain,(
    ! [X0,X1] : k1_relat_1(sK3(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f21])).

fof(f5,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
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
    inference(negated_conjecture,[],[f5])).

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
    inference(ennf_transformation,[],[f6])).

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
   => ( k1_xboole_0 != sK4
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != sK4
              | k1_relat_1(X1) != sK4
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( k1_xboole_0 != sK4
    & ! [X1] :
        ( ! [X2] :
            ( X1 = X2
            | k1_relat_1(X2) != sK4
            | k1_relat_1(X1) != sK4
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) )
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f13,f22])).

fof(f38,plain,(
    ! [X2,X1] :
      ( X1 = X2
      | k1_relat_1(X2) != sK4
      | k1_relat_1(X1) != sK4
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f34,plain,(
    ! [X0,X1] : v1_relat_1(sK3(X0,X1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f35,plain,(
    ! [X0,X1] : v1_funct_1(sK3(X0,X1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X2
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ? [X7] :
                      ( k1_funct_1(X0,X7) = X5
                      & r2_hidden(X7,k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f14])).

fof(f18,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X5)) = X5
        & r2_hidden(sK2(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK1(X0,X1)) = X2
        & r2_hidden(sK1(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( k1_funct_1(X0,X4) = X2
                & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( k1_funct_1(X0,X3) != sK0(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK0(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK0(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK0(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK1(X0,X1)) = sK0(X0,X1)
                  & r2_hidden(sK1(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK0(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK2(X0,X5)) = X5
                    & r2_hidden(sK2(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f18,f17,f16])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(sK1(X0,X1),k1_relat_1(X0))
      | r2_hidden(sK0(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f25,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f8,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(sK3(X0,X1),X3) = X1
      | ~ r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f39,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_11,plain,
    ( k1_relat_1(sK3(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_15,negated_conjecture,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | X0 = X1
    | k1_relat_1(X1) != sK4
    | k1_relat_1(X0) != sK4 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_3659,plain,
    ( X0 = X1
    | k1_relat_1(X1) != sK4
    | k1_relat_1(X0) != sK4
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3744,plain,
    ( sK3(X0,X1) = X2
    | k1_relat_1(X2) != sK4
    | sK4 != X0
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3(X0,X1)) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(sK3(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_3659])).

cnf(c_1037,plain,
    ( X0 = X1
    | k1_relat_1(X1) != sK4
    | k1_relat_1(X0) != sK4
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1080,plain,
    ( sK3(X0,X1) = X2
    | k1_relat_1(X2) != sK4
    | sK4 != X0
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3(X0,X1)) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(sK3(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_1037])).

cnf(c_13,plain,
    ( v1_relat_1(sK3(X0,X1)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_19,plain,
    ( v1_relat_1(sK3(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_12,plain,
    ( v1_funct_1(sK3(X0,X1)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_22,plain,
    ( v1_funct_1(sK3(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1085,plain,
    ( v1_relat_1(X2) != iProver_top
    | sK3(X0,X1) = X2
    | k1_relat_1(X2) != sK4
    | sK4 != X0
    | v1_funct_1(X2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1080,c_19,c_22])).

cnf(c_1086,plain,
    ( sK3(X0,X1) = X2
    | k1_relat_1(X2) != sK4
    | sK4 != X0
    | v1_funct_1(X2) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_1085])).

cnf(c_3751,plain,
    ( v1_relat_1(X2) != iProver_top
    | sK3(X0,X1) = X2
    | k1_relat_1(X2) != sK4
    | sK4 != X0
    | v1_funct_1(X2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3744,c_19,c_22,c_1080])).

cnf(c_3752,plain,
    ( sK3(X0,X1) = X2
    | k1_relat_1(X2) != sK4
    | sK4 != X0
    | v1_funct_1(X2) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_3751])).

cnf(c_3761,plain,
    ( sK3(X0,X1) = sK3(X2,X3)
    | sK4 != X0
    | sK4 != X2
    | v1_funct_1(sK3(X0,X1)) != iProver_top
    | v1_relat_1(sK3(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_3752])).

cnf(c_1096,plain,
    ( sK3(X0,X1) = sK3(X2,X3)
    | sK4 != X0
    | sK4 != X2
    | v1_funct_1(sK3(X0,X1)) != iProver_top
    | v1_relat_1(sK3(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_1086])).

cnf(c_1097,plain,
    ( ~ v1_funct_1(sK3(X0,X1))
    | ~ v1_relat_1(sK3(X0,X1))
    | sK3(X0,X1) = sK3(X2,X3)
    | sK4 != X0
    | sK4 != X2 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1096])).

cnf(c_1106,plain,
    ( sK3(X0,X1) = sK3(X2,X3)
    | sK4 != X0
    | sK4 != X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1096,c_13,c_12,c_1097])).

cnf(c_3774,plain,
    ( sK3(X0,X1) = sK3(X2,X3)
    | sK4 != X0
    | sK4 != X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3761,c_13,c_12,c_1097])).

cnf(c_3779,plain,
    ( sK3(X0,X1) = sK3(sK4,X2)
    | sK4 != X0 ),
    inference(equality_resolution,[status(thm)],[c_3774])).

cnf(c_3821,plain,
    ( sK3(sK4,X0) = sK3(sK4,X1) ),
    inference(equality_resolution,[status(thm)],[c_3779])).

cnf(c_1,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_6,plain,
    ( r2_hidden(sK1(X0,X1),k1_relat_1(X0))
    | r2_hidden(sK0(X0,X1),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_3663,plain,
    ( k2_relat_1(X0) = X1
    | r2_hidden(sK1(X0,X1),k1_relat_1(X0)) = iProver_top
    | r2_hidden(sK0(X0,X1),X1) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3871,plain,
    ( k2_relat_1(k1_xboole_0) = X0
    | r2_hidden(sK1(k1_xboole_0,X0),k1_xboole_0) = iProver_top
    | r2_hidden(sK0(k1_xboole_0,X0),X0) = iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_3663])).

cnf(c_0,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_3910,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(k1_xboole_0,X0),k1_xboole_0) = iProver_top
    | r2_hidden(sK0(k1_xboole_0,X0),X0) = iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3871,c_0])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_2873,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3086,plain,
    ( sK3(X0,X1) = k1_xboole_0
    | k1_xboole_0 != X0
    | v1_relat_1(sK3(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_2873])).

cnf(c_3148,plain,
    ( k1_xboole_0 != X0
    | sK3(X0,X1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3086,c_19])).

cnf(c_3149,plain,
    ( sK3(X0,X1) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(renaming,[status(thm)],[c_3148])).

cnf(c_3153,plain,
    ( sK3(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_3149])).

cnf(c_2872,plain,
    ( v1_funct_1(sK3(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3158,plain,
    ( v1_funct_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3153,c_2872])).

cnf(c_2871,plain,
    ( v1_relat_1(sK3(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3159,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3153,c_2871])).

cnf(c_3923,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(k1_xboole_0,X0),k1_xboole_0) = iProver_top
    | r2_hidden(sK0(k1_xboole_0,X0),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3910,c_3158,c_3159])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_funct_1(sK3(X1,X2),X0) = X2 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_3662,plain,
    ( k1_funct_1(sK3(X0,X1),X2) = X1
    | r2_hidden(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3931,plain,
    ( k1_funct_1(sK3(k1_xboole_0,X0),sK1(k1_xboole_0,X1)) = X0
    | k1_xboole_0 = X1
    | r2_hidden(sK0(k1_xboole_0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3923,c_3662])).

cnf(c_3664,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3802,plain,
    ( sK3(X0,X1) = k1_xboole_0
    | k1_xboole_0 != X0
    | v1_relat_1(sK3(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_3664])).

cnf(c_3811,plain,
    ( k1_xboole_0 != X0
    | sK3(X0,X1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3802,c_19,c_3086])).

cnf(c_3812,plain,
    ( sK3(X0,X1) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(renaming,[status(thm)],[c_3811])).

cnf(c_3815,plain,
    ( sK3(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_3812])).

cnf(c_3935,plain,
    ( k1_funct_1(k1_xboole_0,sK1(k1_xboole_0,X0)) = X1
    | k1_xboole_0 = X0
    | r2_hidden(sK0(k1_xboole_0,X0),X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3931,c_3815])).

cnf(c_3951,plain,
    ( k1_funct_1(sK3(X0,X1),sK0(k1_xboole_0,X0)) = X1
    | k1_funct_1(k1_xboole_0,sK1(k1_xboole_0,X0)) = X2
    | k1_xboole_0 = X0 ),
    inference(superposition,[status(thm)],[c_3935,c_3662])).

cnf(c_4033,plain,
    ( k1_funct_1(sK3(sK4,X0),sK0(k1_xboole_0,sK4)) = X1
    | k1_funct_1(k1_xboole_0,sK1(k1_xboole_0,sK4)) = X2
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3821,c_3951])).

cnf(c_14,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_148,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_163,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_148])).

cnf(c_149,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3006,plain,
    ( sK4 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_149])).

cnf(c_3007,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3006])).

cnf(c_4397,plain,
    ( k1_funct_1(k1_xboole_0,sK1(k1_xboole_0,sK4)) = X2
    | k1_funct_1(sK3(sK4,X0),sK0(k1_xboole_0,sK4)) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4033,c_14,c_163,c_3007])).

cnf(c_4398,plain,
    ( k1_funct_1(sK3(sK4,X0),sK0(k1_xboole_0,sK4)) = X1
    | k1_funct_1(k1_xboole_0,sK1(k1_xboole_0,sK4)) = X2 ),
    inference(renaming,[status(thm)],[c_4397])).

cnf(c_4473,plain,
    ( k1_funct_1(sK3(sK4,X0),sK0(k1_xboole_0,sK4)) = X1
    | k1_funct_1(k1_xboole_0,sK1(k1_xboole_0,sK4)) != X1 ),
    inference(equality_factoring,[status(thm)],[c_4398])).

cnf(c_4476,plain,
    ( k1_funct_1(sK3(sK4,X0),sK0(k1_xboole_0,sK4)) = X1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4473,c_4398])).

cnf(c_4743,plain,
    ( k1_funct_1(sK3(sK4,X0),sK0(k1_xboole_0,sK4)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4476,c_3815])).

cnf(c_4749,plain,
    ( k1_funct_1(sK3(sK4,X0),sK0(k1_xboole_0,sK4)) = sK3(sK4,X1) ),
    inference(superposition,[status(thm)],[c_4476,c_3821])).

cnf(c_5113,plain,
    ( sK3(sK4,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4743,c_4749])).

cnf(c_5554,plain,
    ( k1_relat_1(k1_xboole_0) = sK4 ),
    inference(superposition,[status(thm)],[c_5113,c_11])).

cnf(c_5556,plain,
    ( sK4 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5554,c_1])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5556,c_3007,c_163,c_14])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:28:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.68/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.68/1.00  
% 3.68/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.68/1.00  
% 3.68/1.00  ------  iProver source info
% 3.68/1.00  
% 3.68/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.68/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.68/1.00  git: non_committed_changes: false
% 3.68/1.00  git: last_make_outside_of_git: false
% 3.68/1.00  
% 3.68/1.00  ------ 
% 3.68/1.00  ------ Parsing...
% 3.68/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.68/1.00  
% 3.68/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.68/1.00  
% 3.68/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.68/1.00  
% 3.68/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.68/1.00  ------ Proving...
% 3.68/1.00  ------ Problem Properties 
% 3.68/1.00  
% 3.68/1.00  
% 3.68/1.00  clauses                                 16
% 3.68/1.00  conjectures                             2
% 3.68/1.00  EPR                                     1
% 3.68/1.00  Horn                                    14
% 3.68/1.00  unary                                   6
% 3.68/1.00  binary                                  1
% 3.68/1.00  lits                                    49
% 3.68/1.00  lits eq                                 18
% 3.68/1.00  fd_pure                                 0
% 3.68/1.00  fd_pseudo                               0
% 3.68/1.00  fd_cond                                 2
% 3.68/1.00  fd_pseudo_cond                          4
% 3.68/1.00  AC symbols                              0
% 3.68/1.00  
% 3.68/1.00  ------ Input Options Time Limit: Unbounded
% 3.68/1.00  
% 3.68/1.00  
% 3.68/1.00  
% 3.68/1.00  
% 3.68/1.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.68/1.00  Current options:
% 3.68/1.00  ------ 
% 3.68/1.00  
% 3.68/1.00  
% 3.68/1.00  
% 3.68/1.00  
% 3.68/1.00  ------ Proving...
% 3.68/1.00  
% 3.68/1.00  
% 3.68/1.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.68/1.00  
% 3.68/1.00  ------ Proving...
% 3.68/1.00  
% 3.68/1.00  
% 3.68/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.68/1.00  
% 3.68/1.00  ------ Proving...
% 3.68/1.00  
% 3.68/1.00  
% 3.68/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.68/1.00  
% 3.68/1.00  ------ Proving...
% 3.68/1.00  
% 3.68/1.00  
% 3.68/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.68/1.00  
% 3.68/1.00  ------ Proving...
% 3.68/1.00  
% 3.68/1.00  
% 3.68/1.00  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.68/1.00  
% 3.68/1.00  ------ Proving...
% 3.68/1.00  
% 3.68/1.00  
% 3.68/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.68/1.00  
% 3.68/1.00  ------ Proving...
% 3.68/1.00  
% 3.68/1.00  
% 3.68/1.00  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.68/1.00  
% 3.68/1.00  ------ Proving...
% 3.68/1.00  
% 3.68/1.00  
% 3.68/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.68/1.00  
% 3.68/1.00  ------ Proving...
% 3.68/1.00  
% 3.68/1.00  
% 3.68/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.68/1.00  
% 3.68/1.00  ------ Proving...
% 3.68/1.00  
% 3.68/1.00  
% 3.68/1.00  % SZS status Theorem for theBenchmark.p
% 3.68/1.00  
% 3.68/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.68/1.00  
% 3.68/1.00  fof(f4,axiom,(
% 3.68/1.00    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 3.68/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/1.00  
% 3.68/1.00  fof(f11,plain,(
% 3.68/1.00    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 3.68/1.00    inference(ennf_transformation,[],[f4])).
% 3.68/1.00  
% 3.68/1.00  fof(f20,plain,(
% 3.68/1.00    ! [X1,X0] : (? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (! [X3] : (k1_funct_1(sK3(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK3(X0,X1)) = X0 & v1_funct_1(sK3(X0,X1)) & v1_relat_1(sK3(X0,X1))))),
% 3.68/1.00    introduced(choice_axiom,[])).
% 3.68/1.00  
% 3.68/1.00  fof(f21,plain,(
% 3.68/1.00    ! [X0,X1] : (! [X3] : (k1_funct_1(sK3(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK3(X0,X1)) = X0 & v1_funct_1(sK3(X0,X1)) & v1_relat_1(sK3(X0,X1)))),
% 3.68/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f11,f20])).
% 3.68/1.00  
% 3.68/1.00  fof(f36,plain,(
% 3.68/1.00    ( ! [X0,X1] : (k1_relat_1(sK3(X0,X1)) = X0) )),
% 3.68/1.00    inference(cnf_transformation,[],[f21])).
% 3.68/1.00  
% 3.68/1.00  fof(f5,conjecture,(
% 3.68/1.00    ! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 3.68/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/1.00  
% 3.68/1.00  fof(f6,negated_conjecture,(
% 3.68/1.00    ~! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 3.68/1.00    inference(negated_conjecture,[],[f5])).
% 3.68/1.00  
% 3.68/1.00  fof(f12,plain,(
% 3.68/1.00    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : ((X1 = X2 | (k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))))),
% 3.68/1.00    inference(ennf_transformation,[],[f6])).
% 3.68/1.00  
% 3.68/1.00  fof(f13,plain,(
% 3.68/1.00    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.68/1.00    inference(flattening,[],[f12])).
% 3.68/1.00  
% 3.68/1.00  fof(f22,plain,(
% 3.68/1.00    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) => (k1_xboole_0 != sK4 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != sK4 | k1_relat_1(X1) != sK4 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.68/1.00    introduced(choice_axiom,[])).
% 3.68/1.00  
% 3.68/1.00  fof(f23,plain,(
% 3.68/1.00    k1_xboole_0 != sK4 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != sK4 | k1_relat_1(X1) != sK4 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.68/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f13,f22])).
% 3.68/1.00  
% 3.68/1.00  fof(f38,plain,(
% 3.68/1.00    ( ! [X2,X1] : (X1 = X2 | k1_relat_1(X2) != sK4 | k1_relat_1(X1) != sK4 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.68/1.00    inference(cnf_transformation,[],[f23])).
% 3.68/1.00  
% 3.68/1.00  fof(f34,plain,(
% 3.68/1.00    ( ! [X0,X1] : (v1_relat_1(sK3(X0,X1))) )),
% 3.68/1.00    inference(cnf_transformation,[],[f21])).
% 3.68/1.00  
% 3.68/1.00  fof(f35,plain,(
% 3.68/1.00    ( ! [X0,X1] : (v1_funct_1(sK3(X0,X1))) )),
% 3.68/1.00    inference(cnf_transformation,[],[f21])).
% 3.68/1.00  
% 3.68/1.00  fof(f1,axiom,(
% 3.68/1.00    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.68/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/1.00  
% 3.68/1.00  fof(f24,plain,(
% 3.68/1.00    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.68/1.00    inference(cnf_transformation,[],[f1])).
% 3.68/1.00  
% 3.68/1.00  fof(f3,axiom,(
% 3.68/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 3.68/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/1.00  
% 3.68/1.00  fof(f9,plain,(
% 3.68/1.00    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.68/1.00    inference(ennf_transformation,[],[f3])).
% 3.68/1.00  
% 3.68/1.00  fof(f10,plain,(
% 3.68/1.00    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.68/1.00    inference(flattening,[],[f9])).
% 3.68/1.00  
% 3.68/1.00  fof(f14,plain,(
% 3.68/1.00    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.68/1.00    inference(nnf_transformation,[],[f10])).
% 3.68/1.00  
% 3.68/1.00  fof(f15,plain,(
% 3.68/1.00    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.68/1.00    inference(rectify,[],[f14])).
% 3.68/1.00  
% 3.68/1.00  fof(f18,plain,(
% 3.68/1.00    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X5)) = X5 & r2_hidden(sK2(X0,X5),k1_relat_1(X0))))),
% 3.68/1.00    introduced(choice_axiom,[])).
% 3.68/1.00  
% 3.68/1.00  fof(f17,plain,(
% 3.68/1.00    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK1(X0,X1)) = X2 & r2_hidden(sK1(X0,X1),k1_relat_1(X0))))) )),
% 3.68/1.00    introduced(choice_axiom,[])).
% 3.68/1.00  
% 3.68/1.00  fof(f16,plain,(
% 3.68/1.00    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK0(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK0(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK0(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK0(X0,X1),X1))))),
% 3.68/1.00    introduced(choice_axiom,[])).
% 3.68/1.00  
% 3.68/1.00  fof(f19,plain,(
% 3.68/1.00    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK0(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK0(X0,X1),X1)) & ((k1_funct_1(X0,sK1(X0,X1)) = sK0(X0,X1) & r2_hidden(sK1(X0,X1),k1_relat_1(X0))) | r2_hidden(sK0(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK2(X0,X5)) = X5 & r2_hidden(sK2(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.68/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f18,f17,f16])).
% 3.68/1.00  
% 3.68/1.00  fof(f31,plain,(
% 3.68/1.00    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | r2_hidden(sK1(X0,X1),k1_relat_1(X0)) | r2_hidden(sK0(X0,X1),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.68/1.00    inference(cnf_transformation,[],[f19])).
% 3.68/1.00  
% 3.68/1.00  fof(f25,plain,(
% 3.68/1.00    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 3.68/1.00    inference(cnf_transformation,[],[f1])).
% 3.68/1.00  
% 3.68/1.00  fof(f2,axiom,(
% 3.68/1.00    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 3.68/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/1.00  
% 3.68/1.00  fof(f7,plain,(
% 3.68/1.00    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.68/1.00    inference(ennf_transformation,[],[f2])).
% 3.68/1.00  
% 3.68/1.00  fof(f8,plain,(
% 3.68/1.00    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.68/1.00    inference(flattening,[],[f7])).
% 3.68/1.00  
% 3.68/1.00  fof(f26,plain,(
% 3.68/1.00    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.68/1.00    inference(cnf_transformation,[],[f8])).
% 3.68/1.00  
% 3.68/1.00  fof(f37,plain,(
% 3.68/1.00    ( ! [X0,X3,X1] : (k1_funct_1(sK3(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) )),
% 3.68/1.00    inference(cnf_transformation,[],[f21])).
% 3.68/1.00  
% 3.68/1.00  fof(f39,plain,(
% 3.68/1.00    k1_xboole_0 != sK4),
% 3.68/1.00    inference(cnf_transformation,[],[f23])).
% 3.68/1.00  
% 3.68/1.00  cnf(c_11,plain,
% 3.68/1.00      ( k1_relat_1(sK3(X0,X1)) = X0 ),
% 3.68/1.00      inference(cnf_transformation,[],[f36]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_15,negated_conjecture,
% 3.68/1.00      ( ~ v1_funct_1(X0)
% 3.68/1.00      | ~ v1_funct_1(X1)
% 3.68/1.00      | ~ v1_relat_1(X0)
% 3.68/1.00      | ~ v1_relat_1(X1)
% 3.68/1.00      | X0 = X1
% 3.68/1.00      | k1_relat_1(X1) != sK4
% 3.68/1.00      | k1_relat_1(X0) != sK4 ),
% 3.68/1.00      inference(cnf_transformation,[],[f38]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_3659,plain,
% 3.68/1.00      ( X0 = X1
% 3.68/1.00      | k1_relat_1(X1) != sK4
% 3.68/1.00      | k1_relat_1(X0) != sK4
% 3.68/1.00      | v1_funct_1(X0) != iProver_top
% 3.68/1.00      | v1_funct_1(X1) != iProver_top
% 3.68/1.00      | v1_relat_1(X0) != iProver_top
% 3.68/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.68/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_3744,plain,
% 3.68/1.00      ( sK3(X0,X1) = X2
% 3.68/1.00      | k1_relat_1(X2) != sK4
% 3.68/1.00      | sK4 != X0
% 3.68/1.00      | v1_funct_1(X2) != iProver_top
% 3.68/1.00      | v1_funct_1(sK3(X0,X1)) != iProver_top
% 3.68/1.00      | v1_relat_1(X2) != iProver_top
% 3.68/1.00      | v1_relat_1(sK3(X0,X1)) != iProver_top ),
% 3.68/1.00      inference(superposition,[status(thm)],[c_11,c_3659]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_1037,plain,
% 3.68/1.00      ( X0 = X1
% 3.68/1.00      | k1_relat_1(X1) != sK4
% 3.68/1.00      | k1_relat_1(X0) != sK4
% 3.68/1.00      | v1_funct_1(X0) != iProver_top
% 3.68/1.00      | v1_funct_1(X1) != iProver_top
% 3.68/1.00      | v1_relat_1(X0) != iProver_top
% 3.68/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.68/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_1080,plain,
% 3.68/1.00      ( sK3(X0,X1) = X2
% 3.68/1.00      | k1_relat_1(X2) != sK4
% 3.68/1.00      | sK4 != X0
% 3.68/1.00      | v1_funct_1(X2) != iProver_top
% 3.68/1.00      | v1_funct_1(sK3(X0,X1)) != iProver_top
% 3.68/1.00      | v1_relat_1(X2) != iProver_top
% 3.68/1.00      | v1_relat_1(sK3(X0,X1)) != iProver_top ),
% 3.68/1.00      inference(superposition,[status(thm)],[c_11,c_1037]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_13,plain,
% 3.68/1.00      ( v1_relat_1(sK3(X0,X1)) ),
% 3.68/1.00      inference(cnf_transformation,[],[f34]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_19,plain,
% 3.68/1.00      ( v1_relat_1(sK3(X0,X1)) = iProver_top ),
% 3.68/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_12,plain,
% 3.68/1.00      ( v1_funct_1(sK3(X0,X1)) ),
% 3.68/1.00      inference(cnf_transformation,[],[f35]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_22,plain,
% 3.68/1.00      ( v1_funct_1(sK3(X0,X1)) = iProver_top ),
% 3.68/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_1085,plain,
% 3.68/1.00      ( v1_relat_1(X2) != iProver_top
% 3.68/1.00      | sK3(X0,X1) = X2
% 3.68/1.00      | k1_relat_1(X2) != sK4
% 3.68/1.00      | sK4 != X0
% 3.68/1.00      | v1_funct_1(X2) != iProver_top ),
% 3.68/1.00      inference(global_propositional_subsumption,
% 3.68/1.00                [status(thm)],
% 3.68/1.00                [c_1080,c_19,c_22]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_1086,plain,
% 3.68/1.00      ( sK3(X0,X1) = X2
% 3.68/1.00      | k1_relat_1(X2) != sK4
% 3.68/1.00      | sK4 != X0
% 3.68/1.00      | v1_funct_1(X2) != iProver_top
% 3.68/1.00      | v1_relat_1(X2) != iProver_top ),
% 3.68/1.00      inference(renaming,[status(thm)],[c_1085]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_3751,plain,
% 3.68/1.00      ( v1_relat_1(X2) != iProver_top
% 3.68/1.00      | sK3(X0,X1) = X2
% 3.68/1.00      | k1_relat_1(X2) != sK4
% 3.68/1.00      | sK4 != X0
% 3.68/1.00      | v1_funct_1(X2) != iProver_top ),
% 3.68/1.00      inference(global_propositional_subsumption,
% 3.68/1.00                [status(thm)],
% 3.68/1.00                [c_3744,c_19,c_22,c_1080]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_3752,plain,
% 3.68/1.00      ( sK3(X0,X1) = X2
% 3.68/1.00      | k1_relat_1(X2) != sK4
% 3.68/1.00      | sK4 != X0
% 3.68/1.00      | v1_funct_1(X2) != iProver_top
% 3.68/1.00      | v1_relat_1(X2) != iProver_top ),
% 3.68/1.00      inference(renaming,[status(thm)],[c_3751]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_3761,plain,
% 3.68/1.00      ( sK3(X0,X1) = sK3(X2,X3)
% 3.68/1.00      | sK4 != X0
% 3.68/1.00      | sK4 != X2
% 3.68/1.00      | v1_funct_1(sK3(X0,X1)) != iProver_top
% 3.68/1.00      | v1_relat_1(sK3(X0,X1)) != iProver_top ),
% 3.68/1.00      inference(superposition,[status(thm)],[c_11,c_3752]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_1096,plain,
% 3.68/1.00      ( sK3(X0,X1) = sK3(X2,X3)
% 3.68/1.00      | sK4 != X0
% 3.68/1.00      | sK4 != X2
% 3.68/1.00      | v1_funct_1(sK3(X0,X1)) != iProver_top
% 3.68/1.00      | v1_relat_1(sK3(X0,X1)) != iProver_top ),
% 3.68/1.00      inference(superposition,[status(thm)],[c_11,c_1086]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_1097,plain,
% 3.68/1.00      ( ~ v1_funct_1(sK3(X0,X1))
% 3.68/1.00      | ~ v1_relat_1(sK3(X0,X1))
% 3.68/1.00      | sK3(X0,X1) = sK3(X2,X3)
% 3.68/1.00      | sK4 != X0
% 3.68/1.00      | sK4 != X2 ),
% 3.68/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1096]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_1106,plain,
% 3.68/1.00      ( sK3(X0,X1) = sK3(X2,X3) | sK4 != X0 | sK4 != X2 ),
% 3.68/1.00      inference(global_propositional_subsumption,
% 3.68/1.00                [status(thm)],
% 3.68/1.00                [c_1096,c_13,c_12,c_1097]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_3774,plain,
% 3.68/1.00      ( sK3(X0,X1) = sK3(X2,X3) | sK4 != X0 | sK4 != X2 ),
% 3.68/1.00      inference(global_propositional_subsumption,
% 3.68/1.00                [status(thm)],
% 3.68/1.00                [c_3761,c_13,c_12,c_1097]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_3779,plain,
% 3.68/1.00      ( sK3(X0,X1) = sK3(sK4,X2) | sK4 != X0 ),
% 3.68/1.00      inference(equality_resolution,[status(thm)],[c_3774]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_3821,plain,
% 3.68/1.00      ( sK3(sK4,X0) = sK3(sK4,X1) ),
% 3.68/1.00      inference(equality_resolution,[status(thm)],[c_3779]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_1,plain,
% 3.68/1.00      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.68/1.00      inference(cnf_transformation,[],[f24]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_6,plain,
% 3.68/1.00      ( r2_hidden(sK1(X0,X1),k1_relat_1(X0))
% 3.68/1.00      | r2_hidden(sK0(X0,X1),X1)
% 3.68/1.00      | ~ v1_funct_1(X0)
% 3.68/1.00      | ~ v1_relat_1(X0)
% 3.68/1.00      | k2_relat_1(X0) = X1 ),
% 3.68/1.00      inference(cnf_transformation,[],[f31]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_3663,plain,
% 3.68/1.00      ( k2_relat_1(X0) = X1
% 3.68/1.00      | r2_hidden(sK1(X0,X1),k1_relat_1(X0)) = iProver_top
% 3.68/1.00      | r2_hidden(sK0(X0,X1),X1) = iProver_top
% 3.68/1.00      | v1_funct_1(X0) != iProver_top
% 3.68/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.68/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_3871,plain,
% 3.68/1.00      ( k2_relat_1(k1_xboole_0) = X0
% 3.68/1.00      | r2_hidden(sK1(k1_xboole_0,X0),k1_xboole_0) = iProver_top
% 3.68/1.00      | r2_hidden(sK0(k1_xboole_0,X0),X0) = iProver_top
% 3.68/1.00      | v1_funct_1(k1_xboole_0) != iProver_top
% 3.68/1.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.68/1.00      inference(superposition,[status(thm)],[c_1,c_3663]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_0,plain,
% 3.68/1.00      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.68/1.00      inference(cnf_transformation,[],[f25]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_3910,plain,
% 3.68/1.00      ( k1_xboole_0 = X0
% 3.68/1.00      | r2_hidden(sK1(k1_xboole_0,X0),k1_xboole_0) = iProver_top
% 3.68/1.00      | r2_hidden(sK0(k1_xboole_0,X0),X0) = iProver_top
% 3.68/1.00      | v1_funct_1(k1_xboole_0) != iProver_top
% 3.68/1.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.68/1.00      inference(demodulation,[status(thm)],[c_3871,c_0]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_3,plain,
% 3.68/1.00      ( ~ v1_relat_1(X0)
% 3.68/1.00      | k1_relat_1(X0) != k1_xboole_0
% 3.68/1.00      | k1_xboole_0 = X0 ),
% 3.68/1.00      inference(cnf_transformation,[],[f26]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_2873,plain,
% 3.68/1.00      ( k1_relat_1(X0) != k1_xboole_0
% 3.68/1.00      | k1_xboole_0 = X0
% 3.68/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.68/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_3086,plain,
% 3.68/1.00      ( sK3(X0,X1) = k1_xboole_0
% 3.68/1.00      | k1_xboole_0 != X0
% 3.68/1.00      | v1_relat_1(sK3(X0,X1)) != iProver_top ),
% 3.68/1.00      inference(superposition,[status(thm)],[c_11,c_2873]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_3148,plain,
% 3.68/1.00      ( k1_xboole_0 != X0 | sK3(X0,X1) = k1_xboole_0 ),
% 3.68/1.00      inference(global_propositional_subsumption,
% 3.68/1.00                [status(thm)],
% 3.68/1.00                [c_3086,c_19]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_3149,plain,
% 3.68/1.00      ( sK3(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0 ),
% 3.68/1.00      inference(renaming,[status(thm)],[c_3148]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_3153,plain,
% 3.68/1.00      ( sK3(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.68/1.00      inference(equality_resolution,[status(thm)],[c_3149]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_2872,plain,
% 3.68/1.00      ( v1_funct_1(sK3(X0,X1)) = iProver_top ),
% 3.68/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_3158,plain,
% 3.68/1.00      ( v1_funct_1(k1_xboole_0) = iProver_top ),
% 3.68/1.00      inference(superposition,[status(thm)],[c_3153,c_2872]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_2871,plain,
% 3.68/1.00      ( v1_relat_1(sK3(X0,X1)) = iProver_top ),
% 3.68/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_3159,plain,
% 3.68/1.00      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.68/1.00      inference(superposition,[status(thm)],[c_3153,c_2871]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_3923,plain,
% 3.68/1.00      ( k1_xboole_0 = X0
% 3.68/1.00      | r2_hidden(sK1(k1_xboole_0,X0),k1_xboole_0) = iProver_top
% 3.68/1.00      | r2_hidden(sK0(k1_xboole_0,X0),X0) = iProver_top ),
% 3.68/1.00      inference(global_propositional_subsumption,
% 3.68/1.00                [status(thm)],
% 3.68/1.00                [c_3910,c_3158,c_3159]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_10,plain,
% 3.68/1.00      ( ~ r2_hidden(X0,X1) | k1_funct_1(sK3(X1,X2),X0) = X2 ),
% 3.68/1.00      inference(cnf_transformation,[],[f37]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_3662,plain,
% 3.68/1.00      ( k1_funct_1(sK3(X0,X1),X2) = X1
% 3.68/1.00      | r2_hidden(X2,X0) != iProver_top ),
% 3.68/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_3931,plain,
% 3.68/1.00      ( k1_funct_1(sK3(k1_xboole_0,X0),sK1(k1_xboole_0,X1)) = X0
% 3.68/1.00      | k1_xboole_0 = X1
% 3.68/1.00      | r2_hidden(sK0(k1_xboole_0,X1),X1) = iProver_top ),
% 3.68/1.00      inference(superposition,[status(thm)],[c_3923,c_3662]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_3664,plain,
% 3.68/1.00      ( k1_relat_1(X0) != k1_xboole_0
% 3.68/1.00      | k1_xboole_0 = X0
% 3.68/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.68/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_3802,plain,
% 3.68/1.00      ( sK3(X0,X1) = k1_xboole_0
% 3.68/1.00      | k1_xboole_0 != X0
% 3.68/1.00      | v1_relat_1(sK3(X0,X1)) != iProver_top ),
% 3.68/1.00      inference(superposition,[status(thm)],[c_11,c_3664]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_3811,plain,
% 3.68/1.00      ( k1_xboole_0 != X0 | sK3(X0,X1) = k1_xboole_0 ),
% 3.68/1.00      inference(global_propositional_subsumption,
% 3.68/1.00                [status(thm)],
% 3.68/1.00                [c_3802,c_19,c_3086]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_3812,plain,
% 3.68/1.00      ( sK3(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0 ),
% 3.68/1.00      inference(renaming,[status(thm)],[c_3811]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_3815,plain,
% 3.68/1.00      ( sK3(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.68/1.00      inference(equality_resolution,[status(thm)],[c_3812]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_3935,plain,
% 3.68/1.00      ( k1_funct_1(k1_xboole_0,sK1(k1_xboole_0,X0)) = X1
% 3.68/1.00      | k1_xboole_0 = X0
% 3.68/1.00      | r2_hidden(sK0(k1_xboole_0,X0),X0) = iProver_top ),
% 3.68/1.00      inference(light_normalisation,[status(thm)],[c_3931,c_3815]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_3951,plain,
% 3.68/1.00      ( k1_funct_1(sK3(X0,X1),sK0(k1_xboole_0,X0)) = X1
% 3.68/1.00      | k1_funct_1(k1_xboole_0,sK1(k1_xboole_0,X0)) = X2
% 3.68/1.00      | k1_xboole_0 = X0 ),
% 3.68/1.00      inference(superposition,[status(thm)],[c_3935,c_3662]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_4033,plain,
% 3.68/1.00      ( k1_funct_1(sK3(sK4,X0),sK0(k1_xboole_0,sK4)) = X1
% 3.68/1.00      | k1_funct_1(k1_xboole_0,sK1(k1_xboole_0,sK4)) = X2
% 3.68/1.00      | sK4 = k1_xboole_0 ),
% 3.68/1.00      inference(superposition,[status(thm)],[c_3821,c_3951]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_14,negated_conjecture,
% 3.68/1.00      ( k1_xboole_0 != sK4 ),
% 3.68/1.00      inference(cnf_transformation,[],[f39]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_148,plain,( X0 = X0 ),theory(equality) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_163,plain,
% 3.68/1.00      ( k1_xboole_0 = k1_xboole_0 ),
% 3.68/1.00      inference(instantiation,[status(thm)],[c_148]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_149,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_3006,plain,
% 3.68/1.00      ( sK4 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK4 ),
% 3.68/1.00      inference(instantiation,[status(thm)],[c_149]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_3007,plain,
% 3.68/1.00      ( sK4 != k1_xboole_0
% 3.68/1.00      | k1_xboole_0 = sK4
% 3.68/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.68/1.00      inference(instantiation,[status(thm)],[c_3006]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_4397,plain,
% 3.68/1.00      ( k1_funct_1(k1_xboole_0,sK1(k1_xboole_0,sK4)) = X2
% 3.68/1.00      | k1_funct_1(sK3(sK4,X0),sK0(k1_xboole_0,sK4)) = X1 ),
% 3.68/1.00      inference(global_propositional_subsumption,
% 3.68/1.00                [status(thm)],
% 3.68/1.00                [c_4033,c_14,c_163,c_3007]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_4398,plain,
% 3.68/1.00      ( k1_funct_1(sK3(sK4,X0),sK0(k1_xboole_0,sK4)) = X1
% 3.68/1.00      | k1_funct_1(k1_xboole_0,sK1(k1_xboole_0,sK4)) = X2 ),
% 3.68/1.00      inference(renaming,[status(thm)],[c_4397]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_4473,plain,
% 3.68/1.00      ( k1_funct_1(sK3(sK4,X0),sK0(k1_xboole_0,sK4)) = X1
% 3.68/1.00      | k1_funct_1(k1_xboole_0,sK1(k1_xboole_0,sK4)) != X1 ),
% 3.68/1.00      inference(equality_factoring,[status(thm)],[c_4398]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_4476,plain,
% 3.68/1.00      ( k1_funct_1(sK3(sK4,X0),sK0(k1_xboole_0,sK4)) = X1 ),
% 3.68/1.00      inference(forward_subsumption_resolution,
% 3.68/1.00                [status(thm)],
% 3.68/1.00                [c_4473,c_4398]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_4743,plain,
% 3.68/1.00      ( k1_funct_1(sK3(sK4,X0),sK0(k1_xboole_0,sK4)) = k1_xboole_0 ),
% 3.68/1.00      inference(superposition,[status(thm)],[c_4476,c_3815]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_4749,plain,
% 3.68/1.00      ( k1_funct_1(sK3(sK4,X0),sK0(k1_xboole_0,sK4)) = sK3(sK4,X1) ),
% 3.68/1.00      inference(superposition,[status(thm)],[c_4476,c_3821]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_5113,plain,
% 3.68/1.00      ( sK3(sK4,X0) = k1_xboole_0 ),
% 3.68/1.00      inference(demodulation,[status(thm)],[c_4743,c_4749]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_5554,plain,
% 3.68/1.00      ( k1_relat_1(k1_xboole_0) = sK4 ),
% 3.68/1.00      inference(superposition,[status(thm)],[c_5113,c_11]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_5556,plain,
% 3.68/1.00      ( sK4 = k1_xboole_0 ),
% 3.68/1.00      inference(light_normalisation,[status(thm)],[c_5554,c_1]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(contradiction,plain,
% 3.68/1.00      ( $false ),
% 3.68/1.00      inference(minisat,[status(thm)],[c_5556,c_3007,c_163,c_14]) ).
% 3.68/1.00  
% 3.68/1.00  
% 3.68/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.68/1.00  
% 3.68/1.00  ------                               Statistics
% 3.68/1.00  
% 3.68/1.00  ------ Selected
% 3.68/1.00  
% 3.68/1.00  total_time:                             0.148
% 3.68/1.00  
%------------------------------------------------------------------------------
