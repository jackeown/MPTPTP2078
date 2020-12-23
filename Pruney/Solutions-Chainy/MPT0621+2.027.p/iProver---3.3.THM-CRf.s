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
% DateTime   : Thu Dec  3 11:49:25 EST 2020

% Result     : Theorem 2.85s
% Output     : CNFRefutation 2.85s
% Verified   : 
% Statistics : Number of formulae       :  121 (1744 expanded)
%              Number of clauses        :   80 ( 608 expanded)
%              Number of leaves         :   15 ( 449 expanded)
%              Depth                    :   27
%              Number of atoms          :  403 (8423 expanded)
%              Number of equality atoms :  265 (4238 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_funct_1(X1,X2) = np__1 )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = np__1
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
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

fof(f23,plain,(
    ! [X0] :
      ( ! [X2] :
          ( k1_funct_1(sK4(X0),X2) = np__1
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK4(X0)) = X0
      & v1_funct_1(sK4(X0))
      & v1_relat_1(sK4(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f11,f22])).

fof(f40,plain,(
    ! [X0] : k1_relat_1(sK4(X0)) = X0 ),
    inference(cnf_transformation,[],[f23])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f10,f20])).

fof(f36,plain,(
    ! [X0,X1] : k1_relat_1(sK3(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f21])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f24,plain,
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

fof(f25,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f13,f24])).

fof(f42,plain,(
    ! [X2,X1] :
      ( X1 = X2
      | k1_relat_1(X2) != sK5
      | k1_relat_1(X1) != sK5
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f34,plain,(
    ! [X0,X1] : v1_relat_1(sK3(X0,X1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f35,plain,(
    ! [X0,X1] : v1_funct_1(sK3(X0,X1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f38,plain,(
    ! [X0] : v1_relat_1(sK4(X0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f39,plain,(
    ! [X0] : v1_funct_1(sK4(X0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f15,plain,(
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
    inference(rectify,[],[f14])).

fof(f18,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK1(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK0(X0,X1),X3),X0)
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK0(X0,X1),X4),X0)
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK0(X0,X1),X3),X0)
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0)
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f18,f17,f16])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0)
      | r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f27,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f44,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f27])).

fof(f2,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f26,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f45,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f26])).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(sK3(X0,X1),X3) = X1
      | ~ r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_relat_1(X0) = k1_xboole_0 )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f9,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f32,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_relat_1(X0) != k1_xboole_0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f43,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_13,plain,
    ( k1_relat_1(sK4(X0)) = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_9,plain,
    ( k1_relat_1(sK3(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_17,negated_conjecture,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | X1 = X0
    | k1_relat_1(X0) != sK5
    | k1_relat_1(X1) != sK5 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_408,plain,
    ( X0 = X1
    | k1_relat_1(X0) != sK5
    | k1_relat_1(X1) != sK5
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_770,plain,
    ( sK3(X0,X1) = X2
    | k1_relat_1(X2) != sK5
    | sK5 != X0
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3(X0,X1)) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(sK3(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_408])).

cnf(c_11,plain,
    ( v1_relat_1(sK3(X0,X1)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_31,plain,
    ( v1_relat_1(sK3(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_10,plain,
    ( v1_funct_1(sK3(X0,X1)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_34,plain,
    ( v1_funct_1(sK3(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_850,plain,
    ( v1_relat_1(X2) != iProver_top
    | sK3(X0,X1) = X2
    | k1_relat_1(X2) != sK5
    | sK5 != X0
    | v1_funct_1(X2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_770,c_31,c_34])).

cnf(c_851,plain,
    ( sK3(X0,X1) = X2
    | k1_relat_1(X2) != sK5
    | sK5 != X0
    | v1_funct_1(X2) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_850])).

cnf(c_861,plain,
    ( sK3(X0,X1) = sK4(X2)
    | sK5 != X2
    | sK5 != X0
    | v1_funct_1(sK4(X2)) != iProver_top
    | v1_relat_1(sK4(X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_851])).

cnf(c_571,plain,
    ( sK4(X0) = X1
    | k1_relat_1(X1) != sK5
    | sK5 != X0
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK4(X0)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(sK4(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_408])).

cnf(c_15,plain,
    ( v1_relat_1(sK4(X0)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_21,plain,
    ( v1_relat_1(sK4(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_14,plain,
    ( v1_funct_1(sK4(X0)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_24,plain,
    ( v1_funct_1(sK4(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_719,plain,
    ( v1_relat_1(X1) != iProver_top
    | sK4(X0) = X1
    | k1_relat_1(X1) != sK5
    | sK5 != X0
    | v1_funct_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_571,c_21,c_24])).

cnf(c_720,plain,
    ( sK4(X0) = X1
    | k1_relat_1(X1) != sK5
    | sK5 != X0
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_719])).

cnf(c_769,plain,
    ( sK3(X0,X1) = sK4(X2)
    | sK5 != X0
    | sK5 != X2
    | v1_funct_1(sK3(X0,X1)) != iProver_top
    | v1_relat_1(sK3(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_720])).

cnf(c_795,plain,
    ( ~ v1_funct_1(sK3(X0,X1))
    | ~ v1_relat_1(sK3(X0,X1))
    | sK3(X0,X1) = sK4(X2)
    | sK5 != X0
    | sK5 != X2 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_769])).

cnf(c_960,plain,
    ( sK3(X0,X1) = sK4(X2)
    | sK5 != X2
    | sK5 != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_861,c_11,c_10,c_795])).

cnf(c_961,plain,
    ( sK3(X0,X1) = sK4(X2)
    | sK5 != X0
    | sK5 != X2 ),
    inference(renaming,[status(thm)],[c_960])).

cnf(c_965,plain,
    ( sK3(sK5,X0) = sK4(X1)
    | sK5 != X1 ),
    inference(equality_resolution,[status(thm)],[c_961])).

cnf(c_1019,plain,
    ( sK3(sK5,X0) = sK4(sK5) ),
    inference(equality_resolution,[status(thm)],[c_965])).

cnf(c_1,plain,
    ( r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0)
    | r2_hidden(sK0(X0,X1),X1)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_419,plain,
    ( k1_relat_1(X0) = X1
    | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0) = iProver_top
    | r2_hidden(sK0(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_418,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1747,plain,
    ( k1_relat_1(X0) = X1
    | r2_hidden(sK0(X0,X1),X1) = iProver_top
    | r2_hidden(sK0(X0,X1),k1_relat_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_419,c_418])).

cnf(c_2325,plain,
    ( k1_relat_1(sK3(X0,X1)) = X2
    | r2_hidden(sK0(sK3(X0,X1),X2),X0) = iProver_top
    | r2_hidden(sK0(sK3(X0,X1),X2),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_1747])).

cnf(c_2465,plain,
    ( X0 = X1
    | r2_hidden(sK0(sK3(X1,X2),X0),X1) = iProver_top
    | r2_hidden(sK0(sK3(X1,X2),X0),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2325,c_9])).

cnf(c_3052,plain,
    ( sK5 = X0
    | r2_hidden(sK0(sK3(sK5,X1),X0),X0) = iProver_top
    | r2_hidden(sK0(sK4(sK5),X0),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1019,c_2465])).

cnf(c_3199,plain,
    ( sK5 = X0
    | r2_hidden(sK0(sK4(sK5),X0),X0) = iProver_top
    | r2_hidden(sK0(sK4(sK5),X0),sK5) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3052,c_1019])).

cnf(c_5,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,sK2(X1,X0)),X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_417,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK2(X1,X0)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_funct_1(sK3(X1,X2),X0) = X2 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_414,plain,
    ( k1_funct_1(sK3(X0,X1),X2) = X1
    | r2_hidden(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1576,plain,
    ( k1_funct_1(sK3(X0,X1),k4_tarski(X2,sK2(X0,X2))) = X1
    | r2_hidden(X2,k1_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_417,c_414])).

cnf(c_2127,plain,
    ( k1_funct_1(sK3(k1_xboole_0,X0),k4_tarski(X1,sK2(k1_xboole_0,X1))) = X0
    | r2_hidden(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_1576])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_415,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1141,plain,
    ( sK3(X0,X1) = k1_xboole_0
    | k1_xboole_0 != X0
    | v1_relat_1(sK3(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_415])).

cnf(c_1593,plain,
    ( k1_xboole_0 != X0
    | sK3(X0,X1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1141,c_31])).

cnf(c_1594,plain,
    ( sK3(X0,X1) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(renaming,[status(thm)],[c_1593])).

cnf(c_1598,plain,
    ( sK3(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_1594])).

cnf(c_2140,plain,
    ( k1_funct_1(k1_xboole_0,k4_tarski(X0,sK2(k1_xboole_0,X0))) = X1
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2127,c_1598])).

cnf(c_3373,plain,
    ( k1_funct_1(k1_xboole_0,k4_tarski(sK0(sK4(sK5),k1_xboole_0),sK2(k1_xboole_0,sK0(sK4(sK5),k1_xboole_0)))) = X0
    | sK5 = k1_xboole_0
    | r2_hidden(sK0(sK4(sK5),k1_xboole_0),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3199,c_2140])).

cnf(c_16,negated_conjecture,
    ( k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_161,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_178,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_161])).

cnf(c_162,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_564,plain,
    ( sK5 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_162])).

cnf(c_565,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_564])).

cnf(c_4319,plain,
    ( k1_funct_1(k1_xboole_0,k4_tarski(sK0(sK4(sK5),k1_xboole_0),sK2(k1_xboole_0,sK0(sK4(sK5),k1_xboole_0)))) = X0
    | r2_hidden(sK0(sK4(sK5),k1_xboole_0),sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3373,c_16,c_178,c_565])).

cnf(c_4329,plain,
    ( k1_funct_1(sK3(sK5,X0),sK0(sK4(sK5),k1_xboole_0)) = X0
    | k1_funct_1(k1_xboole_0,k4_tarski(sK0(sK4(sK5),k1_xboole_0),sK2(k1_xboole_0,sK0(sK4(sK5),k1_xboole_0)))) = X1 ),
    inference(superposition,[status(thm)],[c_4319,c_414])).

cnf(c_4348,plain,
    ( k1_funct_1(sK4(sK5),sK0(sK4(sK5),k1_xboole_0)) = X0
    | k1_funct_1(k1_xboole_0,k4_tarski(sK0(sK4(sK5),k1_xboole_0),sK2(k1_xboole_0,sK0(sK4(sK5),k1_xboole_0)))) = X1 ),
    inference(light_normalisation,[status(thm)],[c_4329,c_1019])).

cnf(c_5855,plain,
    ( k1_funct_1(sK4(sK5),sK0(sK4(sK5),k1_xboole_0)) = X0
    | k1_funct_1(k1_xboole_0,k4_tarski(sK0(sK4(sK5),k1_xboole_0),sK2(k1_xboole_0,sK0(sK4(sK5),k1_xboole_0)))) != k1_funct_1(sK4(sK5),sK0(sK4(sK5),k1_xboole_0)) ),
    inference(equality_factoring,[status(thm)],[c_4348])).

cnf(c_5860,plain,
    ( k1_funct_1(sK4(sK5),sK0(sK4(sK5),k1_xboole_0)) = X0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5855,c_4348])).

cnf(c_6049,plain,
    ( k1_funct_1(sK4(sK5),sK0(sK4(sK5),k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5860,c_1598])).

cnf(c_6050,plain,
    ( k1_funct_1(sK4(sK5),sK0(sK4(sK5),k1_xboole_0)) = sK4(sK5) ),
    inference(superposition,[status(thm)],[c_5860,c_1019])).

cnf(c_6735,plain,
    ( sK4(sK5) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6049,c_6050])).

cnf(c_163,plain,
    ( X0 != X1
    | k1_relat_1(X0) = k1_relat_1(X1) ),
    theory(equality)).

cnf(c_2536,plain,
    ( sK4(sK5) != X0
    | k1_relat_1(sK4(sK5)) = k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_163])).

cnf(c_2538,plain,
    ( sK4(sK5) != k1_xboole_0
    | k1_relat_1(sK4(sK5)) = k1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2536])).

cnf(c_1040,plain,
    ( k1_relat_1(X0) != X1
    | k1_xboole_0 != X1
    | k1_xboole_0 = k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_162])).

cnf(c_1795,plain,
    ( k1_relat_1(sK4(sK5)) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k1_relat_1(sK4(sK5)) ),
    inference(instantiation,[status(thm)],[c_1040])).

cnf(c_2533,plain,
    ( k1_relat_1(sK4(sK5)) != k1_relat_1(X0)
    | k1_xboole_0 != k1_relat_1(X0)
    | k1_xboole_0 = k1_relat_1(sK4(sK5)) ),
    inference(instantiation,[status(thm)],[c_1795])).

cnf(c_2537,plain,
    ( k1_relat_1(sK4(sK5)) != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 = k1_relat_1(sK4(sK5))
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2533])).

cnf(c_991,plain,
    ( sK5 != k1_relat_1(X0)
    | k1_xboole_0 != k1_relat_1(X0)
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_564])).

cnf(c_1622,plain,
    ( sK5 != k1_relat_1(sK4(sK5))
    | k1_xboole_0 != k1_relat_1(sK4(sK5))
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_991])).

cnf(c_1281,plain,
    ( k1_relat_1(sK4(sK5)) = sK5 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_579,plain,
    ( X0 != X1
    | sK5 != X1
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_162])).

cnf(c_711,plain,
    ( X0 != sK5
    | sK5 = X0
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_579])).

cnf(c_906,plain,
    ( k1_relat_1(X0) != sK5
    | sK5 = k1_relat_1(X0)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_711])).

cnf(c_1280,plain,
    ( k1_relat_1(sK4(sK5)) != sK5
    | sK5 = k1_relat_1(sK4(sK5))
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_906])).

cnf(c_1041,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1040])).

cnf(c_712,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_161])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6735,c_2538,c_2537,c_1622,c_1281,c_1280,c_1041,c_712,c_178,c_5,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:58:07 EST 2020
% 0.18/0.33  % CPUTime    : 
% 0.18/0.34  % Running in FOF mode
% 2.85/0.96  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.85/0.96  
% 2.85/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.85/0.96  
% 2.85/0.96  ------  iProver source info
% 2.85/0.96  
% 2.85/0.96  git: date: 2020-06-30 10:37:57 +0100
% 2.85/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.85/0.96  git: non_committed_changes: false
% 2.85/0.96  git: last_make_outside_of_git: false
% 2.85/0.96  
% 2.85/0.96  ------ 
% 2.85/0.96  
% 2.85/0.96  ------ Input Options
% 2.85/0.96  
% 2.85/0.96  --out_options                           all
% 2.85/0.96  --tptp_safe_out                         true
% 2.85/0.96  --problem_path                          ""
% 2.85/0.96  --include_path                          ""
% 2.85/0.96  --clausifier                            res/vclausify_rel
% 2.85/0.96  --clausifier_options                    --mode clausify
% 2.85/0.96  --stdin                                 false
% 2.85/0.96  --stats_out                             all
% 2.85/0.96  
% 2.85/0.96  ------ General Options
% 2.85/0.96  
% 2.85/0.96  --fof                                   false
% 2.85/0.96  --time_out_real                         305.
% 2.85/0.96  --time_out_virtual                      -1.
% 2.85/0.96  --symbol_type_check                     false
% 2.85/0.96  --clausify_out                          false
% 2.85/0.96  --sig_cnt_out                           false
% 2.85/0.96  --trig_cnt_out                          false
% 2.85/0.96  --trig_cnt_out_tolerance                1.
% 2.85/0.96  --trig_cnt_out_sk_spl                   false
% 2.85/0.96  --abstr_cl_out                          false
% 2.85/0.96  
% 2.85/0.96  ------ Global Options
% 2.85/0.96  
% 2.85/0.96  --schedule                              default
% 2.85/0.96  --add_important_lit                     false
% 2.85/0.96  --prop_solver_per_cl                    1000
% 2.85/0.96  --min_unsat_core                        false
% 2.85/0.96  --soft_assumptions                      false
% 2.85/0.96  --soft_lemma_size                       3
% 2.85/0.96  --prop_impl_unit_size                   0
% 2.85/0.96  --prop_impl_unit                        []
% 2.85/0.96  --share_sel_clauses                     true
% 2.85/0.96  --reset_solvers                         false
% 2.85/0.96  --bc_imp_inh                            [conj_cone]
% 2.85/0.96  --conj_cone_tolerance                   3.
% 2.85/0.96  --extra_neg_conj                        none
% 2.85/0.96  --large_theory_mode                     true
% 2.85/0.96  --prolific_symb_bound                   200
% 2.85/0.96  --lt_threshold                          2000
% 2.85/0.96  --clause_weak_htbl                      true
% 2.85/0.96  --gc_record_bc_elim                     false
% 2.85/0.96  
% 2.85/0.96  ------ Preprocessing Options
% 2.85/0.96  
% 2.85/0.96  --preprocessing_flag                    true
% 2.85/0.96  --time_out_prep_mult                    0.1
% 2.85/0.96  --splitting_mode                        input
% 2.85/0.96  --splitting_grd                         true
% 2.85/0.96  --splitting_cvd                         false
% 2.85/0.96  --splitting_cvd_svl                     false
% 2.85/0.96  --splitting_nvd                         32
% 2.85/0.96  --sub_typing                            true
% 2.85/0.96  --prep_gs_sim                           true
% 2.85/0.96  --prep_unflatten                        true
% 2.85/0.96  --prep_res_sim                          true
% 2.85/0.96  --prep_upred                            true
% 2.85/0.96  --prep_sem_filter                       exhaustive
% 2.85/0.96  --prep_sem_filter_out                   false
% 2.85/0.96  --pred_elim                             true
% 2.85/0.96  --res_sim_input                         true
% 2.85/0.96  --eq_ax_congr_red                       true
% 2.85/0.96  --pure_diseq_elim                       true
% 2.85/0.96  --brand_transform                       false
% 2.85/0.96  --non_eq_to_eq                          false
% 2.85/0.96  --prep_def_merge                        true
% 2.85/0.96  --prep_def_merge_prop_impl              false
% 2.85/0.96  --prep_def_merge_mbd                    true
% 2.85/0.96  --prep_def_merge_tr_red                 false
% 2.85/0.96  --prep_def_merge_tr_cl                  false
% 2.85/0.96  --smt_preprocessing                     true
% 2.85/0.96  --smt_ac_axioms                         fast
% 2.85/0.96  --preprocessed_out                      false
% 2.85/0.96  --preprocessed_stats                    false
% 2.85/0.96  
% 2.85/0.96  ------ Abstraction refinement Options
% 2.85/0.96  
% 2.85/0.96  --abstr_ref                             []
% 2.85/0.96  --abstr_ref_prep                        false
% 2.85/0.96  --abstr_ref_until_sat                   false
% 2.85/0.96  --abstr_ref_sig_restrict                funpre
% 2.85/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 2.85/0.96  --abstr_ref_under                       []
% 2.85/0.96  
% 2.85/0.96  ------ SAT Options
% 2.85/0.96  
% 2.85/0.96  --sat_mode                              false
% 2.85/0.96  --sat_fm_restart_options                ""
% 2.85/0.96  --sat_gr_def                            false
% 2.85/0.96  --sat_epr_types                         true
% 2.85/0.96  --sat_non_cyclic_types                  false
% 2.85/0.96  --sat_finite_models                     false
% 2.85/0.96  --sat_fm_lemmas                         false
% 2.85/0.96  --sat_fm_prep                           false
% 2.85/0.96  --sat_fm_uc_incr                        true
% 2.85/0.96  --sat_out_model                         small
% 2.85/0.96  --sat_out_clauses                       false
% 2.85/0.96  
% 2.85/0.96  ------ QBF Options
% 2.85/0.96  
% 2.85/0.96  --qbf_mode                              false
% 2.85/0.96  --qbf_elim_univ                         false
% 2.85/0.96  --qbf_dom_inst                          none
% 2.85/0.96  --qbf_dom_pre_inst                      false
% 2.85/0.96  --qbf_sk_in                             false
% 2.85/0.96  --qbf_pred_elim                         true
% 2.85/0.96  --qbf_split                             512
% 2.85/0.96  
% 2.85/0.96  ------ BMC1 Options
% 2.85/0.96  
% 2.85/0.96  --bmc1_incremental                      false
% 2.85/0.96  --bmc1_axioms                           reachable_all
% 2.85/0.96  --bmc1_min_bound                        0
% 2.85/0.96  --bmc1_max_bound                        -1
% 2.85/0.96  --bmc1_max_bound_default                -1
% 2.85/0.96  --bmc1_symbol_reachability              true
% 2.85/0.96  --bmc1_property_lemmas                  false
% 2.85/0.96  --bmc1_k_induction                      false
% 2.85/0.96  --bmc1_non_equiv_states                 false
% 2.85/0.96  --bmc1_deadlock                         false
% 2.85/0.96  --bmc1_ucm                              false
% 2.85/0.96  --bmc1_add_unsat_core                   none
% 2.85/0.97  --bmc1_unsat_core_children              false
% 2.85/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.85/0.97  --bmc1_out_stat                         full
% 2.85/0.97  --bmc1_ground_init                      false
% 2.85/0.97  --bmc1_pre_inst_next_state              false
% 2.85/0.97  --bmc1_pre_inst_state                   false
% 2.85/0.97  --bmc1_pre_inst_reach_state             false
% 2.85/0.97  --bmc1_out_unsat_core                   false
% 2.85/0.97  --bmc1_aig_witness_out                  false
% 2.85/0.97  --bmc1_verbose                          false
% 2.85/0.97  --bmc1_dump_clauses_tptp                false
% 2.85/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.85/0.97  --bmc1_dump_file                        -
% 2.85/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.85/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.85/0.97  --bmc1_ucm_extend_mode                  1
% 2.85/0.97  --bmc1_ucm_init_mode                    2
% 2.85/0.97  --bmc1_ucm_cone_mode                    none
% 2.85/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.85/0.97  --bmc1_ucm_relax_model                  4
% 2.85/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.85/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.85/0.97  --bmc1_ucm_layered_model                none
% 2.85/0.97  --bmc1_ucm_max_lemma_size               10
% 2.85/0.97  
% 2.85/0.97  ------ AIG Options
% 2.85/0.97  
% 2.85/0.97  --aig_mode                              false
% 2.85/0.97  
% 2.85/0.97  ------ Instantiation Options
% 2.85/0.97  
% 2.85/0.97  --instantiation_flag                    true
% 2.85/0.97  --inst_sos_flag                         false
% 2.85/0.97  --inst_sos_phase                        true
% 2.85/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.85/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.85/0.97  --inst_lit_sel_side                     num_symb
% 2.85/0.97  --inst_solver_per_active                1400
% 2.85/0.97  --inst_solver_calls_frac                1.
% 2.85/0.97  --inst_passive_queue_type               priority_queues
% 2.85/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.85/0.97  --inst_passive_queues_freq              [25;2]
% 2.85/0.97  --inst_dismatching                      true
% 2.85/0.97  --inst_eager_unprocessed_to_passive     true
% 2.85/0.97  --inst_prop_sim_given                   true
% 2.85/0.97  --inst_prop_sim_new                     false
% 2.85/0.97  --inst_subs_new                         false
% 2.85/0.97  --inst_eq_res_simp                      false
% 2.85/0.97  --inst_subs_given                       false
% 2.85/0.97  --inst_orphan_elimination               true
% 2.85/0.97  --inst_learning_loop_flag               true
% 2.85/0.97  --inst_learning_start                   3000
% 2.85/0.97  --inst_learning_factor                  2
% 2.85/0.97  --inst_start_prop_sim_after_learn       3
% 2.85/0.97  --inst_sel_renew                        solver
% 2.85/0.97  --inst_lit_activity_flag                true
% 2.85/0.97  --inst_restr_to_given                   false
% 2.85/0.97  --inst_activity_threshold               500
% 2.85/0.97  --inst_out_proof                        true
% 2.85/0.97  
% 2.85/0.97  ------ Resolution Options
% 2.85/0.97  
% 2.85/0.97  --resolution_flag                       true
% 2.85/0.97  --res_lit_sel                           adaptive
% 2.85/0.97  --res_lit_sel_side                      none
% 2.85/0.97  --res_ordering                          kbo
% 2.85/0.97  --res_to_prop_solver                    active
% 2.85/0.97  --res_prop_simpl_new                    false
% 2.85/0.97  --res_prop_simpl_given                  true
% 2.85/0.97  --res_passive_queue_type                priority_queues
% 2.85/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.85/0.97  --res_passive_queues_freq               [15;5]
% 2.85/0.97  --res_forward_subs                      full
% 2.85/0.97  --res_backward_subs                     full
% 2.85/0.97  --res_forward_subs_resolution           true
% 2.85/0.97  --res_backward_subs_resolution          true
% 2.85/0.97  --res_orphan_elimination                true
% 2.85/0.97  --res_time_limit                        2.
% 2.85/0.97  --res_out_proof                         true
% 2.85/0.97  
% 2.85/0.97  ------ Superposition Options
% 2.85/0.97  
% 2.85/0.97  --superposition_flag                    true
% 2.85/0.97  --sup_passive_queue_type                priority_queues
% 2.85/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.85/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.85/0.97  --demod_completeness_check              fast
% 2.85/0.97  --demod_use_ground                      true
% 2.85/0.97  --sup_to_prop_solver                    passive
% 2.85/0.97  --sup_prop_simpl_new                    true
% 2.85/0.97  --sup_prop_simpl_given                  true
% 2.85/0.97  --sup_fun_splitting                     false
% 2.85/0.97  --sup_smt_interval                      50000
% 2.85/0.97  
% 2.85/0.97  ------ Superposition Simplification Setup
% 2.85/0.97  
% 2.85/0.97  --sup_indices_passive                   []
% 2.85/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.85/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.85/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.85/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.85/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.85/0.97  --sup_full_bw                           [BwDemod]
% 2.85/0.97  --sup_immed_triv                        [TrivRules]
% 2.85/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.85/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.85/0.97  --sup_immed_bw_main                     []
% 2.85/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.85/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.85/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.85/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.85/0.97  
% 2.85/0.97  ------ Combination Options
% 2.85/0.97  
% 2.85/0.97  --comb_res_mult                         3
% 2.85/0.97  --comb_sup_mult                         2
% 2.85/0.97  --comb_inst_mult                        10
% 2.85/0.97  
% 2.85/0.97  ------ Debug Options
% 2.85/0.97  
% 2.85/0.97  --dbg_backtrace                         false
% 2.85/0.97  --dbg_dump_prop_clauses                 false
% 2.85/0.97  --dbg_dump_prop_clauses_file            -
% 2.85/0.97  --dbg_out_stat                          false
% 2.85/0.97  ------ Parsing...
% 2.85/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.85/0.97  
% 2.85/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.85/0.97  
% 2.85/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.85/0.97  
% 2.85/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.85/0.97  ------ Proving...
% 2.85/0.97  ------ Problem Properties 
% 2.85/0.97  
% 2.85/0.97  
% 2.85/0.97  clauses                                 18
% 2.85/0.97  conjectures                             2
% 2.85/0.97  EPR                                     1
% 2.85/0.97  Horn                                    17
% 2.85/0.97  unary                                   9
% 2.85/0.97  binary                                  4
% 2.85/0.97  lits                                    36
% 2.85/0.97  lits eq                                 16
% 2.85/0.97  fd_pure                                 0
% 2.85/0.97  fd_pseudo                               0
% 2.85/0.97  fd_cond                                 2
% 2.85/0.97  fd_pseudo_cond                          3
% 2.85/0.97  AC symbols                              0
% 2.85/0.97  
% 2.85/0.97  ------ Schedule dynamic 5 is on 
% 2.85/0.97  
% 2.85/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.85/0.97  
% 2.85/0.97  
% 2.85/0.97  ------ 
% 2.85/0.97  Current options:
% 2.85/0.97  ------ 
% 2.85/0.97  
% 2.85/0.97  ------ Input Options
% 2.85/0.97  
% 2.85/0.97  --out_options                           all
% 2.85/0.97  --tptp_safe_out                         true
% 2.85/0.97  --problem_path                          ""
% 2.85/0.97  --include_path                          ""
% 2.85/0.97  --clausifier                            res/vclausify_rel
% 2.85/0.97  --clausifier_options                    --mode clausify
% 2.85/0.97  --stdin                                 false
% 2.85/0.97  --stats_out                             all
% 2.85/0.97  
% 2.85/0.97  ------ General Options
% 2.85/0.97  
% 2.85/0.97  --fof                                   false
% 2.85/0.97  --time_out_real                         305.
% 2.85/0.97  --time_out_virtual                      -1.
% 2.85/0.97  --symbol_type_check                     false
% 2.85/0.97  --clausify_out                          false
% 2.85/0.97  --sig_cnt_out                           false
% 2.85/0.97  --trig_cnt_out                          false
% 2.85/0.97  --trig_cnt_out_tolerance                1.
% 2.85/0.97  --trig_cnt_out_sk_spl                   false
% 2.85/0.97  --abstr_cl_out                          false
% 2.85/0.97  
% 2.85/0.97  ------ Global Options
% 2.85/0.97  
% 2.85/0.97  --schedule                              default
% 2.85/0.97  --add_important_lit                     false
% 2.85/0.97  --prop_solver_per_cl                    1000
% 2.85/0.97  --min_unsat_core                        false
% 2.85/0.97  --soft_assumptions                      false
% 2.85/0.97  --soft_lemma_size                       3
% 2.85/0.97  --prop_impl_unit_size                   0
% 2.85/0.97  --prop_impl_unit                        []
% 2.85/0.97  --share_sel_clauses                     true
% 2.85/0.97  --reset_solvers                         false
% 2.85/0.97  --bc_imp_inh                            [conj_cone]
% 2.85/0.97  --conj_cone_tolerance                   3.
% 2.85/0.97  --extra_neg_conj                        none
% 2.85/0.97  --large_theory_mode                     true
% 2.85/0.97  --prolific_symb_bound                   200
% 2.85/0.97  --lt_threshold                          2000
% 2.85/0.97  --clause_weak_htbl                      true
% 2.85/0.97  --gc_record_bc_elim                     false
% 2.85/0.97  
% 2.85/0.97  ------ Preprocessing Options
% 2.85/0.97  
% 2.85/0.97  --preprocessing_flag                    true
% 2.85/0.97  --time_out_prep_mult                    0.1
% 2.85/0.97  --splitting_mode                        input
% 2.85/0.97  --splitting_grd                         true
% 2.85/0.97  --splitting_cvd                         false
% 2.85/0.97  --splitting_cvd_svl                     false
% 2.85/0.97  --splitting_nvd                         32
% 2.85/0.97  --sub_typing                            true
% 2.85/0.97  --prep_gs_sim                           true
% 2.85/0.97  --prep_unflatten                        true
% 2.85/0.97  --prep_res_sim                          true
% 2.85/0.97  --prep_upred                            true
% 2.85/0.97  --prep_sem_filter                       exhaustive
% 2.85/0.97  --prep_sem_filter_out                   false
% 2.85/0.97  --pred_elim                             true
% 2.85/0.97  --res_sim_input                         true
% 2.85/0.97  --eq_ax_congr_red                       true
% 2.85/0.97  --pure_diseq_elim                       true
% 2.85/0.97  --brand_transform                       false
% 2.85/0.97  --non_eq_to_eq                          false
% 2.85/0.97  --prep_def_merge                        true
% 2.85/0.97  --prep_def_merge_prop_impl              false
% 2.85/0.97  --prep_def_merge_mbd                    true
% 2.85/0.97  --prep_def_merge_tr_red                 false
% 2.85/0.97  --prep_def_merge_tr_cl                  false
% 2.85/0.97  --smt_preprocessing                     true
% 2.85/0.97  --smt_ac_axioms                         fast
% 2.85/0.97  --preprocessed_out                      false
% 2.85/0.97  --preprocessed_stats                    false
% 2.85/0.97  
% 2.85/0.97  ------ Abstraction refinement Options
% 2.85/0.97  
% 2.85/0.97  --abstr_ref                             []
% 2.85/0.97  --abstr_ref_prep                        false
% 2.85/0.97  --abstr_ref_until_sat                   false
% 2.85/0.97  --abstr_ref_sig_restrict                funpre
% 2.85/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.85/0.97  --abstr_ref_under                       []
% 2.85/0.97  
% 2.85/0.97  ------ SAT Options
% 2.85/0.97  
% 2.85/0.97  --sat_mode                              false
% 2.85/0.97  --sat_fm_restart_options                ""
% 2.85/0.97  --sat_gr_def                            false
% 2.85/0.97  --sat_epr_types                         true
% 2.85/0.97  --sat_non_cyclic_types                  false
% 2.85/0.97  --sat_finite_models                     false
% 2.85/0.97  --sat_fm_lemmas                         false
% 2.85/0.97  --sat_fm_prep                           false
% 2.85/0.97  --sat_fm_uc_incr                        true
% 2.85/0.97  --sat_out_model                         small
% 2.85/0.97  --sat_out_clauses                       false
% 2.85/0.97  
% 2.85/0.97  ------ QBF Options
% 2.85/0.97  
% 2.85/0.97  --qbf_mode                              false
% 2.85/0.97  --qbf_elim_univ                         false
% 2.85/0.97  --qbf_dom_inst                          none
% 2.85/0.97  --qbf_dom_pre_inst                      false
% 2.85/0.97  --qbf_sk_in                             false
% 2.85/0.97  --qbf_pred_elim                         true
% 2.85/0.97  --qbf_split                             512
% 2.85/0.97  
% 2.85/0.97  ------ BMC1 Options
% 2.85/0.97  
% 2.85/0.97  --bmc1_incremental                      false
% 2.85/0.97  --bmc1_axioms                           reachable_all
% 2.85/0.97  --bmc1_min_bound                        0
% 2.85/0.97  --bmc1_max_bound                        -1
% 2.85/0.97  --bmc1_max_bound_default                -1
% 2.85/0.97  --bmc1_symbol_reachability              true
% 2.85/0.97  --bmc1_property_lemmas                  false
% 2.85/0.97  --bmc1_k_induction                      false
% 2.85/0.97  --bmc1_non_equiv_states                 false
% 2.85/0.97  --bmc1_deadlock                         false
% 2.85/0.97  --bmc1_ucm                              false
% 2.85/0.97  --bmc1_add_unsat_core                   none
% 2.85/0.97  --bmc1_unsat_core_children              false
% 2.85/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.85/0.97  --bmc1_out_stat                         full
% 2.85/0.97  --bmc1_ground_init                      false
% 2.85/0.97  --bmc1_pre_inst_next_state              false
% 2.85/0.97  --bmc1_pre_inst_state                   false
% 2.85/0.97  --bmc1_pre_inst_reach_state             false
% 2.85/0.97  --bmc1_out_unsat_core                   false
% 2.85/0.97  --bmc1_aig_witness_out                  false
% 2.85/0.97  --bmc1_verbose                          false
% 2.85/0.97  --bmc1_dump_clauses_tptp                false
% 2.85/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.85/0.97  --bmc1_dump_file                        -
% 2.85/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.85/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.85/0.97  --bmc1_ucm_extend_mode                  1
% 2.85/0.97  --bmc1_ucm_init_mode                    2
% 2.85/0.97  --bmc1_ucm_cone_mode                    none
% 2.85/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.85/0.97  --bmc1_ucm_relax_model                  4
% 2.85/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.85/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.85/0.97  --bmc1_ucm_layered_model                none
% 2.85/0.97  --bmc1_ucm_max_lemma_size               10
% 2.85/0.97  
% 2.85/0.97  ------ AIG Options
% 2.85/0.97  
% 2.85/0.97  --aig_mode                              false
% 2.85/0.97  
% 2.85/0.97  ------ Instantiation Options
% 2.85/0.97  
% 2.85/0.97  --instantiation_flag                    true
% 2.85/0.97  --inst_sos_flag                         false
% 2.85/0.97  --inst_sos_phase                        true
% 2.85/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.85/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.85/0.97  --inst_lit_sel_side                     none
% 2.85/0.97  --inst_solver_per_active                1400
% 2.85/0.97  --inst_solver_calls_frac                1.
% 2.85/0.97  --inst_passive_queue_type               priority_queues
% 2.85/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.85/0.97  --inst_passive_queues_freq              [25;2]
% 2.85/0.97  --inst_dismatching                      true
% 2.85/0.97  --inst_eager_unprocessed_to_passive     true
% 2.85/0.97  --inst_prop_sim_given                   true
% 2.85/0.97  --inst_prop_sim_new                     false
% 2.85/0.97  --inst_subs_new                         false
% 2.85/0.97  --inst_eq_res_simp                      false
% 2.85/0.97  --inst_subs_given                       false
% 2.85/0.97  --inst_orphan_elimination               true
% 2.85/0.97  --inst_learning_loop_flag               true
% 2.85/0.97  --inst_learning_start                   3000
% 2.85/0.97  --inst_learning_factor                  2
% 2.85/0.97  --inst_start_prop_sim_after_learn       3
% 2.85/0.97  --inst_sel_renew                        solver
% 2.85/0.97  --inst_lit_activity_flag                true
% 2.85/0.97  --inst_restr_to_given                   false
% 2.85/0.97  --inst_activity_threshold               500
% 2.85/0.97  --inst_out_proof                        true
% 2.85/0.97  
% 2.85/0.97  ------ Resolution Options
% 2.85/0.97  
% 2.85/0.97  --resolution_flag                       false
% 2.85/0.97  --res_lit_sel                           adaptive
% 2.85/0.97  --res_lit_sel_side                      none
% 2.85/0.97  --res_ordering                          kbo
% 2.85/0.97  --res_to_prop_solver                    active
% 2.85/0.97  --res_prop_simpl_new                    false
% 2.85/0.97  --res_prop_simpl_given                  true
% 2.85/0.97  --res_passive_queue_type                priority_queues
% 2.85/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.85/0.97  --res_passive_queues_freq               [15;5]
% 2.85/0.97  --res_forward_subs                      full
% 2.85/0.97  --res_backward_subs                     full
% 2.85/0.97  --res_forward_subs_resolution           true
% 2.85/0.97  --res_backward_subs_resolution          true
% 2.85/0.97  --res_orphan_elimination                true
% 2.85/0.97  --res_time_limit                        2.
% 2.85/0.97  --res_out_proof                         true
% 2.85/0.97  
% 2.85/0.97  ------ Superposition Options
% 2.85/0.97  
% 2.85/0.97  --superposition_flag                    true
% 2.85/0.97  --sup_passive_queue_type                priority_queues
% 2.85/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.85/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.85/0.97  --demod_completeness_check              fast
% 2.85/0.97  --demod_use_ground                      true
% 2.85/0.97  --sup_to_prop_solver                    passive
% 2.85/0.97  --sup_prop_simpl_new                    true
% 2.85/0.97  --sup_prop_simpl_given                  true
% 2.85/0.97  --sup_fun_splitting                     false
% 2.85/0.97  --sup_smt_interval                      50000
% 2.85/0.97  
% 2.85/0.97  ------ Superposition Simplification Setup
% 2.85/0.97  
% 2.85/0.97  --sup_indices_passive                   []
% 2.85/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.85/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.85/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.85/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.85/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.85/0.97  --sup_full_bw                           [BwDemod]
% 2.85/0.97  --sup_immed_triv                        [TrivRules]
% 2.85/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.85/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.85/0.97  --sup_immed_bw_main                     []
% 2.85/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.85/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.85/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.85/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.85/0.97  
% 2.85/0.97  ------ Combination Options
% 2.85/0.97  
% 2.85/0.97  --comb_res_mult                         3
% 2.85/0.97  --comb_sup_mult                         2
% 2.85/0.97  --comb_inst_mult                        10
% 2.85/0.97  
% 2.85/0.97  ------ Debug Options
% 2.85/0.97  
% 2.85/0.97  --dbg_backtrace                         false
% 2.85/0.97  --dbg_dump_prop_clauses                 false
% 2.85/0.97  --dbg_dump_prop_clauses_file            -
% 2.85/0.97  --dbg_out_stat                          false
% 2.85/0.97  
% 2.85/0.97  
% 2.85/0.97  
% 2.85/0.97  
% 2.85/0.97  ------ Proving...
% 2.85/0.97  
% 2.85/0.97  
% 2.85/0.97  % SZS status Theorem for theBenchmark.p
% 2.85/0.97  
% 2.85/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 2.85/0.97  
% 2.85/0.97  fof(f5,axiom,(
% 2.85/0.97    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = np__1) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 2.85/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/0.97  
% 2.85/0.97  fof(f11,plain,(
% 2.85/0.97    ! [X0] : ? [X1] : (! [X2] : (k1_funct_1(X1,X2) = np__1 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 2.85/0.97    inference(ennf_transformation,[],[f5])).
% 2.85/0.97  
% 2.85/0.97  fof(f22,plain,(
% 2.85/0.97    ! [X0] : (? [X1] : (! [X2] : (k1_funct_1(X1,X2) = np__1 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1)) => (! [X2] : (k1_funct_1(sK4(X0),X2) = np__1 | ~r2_hidden(X2,X0)) & k1_relat_1(sK4(X0)) = X0 & v1_funct_1(sK4(X0)) & v1_relat_1(sK4(X0))))),
% 2.85/0.97    introduced(choice_axiom,[])).
% 2.85/0.97  
% 2.85/0.97  fof(f23,plain,(
% 2.85/0.97    ! [X0] : (! [X2] : (k1_funct_1(sK4(X0),X2) = np__1 | ~r2_hidden(X2,X0)) & k1_relat_1(sK4(X0)) = X0 & v1_funct_1(sK4(X0)) & v1_relat_1(sK4(X0)))),
% 2.85/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f11,f22])).
% 2.85/0.97  
% 2.85/0.97  fof(f40,plain,(
% 2.85/0.97    ( ! [X0] : (k1_relat_1(sK4(X0)) = X0) )),
% 2.85/0.97    inference(cnf_transformation,[],[f23])).
% 2.85/0.97  
% 2.85/0.97  fof(f4,axiom,(
% 2.85/0.97    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 2.85/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/0.97  
% 2.85/0.97  fof(f10,plain,(
% 2.85/0.97    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 2.85/0.97    inference(ennf_transformation,[],[f4])).
% 2.85/0.97  
% 2.85/0.97  fof(f20,plain,(
% 2.85/0.97    ! [X1,X0] : (? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (! [X3] : (k1_funct_1(sK3(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK3(X0,X1)) = X0 & v1_funct_1(sK3(X0,X1)) & v1_relat_1(sK3(X0,X1))))),
% 2.85/0.97    introduced(choice_axiom,[])).
% 2.85/0.97  
% 2.85/0.97  fof(f21,plain,(
% 2.85/0.97    ! [X0,X1] : (! [X3] : (k1_funct_1(sK3(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK3(X0,X1)) = X0 & v1_funct_1(sK3(X0,X1)) & v1_relat_1(sK3(X0,X1)))),
% 2.85/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f10,f20])).
% 2.85/0.97  
% 2.85/0.97  fof(f36,plain,(
% 2.85/0.97    ( ! [X0,X1] : (k1_relat_1(sK3(X0,X1)) = X0) )),
% 2.85/0.97    inference(cnf_transformation,[],[f21])).
% 2.85/0.97  
% 2.85/0.97  fof(f6,conjecture,(
% 2.85/0.97    ! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 2.85/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/0.97  
% 2.85/0.97  fof(f7,negated_conjecture,(
% 2.85/0.97    ~! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 2.85/0.97    inference(negated_conjecture,[],[f6])).
% 2.85/0.97  
% 2.85/0.97  fof(f12,plain,(
% 2.85/0.97    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : ((X1 = X2 | (k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))))),
% 2.85/0.97    inference(ennf_transformation,[],[f7])).
% 2.85/0.97  
% 2.85/0.97  fof(f13,plain,(
% 2.85/0.97    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.85/0.97    inference(flattening,[],[f12])).
% 2.85/0.97  
% 2.85/0.97  fof(f24,plain,(
% 2.85/0.97    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) => (k1_xboole_0 != sK5 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != sK5 | k1_relat_1(X1) != sK5 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.85/0.97    introduced(choice_axiom,[])).
% 2.85/0.97  
% 2.85/0.97  fof(f25,plain,(
% 2.85/0.97    k1_xboole_0 != sK5 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != sK5 | k1_relat_1(X1) != sK5 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.85/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f13,f24])).
% 2.85/0.97  
% 2.85/0.97  fof(f42,plain,(
% 2.85/0.97    ( ! [X2,X1] : (X1 = X2 | k1_relat_1(X2) != sK5 | k1_relat_1(X1) != sK5 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.85/0.97    inference(cnf_transformation,[],[f25])).
% 2.85/0.97  
% 2.85/0.97  fof(f34,plain,(
% 2.85/0.97    ( ! [X0,X1] : (v1_relat_1(sK3(X0,X1))) )),
% 2.85/0.97    inference(cnf_transformation,[],[f21])).
% 2.85/0.97  
% 2.85/0.97  fof(f35,plain,(
% 2.85/0.97    ( ! [X0,X1] : (v1_funct_1(sK3(X0,X1))) )),
% 2.85/0.97    inference(cnf_transformation,[],[f21])).
% 2.85/0.97  
% 2.85/0.97  fof(f38,plain,(
% 2.85/0.97    ( ! [X0] : (v1_relat_1(sK4(X0))) )),
% 2.85/0.97    inference(cnf_transformation,[],[f23])).
% 2.85/0.97  
% 2.85/0.97  fof(f39,plain,(
% 2.85/0.97    ( ! [X0] : (v1_funct_1(sK4(X0))) )),
% 2.85/0.97    inference(cnf_transformation,[],[f23])).
% 2.85/0.97  
% 2.85/0.97  fof(f1,axiom,(
% 2.85/0.97    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 2.85/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/0.97  
% 2.85/0.97  fof(f14,plain,(
% 2.85/0.97    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 2.85/0.97    inference(nnf_transformation,[],[f1])).
% 2.85/0.97  
% 2.85/0.97  fof(f15,plain,(
% 2.85/0.97    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 2.85/0.97    inference(rectify,[],[f14])).
% 2.85/0.97  
% 2.85/0.97  fof(f18,plain,(
% 2.85/0.97    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0))),
% 2.85/0.97    introduced(choice_axiom,[])).
% 2.85/0.97  
% 2.85/0.97  fof(f17,plain,(
% 2.85/0.97    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) => r2_hidden(k4_tarski(X2,sK1(X0,X1)),X0))) )),
% 2.85/0.97    introduced(choice_axiom,[])).
% 2.85/0.97  
% 2.85/0.97  fof(f16,plain,(
% 2.85/0.97    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK0(X0,X1),X3),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK0(X0,X1),X4),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 2.85/0.97    introduced(choice_axiom,[])).
% 2.85/0.97  
% 2.85/0.97  fof(f19,plain,(
% 2.85/0.97    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK0(X0,X1),X3),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 2.85/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f18,f17,f16])).
% 2.85/0.97  
% 2.85/0.97  fof(f28,plain,(
% 2.85/0.97    ( ! [X0,X1] : (k1_relat_1(X0) = X1 | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0) | r2_hidden(sK0(X0,X1),X1)) )),
% 2.85/0.97    inference(cnf_transformation,[],[f19])).
% 2.85/0.97  
% 2.85/0.97  fof(f27,plain,(
% 2.85/0.97    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 2.85/0.97    inference(cnf_transformation,[],[f19])).
% 2.85/0.97  
% 2.85/0.97  fof(f44,plain,(
% 2.85/0.97    ( ! [X6,X0,X5] : (r2_hidden(X5,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X5,X6),X0)) )),
% 2.85/0.97    inference(equality_resolution,[],[f27])).
% 2.85/0.97  
% 2.85/0.97  fof(f2,axiom,(
% 2.85/0.97    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_relat_1(k1_xboole_0) = k1_xboole_0),
% 2.85/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/0.97  
% 2.85/0.97  fof(f30,plain,(
% 2.85/0.97    k1_relat_1(k1_xboole_0) = k1_xboole_0),
% 2.85/0.97    inference(cnf_transformation,[],[f2])).
% 2.85/0.97  
% 2.85/0.97  fof(f26,plain,(
% 2.85/0.97    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 2.85/0.97    inference(cnf_transformation,[],[f19])).
% 2.85/0.97  
% 2.85/0.97  fof(f45,plain,(
% 2.85/0.97    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 2.85/0.97    inference(equality_resolution,[],[f26])).
% 2.85/0.97  
% 2.85/0.97  fof(f37,plain,(
% 2.85/0.97    ( ! [X0,X3,X1] : (k1_funct_1(sK3(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) )),
% 2.85/0.97    inference(cnf_transformation,[],[f21])).
% 2.85/0.97  
% 2.85/0.97  fof(f3,axiom,(
% 2.85/0.97    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_relat_1(X0) = k1_xboole_0) => k1_xboole_0 = X0))),
% 2.85/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/0.97  
% 2.85/0.97  fof(f8,plain,(
% 2.85/0.97    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_relat_1(X0) != k1_xboole_0)) | ~v1_relat_1(X0))),
% 2.85/0.97    inference(ennf_transformation,[],[f3])).
% 2.85/0.97  
% 2.85/0.97  fof(f9,plain,(
% 2.85/0.97    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_relat_1(X0) != k1_xboole_0) | ~v1_relat_1(X0))),
% 2.85/0.97    inference(flattening,[],[f8])).
% 2.85/0.97  
% 2.85/0.97  fof(f32,plain,(
% 2.85/0.97    ( ! [X0] : (k1_xboole_0 = X0 | k1_relat_1(X0) != k1_xboole_0 | ~v1_relat_1(X0)) )),
% 2.85/0.97    inference(cnf_transformation,[],[f9])).
% 2.85/0.97  
% 2.85/0.97  fof(f43,plain,(
% 2.85/0.97    k1_xboole_0 != sK5),
% 2.85/0.97    inference(cnf_transformation,[],[f25])).
% 2.85/0.97  
% 2.85/0.97  cnf(c_13,plain,
% 2.85/0.97      ( k1_relat_1(sK4(X0)) = X0 ),
% 2.85/0.97      inference(cnf_transformation,[],[f40]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_9,plain,
% 2.85/0.97      ( k1_relat_1(sK3(X0,X1)) = X0 ),
% 2.85/0.97      inference(cnf_transformation,[],[f36]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_17,negated_conjecture,
% 2.85/0.97      ( ~ v1_funct_1(X0)
% 2.85/0.97      | ~ v1_funct_1(X1)
% 2.85/0.97      | ~ v1_relat_1(X0)
% 2.85/0.97      | ~ v1_relat_1(X1)
% 2.85/0.97      | X1 = X0
% 2.85/0.97      | k1_relat_1(X0) != sK5
% 2.85/0.97      | k1_relat_1(X1) != sK5 ),
% 2.85/0.97      inference(cnf_transformation,[],[f42]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_408,plain,
% 2.85/0.97      ( X0 = X1
% 2.85/0.97      | k1_relat_1(X0) != sK5
% 2.85/0.97      | k1_relat_1(X1) != sK5
% 2.85/0.97      | v1_funct_1(X1) != iProver_top
% 2.85/0.97      | v1_funct_1(X0) != iProver_top
% 2.85/0.97      | v1_relat_1(X1) != iProver_top
% 2.85/0.97      | v1_relat_1(X0) != iProver_top ),
% 2.85/0.97      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_770,plain,
% 2.85/0.97      ( sK3(X0,X1) = X2
% 2.85/0.97      | k1_relat_1(X2) != sK5
% 2.85/0.97      | sK5 != X0
% 2.85/0.97      | v1_funct_1(X2) != iProver_top
% 2.85/0.97      | v1_funct_1(sK3(X0,X1)) != iProver_top
% 2.85/0.97      | v1_relat_1(X2) != iProver_top
% 2.85/0.97      | v1_relat_1(sK3(X0,X1)) != iProver_top ),
% 2.85/0.97      inference(superposition,[status(thm)],[c_9,c_408]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_11,plain,
% 2.85/0.97      ( v1_relat_1(sK3(X0,X1)) ),
% 2.85/0.97      inference(cnf_transformation,[],[f34]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_31,plain,
% 2.85/0.97      ( v1_relat_1(sK3(X0,X1)) = iProver_top ),
% 2.85/0.97      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_10,plain,
% 2.85/0.97      ( v1_funct_1(sK3(X0,X1)) ),
% 2.85/0.97      inference(cnf_transformation,[],[f35]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_34,plain,
% 2.85/0.97      ( v1_funct_1(sK3(X0,X1)) = iProver_top ),
% 2.85/0.97      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_850,plain,
% 2.85/0.97      ( v1_relat_1(X2) != iProver_top
% 2.85/0.97      | sK3(X0,X1) = X2
% 2.85/0.97      | k1_relat_1(X2) != sK5
% 2.85/0.97      | sK5 != X0
% 2.85/0.97      | v1_funct_1(X2) != iProver_top ),
% 2.85/0.97      inference(global_propositional_subsumption,
% 2.85/0.97                [status(thm)],
% 2.85/0.97                [c_770,c_31,c_34]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_851,plain,
% 2.85/0.97      ( sK3(X0,X1) = X2
% 2.85/0.97      | k1_relat_1(X2) != sK5
% 2.85/0.97      | sK5 != X0
% 2.85/0.97      | v1_funct_1(X2) != iProver_top
% 2.85/0.97      | v1_relat_1(X2) != iProver_top ),
% 2.85/0.97      inference(renaming,[status(thm)],[c_850]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_861,plain,
% 2.85/0.97      ( sK3(X0,X1) = sK4(X2)
% 2.85/0.97      | sK5 != X2
% 2.85/0.97      | sK5 != X0
% 2.85/0.97      | v1_funct_1(sK4(X2)) != iProver_top
% 2.85/0.97      | v1_relat_1(sK4(X2)) != iProver_top ),
% 2.85/0.97      inference(superposition,[status(thm)],[c_13,c_851]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_571,plain,
% 2.85/0.97      ( sK4(X0) = X1
% 2.85/0.97      | k1_relat_1(X1) != sK5
% 2.85/0.97      | sK5 != X0
% 2.85/0.97      | v1_funct_1(X1) != iProver_top
% 2.85/0.97      | v1_funct_1(sK4(X0)) != iProver_top
% 2.85/0.97      | v1_relat_1(X1) != iProver_top
% 2.85/0.97      | v1_relat_1(sK4(X0)) != iProver_top ),
% 2.85/0.97      inference(superposition,[status(thm)],[c_13,c_408]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_15,plain,
% 2.85/0.97      ( v1_relat_1(sK4(X0)) ),
% 2.85/0.97      inference(cnf_transformation,[],[f38]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_21,plain,
% 2.85/0.97      ( v1_relat_1(sK4(X0)) = iProver_top ),
% 2.85/0.97      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_14,plain,
% 2.85/0.97      ( v1_funct_1(sK4(X0)) ),
% 2.85/0.97      inference(cnf_transformation,[],[f39]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_24,plain,
% 2.85/0.97      ( v1_funct_1(sK4(X0)) = iProver_top ),
% 2.85/0.97      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_719,plain,
% 2.85/0.97      ( v1_relat_1(X1) != iProver_top
% 2.85/0.97      | sK4(X0) = X1
% 2.85/0.97      | k1_relat_1(X1) != sK5
% 2.85/0.97      | sK5 != X0
% 2.85/0.97      | v1_funct_1(X1) != iProver_top ),
% 2.85/0.97      inference(global_propositional_subsumption,
% 2.85/0.97                [status(thm)],
% 2.85/0.97                [c_571,c_21,c_24]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_720,plain,
% 2.85/0.97      ( sK4(X0) = X1
% 2.85/0.97      | k1_relat_1(X1) != sK5
% 2.85/0.97      | sK5 != X0
% 2.85/0.97      | v1_funct_1(X1) != iProver_top
% 2.85/0.97      | v1_relat_1(X1) != iProver_top ),
% 2.85/0.97      inference(renaming,[status(thm)],[c_719]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_769,plain,
% 2.85/0.97      ( sK3(X0,X1) = sK4(X2)
% 2.85/0.97      | sK5 != X0
% 2.85/0.97      | sK5 != X2
% 2.85/0.97      | v1_funct_1(sK3(X0,X1)) != iProver_top
% 2.85/0.97      | v1_relat_1(sK3(X0,X1)) != iProver_top ),
% 2.85/0.97      inference(superposition,[status(thm)],[c_9,c_720]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_795,plain,
% 2.85/0.97      ( ~ v1_funct_1(sK3(X0,X1))
% 2.85/0.97      | ~ v1_relat_1(sK3(X0,X1))
% 2.85/0.97      | sK3(X0,X1) = sK4(X2)
% 2.85/0.97      | sK5 != X0
% 2.85/0.97      | sK5 != X2 ),
% 2.85/0.97      inference(predicate_to_equality_rev,[status(thm)],[c_769]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_960,plain,
% 2.85/0.97      ( sK3(X0,X1) = sK4(X2) | sK5 != X2 | sK5 != X0 ),
% 2.85/0.97      inference(global_propositional_subsumption,
% 2.85/0.97                [status(thm)],
% 2.85/0.97                [c_861,c_11,c_10,c_795]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_961,plain,
% 2.85/0.97      ( sK3(X0,X1) = sK4(X2) | sK5 != X0 | sK5 != X2 ),
% 2.85/0.97      inference(renaming,[status(thm)],[c_960]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_965,plain,
% 2.85/0.97      ( sK3(sK5,X0) = sK4(X1) | sK5 != X1 ),
% 2.85/0.97      inference(equality_resolution,[status(thm)],[c_961]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_1019,plain,
% 2.85/0.97      ( sK3(sK5,X0) = sK4(sK5) ),
% 2.85/0.97      inference(equality_resolution,[status(thm)],[c_965]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_1,plain,
% 2.85/0.97      ( r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0)
% 2.85/0.97      | r2_hidden(sK0(X0,X1),X1)
% 2.85/0.97      | k1_relat_1(X0) = X1 ),
% 2.85/0.97      inference(cnf_transformation,[],[f28]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_419,plain,
% 2.85/0.97      ( k1_relat_1(X0) = X1
% 2.85/0.97      | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0) = iProver_top
% 2.85/0.97      | r2_hidden(sK0(X0,X1),X1) = iProver_top ),
% 2.85/0.97      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_2,plain,
% 2.85/0.97      ( r2_hidden(X0,k1_relat_1(X1)) | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
% 2.85/0.97      inference(cnf_transformation,[],[f44]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_418,plain,
% 2.85/0.97      ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
% 2.85/0.97      | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top ),
% 2.85/0.97      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_1747,plain,
% 2.85/0.97      ( k1_relat_1(X0) = X1
% 2.85/0.97      | r2_hidden(sK0(X0,X1),X1) = iProver_top
% 2.85/0.97      | r2_hidden(sK0(X0,X1),k1_relat_1(X0)) = iProver_top ),
% 2.85/0.97      inference(superposition,[status(thm)],[c_419,c_418]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_2325,plain,
% 2.85/0.97      ( k1_relat_1(sK3(X0,X1)) = X2
% 2.85/0.97      | r2_hidden(sK0(sK3(X0,X1),X2),X0) = iProver_top
% 2.85/0.97      | r2_hidden(sK0(sK3(X0,X1),X2),X2) = iProver_top ),
% 2.85/0.97      inference(superposition,[status(thm)],[c_9,c_1747]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_2465,plain,
% 2.85/0.97      ( X0 = X1
% 2.85/0.97      | r2_hidden(sK0(sK3(X1,X2),X0),X1) = iProver_top
% 2.85/0.97      | r2_hidden(sK0(sK3(X1,X2),X0),X0) = iProver_top ),
% 2.85/0.97      inference(demodulation,[status(thm)],[c_2325,c_9]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_3052,plain,
% 2.85/0.97      ( sK5 = X0
% 2.85/0.97      | r2_hidden(sK0(sK3(sK5,X1),X0),X0) = iProver_top
% 2.85/0.97      | r2_hidden(sK0(sK4(sK5),X0),sK5) = iProver_top ),
% 2.85/0.97      inference(superposition,[status(thm)],[c_1019,c_2465]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_3199,plain,
% 2.85/0.97      ( sK5 = X0
% 2.85/0.97      | r2_hidden(sK0(sK4(sK5),X0),X0) = iProver_top
% 2.85/0.97      | r2_hidden(sK0(sK4(sK5),X0),sK5) = iProver_top ),
% 2.85/0.97      inference(demodulation,[status(thm)],[c_3052,c_1019]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_5,plain,
% 2.85/0.97      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.85/0.97      inference(cnf_transformation,[],[f30]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_3,plain,
% 2.85/0.97      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.85/0.97      | r2_hidden(k4_tarski(X0,sK2(X1,X0)),X1) ),
% 2.85/0.97      inference(cnf_transformation,[],[f45]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_417,plain,
% 2.85/0.97      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 2.85/0.97      | r2_hidden(k4_tarski(X0,sK2(X1,X0)),X1) = iProver_top ),
% 2.85/0.97      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_8,plain,
% 2.85/0.97      ( ~ r2_hidden(X0,X1) | k1_funct_1(sK3(X1,X2),X0) = X2 ),
% 2.85/0.97      inference(cnf_transformation,[],[f37]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_414,plain,
% 2.85/0.97      ( k1_funct_1(sK3(X0,X1),X2) = X1
% 2.85/0.97      | r2_hidden(X2,X0) != iProver_top ),
% 2.85/0.97      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_1576,plain,
% 2.85/0.97      ( k1_funct_1(sK3(X0,X1),k4_tarski(X2,sK2(X0,X2))) = X1
% 2.85/0.97      | r2_hidden(X2,k1_relat_1(X0)) != iProver_top ),
% 2.85/0.97      inference(superposition,[status(thm)],[c_417,c_414]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_2127,plain,
% 2.85/0.97      ( k1_funct_1(sK3(k1_xboole_0,X0),k4_tarski(X1,sK2(k1_xboole_0,X1))) = X0
% 2.85/0.97      | r2_hidden(X1,k1_xboole_0) != iProver_top ),
% 2.85/0.97      inference(superposition,[status(thm)],[c_5,c_1576]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_7,plain,
% 2.85/0.97      ( ~ v1_relat_1(X0)
% 2.85/0.97      | k1_relat_1(X0) != k1_xboole_0
% 2.85/0.97      | k1_xboole_0 = X0 ),
% 2.85/0.97      inference(cnf_transformation,[],[f32]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_415,plain,
% 2.85/0.97      ( k1_relat_1(X0) != k1_xboole_0
% 2.85/0.97      | k1_xboole_0 = X0
% 2.85/0.97      | v1_relat_1(X0) != iProver_top ),
% 2.85/0.97      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_1141,plain,
% 2.85/0.97      ( sK3(X0,X1) = k1_xboole_0
% 2.85/0.97      | k1_xboole_0 != X0
% 2.85/0.97      | v1_relat_1(sK3(X0,X1)) != iProver_top ),
% 2.85/0.97      inference(superposition,[status(thm)],[c_9,c_415]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_1593,plain,
% 2.85/0.97      ( k1_xboole_0 != X0 | sK3(X0,X1) = k1_xboole_0 ),
% 2.85/0.97      inference(global_propositional_subsumption,
% 2.85/0.97                [status(thm)],
% 2.85/0.97                [c_1141,c_31]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_1594,plain,
% 2.85/0.97      ( sK3(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0 ),
% 2.85/0.97      inference(renaming,[status(thm)],[c_1593]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_1598,plain,
% 2.85/0.97      ( sK3(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.85/0.97      inference(equality_resolution,[status(thm)],[c_1594]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_2140,plain,
% 2.85/0.97      ( k1_funct_1(k1_xboole_0,k4_tarski(X0,sK2(k1_xboole_0,X0))) = X1
% 2.85/0.97      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.85/0.97      inference(light_normalisation,[status(thm)],[c_2127,c_1598]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_3373,plain,
% 2.85/0.97      ( k1_funct_1(k1_xboole_0,k4_tarski(sK0(sK4(sK5),k1_xboole_0),sK2(k1_xboole_0,sK0(sK4(sK5),k1_xboole_0)))) = X0
% 2.85/0.97      | sK5 = k1_xboole_0
% 2.85/0.97      | r2_hidden(sK0(sK4(sK5),k1_xboole_0),sK5) = iProver_top ),
% 2.85/0.97      inference(superposition,[status(thm)],[c_3199,c_2140]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_16,negated_conjecture,
% 2.85/0.97      ( k1_xboole_0 != sK5 ),
% 2.85/0.97      inference(cnf_transformation,[],[f43]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_161,plain,( X0 = X0 ),theory(equality) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_178,plain,
% 2.85/0.97      ( k1_xboole_0 = k1_xboole_0 ),
% 2.85/0.97      inference(instantiation,[status(thm)],[c_161]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_162,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_564,plain,
% 2.85/0.97      ( sK5 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK5 ),
% 2.85/0.97      inference(instantiation,[status(thm)],[c_162]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_565,plain,
% 2.85/0.97      ( sK5 != k1_xboole_0
% 2.85/0.97      | k1_xboole_0 = sK5
% 2.85/0.97      | k1_xboole_0 != k1_xboole_0 ),
% 2.85/0.97      inference(instantiation,[status(thm)],[c_564]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_4319,plain,
% 2.85/0.97      ( k1_funct_1(k1_xboole_0,k4_tarski(sK0(sK4(sK5),k1_xboole_0),sK2(k1_xboole_0,sK0(sK4(sK5),k1_xboole_0)))) = X0
% 2.85/0.97      | r2_hidden(sK0(sK4(sK5),k1_xboole_0),sK5) = iProver_top ),
% 2.85/0.97      inference(global_propositional_subsumption,
% 2.85/0.97                [status(thm)],
% 2.85/0.97                [c_3373,c_16,c_178,c_565]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_4329,plain,
% 2.85/0.97      ( k1_funct_1(sK3(sK5,X0),sK0(sK4(sK5),k1_xboole_0)) = X0
% 2.85/0.97      | k1_funct_1(k1_xboole_0,k4_tarski(sK0(sK4(sK5),k1_xboole_0),sK2(k1_xboole_0,sK0(sK4(sK5),k1_xboole_0)))) = X1 ),
% 2.85/0.97      inference(superposition,[status(thm)],[c_4319,c_414]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_4348,plain,
% 2.85/0.97      ( k1_funct_1(sK4(sK5),sK0(sK4(sK5),k1_xboole_0)) = X0
% 2.85/0.97      | k1_funct_1(k1_xboole_0,k4_tarski(sK0(sK4(sK5),k1_xboole_0),sK2(k1_xboole_0,sK0(sK4(sK5),k1_xboole_0)))) = X1 ),
% 2.85/0.97      inference(light_normalisation,[status(thm)],[c_4329,c_1019]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_5855,plain,
% 2.85/0.97      ( k1_funct_1(sK4(sK5),sK0(sK4(sK5),k1_xboole_0)) = X0
% 2.85/0.97      | k1_funct_1(k1_xboole_0,k4_tarski(sK0(sK4(sK5),k1_xboole_0),sK2(k1_xboole_0,sK0(sK4(sK5),k1_xboole_0)))) != k1_funct_1(sK4(sK5),sK0(sK4(sK5),k1_xboole_0)) ),
% 2.85/0.97      inference(equality_factoring,[status(thm)],[c_4348]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_5860,plain,
% 2.85/0.97      ( k1_funct_1(sK4(sK5),sK0(sK4(sK5),k1_xboole_0)) = X0 ),
% 2.85/0.97      inference(forward_subsumption_resolution,
% 2.85/0.97                [status(thm)],
% 2.85/0.97                [c_5855,c_4348]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_6049,plain,
% 2.85/0.97      ( k1_funct_1(sK4(sK5),sK0(sK4(sK5),k1_xboole_0)) = k1_xboole_0 ),
% 2.85/0.97      inference(superposition,[status(thm)],[c_5860,c_1598]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_6050,plain,
% 2.85/0.97      ( k1_funct_1(sK4(sK5),sK0(sK4(sK5),k1_xboole_0)) = sK4(sK5) ),
% 2.85/0.97      inference(superposition,[status(thm)],[c_5860,c_1019]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_6735,plain,
% 2.85/0.97      ( sK4(sK5) = k1_xboole_0 ),
% 2.85/0.97      inference(demodulation,[status(thm)],[c_6049,c_6050]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_163,plain,
% 2.85/0.97      ( X0 != X1 | k1_relat_1(X0) = k1_relat_1(X1) ),
% 2.85/0.97      theory(equality) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_2536,plain,
% 2.85/0.97      ( sK4(sK5) != X0 | k1_relat_1(sK4(sK5)) = k1_relat_1(X0) ),
% 2.85/0.97      inference(instantiation,[status(thm)],[c_163]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_2538,plain,
% 2.85/0.97      ( sK4(sK5) != k1_xboole_0
% 2.85/0.97      | k1_relat_1(sK4(sK5)) = k1_relat_1(k1_xboole_0) ),
% 2.85/0.97      inference(instantiation,[status(thm)],[c_2536]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_1040,plain,
% 2.85/0.97      ( k1_relat_1(X0) != X1
% 2.85/0.97      | k1_xboole_0 != X1
% 2.85/0.97      | k1_xboole_0 = k1_relat_1(X0) ),
% 2.85/0.97      inference(instantiation,[status(thm)],[c_162]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_1795,plain,
% 2.85/0.97      ( k1_relat_1(sK4(sK5)) != X0
% 2.85/0.97      | k1_xboole_0 != X0
% 2.85/0.97      | k1_xboole_0 = k1_relat_1(sK4(sK5)) ),
% 2.85/0.97      inference(instantiation,[status(thm)],[c_1040]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_2533,plain,
% 2.85/0.97      ( k1_relat_1(sK4(sK5)) != k1_relat_1(X0)
% 2.85/0.97      | k1_xboole_0 != k1_relat_1(X0)
% 2.85/0.97      | k1_xboole_0 = k1_relat_1(sK4(sK5)) ),
% 2.85/0.97      inference(instantiation,[status(thm)],[c_1795]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_2537,plain,
% 2.85/0.97      ( k1_relat_1(sK4(sK5)) != k1_relat_1(k1_xboole_0)
% 2.85/0.97      | k1_xboole_0 = k1_relat_1(sK4(sK5))
% 2.85/0.97      | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
% 2.85/0.97      inference(instantiation,[status(thm)],[c_2533]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_991,plain,
% 2.85/0.97      ( sK5 != k1_relat_1(X0)
% 2.85/0.97      | k1_xboole_0 != k1_relat_1(X0)
% 2.85/0.97      | k1_xboole_0 = sK5 ),
% 2.85/0.97      inference(instantiation,[status(thm)],[c_564]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_1622,plain,
% 2.85/0.97      ( sK5 != k1_relat_1(sK4(sK5))
% 2.85/0.97      | k1_xboole_0 != k1_relat_1(sK4(sK5))
% 2.85/0.97      | k1_xboole_0 = sK5 ),
% 2.85/0.97      inference(instantiation,[status(thm)],[c_991]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_1281,plain,
% 2.85/0.97      ( k1_relat_1(sK4(sK5)) = sK5 ),
% 2.85/0.97      inference(instantiation,[status(thm)],[c_13]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_579,plain,
% 2.85/0.97      ( X0 != X1 | sK5 != X1 | sK5 = X0 ),
% 2.85/0.97      inference(instantiation,[status(thm)],[c_162]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_711,plain,
% 2.85/0.97      ( X0 != sK5 | sK5 = X0 | sK5 != sK5 ),
% 2.85/0.97      inference(instantiation,[status(thm)],[c_579]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_906,plain,
% 2.85/0.97      ( k1_relat_1(X0) != sK5 | sK5 = k1_relat_1(X0) | sK5 != sK5 ),
% 2.85/0.97      inference(instantiation,[status(thm)],[c_711]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_1280,plain,
% 2.85/0.97      ( k1_relat_1(sK4(sK5)) != sK5
% 2.85/0.97      | sK5 = k1_relat_1(sK4(sK5))
% 2.85/0.97      | sK5 != sK5 ),
% 2.85/0.97      inference(instantiation,[status(thm)],[c_906]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_1041,plain,
% 2.85/0.97      ( k1_relat_1(k1_xboole_0) != k1_xboole_0
% 2.85/0.97      | k1_xboole_0 = k1_relat_1(k1_xboole_0)
% 2.85/0.97      | k1_xboole_0 != k1_xboole_0 ),
% 2.85/0.97      inference(instantiation,[status(thm)],[c_1040]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_712,plain,
% 2.85/0.97      ( sK5 = sK5 ),
% 2.85/0.97      inference(instantiation,[status(thm)],[c_161]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(contradiction,plain,
% 2.85/0.97      ( $false ),
% 2.85/0.97      inference(minisat,
% 2.85/0.97                [status(thm)],
% 2.85/0.97                [c_6735,c_2538,c_2537,c_1622,c_1281,c_1280,c_1041,c_712,
% 2.85/0.97                 c_178,c_5,c_16]) ).
% 2.85/0.97  
% 2.85/0.97  
% 2.85/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 2.85/0.97  
% 2.85/0.97  ------                               Statistics
% 2.85/0.97  
% 2.85/0.97  ------ General
% 2.85/0.97  
% 2.85/0.97  abstr_ref_over_cycles:                  0
% 2.85/0.97  abstr_ref_under_cycles:                 0
% 2.85/0.97  gc_basic_clause_elim:                   0
% 2.85/0.97  forced_gc_time:                         0
% 2.85/0.97  parsing_time:                           0.01
% 2.85/0.97  unif_index_cands_time:                  0.
% 2.85/0.97  unif_index_add_time:                    0.
% 2.85/0.97  orderings_time:                         0.
% 2.85/0.97  out_proof_time:                         0.008
% 2.85/0.97  total_time:                             0.211
% 2.85/0.97  num_of_symbols:                         46
% 2.85/0.97  num_of_terms:                           5238
% 2.85/0.97  
% 2.85/0.97  ------ Preprocessing
% 2.85/0.97  
% 2.85/0.97  num_of_splits:                          0
% 2.85/0.97  num_of_split_atoms:                     0
% 2.85/0.97  num_of_reused_defs:                     0
% 2.85/0.97  num_eq_ax_congr_red:                    20
% 2.85/0.97  num_of_sem_filtered_clauses:            1
% 2.85/0.97  num_of_subtypes:                        0
% 2.85/0.97  monotx_restored_types:                  0
% 2.85/0.97  sat_num_of_epr_types:                   0
% 2.85/0.97  sat_num_of_non_cyclic_types:            0
% 2.85/0.97  sat_guarded_non_collapsed_types:        0
% 2.85/0.97  num_pure_diseq_elim:                    0
% 2.85/0.97  simp_replaced_by:                       0
% 2.85/0.97  res_preprocessed:                       73
% 2.85/0.97  prep_upred:                             0
% 2.85/0.97  prep_unflattend:                        0
% 2.85/0.97  smt_new_axioms:                         0
% 2.85/0.97  pred_elim_cands:                        3
% 2.85/0.97  pred_elim:                              0
% 2.85/0.97  pred_elim_cl:                           0
% 2.85/0.97  pred_elim_cycles:                       1
% 2.85/0.97  merged_defs:                            0
% 2.85/0.97  merged_defs_ncl:                        0
% 2.85/0.97  bin_hyper_res:                          0
% 2.85/0.97  prep_cycles:                            3
% 2.85/0.97  pred_elim_time:                         0.
% 2.85/0.97  splitting_time:                         0.
% 2.85/0.97  sem_filter_time:                        0.
% 2.85/0.97  monotx_time:                            0.
% 2.85/0.97  subtype_inf_time:                       0.
% 2.85/0.97  
% 2.85/0.97  ------ Problem properties
% 2.85/0.97  
% 2.85/0.97  clauses:                                18
% 2.85/0.97  conjectures:                            2
% 2.85/0.97  epr:                                    1
% 2.85/0.97  horn:                                   17
% 2.85/0.97  ground:                                 3
% 2.85/0.97  unary:                                  9
% 2.85/0.97  binary:                                 4
% 2.85/0.97  lits:                                   36
% 2.85/0.97  lits_eq:                                16
% 2.85/0.97  fd_pure:                                0
% 2.85/0.97  fd_pseudo:                              0
% 2.85/0.97  fd_cond:                                2
% 2.85/0.97  fd_pseudo_cond:                         3
% 2.85/0.97  ac_symbols:                             0
% 2.85/0.97  
% 2.85/0.97  ------ Propositional Solver
% 2.85/0.97  
% 2.85/0.97  prop_solver_calls:                      28
% 2.85/0.97  prop_fast_solver_calls:                 540
% 2.85/0.97  smt_solver_calls:                       0
% 2.85/0.97  smt_fast_solver_calls:                  0
% 2.85/0.97  prop_num_of_clauses:                    1645
% 2.85/0.97  prop_preprocess_simplified:             3722
% 2.85/0.97  prop_fo_subsumed:                       31
% 2.85/0.97  prop_solver_time:                       0.
% 2.85/0.97  smt_solver_time:                        0.
% 2.85/0.97  smt_fast_solver_time:                   0.
% 2.85/0.97  prop_fast_solver_time:                  0.
% 2.85/0.97  prop_unsat_core_time:                   0.
% 2.85/0.97  
% 2.85/0.97  ------ QBF
% 2.85/0.97  
% 2.85/0.97  qbf_q_res:                              0
% 2.85/0.97  qbf_num_tautologies:                    0
% 2.85/0.97  qbf_prep_cycles:                        0
% 2.85/0.97  
% 2.85/0.97  ------ BMC1
% 2.85/0.97  
% 2.85/0.97  bmc1_current_bound:                     -1
% 2.85/0.97  bmc1_last_solved_bound:                 -1
% 2.85/0.97  bmc1_unsat_core_size:                   -1
% 2.85/0.97  bmc1_unsat_core_parents_size:           -1
% 2.85/0.97  bmc1_merge_next_fun:                    0
% 2.85/0.97  bmc1_unsat_core_clauses_time:           0.
% 2.85/0.97  
% 2.85/0.97  ------ Instantiation
% 2.85/0.97  
% 2.85/0.97  inst_num_of_clauses:                    413
% 2.85/0.97  inst_num_in_passive:                    171
% 2.85/0.97  inst_num_in_active:                     218
% 2.85/0.97  inst_num_in_unprocessed:                24
% 2.85/0.97  inst_num_of_loops:                      330
% 2.85/0.97  inst_num_of_learning_restarts:          0
% 2.85/0.97  inst_num_moves_active_passive:          104
% 2.85/0.97  inst_lit_activity:                      0
% 2.85/0.97  inst_lit_activity_moves:                0
% 2.85/0.97  inst_num_tautologies:                   0
% 2.85/0.97  inst_num_prop_implied:                  0
% 2.85/0.97  inst_num_existing_simplified:           0
% 2.85/0.97  inst_num_eq_res_simplified:             0
% 2.85/0.97  inst_num_child_elim:                    0
% 2.85/0.97  inst_num_of_dismatching_blockings:      202
% 2.85/0.97  inst_num_of_non_proper_insts:           615
% 2.85/0.97  inst_num_of_duplicates:                 0
% 2.85/0.97  inst_inst_num_from_inst_to_res:         0
% 2.85/0.97  inst_dismatching_checking_time:         0.
% 2.85/0.97  
% 2.85/0.97  ------ Resolution
% 2.85/0.97  
% 2.85/0.97  res_num_of_clauses:                     0
% 2.85/0.97  res_num_in_passive:                     0
% 2.85/0.97  res_num_in_active:                      0
% 2.85/0.97  res_num_of_loops:                       76
% 2.85/0.97  res_forward_subset_subsumed:            75
% 2.85/0.97  res_backward_subset_subsumed:           0
% 2.85/0.97  res_forward_subsumed:                   0
% 2.85/0.97  res_backward_subsumed:                  0
% 2.85/0.97  res_forward_subsumption_resolution:     0
% 2.85/0.97  res_backward_subsumption_resolution:    0
% 2.85/0.97  res_clause_to_clause_subsumption:       958
% 2.85/0.97  res_orphan_elimination:                 0
% 2.85/0.97  res_tautology_del:                      37
% 2.85/0.97  res_num_eq_res_simplified:              0
% 2.85/0.97  res_num_sel_changes:                    0
% 2.85/0.97  res_moves_from_active_to_pass:          0
% 2.85/0.97  
% 2.85/0.97  ------ Superposition
% 2.85/0.97  
% 2.85/0.97  sup_time_total:                         0.
% 2.85/0.97  sup_time_generating:                    0.
% 2.85/0.97  sup_time_sim_full:                      0.
% 2.85/0.97  sup_time_sim_immed:                     0.
% 2.85/0.97  
% 2.85/0.97  sup_num_of_clauses:                     197
% 2.85/0.97  sup_num_in_active:                      39
% 2.85/0.97  sup_num_in_passive:                     158
% 2.85/0.97  sup_num_of_loops:                       65
% 2.85/0.97  sup_fw_superposition:                   89
% 2.85/0.97  sup_bw_superposition:                   481
% 2.85/0.97  sup_immediate_simplified:               316
% 2.85/0.97  sup_given_eliminated:                   4
% 2.85/0.97  comparisons_done:                       0
% 2.85/0.97  comparisons_avoided:                    17
% 2.85/0.97  
% 2.85/0.97  ------ Simplifications
% 2.85/0.97  
% 2.85/0.97  
% 2.85/0.97  sim_fw_subset_subsumed:                 121
% 2.85/0.97  sim_bw_subset_subsumed:                 70
% 2.85/0.97  sim_fw_subsumed:                        75
% 2.85/0.97  sim_bw_subsumed:                        43
% 2.85/0.97  sim_fw_subsumption_res:                 11
% 2.85/0.97  sim_bw_subsumption_res:                 3
% 2.85/0.97  sim_tautology_del:                      2
% 2.85/0.97  sim_eq_tautology_del:                   27
% 2.85/0.97  sim_eq_res_simp:                        1
% 2.85/0.97  sim_fw_demodulated:                     16
% 2.85/0.97  sim_bw_demodulated:                     72
% 2.85/0.97  sim_light_normalised:                   36
% 2.85/0.97  sim_joinable_taut:                      0
% 2.85/0.97  sim_joinable_simp:                      0
% 2.85/0.97  sim_ac_normalised:                      0
% 2.85/0.97  sim_smt_subsumption:                    0
% 2.85/0.97  
%------------------------------------------------------------------------------
