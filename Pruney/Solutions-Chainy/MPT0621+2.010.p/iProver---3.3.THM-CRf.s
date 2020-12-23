%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:49:22 EST 2020

% Result     : Theorem 11.85s
% Output     : CNFRefutation 11.85s
% Verified   : 
% Statistics : Number of formulae       :  118 (2291 expanded)
%              Number of clauses        :   63 ( 730 expanded)
%              Number of leaves         :   16 ( 566 expanded)
%              Depth                    :   29
%              Number of atoms          :  414 (11109 expanded)
%              Number of equality atoms :  265 (5917 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_xboole_0 = k1_funct_1(X1,X2) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_xboole_0 = k1_funct_1(X1,X2)
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ! [X2] :
            ( k1_xboole_0 = k1_funct_1(sK7(X0),X2)
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK7(X0)) = X0
        & v1_funct_1(sK7(X0))
        & v1_relat_1(sK7(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(sK7(X0),X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK7(X0)) = X0
      & v1_funct_1(sK7(X0))
      & v1_relat_1(sK7(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f18,f34])).

fof(f56,plain,(
    ! [X0] : k1_relat_1(sK7(X0)) = X0 ),
    inference(cnf_transformation,[],[f35])).

fof(f8,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X0)
         => k1_funct_1(X2,X3) = X1 )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k1_funct_1(X2,X3) = X1
              | ~ r2_hidden(X3,X0) )
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( ! [X3] :
            ( k1_funct_1(sK6(X0,X1),X3) = X1
            | ~ r2_hidden(X3,X0) )
        & k1_relat_1(sK6(X0,X1)) = X0
        & v1_funct_1(sK6(X0,X1))
        & v1_relat_1(sK6(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X3] :
          ( k1_funct_1(sK6(X0,X1),X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(sK6(X0,X1)) = X0
      & v1_funct_1(sK6(X0,X1))
      & v1_relat_1(sK6(X0,X1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f17,f32])).

fof(f52,plain,(
    ! [X0,X1] : k1_relat_1(sK6(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f33])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f19,plain,(
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

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f36,plain,
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
   => ( k1_xboole_0 != sK8
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != sK8
              | k1_relat_1(X1) != sK8
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( k1_xboole_0 != sK8
    & ! [X1] :
        ( ! [X2] :
            ( X1 = X2
            | k1_relat_1(X2) != sK8
            | k1_relat_1(X1) != sK8
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) )
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f20,f36])).

fof(f58,plain,(
    ! [X2,X1] :
      ( X1 = X2
      | k1_relat_1(X2) != sK8
      | k1_relat_1(X1) != sK8
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f50,plain,(
    ! [X0,X1] : v1_relat_1(sK6(X0,X1)) ),
    inference(cnf_transformation,[],[f33])).

fof(f54,plain,(
    ! [X0] : v1_relat_1(sK7(X0)) ),
    inference(cnf_transformation,[],[f35])).

fof(f55,plain,(
    ! [X0] : v1_funct_1(sK7(X0)) ),
    inference(cnf_transformation,[],[f35])).

fof(f51,plain,(
    ! [X0,X1] : v1_funct_1(sK6(X0,X1)) ),
    inference(cnf_transformation,[],[f33])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( ? [X2,X3] : k4_tarski(X2,X3) = X1
            | ~ r2_hidden(X1,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X4] :
            ( ? [X5,X6] : k4_tarski(X5,X6) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(rectify,[],[f25])).

fof(f28,plain,(
    ! [X4] :
      ( ? [X5,X6] : k4_tarski(X5,X6) = X4
     => k4_tarski(sK2(X4),sK3(X4)) = X4 ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK1(X0)
        & r2_hidden(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ( ! [X2,X3] : k4_tarski(X2,X3) != sK1(X0)
          & r2_hidden(sK1(X0),X0) ) )
      & ( ! [X4] :
            ( k4_tarski(sK2(X4),sK3(X4)) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f26,f28,f27])).

fof(f47,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | r2_hidden(sK1(X0),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(sK6(X0,X1),X3) = X1
      | ~ r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
     => r2_hidden(k4_tarski(sK4(X0),sK5(X0)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(k4_tarski(sK4(X0),sK5(X0)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f16,f30])).

fof(f49,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(k4_tarski(sK4(X0),sK5(X0)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f57,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = k1_funct_1(sK7(X0),X2)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f59,plain,(
    k1_xboole_0 != sK8 ),
    inference(cnf_transformation,[],[f37])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f21])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK0(X0,X1) != X0
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( sK0(X0,X1) = X0
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK0(X0,X1) != X0
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( sK0(X0,X1) = X0
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f60,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f44,f45])).

fof(f64,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f40,f60])).

fof(f67,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_enumset1(X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f64])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f41,f60])).

fof(f65,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_enumset1(X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f63])).

fof(f66,plain,(
    ! [X3] : r2_hidden(X3,k1_enumset1(X3,X3,X3)) ),
    inference(equality_resolution,[],[f65])).

cnf(c_15,plain,
    ( k1_relat_1(sK7(X0)) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_11,plain,
    ( k1_relat_1(sK6(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_19,negated_conjecture,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | X1 = X0
    | k1_relat_1(X0) != sK8
    | k1_relat_1(X1) != sK8 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_62955,negated_conjecture,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ iProver_ARSWP_484
    | ~ arAF5_v1_funct_1_0
    | X0 = X1
    | k1_relat_1(X1) != sK8
    | k1_relat_1(X0) != sK8 ),
    inference(arg_filter_abstr,[status(unp)],[c_19])).

cnf(c_63127,plain,
    ( X0 = X1
    | k1_relat_1(X0) != sK8
    | k1_relat_1(X1) != sK8
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | iProver_ARSWP_484 != iProver_top
    | arAF5_v1_funct_1_0 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_62955])).

cnf(c_63277,plain,
    ( sK6(X0,X1) = X2
    | k1_relat_1(X2) != sK8
    | sK8 != X0
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(sK6(X0,X1)) != iProver_top
    | iProver_ARSWP_484 != iProver_top
    | arAF5_v1_funct_1_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_63127])).

cnf(c_13,plain,
    ( v1_relat_1(sK6(X0,X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_36,plain,
    ( v1_relat_1(sK6(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_63331,plain,
    ( v1_relat_1(X2) != iProver_top
    | sK8 != X0
    | k1_relat_1(X2) != sK8
    | sK6(X0,X1) = X2
    | iProver_ARSWP_484 != iProver_top
    | arAF5_v1_funct_1_0 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_63277,c_36])).

cnf(c_63332,plain,
    ( sK6(X0,X1) = X2
    | k1_relat_1(X2) != sK8
    | sK8 != X0
    | v1_relat_1(X2) != iProver_top
    | iProver_ARSWP_484 != iProver_top
    | arAF5_v1_funct_1_0 != iProver_top ),
    inference(renaming,[status(thm)],[c_63331])).

cnf(c_63342,plain,
    ( sK6(X0,X1) = sK7(X2)
    | sK8 != X2
    | sK8 != X0
    | v1_relat_1(sK7(X2)) != iProver_top
    | iProver_ARSWP_484 != iProver_top
    | arAF5_v1_funct_1_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_63332])).

cnf(c_35680,plain,
    ( X0 = X1
    | k1_relat_1(X1) != sK8
    | k1_relat_1(X0) != sK8
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_35740,plain,
    ( sK7(X0) = X1
    | k1_relat_1(X1) != sK8
    | sK8 != X0
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK7(X0)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(sK7(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_35680])).

cnf(c_17,plain,
    ( v1_relat_1(sK7(X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_26,plain,
    ( v1_relat_1(sK7(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_16,plain,
    ( v1_funct_1(sK7(X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_29,plain,
    ( v1_funct_1(sK7(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_35743,plain,
    ( v1_relat_1(X1) != iProver_top
    | sK7(X0) = X1
    | k1_relat_1(X1) != sK8
    | sK8 != X0
    | v1_funct_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_35740,c_26,c_29])).

cnf(c_35744,plain,
    ( sK7(X0) = X1
    | k1_relat_1(X1) != sK8
    | sK8 != X0
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_35743])).

cnf(c_35800,plain,
    ( sK6(X0,X1) = sK7(X2)
    | sK8 != X0
    | sK8 != X2
    | v1_funct_1(sK6(X0,X1)) != iProver_top
    | v1_relat_1(sK6(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_35744])).

cnf(c_12,plain,
    ( v1_funct_1(sK6(X0,X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_35826,plain,
    ( ~ v1_funct_1(sK6(X0,X1))
    | ~ v1_relat_1(sK6(X0,X1))
    | sK6(X0,X1) = sK7(X2)
    | sK8 != X0
    | sK8 != X2 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_35800])).

cnf(c_35842,plain,
    ( sK6(X0,X1) = sK7(X2)
    | sK8 != X0
    | sK8 != X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_35800,c_13,c_12,c_35826])).

cnf(c_63379,plain,
    ( sK8 != X0
    | sK8 != X2
    | sK6(X0,X1) = sK7(X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_63342,c_35842])).

cnf(c_63380,plain,
    ( sK6(X0,X1) = sK7(X2)
    | sK8 != X0
    | sK8 != X2 ),
    inference(renaming,[status(thm)],[c_63379])).

cnf(c_63384,plain,
    ( sK6(sK8,X0) = sK7(X1)
    | sK8 != X1 ),
    inference(equality_resolution,[status(thm)],[c_63380])).

cnf(c_63404,plain,
    ( sK6(sK8,X0) = sK7(sK8) ),
    inference(equality_resolution,[status(thm)],[c_63384])).

cnf(c_7,plain,
    ( r2_hidden(sK1(X0),X0)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_63138,plain,
    ( r2_hidden(sK1(X0),X0) = iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_funct_1(sK6(X1,X2),X0) = X2 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_63136,plain,
    ( k1_funct_1(sK6(X0,X1),X2) = X1
    | r2_hidden(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_63444,plain,
    ( k1_funct_1(sK6(X0,X1),sK1(X0)) = X1
    | v1_relat_1(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_63138,c_63136])).

cnf(c_9,plain,
    ( r2_hidden(k4_tarski(sK4(X0),sK5(X0)),X0)
    | ~ v1_relat_1(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_63137,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(k4_tarski(sK4(X0),sK5(X0)),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_63456,plain,
    ( k1_funct_1(sK6(X0,X1),k4_tarski(sK4(X0),sK5(X0))) = X1
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_63137,c_63136])).

cnf(c_63581,plain,
    ( k1_funct_1(sK6(X0,X1),k4_tarski(sK4(X0),sK5(X0))) = X1
    | k1_funct_1(sK6(X0,X2),sK1(X0)) = X2
    | k1_xboole_0 = X0 ),
    inference(superposition,[status(thm)],[c_63444,c_63456])).

cnf(c_64020,plain,
    ( k1_funct_1(sK6(sK8,X0),sK1(sK8)) = X0
    | k1_funct_1(sK7(sK8),k4_tarski(sK4(sK8),sK5(sK8))) = X1
    | sK8 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_63404,c_63581])).

cnf(c_64048,plain,
    ( k1_funct_1(sK7(sK8),k4_tarski(sK4(sK8),sK5(sK8))) = X0
    | k1_funct_1(sK7(sK8),sK1(sK8)) = X1
    | sK8 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_64020,c_63404])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_funct_1(sK7(X1),X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_63134,plain,
    ( k1_funct_1(sK7(X0),X1) = k1_xboole_0
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_63455,plain,
    ( k1_funct_1(sK7(X0),k4_tarski(sK4(X0),sK5(X0))) = k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_63137,c_63134])).

cnf(c_63543,plain,
    ( k1_funct_1(sK6(X0,X1),sK1(X0)) = X1
    | k1_funct_1(sK7(X0),k4_tarski(sK4(X0),sK5(X0))) = k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(superposition,[status(thm)],[c_63444,c_63455])).

cnf(c_63866,plain,
    ( k1_funct_1(sK7(sK8),k4_tarski(sK4(sK8),sK5(sK8))) = k1_xboole_0
    | k1_funct_1(sK7(sK8),sK1(sK8)) = X0
    | sK8 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_63404,c_63543])).

cnf(c_18,negated_conjecture,
    ( k1_xboole_0 != sK8 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_59,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_4,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X0,X0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_62,plain,
    ( r2_hidden(k1_xboole_0,k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_925,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2172,plain,
    ( sK8 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK8 ),
    inference(instantiation,[status(thm)],[c_925])).

cnf(c_2173,plain,
    ( sK8 != k1_xboole_0
    | k1_xboole_0 = sK8
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2172])).

cnf(c_63883,plain,
    ( k1_funct_1(sK7(sK8),sK1(sK8)) = X0
    | k1_funct_1(sK7(sK8),k4_tarski(sK4(sK8),sK5(sK8))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_63866,c_18,c_59,c_62,c_2173])).

cnf(c_63884,plain,
    ( k1_funct_1(sK7(sK8),k4_tarski(sK4(sK8),sK5(sK8))) = k1_xboole_0
    | k1_funct_1(sK7(sK8),sK1(sK8)) = X0 ),
    inference(renaming,[status(thm)],[c_63883])).

cnf(c_63976,plain,
    ( k1_funct_1(sK7(sK8),k4_tarski(sK4(sK8),sK5(sK8))) = k1_xboole_0
    | k1_funct_1(sK7(sK8),sK1(sK8)) != k1_xboole_0 ),
    inference(equality_factoring,[status(thm)],[c_63884])).

cnf(c_63979,plain,
    ( k1_funct_1(sK7(sK8),k4_tarski(sK4(sK8),sK5(sK8))) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_63976,c_63884])).

cnf(c_64049,plain,
    ( k1_funct_1(sK7(sK8),sK1(sK8)) = X0
    | sK8 = k1_xboole_0
    | k1_xboole_0 = X1 ),
    inference(demodulation,[status(thm)],[c_64048,c_63979])).

cnf(c_64157,plain,
    ( k1_funct_1(sK7(sK8),sK1(sK8)) = X0
    | k1_xboole_0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_64049,c_18,c_59,c_62,c_2173])).

cnf(c_64407,plain,
    ( k1_funct_1(sK7(sK8),sK1(sK8)) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(equality_factoring,[status(thm)],[c_64157])).

cnf(c_64411,plain,
    ( k1_funct_1(sK7(sK8),sK1(sK8)) = X0
    | k1_xboole_0 != X0 ),
    inference(equality_factoring,[status(thm)],[c_64157])).

cnf(c_64418,plain,
    ( k1_funct_1(sK7(sK8),sK1(sK8)) = X0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_64411,c_64157])).

cnf(c_64422,plain,
    ( k1_xboole_0 = X0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_64407,c_64418])).

cnf(c_64625,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_64422,c_18])).

cnf(c_64640,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_64625])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:28:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 11.85/2.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.85/2.01  
% 11.85/2.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.85/2.01  
% 11.85/2.01  ------  iProver source info
% 11.85/2.01  
% 11.85/2.01  git: date: 2020-06-30 10:37:57 +0100
% 11.85/2.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.85/2.01  git: non_committed_changes: false
% 11.85/2.01  git: last_make_outside_of_git: false
% 11.85/2.01  
% 11.85/2.01  ------ 
% 11.85/2.01  ------ Parsing...
% 11.85/2.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  ------ Proving...
% 11.85/2.01  ------ Problem Properties 
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  clauses                                 19
% 11.85/2.01  conjectures                             2
% 11.85/2.01  EPR                                     2
% 11.85/2.01  Horn                                    16
% 11.85/2.01  unary                                   9
% 11.85/2.01  binary                                  5
% 11.85/2.01  lits                                    38
% 11.85/2.01  lits eq                                 16
% 11.85/2.01  fd_pure                                 0
% 11.85/2.01  fd_pseudo                               0
% 11.85/2.01  fd_cond                                 1
% 11.85/2.01  fd_pseudo_cond                          3
% 11.85/2.01  AC symbols                              0
% 11.85/2.01  
% 11.85/2.01  ------ Input Options Time Limit: Unbounded
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 11.85/2.01  Current options:
% 11.85/2.01  ------ 
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.85/2.01  
% 11.85/2.01  ------ Proving...
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  % SZS status Theorem for theBenchmark.p
% 11.85/2.01  
% 11.85/2.01   Resolution empty clause
% 11.85/2.01  
% 11.85/2.01  % SZS output start CNFRefutation for theBenchmark.p
% 11.85/2.01  
% 11.85/2.01  fof(f9,axiom,(
% 11.85/2.01    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_xboole_0 = k1_funct_1(X1,X2)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 11.85/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.85/2.01  
% 11.85/2.01  fof(f18,plain,(
% 11.85/2.01    ! [X0] : ? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 11.85/2.01    inference(ennf_transformation,[],[f9])).
% 11.85/2.01  
% 11.85/2.01  fof(f34,plain,(
% 11.85/2.01    ! [X0] : (? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1)) => (! [X2] : (k1_xboole_0 = k1_funct_1(sK7(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK7(X0)) = X0 & v1_funct_1(sK7(X0)) & v1_relat_1(sK7(X0))))),
% 11.85/2.01    introduced(choice_axiom,[])).
% 11.85/2.01  
% 11.85/2.01  fof(f35,plain,(
% 11.85/2.01    ! [X0] : (! [X2] : (k1_xboole_0 = k1_funct_1(sK7(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK7(X0)) = X0 & v1_funct_1(sK7(X0)) & v1_relat_1(sK7(X0)))),
% 11.85/2.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f18,f34])).
% 11.85/2.01  
% 11.85/2.01  fof(f56,plain,(
% 11.85/2.01    ( ! [X0] : (k1_relat_1(sK7(X0)) = X0) )),
% 11.85/2.01    inference(cnf_transformation,[],[f35])).
% 11.85/2.01  
% 11.85/2.01  fof(f8,axiom,(
% 11.85/2.01    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 11.85/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.85/2.01  
% 11.85/2.01  fof(f17,plain,(
% 11.85/2.01    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 11.85/2.01    inference(ennf_transformation,[],[f8])).
% 11.85/2.01  
% 11.85/2.01  fof(f32,plain,(
% 11.85/2.01    ! [X1,X0] : (? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (! [X3] : (k1_funct_1(sK6(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK6(X0,X1)) = X0 & v1_funct_1(sK6(X0,X1)) & v1_relat_1(sK6(X0,X1))))),
% 11.85/2.01    introduced(choice_axiom,[])).
% 11.85/2.01  
% 11.85/2.01  fof(f33,plain,(
% 11.85/2.01    ! [X0,X1] : (! [X3] : (k1_funct_1(sK6(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK6(X0,X1)) = X0 & v1_funct_1(sK6(X0,X1)) & v1_relat_1(sK6(X0,X1)))),
% 11.85/2.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f17,f32])).
% 11.85/2.01  
% 11.85/2.01  fof(f52,plain,(
% 11.85/2.01    ( ! [X0,X1] : (k1_relat_1(sK6(X0,X1)) = X0) )),
% 11.85/2.01    inference(cnf_transformation,[],[f33])).
% 11.85/2.01  
% 11.85/2.01  fof(f10,conjecture,(
% 11.85/2.01    ! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 11.85/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.85/2.01  
% 11.85/2.01  fof(f11,negated_conjecture,(
% 11.85/2.01    ~! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 11.85/2.01    inference(negated_conjecture,[],[f10])).
% 11.85/2.01  
% 11.85/2.01  fof(f19,plain,(
% 11.85/2.01    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : ((X1 = X2 | (k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))))),
% 11.85/2.01    inference(ennf_transformation,[],[f11])).
% 11.85/2.01  
% 11.85/2.01  fof(f20,plain,(
% 11.85/2.01    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 11.85/2.01    inference(flattening,[],[f19])).
% 11.85/2.01  
% 11.85/2.01  fof(f36,plain,(
% 11.85/2.01    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) => (k1_xboole_0 != sK8 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != sK8 | k1_relat_1(X1) != sK8 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 11.85/2.01    introduced(choice_axiom,[])).
% 11.85/2.01  
% 11.85/2.01  fof(f37,plain,(
% 11.85/2.01    k1_xboole_0 != sK8 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != sK8 | k1_relat_1(X1) != sK8 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 11.85/2.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f20,f36])).
% 11.85/2.01  
% 11.85/2.01  fof(f58,plain,(
% 11.85/2.01    ( ! [X2,X1] : (X1 = X2 | k1_relat_1(X2) != sK8 | k1_relat_1(X1) != sK8 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 11.85/2.01    inference(cnf_transformation,[],[f37])).
% 11.85/2.01  
% 11.85/2.01  fof(f50,plain,(
% 11.85/2.01    ( ! [X0,X1] : (v1_relat_1(sK6(X0,X1))) )),
% 11.85/2.01    inference(cnf_transformation,[],[f33])).
% 11.85/2.01  
% 11.85/2.01  fof(f54,plain,(
% 11.85/2.01    ( ! [X0] : (v1_relat_1(sK7(X0))) )),
% 11.85/2.01    inference(cnf_transformation,[],[f35])).
% 11.85/2.01  
% 11.85/2.01  fof(f55,plain,(
% 11.85/2.01    ( ! [X0] : (v1_funct_1(sK7(X0))) )),
% 11.85/2.01    inference(cnf_transformation,[],[f35])).
% 11.85/2.01  
% 11.85/2.01  fof(f51,plain,(
% 11.85/2.01    ( ! [X0,X1] : (v1_funct_1(sK6(X0,X1))) )),
% 11.85/2.01    inference(cnf_transformation,[],[f33])).
% 11.85/2.01  
% 11.85/2.01  fof(f6,axiom,(
% 11.85/2.01    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 11.85/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.85/2.01  
% 11.85/2.01  fof(f14,plain,(
% 11.85/2.01    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)))),
% 11.85/2.01    inference(ennf_transformation,[],[f6])).
% 11.85/2.01  
% 11.85/2.01  fof(f25,plain,(
% 11.85/2.01    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)) | ~v1_relat_1(X0)))),
% 11.85/2.01    inference(nnf_transformation,[],[f14])).
% 11.85/2.01  
% 11.85/2.01  fof(f26,plain,(
% 11.85/2.01    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 11.85/2.01    inference(rectify,[],[f25])).
% 11.85/2.01  
% 11.85/2.01  fof(f28,plain,(
% 11.85/2.01    ! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 => k4_tarski(sK2(X4),sK3(X4)) = X4)),
% 11.85/2.01    introduced(choice_axiom,[])).
% 11.85/2.01  
% 11.85/2.01  fof(f27,plain,(
% 11.85/2.01    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK1(X0) & r2_hidden(sK1(X0),X0)))),
% 11.85/2.01    introduced(choice_axiom,[])).
% 11.85/2.01  
% 11.85/2.01  fof(f29,plain,(
% 11.85/2.01    ! [X0] : ((v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK1(X0) & r2_hidden(sK1(X0),X0))) & (! [X4] : (k4_tarski(sK2(X4),sK3(X4)) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 11.85/2.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f26,f28,f27])).
% 11.85/2.01  
% 11.85/2.01  fof(f47,plain,(
% 11.85/2.01    ( ! [X0] : (v1_relat_1(X0) | r2_hidden(sK1(X0),X0)) )),
% 11.85/2.01    inference(cnf_transformation,[],[f29])).
% 11.85/2.01  
% 11.85/2.01  fof(f53,plain,(
% 11.85/2.01    ( ! [X0,X3,X1] : (k1_funct_1(sK6(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) )),
% 11.85/2.01    inference(cnf_transformation,[],[f33])).
% 11.85/2.01  
% 11.85/2.01  fof(f7,axiom,(
% 11.85/2.01    ! [X0] : (v1_relat_1(X0) => (! [X1,X2] : ~r2_hidden(k4_tarski(X1,X2),X0) => k1_xboole_0 = X0))),
% 11.85/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.85/2.01  
% 11.85/2.01  fof(f15,plain,(
% 11.85/2.01    ! [X0] : ((k1_xboole_0 = X0 | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)) | ~v1_relat_1(X0))),
% 11.85/2.01    inference(ennf_transformation,[],[f7])).
% 11.85/2.01  
% 11.85/2.01  fof(f16,plain,(
% 11.85/2.01    ! [X0] : (k1_xboole_0 = X0 | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0) | ~v1_relat_1(X0))),
% 11.85/2.01    inference(flattening,[],[f15])).
% 11.85/2.01  
% 11.85/2.01  fof(f30,plain,(
% 11.85/2.01    ! [X0] : (? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0) => r2_hidden(k4_tarski(sK4(X0),sK5(X0)),X0))),
% 11.85/2.01    introduced(choice_axiom,[])).
% 11.85/2.01  
% 11.85/2.01  fof(f31,plain,(
% 11.85/2.01    ! [X0] : (k1_xboole_0 = X0 | r2_hidden(k4_tarski(sK4(X0),sK5(X0)),X0) | ~v1_relat_1(X0))),
% 11.85/2.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f16,f30])).
% 11.85/2.01  
% 11.85/2.01  fof(f49,plain,(
% 11.85/2.01    ( ! [X0] : (k1_xboole_0 = X0 | r2_hidden(k4_tarski(sK4(X0),sK5(X0)),X0) | ~v1_relat_1(X0)) )),
% 11.85/2.01    inference(cnf_transformation,[],[f31])).
% 11.85/2.01  
% 11.85/2.01  fof(f57,plain,(
% 11.85/2.01    ( ! [X2,X0] : (k1_xboole_0 = k1_funct_1(sK7(X0),X2) | ~r2_hidden(X2,X0)) )),
% 11.85/2.01    inference(cnf_transformation,[],[f35])).
% 11.85/2.01  
% 11.85/2.01  fof(f59,plain,(
% 11.85/2.01    k1_xboole_0 != sK8),
% 11.85/2.01    inference(cnf_transformation,[],[f37])).
% 11.85/2.01  
% 11.85/2.01  fof(f3,axiom,(
% 11.85/2.01    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 11.85/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.85/2.01  
% 11.85/2.01  fof(f21,plain,(
% 11.85/2.01    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 11.85/2.01    inference(nnf_transformation,[],[f3])).
% 11.85/2.01  
% 11.85/2.01  fof(f22,plain,(
% 11.85/2.01    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 11.85/2.01    inference(rectify,[],[f21])).
% 11.85/2.01  
% 11.85/2.01  fof(f23,plain,(
% 11.85/2.01    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1))))),
% 11.85/2.01    introduced(choice_axiom,[])).
% 11.85/2.01  
% 11.85/2.01  fof(f24,plain,(
% 11.85/2.01    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 11.85/2.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).
% 11.85/2.01  
% 11.85/2.01  fof(f40,plain,(
% 11.85/2.01    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 11.85/2.01    inference(cnf_transformation,[],[f24])).
% 11.85/2.01  
% 11.85/2.01  fof(f4,axiom,(
% 11.85/2.01    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 11.85/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.85/2.01  
% 11.85/2.01  fof(f44,plain,(
% 11.85/2.01    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 11.85/2.01    inference(cnf_transformation,[],[f4])).
% 11.85/2.01  
% 11.85/2.01  fof(f5,axiom,(
% 11.85/2.01    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 11.85/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.85/2.01  
% 11.85/2.01  fof(f45,plain,(
% 11.85/2.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 11.85/2.01    inference(cnf_transformation,[],[f5])).
% 11.85/2.01  
% 11.85/2.01  fof(f60,plain,(
% 11.85/2.01    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 11.85/2.01    inference(definition_unfolding,[],[f44,f45])).
% 11.85/2.01  
% 11.85/2.01  fof(f64,plain,(
% 11.85/2.01    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_enumset1(X0,X0,X0) != X1) )),
% 11.85/2.01    inference(definition_unfolding,[],[f40,f60])).
% 11.85/2.01  
% 11.85/2.01  fof(f67,plain,(
% 11.85/2.01    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_enumset1(X0,X0,X0))) )),
% 11.85/2.01    inference(equality_resolution,[],[f64])).
% 11.85/2.01  
% 11.85/2.01  fof(f41,plain,(
% 11.85/2.01    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 11.85/2.01    inference(cnf_transformation,[],[f24])).
% 11.85/2.01  
% 11.85/2.01  fof(f63,plain,(
% 11.85/2.01    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_enumset1(X0,X0,X0) != X1) )),
% 11.85/2.01    inference(definition_unfolding,[],[f41,f60])).
% 11.85/2.01  
% 11.85/2.01  fof(f65,plain,(
% 11.85/2.01    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_enumset1(X3,X3,X3) != X1) )),
% 11.85/2.01    inference(equality_resolution,[],[f63])).
% 11.85/2.01  
% 11.85/2.01  fof(f66,plain,(
% 11.85/2.01    ( ! [X3] : (r2_hidden(X3,k1_enumset1(X3,X3,X3))) )),
% 11.85/2.01    inference(equality_resolution,[],[f65])).
% 11.85/2.01  
% 11.85/2.01  cnf(c_15,plain,
% 11.85/2.01      ( k1_relat_1(sK7(X0)) = X0 ),
% 11.85/2.01      inference(cnf_transformation,[],[f56]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_11,plain,
% 11.85/2.01      ( k1_relat_1(sK6(X0,X1)) = X0 ),
% 11.85/2.01      inference(cnf_transformation,[],[f52]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_19,negated_conjecture,
% 11.85/2.01      ( ~ v1_funct_1(X0)
% 11.85/2.01      | ~ v1_funct_1(X1)
% 11.85/2.01      | ~ v1_relat_1(X1)
% 11.85/2.01      | ~ v1_relat_1(X0)
% 11.85/2.01      | X1 = X0
% 11.85/2.01      | k1_relat_1(X0) != sK8
% 11.85/2.01      | k1_relat_1(X1) != sK8 ),
% 11.85/2.01      inference(cnf_transformation,[],[f58]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_62955,negated_conjecture,
% 11.85/2.01      ( ~ v1_relat_1(X0)
% 11.85/2.01      | ~ v1_relat_1(X1)
% 11.85/2.01      | ~ iProver_ARSWP_484
% 11.85/2.01      | ~ arAF5_v1_funct_1_0
% 11.85/2.01      | X0 = X1
% 11.85/2.01      | k1_relat_1(X1) != sK8
% 11.85/2.01      | k1_relat_1(X0) != sK8 ),
% 11.85/2.01      inference(arg_filter_abstr,[status(unp)],[c_19]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_63127,plain,
% 11.85/2.01      ( X0 = X1
% 11.85/2.01      | k1_relat_1(X0) != sK8
% 11.85/2.01      | k1_relat_1(X1) != sK8
% 11.85/2.01      | v1_relat_1(X1) != iProver_top
% 11.85/2.01      | v1_relat_1(X0) != iProver_top
% 11.85/2.01      | iProver_ARSWP_484 != iProver_top
% 11.85/2.01      | arAF5_v1_funct_1_0 != iProver_top ),
% 11.85/2.01      inference(predicate_to_equality,[status(thm)],[c_62955]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_63277,plain,
% 11.85/2.01      ( sK6(X0,X1) = X2
% 11.85/2.01      | k1_relat_1(X2) != sK8
% 11.85/2.01      | sK8 != X0
% 11.85/2.01      | v1_relat_1(X2) != iProver_top
% 11.85/2.01      | v1_relat_1(sK6(X0,X1)) != iProver_top
% 11.85/2.01      | iProver_ARSWP_484 != iProver_top
% 11.85/2.01      | arAF5_v1_funct_1_0 != iProver_top ),
% 11.85/2.01      inference(superposition,[status(thm)],[c_11,c_63127]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_13,plain,
% 11.85/2.01      ( v1_relat_1(sK6(X0,X1)) ),
% 11.85/2.01      inference(cnf_transformation,[],[f50]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_36,plain,
% 11.85/2.01      ( v1_relat_1(sK6(X0,X1)) = iProver_top ),
% 11.85/2.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_63331,plain,
% 11.85/2.01      ( v1_relat_1(X2) != iProver_top
% 11.85/2.01      | sK8 != X0
% 11.85/2.01      | k1_relat_1(X2) != sK8
% 11.85/2.01      | sK6(X0,X1) = X2
% 11.85/2.01      | iProver_ARSWP_484 != iProver_top
% 11.85/2.01      | arAF5_v1_funct_1_0 != iProver_top ),
% 11.85/2.01      inference(global_propositional_subsumption,[status(thm)],[c_63277,c_36]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_63332,plain,
% 11.85/2.01      ( sK6(X0,X1) = X2
% 11.85/2.01      | k1_relat_1(X2) != sK8
% 11.85/2.01      | sK8 != X0
% 11.85/2.01      | v1_relat_1(X2) != iProver_top
% 11.85/2.01      | iProver_ARSWP_484 != iProver_top
% 11.85/2.01      | arAF5_v1_funct_1_0 != iProver_top ),
% 11.85/2.01      inference(renaming,[status(thm)],[c_63331]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_63342,plain,
% 11.85/2.01      ( sK6(X0,X1) = sK7(X2)
% 11.85/2.01      | sK8 != X2
% 11.85/2.01      | sK8 != X0
% 11.85/2.01      | v1_relat_1(sK7(X2)) != iProver_top
% 11.85/2.01      | iProver_ARSWP_484 != iProver_top
% 11.85/2.01      | arAF5_v1_funct_1_0 != iProver_top ),
% 11.85/2.01      inference(superposition,[status(thm)],[c_15,c_63332]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_35680,plain,
% 11.85/2.01      ( X0 = X1
% 11.85/2.01      | k1_relat_1(X1) != sK8
% 11.85/2.01      | k1_relat_1(X0) != sK8
% 11.85/2.01      | v1_funct_1(X1) != iProver_top
% 11.85/2.01      | v1_funct_1(X0) != iProver_top
% 11.85/2.01      | v1_relat_1(X0) != iProver_top
% 11.85/2.01      | v1_relat_1(X1) != iProver_top ),
% 11.85/2.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_35740,plain,
% 11.85/2.01      ( sK7(X0) = X1
% 11.85/2.01      | k1_relat_1(X1) != sK8
% 11.85/2.01      | sK8 != X0
% 11.85/2.01      | v1_funct_1(X1) != iProver_top
% 11.85/2.01      | v1_funct_1(sK7(X0)) != iProver_top
% 11.85/2.01      | v1_relat_1(X1) != iProver_top
% 11.85/2.01      | v1_relat_1(sK7(X0)) != iProver_top ),
% 11.85/2.01      inference(superposition,[status(thm)],[c_15,c_35680]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_17,plain,
% 11.85/2.01      ( v1_relat_1(sK7(X0)) ),
% 11.85/2.01      inference(cnf_transformation,[],[f54]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_26,plain,
% 11.85/2.01      ( v1_relat_1(sK7(X0)) = iProver_top ),
% 11.85/2.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_16,plain,
% 11.85/2.01      ( v1_funct_1(sK7(X0)) ),
% 11.85/2.01      inference(cnf_transformation,[],[f55]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_29,plain,
% 11.85/2.01      ( v1_funct_1(sK7(X0)) = iProver_top ),
% 11.85/2.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_35743,plain,
% 11.85/2.01      ( v1_relat_1(X1) != iProver_top
% 11.85/2.01      | sK7(X0) = X1
% 11.85/2.01      | k1_relat_1(X1) != sK8
% 11.85/2.01      | sK8 != X0
% 11.85/2.01      | v1_funct_1(X1) != iProver_top ),
% 11.85/2.01      inference(global_propositional_subsumption,
% 11.85/2.01                [status(thm)],
% 11.85/2.01                [c_35740,c_26,c_29]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_35744,plain,
% 11.85/2.01      ( sK7(X0) = X1
% 11.85/2.01      | k1_relat_1(X1) != sK8
% 11.85/2.01      | sK8 != X0
% 11.85/2.01      | v1_funct_1(X1) != iProver_top
% 11.85/2.01      | v1_relat_1(X1) != iProver_top ),
% 11.85/2.01      inference(renaming,[status(thm)],[c_35743]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_35800,plain,
% 11.85/2.01      ( sK6(X0,X1) = sK7(X2)
% 11.85/2.01      | sK8 != X0
% 11.85/2.01      | sK8 != X2
% 11.85/2.01      | v1_funct_1(sK6(X0,X1)) != iProver_top
% 11.85/2.01      | v1_relat_1(sK6(X0,X1)) != iProver_top ),
% 11.85/2.01      inference(superposition,[status(thm)],[c_11,c_35744]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_12,plain,
% 11.85/2.01      ( v1_funct_1(sK6(X0,X1)) ),
% 11.85/2.01      inference(cnf_transformation,[],[f51]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_35826,plain,
% 11.85/2.01      ( ~ v1_funct_1(sK6(X0,X1))
% 11.85/2.01      | ~ v1_relat_1(sK6(X0,X1))
% 11.85/2.01      | sK6(X0,X1) = sK7(X2)
% 11.85/2.01      | sK8 != X0
% 11.85/2.01      | sK8 != X2 ),
% 11.85/2.01      inference(predicate_to_equality_rev,[status(thm)],[c_35800]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_35842,plain,
% 11.85/2.01      ( sK6(X0,X1) = sK7(X2) | sK8 != X0 | sK8 != X2 ),
% 11.85/2.01      inference(global_propositional_subsumption,
% 11.85/2.01                [status(thm)],
% 11.85/2.01                [c_35800,c_13,c_12,c_35826]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_63379,plain,
% 11.85/2.01      ( sK8 != X0 | sK8 != X2 | sK6(X0,X1) = sK7(X2) ),
% 11.85/2.01      inference(global_propositional_subsumption,
% 11.85/2.01                [status(thm)],
% 11.85/2.01                [c_63342,c_35842]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_63380,plain,
% 11.85/2.01      ( sK6(X0,X1) = sK7(X2) | sK8 != X0 | sK8 != X2 ),
% 11.85/2.01      inference(renaming,[status(thm)],[c_63379]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_63384,plain,
% 11.85/2.01      ( sK6(sK8,X0) = sK7(X1) | sK8 != X1 ),
% 11.85/2.01      inference(equality_resolution,[status(thm)],[c_63380]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_63404,plain,
% 11.85/2.01      ( sK6(sK8,X0) = sK7(sK8) ),
% 11.85/2.01      inference(equality_resolution,[status(thm)],[c_63384]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_7,plain,
% 11.85/2.01      ( r2_hidden(sK1(X0),X0) | v1_relat_1(X0) ),
% 11.85/2.01      inference(cnf_transformation,[],[f47]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_63138,plain,
% 11.85/2.01      ( r2_hidden(sK1(X0),X0) = iProver_top | v1_relat_1(X0) = iProver_top ),
% 11.85/2.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_10,plain,
% 11.85/2.01      ( ~ r2_hidden(X0,X1) | k1_funct_1(sK6(X1,X2),X0) = X2 ),
% 11.85/2.01      inference(cnf_transformation,[],[f53]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_63136,plain,
% 11.85/2.01      ( k1_funct_1(sK6(X0,X1),X2) = X1 | r2_hidden(X2,X0) != iProver_top ),
% 11.85/2.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_63444,plain,
% 11.85/2.01      ( k1_funct_1(sK6(X0,X1),sK1(X0)) = X1 | v1_relat_1(X0) = iProver_top ),
% 11.85/2.01      inference(superposition,[status(thm)],[c_63138,c_63136]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_9,plain,
% 11.85/2.01      ( r2_hidden(k4_tarski(sK4(X0),sK5(X0)),X0)
% 11.85/2.01      | ~ v1_relat_1(X0)
% 11.85/2.01      | k1_xboole_0 = X0 ),
% 11.85/2.01      inference(cnf_transformation,[],[f49]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_63137,plain,
% 11.85/2.01      ( k1_xboole_0 = X0
% 11.85/2.01      | r2_hidden(k4_tarski(sK4(X0),sK5(X0)),X0) = iProver_top
% 11.85/2.01      | v1_relat_1(X0) != iProver_top ),
% 11.85/2.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_63456,plain,
% 11.85/2.01      ( k1_funct_1(sK6(X0,X1),k4_tarski(sK4(X0),sK5(X0))) = X1
% 11.85/2.01      | k1_xboole_0 = X0
% 11.85/2.01      | v1_relat_1(X0) != iProver_top ),
% 11.85/2.01      inference(superposition,[status(thm)],[c_63137,c_63136]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_63581,plain,
% 11.85/2.01      ( k1_funct_1(sK6(X0,X1),k4_tarski(sK4(X0),sK5(X0))) = X1
% 11.85/2.01      | k1_funct_1(sK6(X0,X2),sK1(X0)) = X2
% 11.85/2.01      | k1_xboole_0 = X0 ),
% 11.85/2.01      inference(superposition,[status(thm)],[c_63444,c_63456]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_64020,plain,
% 11.85/2.01      ( k1_funct_1(sK6(sK8,X0),sK1(sK8)) = X0
% 11.85/2.01      | k1_funct_1(sK7(sK8),k4_tarski(sK4(sK8),sK5(sK8))) = X1
% 11.85/2.01      | sK8 = k1_xboole_0 ),
% 11.85/2.01      inference(superposition,[status(thm)],[c_63404,c_63581]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_64048,plain,
% 11.85/2.01      ( k1_funct_1(sK7(sK8),k4_tarski(sK4(sK8),sK5(sK8))) = X0
% 11.85/2.01      | k1_funct_1(sK7(sK8),sK1(sK8)) = X1
% 11.85/2.01      | sK8 = k1_xboole_0 ),
% 11.85/2.01      inference(light_normalisation,[status(thm)],[c_64020,c_63404]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_14,plain,
% 11.85/2.01      ( ~ r2_hidden(X0,X1) | k1_funct_1(sK7(X1),X0) = k1_xboole_0 ),
% 11.85/2.01      inference(cnf_transformation,[],[f57]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_63134,plain,
% 11.85/2.01      ( k1_funct_1(sK7(X0),X1) = k1_xboole_0
% 11.85/2.01      | r2_hidden(X1,X0) != iProver_top ),
% 11.85/2.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_63455,plain,
% 11.85/2.01      ( k1_funct_1(sK7(X0),k4_tarski(sK4(X0),sK5(X0))) = k1_xboole_0
% 11.85/2.01      | k1_xboole_0 = X0
% 11.85/2.01      | v1_relat_1(X0) != iProver_top ),
% 11.85/2.01      inference(superposition,[status(thm)],[c_63137,c_63134]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_63543,plain,
% 11.85/2.01      ( k1_funct_1(sK6(X0,X1),sK1(X0)) = X1
% 11.85/2.01      | k1_funct_1(sK7(X0),k4_tarski(sK4(X0),sK5(X0))) = k1_xboole_0
% 11.85/2.01      | k1_xboole_0 = X0 ),
% 11.85/2.01      inference(superposition,[status(thm)],[c_63444,c_63455]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_63866,plain,
% 11.85/2.01      ( k1_funct_1(sK7(sK8),k4_tarski(sK4(sK8),sK5(sK8))) = k1_xboole_0
% 11.85/2.01      | k1_funct_1(sK7(sK8),sK1(sK8)) = X0
% 11.85/2.01      | sK8 = k1_xboole_0 ),
% 11.85/2.01      inference(superposition,[status(thm)],[c_63404,c_63543]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_18,negated_conjecture,
% 11.85/2.01      ( k1_xboole_0 != sK8 ),
% 11.85/2.01      inference(cnf_transformation,[],[f59]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_5,plain,
% 11.85/2.01      ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X1)) | X0 = X1 ),
% 11.85/2.01      inference(cnf_transformation,[],[f67]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_59,plain,
% 11.85/2.01      ( ~ r2_hidden(k1_xboole_0,k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0))
% 11.85/2.01      | k1_xboole_0 = k1_xboole_0 ),
% 11.85/2.01      inference(instantiation,[status(thm)],[c_5]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_4,plain,
% 11.85/2.01      ( r2_hidden(X0,k1_enumset1(X0,X0,X0)) ),
% 11.85/2.01      inference(cnf_transformation,[],[f66]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_62,plain,
% 11.85/2.01      ( r2_hidden(k1_xboole_0,k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
% 11.85/2.01      inference(instantiation,[status(thm)],[c_4]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_925,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_2172,plain,
% 11.85/2.01      ( sK8 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK8 ),
% 11.85/2.01      inference(instantiation,[status(thm)],[c_925]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_2173,plain,
% 11.85/2.01      ( sK8 != k1_xboole_0 | k1_xboole_0 = sK8 | k1_xboole_0 != k1_xboole_0 ),
% 11.85/2.01      inference(instantiation,[status(thm)],[c_2172]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_63883,plain,
% 11.85/2.01      ( k1_funct_1(sK7(sK8),sK1(sK8)) = X0
% 11.85/2.01      | k1_funct_1(sK7(sK8),k4_tarski(sK4(sK8),sK5(sK8))) = k1_xboole_0 ),
% 11.85/2.01      inference(global_propositional_subsumption,
% 11.85/2.01                [status(thm)],
% 11.85/2.01                [c_63866,c_18,c_59,c_62,c_2173]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_63884,plain,
% 11.85/2.01      ( k1_funct_1(sK7(sK8),k4_tarski(sK4(sK8),sK5(sK8))) = k1_xboole_0
% 11.85/2.01      | k1_funct_1(sK7(sK8),sK1(sK8)) = X0 ),
% 11.85/2.01      inference(renaming,[status(thm)],[c_63883]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_63976,plain,
% 11.85/2.01      ( k1_funct_1(sK7(sK8),k4_tarski(sK4(sK8),sK5(sK8))) = k1_xboole_0
% 11.85/2.01      | k1_funct_1(sK7(sK8),sK1(sK8)) != k1_xboole_0 ),
% 11.85/2.01      inference(equality_factoring,[status(thm)],[c_63884]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_63979,plain,
% 11.85/2.01      ( k1_funct_1(sK7(sK8),k4_tarski(sK4(sK8),sK5(sK8))) = k1_xboole_0 ),
% 11.85/2.01      inference(forward_subsumption_resolution,[status(thm)],[c_63976,c_63884]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_64049,plain,
% 11.85/2.01      ( k1_funct_1(sK7(sK8),sK1(sK8)) = X0
% 11.85/2.01      | sK8 = k1_xboole_0
% 11.85/2.01      | k1_xboole_0 = X1 ),
% 11.85/2.01      inference(demodulation,[status(thm)],[c_64048,c_63979]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_64157,plain,
% 11.85/2.01      ( k1_funct_1(sK7(sK8),sK1(sK8)) = X0 | k1_xboole_0 = X1 ),
% 11.85/2.01      inference(global_propositional_subsumption,
% 11.85/2.01                [status(thm)],
% 11.85/2.01                [c_64049,c_18,c_59,c_62,c_2173]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_64407,plain,
% 11.85/2.01      ( k1_funct_1(sK7(sK8),sK1(sK8)) != k1_xboole_0 | k1_xboole_0 = X0 ),
% 11.85/2.01      inference(equality_factoring,[status(thm)],[c_64157]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_64411,plain,
% 11.85/2.01      ( k1_funct_1(sK7(sK8),sK1(sK8)) = X0 | k1_xboole_0 != X0 ),
% 11.85/2.01      inference(equality_factoring,[status(thm)],[c_64157]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_64418,plain,
% 11.85/2.01      ( k1_funct_1(sK7(sK8),sK1(sK8)) = X0 ),
% 11.85/2.01      inference(forward_subsumption_resolution,[status(thm)],[c_64411,c_64157]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_64422,plain,
% 11.85/2.01      ( k1_xboole_0 = X0 ),
% 11.85/2.01      inference(forward_subsumption_resolution,[status(thm)],[c_64407,c_64418]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_64625,plain,
% 11.85/2.01      ( k1_xboole_0 != k1_xboole_0 ),
% 11.85/2.01      inference(demodulation,[status(thm)],[c_64422,c_18]) ).
% 11.85/2.01  
% 11.85/2.01  cnf(c_64640,plain,
% 11.85/2.01      ( $false ),
% 11.85/2.01      inference(equality_resolution_simp,[status(thm)],[c_64625]) ).
% 11.85/2.01  
% 11.85/2.01  
% 11.85/2.01  % SZS output end CNFRefutation for theBenchmark.p
% 11.85/2.01  
% 11.85/2.01  ------                               Statistics
% 11.85/2.01  
% 11.85/2.01  ------ Selected
% 11.85/2.01  
% 11.85/2.01  total_time:                             1.164
% 11.85/2.01  
%------------------------------------------------------------------------------
