%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:49:41 EST 2020

% Result     : Theorem 3.86s
% Output     : CNFRefutation 3.86s
% Verified   : 
% Statistics : Number of formulae       :  143 (5415 expanded)
%              Number of clauses        :   99 (1783 expanded)
%              Number of leaves         :   14 (1358 expanded)
%              Depth                    :   27
%              Number of atoms          :  472 (25077 expanded)
%              Number of equality atoms :  280 (10702 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X0)
         => k1_funct_1(X2,X3) = X1 )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k1_funct_1(X2,X3) = X1
              | ~ r2_hidden(X3,X0) )
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( ! [X3] :
            ( k1_funct_1(sK4(X0,X1),X3) = X1
            | ~ r2_hidden(X3,X0) )
        & k1_relat_1(sK4(X0,X1)) = X0
        & v1_funct_1(sK4(X0,X1))
        & v1_relat_1(sK4(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X3] :
          ( k1_funct_1(sK4(X0,X1),X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(sK4(X0,X1)) = X0
      & v1_funct_1(sK4(X0,X1))
      & v1_relat_1(sK4(X0,X1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f14,f25])).

fof(f43,plain,(
    ! [X0,X1] : k1_relat_1(sK4(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f19,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f20,plain,(
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
    inference(rectify,[],[f19])).

fof(f23,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X5)) = X5
        & r2_hidden(sK3(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1)) = X2
        & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
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
              ( k1_funct_1(X0,X3) != sK1(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK1(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK1(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK1(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1)
                  & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK1(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK3(X0,X5)) = X5
                    & r2_hidden(sK3(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f20,f23,f22,f21])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(sK2(X0,X1),k1_relat_1(X0))
      | r2_hidden(sK1(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f41,plain,(
    ! [X0,X1] : v1_relat_1(sK4(X0,X1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f42,plain,(
    ! [X0,X1] : v1_funct_1(sK4(X0,X1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f17])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ~ ( r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X1 ) )
        & ~ ( k1_xboole_0 != X1
            & k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ~ ( r1_tarski(k2_relat_1(X2),X0)
                  & k1_relat_1(X2) = X1 ) )
          & ~ ( k1_xboole_0 != X1
              & k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(flattening,[],[f15])).

fof(f27,plain,
    ( ? [X0,X1] :
        ( ! [X2] :
            ( ~ r1_tarski(k2_relat_1(X2),X0)
            | k1_relat_1(X2) != X1
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) )
        & ( k1_xboole_0 = X1
          | k1_xboole_0 != X0 ) )
   => ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),sK5)
          | k1_relat_1(X2) != sK6
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = sK6
        | k1_xboole_0 != sK5 ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k2_relat_1(X2),sK5)
        | k1_relat_1(X2) != sK6
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    & ( k1_xboole_0 = sK6
      | k1_xboole_0 != sK5 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f16,f27])).

fof(f46,plain,(
    ! [X2] :
      ( ~ r1_tarski(k2_relat_1(X2),sK5)
      | k1_relat_1(X2) != sK6
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f35,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK3(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f50,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK3(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f35])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(sK4(X0,X1),X3) = X1
      | ~ r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f36,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK3(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f49,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK3(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f32,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f11,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f33,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f45,plain,
    ( k1_xboole_0 = sK6
    | k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_13,plain,
    ( k1_relat_1(sK4(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_8,plain,
    ( r2_hidden(sK2(X0,X1),k1_relat_1(X0))
    | r2_hidden(sK1(X0,X1),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1219,plain,
    ( k2_relat_1(X0) = X1
    | r2_hidden(sK2(X0,X1),k1_relat_1(X0)) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3234,plain,
    ( k2_relat_1(sK4(X0,X1)) = X2
    | r2_hidden(sK2(sK4(X0,X1),X2),X0) = iProver_top
    | r2_hidden(sK1(sK4(X0,X1),X2),X2) = iProver_top
    | v1_funct_1(sK4(X0,X1)) != iProver_top
    | v1_relat_1(sK4(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_1219])).

cnf(c_15,plain,
    ( v1_relat_1(sK4(X0,X1)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_21,plain,
    ( v1_relat_1(sK4(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_14,plain,
    ( v1_funct_1(sK4(X0,X1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_24,plain,
    ( v1_funct_1(sK4(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4834,plain,
    ( k2_relat_1(sK4(X0,X1)) = X2
    | r2_hidden(sK2(sK4(X0,X1),X2),X0) = iProver_top
    | r2_hidden(sK1(sK4(X0,X1),X2),X2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3234,c_21,c_24])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_16,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(X0),sK5)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) != sK6 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_172,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_relat_1(X2) != sK6
    | k2_relat_1(X2) != X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_16])).

cnf(c_173,plain,
    ( r2_hidden(sK0(k2_relat_1(X0),sK5),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) != sK6 ),
    inference(unflattening,[status(thm)],[c_172])).

cnf(c_1212,plain,
    ( k1_relat_1(X0) != sK6
    | r2_hidden(sK0(k2_relat_1(X0),sK5),k2_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_173])).

cnf(c_1518,plain,
    ( sK6 != X0
    | r2_hidden(sK0(k2_relat_1(sK4(X0,X1)),sK5),k2_relat_1(sK4(X0,X1))) = iProver_top
    | v1_funct_1(sK4(X0,X1)) != iProver_top
    | v1_relat_1(sK4(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_1212])).

cnf(c_1909,plain,
    ( sK6 != X0
    | r2_hidden(sK0(k2_relat_1(sK4(X0,X1)),sK5),k2_relat_1(sK4(X0,X1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1518,c_21,c_24])).

cnf(c_1917,plain,
    ( r2_hidden(sK0(k2_relat_1(sK4(sK6,X0)),sK5),k2_relat_1(sK4(sK6,X0))) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1909])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK3(X1,X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1216,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(sK3(X1,X0),k1_relat_1(X1)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_funct_1(sK4(X1,X2),X0) = X2 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1215,plain,
    ( k1_funct_1(sK4(X0,X1),X2) = X1
    | r2_hidden(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2364,plain,
    ( k1_funct_1(sK4(k1_relat_1(X0),X1),sK3(X0,X2)) = X1
    | r2_hidden(X2,k2_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1216,c_1215])).

cnf(c_8059,plain,
    ( k1_funct_1(sK4(k1_relat_1(sK4(sK6,X0)),X1),sK3(sK4(sK6,X0),sK0(k2_relat_1(sK4(sK6,X0)),sK5))) = X1
    | v1_funct_1(sK4(sK6,X0)) != iProver_top
    | v1_relat_1(sK4(sK6,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1917,c_2364])).

cnf(c_8188,plain,
    ( k1_funct_1(sK4(sK6,X0),sK3(sK4(sK6,X1),sK0(k2_relat_1(sK4(sK6,X1)),sK5))) = X0
    | v1_funct_1(sK4(sK6,X1)) != iProver_top
    | v1_relat_1(sK4(sK6,X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8059,c_13])).

cnf(c_1213,plain,
    ( v1_relat_1(sK4(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1214,plain,
    ( v1_funct_1(sK4(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_8271,plain,
    ( k1_funct_1(sK4(sK6,X0),sK3(sK4(sK6,X1),sK0(k2_relat_1(sK4(sK6,X1)),sK5))) = X0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8188,c_1213,c_1214])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK3(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1217,plain,
    ( k1_funct_1(X0,sK3(X0,X1)) = X1
    | r2_hidden(X1,k2_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2507,plain,
    ( k1_funct_1(sK4(sK6,X0),sK3(sK4(sK6,X0),sK0(k2_relat_1(sK4(sK6,X0)),sK5))) = sK0(k2_relat_1(sK4(sK6,X0)),sK5)
    | v1_funct_1(sK4(sK6,X0)) != iProver_top
    | v1_relat_1(sK4(sK6,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1917,c_1217])).

cnf(c_1379,plain,
    ( r2_hidden(sK0(k2_relat_1(sK4(X0,X1)),sK5),k2_relat_1(sK4(X0,X1)))
    | ~ v1_funct_1(sK4(X0,X1))
    | ~ v1_relat_1(sK4(X0,X1))
    | k1_relat_1(sK4(X0,X1)) != sK6 ),
    inference(instantiation,[status(thm)],[c_173])).

cnf(c_1496,plain,
    ( r2_hidden(sK0(k2_relat_1(sK4(sK6,X0)),sK5),k2_relat_1(sK4(sK6,X0)))
    | ~ v1_funct_1(sK4(sK6,X0))
    | ~ v1_relat_1(sK4(sK6,X0))
    | k1_relat_1(sK4(sK6,X0)) != sK6 ),
    inference(instantiation,[status(thm)],[c_1379])).

cnf(c_1497,plain,
    ( k1_relat_1(sK4(sK6,X0)) = sK6 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1601,plain,
    ( v1_relat_1(sK4(sK6,X0)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1769,plain,
    ( v1_funct_1(sK4(sK6,X0)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1935,plain,
    ( ~ r2_hidden(sK0(k2_relat_1(sK4(sK6,X0)),sK5),k2_relat_1(sK4(sK6,X0)))
    | ~ v1_funct_1(sK4(sK6,X0))
    | ~ v1_relat_1(sK4(sK6,X0))
    | k1_funct_1(sK4(sK6,X0),sK3(sK4(sK6,X0),sK0(k2_relat_1(sK4(sK6,X0)),sK5))) = sK0(k2_relat_1(sK4(sK6,X0)),sK5) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2757,plain,
    ( k1_funct_1(sK4(sK6,X0),sK3(sK4(sK6,X0),sK0(k2_relat_1(sK4(sK6,X0)),sK5))) = sK0(k2_relat_1(sK4(sK6,X0)),sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2507,c_1496,c_1497,c_1601,c_1769,c_1935])).

cnf(c_8273,plain,
    ( sK0(k2_relat_1(sK4(sK6,X0)),sK5) = X0 ),
    inference(demodulation,[status(thm)],[c_8271,c_2757])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_190,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_relat_1(X2) != sK6
    | k2_relat_1(X2) != X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_16])).

cnf(c_191,plain,
    ( ~ r2_hidden(sK0(k2_relat_1(X0),sK5),sK5)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) != sK6 ),
    inference(unflattening,[status(thm)],[c_190])).

cnf(c_1211,plain,
    ( k1_relat_1(X0) != sK6
    | r2_hidden(sK0(k2_relat_1(X0),sK5),sK5) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_191])).

cnf(c_1519,plain,
    ( sK6 != X0
    | r2_hidden(sK0(k2_relat_1(sK4(X0,X1)),sK5),sK5) != iProver_top
    | v1_funct_1(sK4(X0,X1)) != iProver_top
    | v1_relat_1(sK4(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_1211])).

cnf(c_1811,plain,
    ( sK6 != X0
    | r2_hidden(sK0(k2_relat_1(sK4(X0,X1)),sK5),sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1519,c_21,c_24])).

cnf(c_1819,plain,
    ( r2_hidden(sK0(k2_relat_1(sK4(sK6,X0)),sK5),sK5) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1811])).

cnf(c_8572,plain,
    ( r2_hidden(X0,sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8273,c_1819])).

cnf(c_8677,plain,
    ( k2_relat_1(sK4(X0,X1)) = sK5
    | r2_hidden(sK2(sK4(X0,X1),sK5),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4834,c_8572])).

cnf(c_3,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_2362,plain,
    ( r2_hidden(X0,k2_relat_1(k1_xboole_0)) != iProver_top
    | r2_hidden(sK3(k1_xboole_0,X0),k1_xboole_0) = iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_1216])).

cnf(c_2,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_2385,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r2_hidden(sK3(k1_xboole_0,X0),k1_xboole_0) = iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2362,c_2])).

cnf(c_23,plain,
    ( v1_relat_1(sK4(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_26,plain,
    ( v1_funct_1(sK4(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_27,plain,
    ( k1_relat_1(sK4(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_452,plain,
    ( sK4(X0,X1) != X2
    | k1_relat_1(X2) != k1_xboole_0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_15])).

cnf(c_453,plain,
    ( k1_relat_1(sK4(X0,X1)) != k1_xboole_0
    | k1_xboole_0 = sK4(X0,X1) ),
    inference(unflattening,[status(thm)],[c_452])).

cnf(c_454,plain,
    ( k1_relat_1(sK4(k1_xboole_0,k1_xboole_0)) != k1_xboole_0
    | k1_xboole_0 = sK4(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_453])).

cnf(c_960,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1415,plain,
    ( v1_relat_1(X0)
    | ~ v1_relat_1(sK4(X1,X2))
    | X0 != sK4(X1,X2) ),
    inference(instantiation,[status(thm)],[c_960])).

cnf(c_1416,plain,
    ( X0 != sK4(X1,X2)
    | v1_relat_1(X0) = iProver_top
    | v1_relat_1(sK4(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1415])).

cnf(c_1418,plain,
    ( k1_xboole_0 != sK4(k1_xboole_0,k1_xboole_0)
    | v1_relat_1(sK4(k1_xboole_0,k1_xboole_0)) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1416])).

cnf(c_962,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1420,plain,
    ( v1_funct_1(X0)
    | ~ v1_funct_1(sK4(X1,X2))
    | X0 != sK4(X1,X2) ),
    inference(instantiation,[status(thm)],[c_962])).

cnf(c_1421,plain,
    ( X0 != sK4(X1,X2)
    | v1_funct_1(X0) = iProver_top
    | v1_funct_1(sK4(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1420])).

cnf(c_1423,plain,
    ( k1_xboole_0 != sK4(k1_xboole_0,k1_xboole_0)
    | v1_funct_1(sK4(k1_xboole_0,k1_xboole_0)) != iProver_top
    | v1_funct_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1421])).

cnf(c_2400,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r2_hidden(sK3(k1_xboole_0,X0),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2385,c_23,c_26,c_27,c_454,c_1418,c_1423])).

cnf(c_2408,plain,
    ( k1_funct_1(sK4(k1_xboole_0,X0),sK3(k1_xboole_0,X1)) = X0
    | r2_hidden(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2400,c_1215])).

cnf(c_1222,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1716,plain,
    ( sK4(X0,X1) = k1_xboole_0
    | k1_xboole_0 != X0
    | v1_relat_1(sK4(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_1222])).

cnf(c_2140,plain,
    ( k1_xboole_0 != X0
    | sK4(X0,X1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1716,c_21])).

cnf(c_2141,plain,
    ( sK4(X0,X1) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(renaming,[status(thm)],[c_2140])).

cnf(c_2145,plain,
    ( sK4(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_2141])).

cnf(c_2409,plain,
    ( k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,X0)) = X1
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2408,c_2145])).

cnf(c_9760,plain,
    ( k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,sK2(sK4(k1_xboole_0,X0),sK5))) = X1
    | k2_relat_1(sK4(k1_xboole_0,X0)) = sK5 ),
    inference(superposition,[status(thm)],[c_8677,c_2409])).

cnf(c_9763,plain,
    ( k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,sK2(k1_xboole_0,sK5))) = X0
    | sK5 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_9760,c_2,c_2145])).

cnf(c_2363,plain,
    ( r2_hidden(X0,k2_relat_1(sK4(X1,X2))) != iProver_top
    | r2_hidden(sK3(sK4(X1,X2),X0),X1) = iProver_top
    | v1_funct_1(sK4(X1,X2)) != iProver_top
    | v1_relat_1(sK4(X1,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_1216])).

cnf(c_3722,plain,
    ( r2_hidden(X0,k2_relat_1(sK4(X1,X2))) != iProver_top
    | r2_hidden(sK3(sK4(X1,X2),X0),X1) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2363,c_1213,c_1214])).

cnf(c_8678,plain,
    ( r2_hidden(X0,k2_relat_1(sK4(sK5,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3722,c_8572])).

cnf(c_10520,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(X0,k2_relat_1(k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,sK2(k1_xboole_0,sK5))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_9763,c_8678])).

cnf(c_8571,plain,
    ( r2_hidden(X0,k2_relat_1(sK4(sK6,X0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8273,c_1917])).

cnf(c_10584,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(X0,k2_relat_1(k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,sK2(k1_xboole_0,sK5))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_9763,c_8571])).

cnf(c_11302,plain,
    ( sK5 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_10520,c_10584])).

cnf(c_1452,plain,
    ( sK6 != k1_xboole_0
    | r2_hidden(sK0(k2_relat_1(k1_xboole_0),sK5),sK5) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_1211])).

cnf(c_1457,plain,
    ( sK6 != k1_xboole_0
    | r2_hidden(sK0(k1_xboole_0,sK5),sK5) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1452,c_2])).

cnf(c_1511,plain,
    ( sK6 != k1_xboole_0
    | r2_hidden(sK0(k1_xboole_0,sK5),sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1457,c_23,c_26,c_27,c_454,c_1418,c_1423])).

cnf(c_12732,plain,
    ( sK6 != k1_xboole_0
    | r2_hidden(sK0(k1_xboole_0,k1_xboole_0),k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11302,c_1511])).

cnf(c_17,negated_conjecture,
    ( k1_xboole_0 = sK6
    | k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_12736,plain,
    ( sK6 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_11302,c_17])).

cnf(c_12737,plain,
    ( sK6 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_12736])).

cnf(c_12762,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r2_hidden(sK0(k1_xboole_0,k1_xboole_0),k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12732,c_12737])).

cnf(c_12763,plain,
    ( r2_hidden(sK0(k1_xboole_0,k1_xboole_0),k1_xboole_0) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_12762])).

cnf(c_1451,plain,
    ( sK6 != k1_xboole_0
    | r2_hidden(sK0(k2_relat_1(k1_xboole_0),sK5),k2_relat_1(k1_xboole_0)) = iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_1212])).

cnf(c_1466,plain,
    ( sK6 != k1_xboole_0
    | r2_hidden(sK0(k1_xboole_0,sK5),k1_xboole_0) = iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1451,c_2])).

cnf(c_1474,plain,
    ( sK6 != k1_xboole_0
    | r2_hidden(sK0(k1_xboole_0,sK5),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1466,c_23,c_26,c_27,c_454,c_1418,c_1423])).

cnf(c_12733,plain,
    ( sK6 != k1_xboole_0
    | r2_hidden(sK0(k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11302,c_1474])).

cnf(c_12758,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r2_hidden(sK0(k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12733,c_12737])).

cnf(c_12759,plain,
    ( r2_hidden(sK0(k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_12758])).

cnf(c_12765,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_12763,c_12759])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:36:25 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.86/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.86/1.00  
% 3.86/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.86/1.00  
% 3.86/1.00  ------  iProver source info
% 3.86/1.00  
% 3.86/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.86/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.86/1.00  git: non_committed_changes: false
% 3.86/1.00  git: last_make_outside_of_git: false
% 3.86/1.00  
% 3.86/1.00  ------ 
% 3.86/1.00  ------ Parsing...
% 3.86/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.86/1.00  
% 3.86/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.86/1.00  
% 3.86/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.86/1.00  
% 3.86/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.86/1.00  ------ Proving...
% 3.86/1.00  ------ Problem Properties 
% 3.86/1.00  
% 3.86/1.00  
% 3.86/1.00  clauses                                 17
% 3.86/1.00  conjectures                             1
% 3.86/1.00  EPR                                     1
% 3.86/1.00  Horn                                    15
% 3.86/1.00  unary                                   5
% 3.86/1.00  binary                                  2
% 3.86/1.00  lits                                    51
% 3.86/1.00  lits eq                                 18
% 3.86/1.00  fd_pure                                 0
% 3.86/1.00  fd_pseudo                               0
% 3.86/1.00  fd_cond                                 2
% 3.86/1.00  fd_pseudo_cond                          3
% 3.86/1.00  AC symbols                              0
% 3.86/1.00  
% 3.86/1.00  ------ Input Options Time Limit: Unbounded
% 3.86/1.00  
% 3.86/1.00  
% 3.86/1.00  ------ 
% 3.86/1.00  Current options:
% 3.86/1.00  ------ 
% 3.86/1.00  
% 3.86/1.00  
% 3.86/1.00  
% 3.86/1.00  
% 3.86/1.00  ------ Proving...
% 3.86/1.00  
% 3.86/1.00  
% 3.86/1.00  % SZS status Theorem for theBenchmark.p
% 3.86/1.00  
% 3.86/1.00   Resolution empty clause
% 3.86/1.00  
% 3.86/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.86/1.00  
% 3.86/1.00  fof(f5,axiom,(
% 3.86/1.00    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 3.86/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.86/1.00  
% 3.86/1.00  fof(f14,plain,(
% 3.86/1.00    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 3.86/1.00    inference(ennf_transformation,[],[f5])).
% 3.86/1.00  
% 3.86/1.00  fof(f25,plain,(
% 3.86/1.00    ! [X1,X0] : (? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (! [X3] : (k1_funct_1(sK4(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK4(X0,X1)) = X0 & v1_funct_1(sK4(X0,X1)) & v1_relat_1(sK4(X0,X1))))),
% 3.86/1.00    introduced(choice_axiom,[])).
% 3.86/1.00  
% 3.86/1.00  fof(f26,plain,(
% 3.86/1.00    ! [X0,X1] : (! [X3] : (k1_funct_1(sK4(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK4(X0,X1)) = X0 & v1_funct_1(sK4(X0,X1)) & v1_relat_1(sK4(X0,X1)))),
% 3.86/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f14,f25])).
% 3.86/1.00  
% 3.86/1.00  fof(f43,plain,(
% 3.86/1.00    ( ! [X0,X1] : (k1_relat_1(sK4(X0,X1)) = X0) )),
% 3.86/1.00    inference(cnf_transformation,[],[f26])).
% 3.86/1.00  
% 3.86/1.00  fof(f4,axiom,(
% 3.86/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 3.86/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.86/1.00  
% 3.86/1.00  fof(f12,plain,(
% 3.86/1.00    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.86/1.00    inference(ennf_transformation,[],[f4])).
% 3.86/1.00  
% 3.86/1.00  fof(f13,plain,(
% 3.86/1.00    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.86/1.00    inference(flattening,[],[f12])).
% 3.86/1.00  
% 3.86/1.00  fof(f19,plain,(
% 3.86/1.00    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.86/1.00    inference(nnf_transformation,[],[f13])).
% 3.86/1.00  
% 3.86/1.00  fof(f20,plain,(
% 3.86/1.00    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.86/1.00    inference(rectify,[],[f19])).
% 3.86/1.00  
% 3.86/1.00  fof(f23,plain,(
% 3.86/1.00    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))))),
% 3.86/1.00    introduced(choice_axiom,[])).
% 3.86/1.00  
% 3.86/1.00  fof(f22,plain,(
% 3.86/1.00    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X1)) = X2 & r2_hidden(sK2(X0,X1),k1_relat_1(X0))))) )),
% 3.86/1.00    introduced(choice_axiom,[])).
% 3.86/1.00  
% 3.86/1.00  fof(f21,plain,(
% 3.86/1.00    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK1(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1))))),
% 3.86/1.00    introduced(choice_axiom,[])).
% 3.86/1.00  
% 3.86/1.00  fof(f24,plain,(
% 3.86/1.00    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & ((k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.86/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f20,f23,f22,f21])).
% 3.86/1.00  
% 3.86/1.00  fof(f38,plain,(
% 3.86/1.00    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | r2_hidden(sK2(X0,X1),k1_relat_1(X0)) | r2_hidden(sK1(X0,X1),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.86/1.00    inference(cnf_transformation,[],[f24])).
% 3.86/1.00  
% 3.86/1.00  fof(f41,plain,(
% 3.86/1.00    ( ! [X0,X1] : (v1_relat_1(sK4(X0,X1))) )),
% 3.86/1.00    inference(cnf_transformation,[],[f26])).
% 3.86/1.00  
% 3.86/1.00  fof(f42,plain,(
% 3.86/1.00    ( ! [X0,X1] : (v1_funct_1(sK4(X0,X1))) )),
% 3.86/1.00    inference(cnf_transformation,[],[f26])).
% 3.86/1.00  
% 3.86/1.00  fof(f1,axiom,(
% 3.86/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.86/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.86/1.00  
% 3.86/1.00  fof(f8,plain,(
% 3.86/1.00    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 3.86/1.00    inference(unused_predicate_definition_removal,[],[f1])).
% 3.86/1.00  
% 3.86/1.00  fof(f9,plain,(
% 3.86/1.00    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 3.86/1.00    inference(ennf_transformation,[],[f8])).
% 3.86/1.00  
% 3.86/1.00  fof(f17,plain,(
% 3.86/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.86/1.00    introduced(choice_axiom,[])).
% 3.86/1.00  
% 3.86/1.00  fof(f18,plain,(
% 3.86/1.00    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.86/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f17])).
% 3.86/1.00  
% 3.86/1.00  fof(f29,plain,(
% 3.86/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.86/1.00    inference(cnf_transformation,[],[f18])).
% 3.86/1.00  
% 3.86/1.00  fof(f6,conjecture,(
% 3.86/1.00    ! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 3.86/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.86/1.00  
% 3.86/1.00  fof(f7,negated_conjecture,(
% 3.86/1.00    ~! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 3.86/1.00    inference(negated_conjecture,[],[f6])).
% 3.86/1.00  
% 3.86/1.00  fof(f15,plain,(
% 3.86/1.00    ? [X0,X1] : (! [X2] : ((~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 3.86/1.00    inference(ennf_transformation,[],[f7])).
% 3.86/1.00  
% 3.86/1.00  fof(f16,plain,(
% 3.86/1.00    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 3.86/1.00    inference(flattening,[],[f15])).
% 3.86/1.00  
% 3.86/1.00  fof(f27,plain,(
% 3.86/1.00    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0)) => (! [X2] : (~r1_tarski(k2_relat_1(X2),sK5) | k1_relat_1(X2) != sK6 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = sK6 | k1_xboole_0 != sK5))),
% 3.86/1.00    introduced(choice_axiom,[])).
% 3.86/1.00  
% 3.86/1.00  fof(f28,plain,(
% 3.86/1.00    ! [X2] : (~r1_tarski(k2_relat_1(X2),sK5) | k1_relat_1(X2) != sK6 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = sK6 | k1_xboole_0 != sK5)),
% 3.86/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f16,f27])).
% 3.86/1.00  
% 3.86/1.00  fof(f46,plain,(
% 3.86/1.00    ( ! [X2] : (~r1_tarski(k2_relat_1(X2),sK5) | k1_relat_1(X2) != sK6 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.86/1.00    inference(cnf_transformation,[],[f28])).
% 3.86/1.00  
% 3.86/1.00  fof(f35,plain,(
% 3.86/1.00    ( ! [X0,X5,X1] : (r2_hidden(sK3(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.86/1.00    inference(cnf_transformation,[],[f24])).
% 3.86/1.00  
% 3.86/1.00  fof(f50,plain,(
% 3.86/1.00    ( ! [X0,X5] : (r2_hidden(sK3(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.86/1.00    inference(equality_resolution,[],[f35])).
% 3.86/1.00  
% 3.86/1.00  fof(f44,plain,(
% 3.86/1.00    ( ! [X0,X3,X1] : (k1_funct_1(sK4(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) )),
% 3.86/1.00    inference(cnf_transformation,[],[f26])).
% 3.86/1.00  
% 3.86/1.00  fof(f36,plain,(
% 3.86/1.00    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK3(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.86/1.00    inference(cnf_transformation,[],[f24])).
% 3.86/1.00  
% 3.86/1.00  fof(f49,plain,(
% 3.86/1.00    ( ! [X0,X5] : (k1_funct_1(X0,sK3(X0,X5)) = X5 | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.86/1.00    inference(equality_resolution,[],[f36])).
% 3.86/1.00  
% 3.86/1.00  fof(f30,plain,(
% 3.86/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.86/1.00    inference(cnf_transformation,[],[f18])).
% 3.86/1.00  
% 3.86/1.00  fof(f2,axiom,(
% 3.86/1.00    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.86/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.86/1.00  
% 3.86/1.00  fof(f31,plain,(
% 3.86/1.00    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.86/1.00    inference(cnf_transformation,[],[f2])).
% 3.86/1.00  
% 3.86/1.00  fof(f32,plain,(
% 3.86/1.00    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 3.86/1.00    inference(cnf_transformation,[],[f2])).
% 3.86/1.00  
% 3.86/1.00  fof(f3,axiom,(
% 3.86/1.00    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 3.86/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.86/1.00  
% 3.86/1.00  fof(f10,plain,(
% 3.86/1.00    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.86/1.00    inference(ennf_transformation,[],[f3])).
% 3.86/1.00  
% 3.86/1.00  fof(f11,plain,(
% 3.86/1.00    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.86/1.00    inference(flattening,[],[f10])).
% 3.86/1.00  
% 3.86/1.00  fof(f33,plain,(
% 3.86/1.00    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.86/1.00    inference(cnf_transformation,[],[f11])).
% 3.86/1.00  
% 3.86/1.00  fof(f45,plain,(
% 3.86/1.00    k1_xboole_0 = sK6 | k1_xboole_0 != sK5),
% 3.86/1.00    inference(cnf_transformation,[],[f28])).
% 3.86/1.00  
% 3.86/1.00  cnf(c_13,plain,
% 3.86/1.00      ( k1_relat_1(sK4(X0,X1)) = X0 ),
% 3.86/1.00      inference(cnf_transformation,[],[f43]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_8,plain,
% 3.86/1.00      ( r2_hidden(sK2(X0,X1),k1_relat_1(X0))
% 3.86/1.00      | r2_hidden(sK1(X0,X1),X1)
% 3.86/1.00      | ~ v1_funct_1(X0)
% 3.86/1.00      | ~ v1_relat_1(X0)
% 3.86/1.00      | k2_relat_1(X0) = X1 ),
% 3.86/1.00      inference(cnf_transformation,[],[f38]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1219,plain,
% 3.86/1.00      ( k2_relat_1(X0) = X1
% 3.86/1.00      | r2_hidden(sK2(X0,X1),k1_relat_1(X0)) = iProver_top
% 3.86/1.00      | r2_hidden(sK1(X0,X1),X1) = iProver_top
% 3.86/1.00      | v1_funct_1(X0) != iProver_top
% 3.86/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.86/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_3234,plain,
% 3.86/1.00      ( k2_relat_1(sK4(X0,X1)) = X2
% 3.86/1.00      | r2_hidden(sK2(sK4(X0,X1),X2),X0) = iProver_top
% 3.86/1.00      | r2_hidden(sK1(sK4(X0,X1),X2),X2) = iProver_top
% 3.86/1.00      | v1_funct_1(sK4(X0,X1)) != iProver_top
% 3.86/1.00      | v1_relat_1(sK4(X0,X1)) != iProver_top ),
% 3.86/1.00      inference(superposition,[status(thm)],[c_13,c_1219]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_15,plain,
% 3.86/1.00      ( v1_relat_1(sK4(X0,X1)) ),
% 3.86/1.00      inference(cnf_transformation,[],[f41]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_21,plain,
% 3.86/1.00      ( v1_relat_1(sK4(X0,X1)) = iProver_top ),
% 3.86/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_14,plain,
% 3.86/1.00      ( v1_funct_1(sK4(X0,X1)) ),
% 3.86/1.00      inference(cnf_transformation,[],[f42]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_24,plain,
% 3.86/1.00      ( v1_funct_1(sK4(X0,X1)) = iProver_top ),
% 3.86/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_4834,plain,
% 3.86/1.00      ( k2_relat_1(sK4(X0,X1)) = X2
% 3.86/1.00      | r2_hidden(sK2(sK4(X0,X1),X2),X0) = iProver_top
% 3.86/1.00      | r2_hidden(sK1(sK4(X0,X1),X2),X2) = iProver_top ),
% 3.86/1.00      inference(global_propositional_subsumption,
% 3.86/1.00                [status(thm)],
% 3.86/1.00                [c_3234,c_21,c_24]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1,plain,
% 3.86/1.00      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.86/1.00      inference(cnf_transformation,[],[f29]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_16,negated_conjecture,
% 3.86/1.00      ( ~ r1_tarski(k2_relat_1(X0),sK5)
% 3.86/1.00      | ~ v1_funct_1(X0)
% 3.86/1.00      | ~ v1_relat_1(X0)
% 3.86/1.00      | k1_relat_1(X0) != sK6 ),
% 3.86/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_172,plain,
% 3.86/1.00      ( r2_hidden(sK0(X0,X1),X0)
% 3.86/1.00      | ~ v1_funct_1(X2)
% 3.86/1.00      | ~ v1_relat_1(X2)
% 3.86/1.00      | k1_relat_1(X2) != sK6
% 3.86/1.00      | k2_relat_1(X2) != X0
% 3.86/1.00      | sK5 != X1 ),
% 3.86/1.00      inference(resolution_lifted,[status(thm)],[c_1,c_16]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_173,plain,
% 3.86/1.00      ( r2_hidden(sK0(k2_relat_1(X0),sK5),k2_relat_1(X0))
% 3.86/1.00      | ~ v1_funct_1(X0)
% 3.86/1.00      | ~ v1_relat_1(X0)
% 3.86/1.00      | k1_relat_1(X0) != sK6 ),
% 3.86/1.00      inference(unflattening,[status(thm)],[c_172]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1212,plain,
% 3.86/1.00      ( k1_relat_1(X0) != sK6
% 3.86/1.00      | r2_hidden(sK0(k2_relat_1(X0),sK5),k2_relat_1(X0)) = iProver_top
% 3.86/1.00      | v1_funct_1(X0) != iProver_top
% 3.86/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.86/1.00      inference(predicate_to_equality,[status(thm)],[c_173]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1518,plain,
% 3.86/1.00      ( sK6 != X0
% 3.86/1.00      | r2_hidden(sK0(k2_relat_1(sK4(X0,X1)),sK5),k2_relat_1(sK4(X0,X1))) = iProver_top
% 3.86/1.00      | v1_funct_1(sK4(X0,X1)) != iProver_top
% 3.86/1.00      | v1_relat_1(sK4(X0,X1)) != iProver_top ),
% 3.86/1.00      inference(superposition,[status(thm)],[c_13,c_1212]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1909,plain,
% 3.86/1.00      ( sK6 != X0
% 3.86/1.00      | r2_hidden(sK0(k2_relat_1(sK4(X0,X1)),sK5),k2_relat_1(sK4(X0,X1))) = iProver_top ),
% 3.86/1.00      inference(global_propositional_subsumption,
% 3.86/1.00                [status(thm)],
% 3.86/1.00                [c_1518,c_21,c_24]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1917,plain,
% 3.86/1.00      ( r2_hidden(sK0(k2_relat_1(sK4(sK6,X0)),sK5),k2_relat_1(sK4(sK6,X0))) = iProver_top ),
% 3.86/1.00      inference(equality_resolution,[status(thm)],[c_1909]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_11,plain,
% 3.86/1.00      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 3.86/1.00      | r2_hidden(sK3(X1,X0),k1_relat_1(X1))
% 3.86/1.00      | ~ v1_funct_1(X1)
% 3.86/1.00      | ~ v1_relat_1(X1) ),
% 3.86/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1216,plain,
% 3.86/1.00      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 3.86/1.00      | r2_hidden(sK3(X1,X0),k1_relat_1(X1)) = iProver_top
% 3.86/1.00      | v1_funct_1(X1) != iProver_top
% 3.86/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.86/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_12,plain,
% 3.86/1.00      ( ~ r2_hidden(X0,X1) | k1_funct_1(sK4(X1,X2),X0) = X2 ),
% 3.86/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1215,plain,
% 3.86/1.00      ( k1_funct_1(sK4(X0,X1),X2) = X1 | r2_hidden(X2,X0) != iProver_top ),
% 3.86/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_2364,plain,
% 3.86/1.00      ( k1_funct_1(sK4(k1_relat_1(X0),X1),sK3(X0,X2)) = X1
% 3.86/1.00      | r2_hidden(X2,k2_relat_1(X0)) != iProver_top
% 3.86/1.00      | v1_funct_1(X0) != iProver_top
% 3.86/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.86/1.00      inference(superposition,[status(thm)],[c_1216,c_1215]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_8059,plain,
% 3.86/1.00      ( k1_funct_1(sK4(k1_relat_1(sK4(sK6,X0)),X1),sK3(sK4(sK6,X0),sK0(k2_relat_1(sK4(sK6,X0)),sK5))) = X1
% 3.86/1.00      | v1_funct_1(sK4(sK6,X0)) != iProver_top
% 3.86/1.00      | v1_relat_1(sK4(sK6,X0)) != iProver_top ),
% 3.86/1.00      inference(superposition,[status(thm)],[c_1917,c_2364]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_8188,plain,
% 3.86/1.00      ( k1_funct_1(sK4(sK6,X0),sK3(sK4(sK6,X1),sK0(k2_relat_1(sK4(sK6,X1)),sK5))) = X0
% 3.86/1.00      | v1_funct_1(sK4(sK6,X1)) != iProver_top
% 3.86/1.00      | v1_relat_1(sK4(sK6,X1)) != iProver_top ),
% 3.86/1.00      inference(demodulation,[status(thm)],[c_8059,c_13]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1213,plain,
% 3.86/1.00      ( v1_relat_1(sK4(X0,X1)) = iProver_top ),
% 3.86/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1214,plain,
% 3.86/1.00      ( v1_funct_1(sK4(X0,X1)) = iProver_top ),
% 3.86/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_8271,plain,
% 3.86/1.00      ( k1_funct_1(sK4(sK6,X0),sK3(sK4(sK6,X1),sK0(k2_relat_1(sK4(sK6,X1)),sK5))) = X0 ),
% 3.86/1.00      inference(forward_subsumption_resolution,
% 3.86/1.00                [status(thm)],
% 3.86/1.00                [c_8188,c_1213,c_1214]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_10,plain,
% 3.86/1.00      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 3.86/1.00      | ~ v1_funct_1(X1)
% 3.86/1.00      | ~ v1_relat_1(X1)
% 3.86/1.00      | k1_funct_1(X1,sK3(X1,X0)) = X0 ),
% 3.86/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1217,plain,
% 3.86/1.00      ( k1_funct_1(X0,sK3(X0,X1)) = X1
% 3.86/1.00      | r2_hidden(X1,k2_relat_1(X0)) != iProver_top
% 3.86/1.00      | v1_funct_1(X0) != iProver_top
% 3.86/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.86/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_2507,plain,
% 3.86/1.00      ( k1_funct_1(sK4(sK6,X0),sK3(sK4(sK6,X0),sK0(k2_relat_1(sK4(sK6,X0)),sK5))) = sK0(k2_relat_1(sK4(sK6,X0)),sK5)
% 3.86/1.00      | v1_funct_1(sK4(sK6,X0)) != iProver_top
% 3.86/1.00      | v1_relat_1(sK4(sK6,X0)) != iProver_top ),
% 3.86/1.00      inference(superposition,[status(thm)],[c_1917,c_1217]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1379,plain,
% 3.86/1.00      ( r2_hidden(sK0(k2_relat_1(sK4(X0,X1)),sK5),k2_relat_1(sK4(X0,X1)))
% 3.86/1.00      | ~ v1_funct_1(sK4(X0,X1))
% 3.86/1.00      | ~ v1_relat_1(sK4(X0,X1))
% 3.86/1.00      | k1_relat_1(sK4(X0,X1)) != sK6 ),
% 3.86/1.00      inference(instantiation,[status(thm)],[c_173]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1496,plain,
% 3.86/1.00      ( r2_hidden(sK0(k2_relat_1(sK4(sK6,X0)),sK5),k2_relat_1(sK4(sK6,X0)))
% 3.86/1.00      | ~ v1_funct_1(sK4(sK6,X0))
% 3.86/1.00      | ~ v1_relat_1(sK4(sK6,X0))
% 3.86/1.00      | k1_relat_1(sK4(sK6,X0)) != sK6 ),
% 3.86/1.00      inference(instantiation,[status(thm)],[c_1379]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1497,plain,
% 3.86/1.00      ( k1_relat_1(sK4(sK6,X0)) = sK6 ),
% 3.86/1.00      inference(instantiation,[status(thm)],[c_13]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1601,plain,
% 3.86/1.00      ( v1_relat_1(sK4(sK6,X0)) ),
% 3.86/1.00      inference(instantiation,[status(thm)],[c_15]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1769,plain,
% 3.86/1.00      ( v1_funct_1(sK4(sK6,X0)) ),
% 3.86/1.00      inference(instantiation,[status(thm)],[c_14]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1935,plain,
% 3.86/1.00      ( ~ r2_hidden(sK0(k2_relat_1(sK4(sK6,X0)),sK5),k2_relat_1(sK4(sK6,X0)))
% 3.86/1.00      | ~ v1_funct_1(sK4(sK6,X0))
% 3.86/1.00      | ~ v1_relat_1(sK4(sK6,X0))
% 3.86/1.00      | k1_funct_1(sK4(sK6,X0),sK3(sK4(sK6,X0),sK0(k2_relat_1(sK4(sK6,X0)),sK5))) = sK0(k2_relat_1(sK4(sK6,X0)),sK5) ),
% 3.86/1.00      inference(instantiation,[status(thm)],[c_10]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_2757,plain,
% 3.86/1.00      ( k1_funct_1(sK4(sK6,X0),sK3(sK4(sK6,X0),sK0(k2_relat_1(sK4(sK6,X0)),sK5))) = sK0(k2_relat_1(sK4(sK6,X0)),sK5) ),
% 3.86/1.00      inference(global_propositional_subsumption,
% 3.86/1.00                [status(thm)],
% 3.86/1.00                [c_2507,c_1496,c_1497,c_1601,c_1769,c_1935]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_8273,plain,
% 3.86/1.00      ( sK0(k2_relat_1(sK4(sK6,X0)),sK5) = X0 ),
% 3.86/1.00      inference(demodulation,[status(thm)],[c_8271,c_2757]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_0,plain,
% 3.86/1.00      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.86/1.00      inference(cnf_transformation,[],[f30]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_190,plain,
% 3.86/1.00      ( ~ r2_hidden(sK0(X0,X1),X1)
% 3.86/1.00      | ~ v1_funct_1(X2)
% 3.86/1.00      | ~ v1_relat_1(X2)
% 3.86/1.00      | k1_relat_1(X2) != sK6
% 3.86/1.00      | k2_relat_1(X2) != X0
% 3.86/1.00      | sK5 != X1 ),
% 3.86/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_16]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_191,plain,
% 3.86/1.00      ( ~ r2_hidden(sK0(k2_relat_1(X0),sK5),sK5)
% 3.86/1.00      | ~ v1_funct_1(X0)
% 3.86/1.00      | ~ v1_relat_1(X0)
% 3.86/1.00      | k1_relat_1(X0) != sK6 ),
% 3.86/1.00      inference(unflattening,[status(thm)],[c_190]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1211,plain,
% 3.86/1.00      ( k1_relat_1(X0) != sK6
% 3.86/1.00      | r2_hidden(sK0(k2_relat_1(X0),sK5),sK5) != iProver_top
% 3.86/1.00      | v1_funct_1(X0) != iProver_top
% 3.86/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.86/1.00      inference(predicate_to_equality,[status(thm)],[c_191]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1519,plain,
% 3.86/1.00      ( sK6 != X0
% 3.86/1.00      | r2_hidden(sK0(k2_relat_1(sK4(X0,X1)),sK5),sK5) != iProver_top
% 3.86/1.00      | v1_funct_1(sK4(X0,X1)) != iProver_top
% 3.86/1.00      | v1_relat_1(sK4(X0,X1)) != iProver_top ),
% 3.86/1.00      inference(superposition,[status(thm)],[c_13,c_1211]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1811,plain,
% 3.86/1.00      ( sK6 != X0
% 3.86/1.00      | r2_hidden(sK0(k2_relat_1(sK4(X0,X1)),sK5),sK5) != iProver_top ),
% 3.86/1.00      inference(global_propositional_subsumption,
% 3.86/1.00                [status(thm)],
% 3.86/1.00                [c_1519,c_21,c_24]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1819,plain,
% 3.86/1.00      ( r2_hidden(sK0(k2_relat_1(sK4(sK6,X0)),sK5),sK5) != iProver_top ),
% 3.86/1.00      inference(equality_resolution,[status(thm)],[c_1811]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_8572,plain,
% 3.86/1.00      ( r2_hidden(X0,sK5) != iProver_top ),
% 3.86/1.00      inference(demodulation,[status(thm)],[c_8273,c_1819]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_8677,plain,
% 3.86/1.00      ( k2_relat_1(sK4(X0,X1)) = sK5
% 3.86/1.00      | r2_hidden(sK2(sK4(X0,X1),sK5),X0) = iProver_top ),
% 3.86/1.00      inference(superposition,[status(thm)],[c_4834,c_8572]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_3,plain,
% 3.86/1.00      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.86/1.00      inference(cnf_transformation,[],[f31]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_2362,plain,
% 3.86/1.00      ( r2_hidden(X0,k2_relat_1(k1_xboole_0)) != iProver_top
% 3.86/1.00      | r2_hidden(sK3(k1_xboole_0,X0),k1_xboole_0) = iProver_top
% 3.86/1.00      | v1_funct_1(k1_xboole_0) != iProver_top
% 3.86/1.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.86/1.00      inference(superposition,[status(thm)],[c_3,c_1216]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_2,plain,
% 3.86/1.00      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.86/1.00      inference(cnf_transformation,[],[f32]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_2385,plain,
% 3.86/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 3.86/1.00      | r2_hidden(sK3(k1_xboole_0,X0),k1_xboole_0) = iProver_top
% 3.86/1.00      | v1_funct_1(k1_xboole_0) != iProver_top
% 3.86/1.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.86/1.00      inference(light_normalisation,[status(thm)],[c_2362,c_2]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_23,plain,
% 3.86/1.00      ( v1_relat_1(sK4(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 3.86/1.00      inference(instantiation,[status(thm)],[c_21]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_26,plain,
% 3.86/1.00      ( v1_funct_1(sK4(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 3.86/1.00      inference(instantiation,[status(thm)],[c_24]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_27,plain,
% 3.86/1.00      ( k1_relat_1(sK4(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
% 3.86/1.00      inference(instantiation,[status(thm)],[c_13]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_5,plain,
% 3.86/1.00      ( ~ v1_relat_1(X0) | k1_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = X0 ),
% 3.86/1.00      inference(cnf_transformation,[],[f33]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_452,plain,
% 3.86/1.00      ( sK4(X0,X1) != X2 | k1_relat_1(X2) != k1_xboole_0 | k1_xboole_0 = X2 ),
% 3.86/1.00      inference(resolution_lifted,[status(thm)],[c_5,c_15]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_453,plain,
% 3.86/1.00      ( k1_relat_1(sK4(X0,X1)) != k1_xboole_0 | k1_xboole_0 = sK4(X0,X1) ),
% 3.86/1.00      inference(unflattening,[status(thm)],[c_452]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_454,plain,
% 3.86/1.00      ( k1_relat_1(sK4(k1_xboole_0,k1_xboole_0)) != k1_xboole_0
% 3.86/1.00      | k1_xboole_0 = sK4(k1_xboole_0,k1_xboole_0) ),
% 3.86/1.00      inference(instantiation,[status(thm)],[c_453]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_960,plain,
% 3.86/1.00      ( ~ v1_relat_1(X0) | v1_relat_1(X1) | X1 != X0 ),
% 3.86/1.00      theory(equality) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1415,plain,
% 3.86/1.00      ( v1_relat_1(X0) | ~ v1_relat_1(sK4(X1,X2)) | X0 != sK4(X1,X2) ),
% 3.86/1.00      inference(instantiation,[status(thm)],[c_960]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1416,plain,
% 3.86/1.00      ( X0 != sK4(X1,X2)
% 3.86/1.00      | v1_relat_1(X0) = iProver_top
% 3.86/1.00      | v1_relat_1(sK4(X1,X2)) != iProver_top ),
% 3.86/1.00      inference(predicate_to_equality,[status(thm)],[c_1415]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1418,plain,
% 3.86/1.00      ( k1_xboole_0 != sK4(k1_xboole_0,k1_xboole_0)
% 3.86/1.00      | v1_relat_1(sK4(k1_xboole_0,k1_xboole_0)) != iProver_top
% 3.86/1.00      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.86/1.00      inference(instantiation,[status(thm)],[c_1416]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_962,plain,
% 3.86/1.00      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 3.86/1.00      theory(equality) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1420,plain,
% 3.86/1.00      ( v1_funct_1(X0) | ~ v1_funct_1(sK4(X1,X2)) | X0 != sK4(X1,X2) ),
% 3.86/1.00      inference(instantiation,[status(thm)],[c_962]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1421,plain,
% 3.86/1.00      ( X0 != sK4(X1,X2)
% 3.86/1.00      | v1_funct_1(X0) = iProver_top
% 3.86/1.00      | v1_funct_1(sK4(X1,X2)) != iProver_top ),
% 3.86/1.00      inference(predicate_to_equality,[status(thm)],[c_1420]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1423,plain,
% 3.86/1.00      ( k1_xboole_0 != sK4(k1_xboole_0,k1_xboole_0)
% 3.86/1.00      | v1_funct_1(sK4(k1_xboole_0,k1_xboole_0)) != iProver_top
% 3.86/1.00      | v1_funct_1(k1_xboole_0) = iProver_top ),
% 3.86/1.00      inference(instantiation,[status(thm)],[c_1421]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_2400,plain,
% 3.86/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 3.86/1.00      | r2_hidden(sK3(k1_xboole_0,X0),k1_xboole_0) = iProver_top ),
% 3.86/1.00      inference(global_propositional_subsumption,
% 3.86/1.00                [status(thm)],
% 3.86/1.00                [c_2385,c_23,c_26,c_27,c_454,c_1418,c_1423]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_2408,plain,
% 3.86/1.00      ( k1_funct_1(sK4(k1_xboole_0,X0),sK3(k1_xboole_0,X1)) = X0
% 3.86/1.00      | r2_hidden(X1,k1_xboole_0) != iProver_top ),
% 3.86/1.00      inference(superposition,[status(thm)],[c_2400,c_1215]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1222,plain,
% 3.86/1.00      ( k1_relat_1(X0) != k1_xboole_0
% 3.86/1.00      | k1_xboole_0 = X0
% 3.86/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.86/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1716,plain,
% 3.86/1.00      ( sK4(X0,X1) = k1_xboole_0
% 3.86/1.00      | k1_xboole_0 != X0
% 3.86/1.00      | v1_relat_1(sK4(X0,X1)) != iProver_top ),
% 3.86/1.00      inference(superposition,[status(thm)],[c_13,c_1222]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_2140,plain,
% 3.86/1.00      ( k1_xboole_0 != X0 | sK4(X0,X1) = k1_xboole_0 ),
% 3.86/1.00      inference(global_propositional_subsumption,[status(thm)],[c_1716,c_21]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_2141,plain,
% 3.86/1.00      ( sK4(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0 ),
% 3.86/1.00      inference(renaming,[status(thm)],[c_2140]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_2145,plain,
% 3.86/1.00      ( sK4(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.86/1.00      inference(equality_resolution,[status(thm)],[c_2141]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_2409,plain,
% 3.86/1.00      ( k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,X0)) = X1
% 3.86/1.00      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.86/1.00      inference(light_normalisation,[status(thm)],[c_2408,c_2145]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_9760,plain,
% 3.86/1.00      ( k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,sK2(sK4(k1_xboole_0,X0),sK5))) = X1
% 3.86/1.00      | k2_relat_1(sK4(k1_xboole_0,X0)) = sK5 ),
% 3.86/1.00      inference(superposition,[status(thm)],[c_8677,c_2409]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_9763,plain,
% 3.86/1.00      ( k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,sK2(k1_xboole_0,sK5))) = X0
% 3.86/1.00      | sK5 = k1_xboole_0 ),
% 3.86/1.00      inference(light_normalisation,[status(thm)],[c_9760,c_2,c_2145]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_2363,plain,
% 3.86/1.00      ( r2_hidden(X0,k2_relat_1(sK4(X1,X2))) != iProver_top
% 3.86/1.00      | r2_hidden(sK3(sK4(X1,X2),X0),X1) = iProver_top
% 3.86/1.00      | v1_funct_1(sK4(X1,X2)) != iProver_top
% 3.86/1.00      | v1_relat_1(sK4(X1,X2)) != iProver_top ),
% 3.86/1.00      inference(superposition,[status(thm)],[c_13,c_1216]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_3722,plain,
% 3.86/1.00      ( r2_hidden(X0,k2_relat_1(sK4(X1,X2))) != iProver_top
% 3.86/1.00      | r2_hidden(sK3(sK4(X1,X2),X0),X1) = iProver_top ),
% 3.86/1.00      inference(forward_subsumption_resolution,
% 3.86/1.00                [status(thm)],
% 3.86/1.00                [c_2363,c_1213,c_1214]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_8678,plain,
% 3.86/1.00      ( r2_hidden(X0,k2_relat_1(sK4(sK5,X1))) != iProver_top ),
% 3.86/1.00      inference(superposition,[status(thm)],[c_3722,c_8572]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_10520,plain,
% 3.86/1.00      ( sK5 = k1_xboole_0
% 3.86/1.00      | r2_hidden(X0,k2_relat_1(k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,sK2(k1_xboole_0,sK5))))) != iProver_top ),
% 3.86/1.00      inference(superposition,[status(thm)],[c_9763,c_8678]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_8571,plain,
% 3.86/1.00      ( r2_hidden(X0,k2_relat_1(sK4(sK6,X0))) = iProver_top ),
% 3.86/1.00      inference(demodulation,[status(thm)],[c_8273,c_1917]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_10584,plain,
% 3.86/1.00      ( sK5 = k1_xboole_0
% 3.86/1.00      | r2_hidden(X0,k2_relat_1(k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,sK2(k1_xboole_0,sK5))))) = iProver_top ),
% 3.86/1.00      inference(superposition,[status(thm)],[c_9763,c_8571]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_11302,plain,
% 3.86/1.00      ( sK5 = k1_xboole_0 ),
% 3.86/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_10520,c_10584]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1452,plain,
% 3.86/1.00      ( sK6 != k1_xboole_0
% 3.86/1.00      | r2_hidden(sK0(k2_relat_1(k1_xboole_0),sK5),sK5) != iProver_top
% 3.86/1.00      | v1_funct_1(k1_xboole_0) != iProver_top
% 3.86/1.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.86/1.00      inference(superposition,[status(thm)],[c_3,c_1211]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1457,plain,
% 3.86/1.00      ( sK6 != k1_xboole_0
% 3.86/1.00      | r2_hidden(sK0(k1_xboole_0,sK5),sK5) != iProver_top
% 3.86/1.00      | v1_funct_1(k1_xboole_0) != iProver_top
% 3.86/1.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.86/1.00      inference(light_normalisation,[status(thm)],[c_1452,c_2]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1511,plain,
% 3.86/1.00      ( sK6 != k1_xboole_0
% 3.86/1.00      | r2_hidden(sK0(k1_xboole_0,sK5),sK5) != iProver_top ),
% 3.86/1.00      inference(global_propositional_subsumption,
% 3.86/1.00                [status(thm)],
% 3.86/1.00                [c_1457,c_23,c_26,c_27,c_454,c_1418,c_1423]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_12732,plain,
% 3.86/1.00      ( sK6 != k1_xboole_0
% 3.86/1.00      | r2_hidden(sK0(k1_xboole_0,k1_xboole_0),k1_xboole_0) != iProver_top ),
% 3.86/1.00      inference(demodulation,[status(thm)],[c_11302,c_1511]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_17,negated_conjecture,
% 3.86/1.00      ( k1_xboole_0 = sK6 | k1_xboole_0 != sK5 ),
% 3.86/1.00      inference(cnf_transformation,[],[f45]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_12736,plain,
% 3.86/1.00      ( sK6 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.86/1.00      inference(demodulation,[status(thm)],[c_11302,c_17]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_12737,plain,
% 3.86/1.00      ( sK6 = k1_xboole_0 ),
% 3.86/1.00      inference(equality_resolution_simp,[status(thm)],[c_12736]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_12762,plain,
% 3.86/1.00      ( k1_xboole_0 != k1_xboole_0
% 3.86/1.00      | r2_hidden(sK0(k1_xboole_0,k1_xboole_0),k1_xboole_0) != iProver_top ),
% 3.86/1.00      inference(light_normalisation,[status(thm)],[c_12732,c_12737]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_12763,plain,
% 3.86/1.00      ( r2_hidden(sK0(k1_xboole_0,k1_xboole_0),k1_xboole_0) != iProver_top ),
% 3.86/1.00      inference(equality_resolution_simp,[status(thm)],[c_12762]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1451,plain,
% 3.86/1.00      ( sK6 != k1_xboole_0
% 3.86/1.00      | r2_hidden(sK0(k2_relat_1(k1_xboole_0),sK5),k2_relat_1(k1_xboole_0)) = iProver_top
% 3.86/1.00      | v1_funct_1(k1_xboole_0) != iProver_top
% 3.86/1.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.86/1.00      inference(superposition,[status(thm)],[c_3,c_1212]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1466,plain,
% 3.86/1.00      ( sK6 != k1_xboole_0
% 3.86/1.00      | r2_hidden(sK0(k1_xboole_0,sK5),k1_xboole_0) = iProver_top
% 3.86/1.00      | v1_funct_1(k1_xboole_0) != iProver_top
% 3.86/1.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.86/1.00      inference(light_normalisation,[status(thm)],[c_1451,c_2]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1474,plain,
% 3.86/1.00      ( sK6 != k1_xboole_0
% 3.86/1.00      | r2_hidden(sK0(k1_xboole_0,sK5),k1_xboole_0) = iProver_top ),
% 3.86/1.00      inference(global_propositional_subsumption,
% 3.86/1.00                [status(thm)],
% 3.86/1.00                [c_1466,c_23,c_26,c_27,c_454,c_1418,c_1423]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_12733,plain,
% 3.86/1.00      ( sK6 != k1_xboole_0
% 3.86/1.00      | r2_hidden(sK0(k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 3.86/1.00      inference(demodulation,[status(thm)],[c_11302,c_1474]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_12758,plain,
% 3.86/1.00      ( k1_xboole_0 != k1_xboole_0
% 3.86/1.00      | r2_hidden(sK0(k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 3.86/1.00      inference(light_normalisation,[status(thm)],[c_12733,c_12737]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_12759,plain,
% 3.86/1.00      ( r2_hidden(sK0(k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 3.86/1.00      inference(equality_resolution_simp,[status(thm)],[c_12758]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_12765,plain,
% 3.86/1.00      ( $false ),
% 3.86/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_12763,c_12759]) ).
% 3.86/1.00  
% 3.86/1.00  
% 3.86/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.86/1.00  
% 3.86/1.00  ------                               Statistics
% 3.86/1.00  
% 3.86/1.00  ------ Selected
% 3.86/1.00  
% 3.86/1.00  total_time:                             0.4
% 3.86/1.00  
%------------------------------------------------------------------------------
