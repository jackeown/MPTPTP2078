%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:49:42 EST 2020

% Result     : Theorem 7.91s
% Output     : CNFRefutation 7.91s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_6000)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f27,plain,(
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

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X3] :
          ( k1_funct_1(sK4(X0,X1),X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(sK4(X0,X1)) = X0
      & v1_funct_1(sK4(X0,X1))
      & v1_relat_1(sK4(X0,X1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f15,f27])).

fof(f45,plain,(
    ! [X0,X1] : k1_relat_1(sK4(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_relat_1(X0) = k1_xboole_0 )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f11,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f33,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_relat_1(X0) != k1_xboole_0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f43,plain,(
    ! [X0,X1] : v1_relat_1(sK4(X0,X1)) ),
    inference(cnf_transformation,[],[f28])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f25,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X5)) = X5
        & r2_hidden(sK3(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1)) = X2
        & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
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

fof(f26,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f22,f25,f24,f23])).

fof(f37,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK3(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f52,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK3(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f44,plain,(
    ! [X0,X1] : v1_funct_1(sK4(X0,X1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k1_xboole_0
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k1_xboole_0
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0] :
      ( ( ( k1_relat_1(X0) = k1_xboole_0
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_relat_1(X0) != k1_xboole_0 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f35,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | k1_relat_1(X0) != k1_xboole_0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(sK4(X0,X1),X3) = X1
      | ~ r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(sK2(X0,X1),k1_relat_1(X0))
      | r2_hidden(sK1(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f18])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ~ ( r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X1 ) )
        & ~ ( k1_xboole_0 != X1
            & k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f16,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(flattening,[],[f16])).

fof(f29,plain,
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

fof(f30,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k2_relat_1(X2),sK5)
        | k1_relat_1(X2) != sK6
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    & ( k1_xboole_0 = sK6
      | k1_xboole_0 != sK5 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f17,f29])).

fof(f48,plain,(
    ! [X2] :
      ( ~ r1_tarski(k2_relat_1(X2),sK5)
      | k1_relat_1(X2) != sK6
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f38,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK3(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f51,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK3(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f38])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f39,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f49,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f39])).

fof(f50,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f34,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f47,plain,
    ( k1_xboole_0 = sK6
    | k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_13,plain,
    ( k1_relat_1(sK4(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1289,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1573,plain,
    ( sK4(X0,X1) = k1_xboole_0
    | k1_xboole_0 != X0
    | v1_relat_1(sK4(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_1289])).

cnf(c_15,plain,
    ( v1_relat_1(sK4(X0,X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_21,plain,
    ( v1_relat_1(sK4(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1830,plain,
    ( k1_xboole_0 != X0
    | sK4(X0,X1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1573,c_21])).

cnf(c_1831,plain,
    ( sK4(X0,X1) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(renaming,[status(thm)],[c_1830])).

cnf(c_1833,plain,
    ( sK4(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_1831])).

cnf(c_1837,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1833,c_13])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK3(X1,X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1281,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(sK3(X1,X0),k1_relat_1(X1)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1932,plain,
    ( r2_hidden(X0,k2_relat_1(k1_xboole_0)) != iProver_top
    | r2_hidden(sK3(k1_xboole_0,X0),k1_xboole_0) = iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1837,c_1281])).

cnf(c_23,plain,
    ( v1_relat_1(sK4(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_14,plain,
    ( v1_funct_1(sK4(X0,X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_24,plain,
    ( v1_funct_1(sK4(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_26,plain,
    ( v1_funct_1(sK4(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_27,plain,
    ( k1_relat_1(sK4(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_488,plain,
    ( sK4(X0,X1) != X2
    | k1_relat_1(X2) != k1_xboole_0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_15])).

cnf(c_489,plain,
    ( k1_relat_1(sK4(X0,X1)) != k1_xboole_0
    | k1_xboole_0 = sK4(X0,X1) ),
    inference(unflattening,[status(thm)],[c_488])).

cnf(c_490,plain,
    ( k1_relat_1(sK4(k1_xboole_0,k1_xboole_0)) != k1_xboole_0
    | k1_xboole_0 = sK4(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_489])).

cnf(c_1032,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1343,plain,
    ( v1_funct_1(X0)
    | ~ v1_funct_1(sK4(X1,X2))
    | X0 != sK4(X1,X2) ),
    inference(instantiation,[status(thm)],[c_1032])).

cnf(c_1344,plain,
    ( X0 != sK4(X1,X2)
    | v1_funct_1(X0) = iProver_top
    | v1_funct_1(sK4(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1343])).

cnf(c_1346,plain,
    ( k1_xboole_0 != sK4(k1_xboole_0,k1_xboole_0)
    | v1_funct_1(sK4(k1_xboole_0,k1_xboole_0)) != iProver_top
    | v1_funct_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1344])).

cnf(c_1029,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1379,plain,
    ( v1_relat_1(X0)
    | ~ v1_relat_1(sK4(X1,X2))
    | X0 != sK4(X1,X2) ),
    inference(instantiation,[status(thm)],[c_1029])).

cnf(c_1380,plain,
    ( X0 != sK4(X1,X2)
    | v1_relat_1(X0) = iProver_top
    | v1_relat_1(sK4(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1379])).

cnf(c_1382,plain,
    ( k1_xboole_0 != sK4(k1_xboole_0,k1_xboole_0)
    | v1_relat_1(sK4(k1_xboole_0,k1_xboole_0)) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1380])).

cnf(c_3310,plain,
    ( r2_hidden(X0,k2_relat_1(k1_xboole_0)) != iProver_top
    | r2_hidden(sK3(k1_xboole_0,X0),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1932,c_23,c_26,c_27,c_490,c_1346,c_1382])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k2_relat_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1287,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | k2_relat_1(X0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1756,plain,
    ( k2_relat_1(sK4(X0,X1)) = k1_xboole_0
    | k1_xboole_0 != X0
    | v1_relat_1(sK4(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_1287])).

cnf(c_1977,plain,
    ( k1_xboole_0 != X0
    | k2_relat_1(sK4(X0,X1)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1756,c_21])).

cnf(c_1978,plain,
    ( k2_relat_1(sK4(X0,X1)) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(renaming,[status(thm)],[c_1977])).

cnf(c_1980,plain,
    ( k2_relat_1(sK4(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_1978])).

cnf(c_1981,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1980,c_1833])).

cnf(c_3316,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r2_hidden(sK3(k1_xboole_0,X0),k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3310,c_1981])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_funct_1(sK4(X1,X2),X0) = X2 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1280,plain,
    ( k1_funct_1(sK4(X0,X1),X2) = X1
    | r2_hidden(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3320,plain,
    ( k1_funct_1(sK4(k1_xboole_0,X0),sK3(k1_xboole_0,X1)) = X0
    | r2_hidden(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3316,c_1280])).

cnf(c_3321,plain,
    ( k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,X0)) = X1
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3320,c_1833])).

cnf(c_22,plain,
    ( v1_relat_1(sK4(k1_xboole_0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_25,plain,
    ( v1_funct_1(sK4(k1_xboole_0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1345,plain,
    ( ~ v1_funct_1(sK4(k1_xboole_0,k1_xboole_0))
    | v1_funct_1(k1_xboole_0)
    | k1_xboole_0 != sK4(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1343])).

cnf(c_1381,plain,
    ( ~ v1_relat_1(sK4(k1_xboole_0,k1_xboole_0))
    | v1_relat_1(k1_xboole_0)
    | k1_xboole_0 != sK4(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1379])).

cnf(c_8,plain,
    ( r2_hidden(sK2(X0,X1),k1_relat_1(X0))
    | r2_hidden(sK1(X0,X1),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1284,plain,
    ( k2_relat_1(X0) = X1
    | r2_hidden(sK2(X0,X1),k1_relat_1(X0)) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2082,plain,
    ( k2_relat_1(sK4(X0,X1)) = X2
    | r2_hidden(sK2(sK4(X0,X1),X2),X0) = iProver_top
    | r2_hidden(sK1(sK4(X0,X1),X2),X2) = iProver_top
    | v1_funct_1(sK4(X0,X1)) != iProver_top
    | v1_relat_1(sK4(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_1284])).

cnf(c_2735,plain,
    ( k2_relat_1(sK4(X0,X1)) = X2
    | r2_hidden(sK2(sK4(X0,X1),X2),X0) = iProver_top
    | r2_hidden(sK1(sK4(X0,X1),X2),X2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2082,c_21,c_24])).

cnf(c_2745,plain,
    ( k1_funct_1(sK4(X0,X1),sK2(sK4(X0,X2),X3)) = X1
    | k2_relat_1(sK4(X0,X2)) = X3
    | r2_hidden(sK1(sK4(X0,X2),X3),X3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2735,c_1280])).

cnf(c_1278,plain,
    ( v1_relat_1(sK4(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1279,plain,
    ( v1_funct_1(sK4(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_16,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(X0),sK5)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) != sK6 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_191,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_relat_1(X2) != sK6
    | k2_relat_1(X2) != X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_16])).

cnf(c_192,plain,
    ( r2_hidden(sK0(k2_relat_1(X0),sK5),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) != sK6 ),
    inference(unflattening,[status(thm)],[c_191])).

cnf(c_1277,plain,
    ( k1_relat_1(X0) != sK6
    | r2_hidden(sK0(k2_relat_1(X0),sK5),k2_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_192])).

cnf(c_1389,plain,
    ( sK6 != X0
    | r2_hidden(sK0(k2_relat_1(sK4(X0,X1)),sK5),k2_relat_1(sK4(X0,X1))) = iProver_top
    | v1_funct_1(sK4(X0,X1)) != iProver_top
    | v1_relat_1(sK4(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_1277])).

cnf(c_1444,plain,
    ( sK6 != X0
    | r2_hidden(sK0(k2_relat_1(sK4(X0,X1)),sK5),k2_relat_1(sK4(X0,X1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1389,c_21,c_24])).

cnf(c_1450,plain,
    ( r2_hidden(sK0(k2_relat_1(sK4(sK6,X0)),sK5),k2_relat_1(sK4(sK6,X0))) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1444])).

cnf(c_1933,plain,
    ( k1_funct_1(sK4(k1_relat_1(X0),X1),sK3(X0,X2)) = X1
    | r2_hidden(X2,k2_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1281,c_1280])).

cnf(c_3964,plain,
    ( k1_funct_1(sK4(k1_relat_1(sK4(sK6,X0)),X1),sK3(sK4(sK6,X0),sK0(k2_relat_1(sK4(sK6,X0)),sK5))) = X1
    | v1_funct_1(sK4(sK6,X0)) != iProver_top
    | v1_relat_1(sK4(sK6,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1450,c_1933])).

cnf(c_3973,plain,
    ( k1_funct_1(sK4(sK6,X0),sK3(sK4(sK6,X1),sK0(k2_relat_1(sK4(sK6,X1)),sK5))) = X0
    | v1_funct_1(sK4(sK6,X1)) != iProver_top
    | v1_relat_1(sK4(sK6,X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3964,c_13])).

cnf(c_4154,plain,
    ( k1_funct_1(sK4(sK6,X0),sK3(sK4(sK6,X1),sK0(k2_relat_1(sK4(sK6,X1)),sK5))) = X0
    | v1_relat_1(sK4(sK6,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1279,c_3973])).

cnf(c_4353,plain,
    ( k1_funct_1(sK4(sK6,X0),sK3(sK4(sK6,X1),sK0(k2_relat_1(sK4(sK6,X1)),sK5))) = X0 ),
    inference(superposition,[status(thm)],[c_1278,c_4154])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK3(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1282,plain,
    ( k1_funct_1(X0,sK3(X0,X1)) = X1
    | r2_hidden(X1,k2_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1983,plain,
    ( k1_funct_1(sK4(sK6,X0),sK3(sK4(sK6,X0),sK0(k2_relat_1(sK4(sK6,X0)),sK5))) = sK0(k2_relat_1(sK4(sK6,X0)),sK5)
    | v1_funct_1(sK4(sK6,X0)) != iProver_top
    | v1_relat_1(sK4(sK6,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1450,c_1282])).

cnf(c_1370,plain,
    ( v1_funct_1(sK4(sK6,X0)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1371,plain,
    ( v1_funct_1(sK4(sK6,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1370])).

cnf(c_1416,plain,
    ( v1_relat_1(sK4(sK6,X0)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1417,plain,
    ( v1_relat_1(sK4(sK6,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1416])).

cnf(c_2272,plain,
    ( k1_funct_1(sK4(sK6,X0),sK3(sK4(sK6,X0),sK0(k2_relat_1(sK4(sK6,X0)),sK5))) = sK0(k2_relat_1(sK4(sK6,X0)),sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1983,c_1371,c_1417])).

cnf(c_4486,plain,
    ( sK0(k2_relat_1(sK4(sK6,X0)),sK5) = X0 ),
    inference(demodulation,[status(thm)],[c_4353,c_2272])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_209,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_relat_1(X2) != sK6
    | k2_relat_1(X2) != X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_16])).

cnf(c_210,plain,
    ( ~ r2_hidden(sK0(k2_relat_1(X0),sK5),sK5)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) != sK6 ),
    inference(unflattening,[status(thm)],[c_209])).

cnf(c_1276,plain,
    ( k1_relat_1(X0) != sK6
    | r2_hidden(sK0(k2_relat_1(X0),sK5),sK5) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_210])).

cnf(c_1390,plain,
    ( sK6 != X0
    | r2_hidden(sK0(k2_relat_1(sK4(X0,X1)),sK5),sK5) != iProver_top
    | v1_funct_1(sK4(X0,X1)) != iProver_top
    | v1_relat_1(sK4(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_1276])).

cnf(c_1433,plain,
    ( sK6 != X0
    | r2_hidden(sK0(k2_relat_1(sK4(X0,X1)),sK5),sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1390,c_21,c_24])).

cnf(c_1439,plain,
    ( r2_hidden(sK0(k2_relat_1(sK4(sK6,X0)),sK5),sK5) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1433])).

cnf(c_4501,plain,
    ( r2_hidden(X0,sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4486,c_1439])).

cnf(c_4734,plain,
    ( k1_funct_1(sK4(X0,X1),sK2(sK4(X0,X2),sK5)) = X1
    | k2_relat_1(sK4(X0,X2)) = sK5 ),
    inference(superposition,[status(thm)],[c_2745,c_4501])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1283,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_5533,plain,
    ( k2_relat_1(sK4(X0,X1)) = sK5
    | r2_hidden(X2,k2_relat_1(sK4(X0,X2))) = iProver_top
    | r2_hidden(sK2(sK4(X0,X1),sK5),k1_relat_1(sK4(X0,X2))) != iProver_top
    | v1_funct_1(sK4(X0,X2)) != iProver_top
    | v1_relat_1(sK4(X0,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4734,c_1283])).

cnf(c_5534,plain,
    ( k2_relat_1(sK4(X0,X1)) = sK5
    | r2_hidden(X2,k2_relat_1(sK4(X0,X2))) = iProver_top
    | r2_hidden(sK2(sK4(X0,X1),sK5),X0) != iProver_top
    | v1_funct_1(sK4(X0,X2)) != iProver_top
    | v1_relat_1(sK4(X0,X2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5533,c_13])).

cnf(c_4730,plain,
    ( k2_relat_1(sK4(X0,X1)) = sK5
    | r2_hidden(sK2(sK4(X0,X1),sK5),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2735,c_4501])).

cnf(c_5984,plain,
    ( r2_hidden(X2,k2_relat_1(sK4(X0,X2))) = iProver_top
    | k2_relat_1(sK4(X0,X1)) = sK5
    | v1_funct_1(sK4(X0,X2)) != iProver_top
    | v1_relat_1(sK4(X0,X2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5534,c_4730])).

cnf(c_5985,plain,
    ( k2_relat_1(sK4(X0,X1)) = sK5
    | r2_hidden(X2,k2_relat_1(sK4(X0,X2))) = iProver_top
    | v1_funct_1(sK4(X0,X2)) != iProver_top
    | v1_relat_1(sK4(X0,X2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5984])).

cnf(c_5994,plain,
    ( k1_funct_1(sK4(k1_relat_1(sK4(X0,X1)),X2),sK3(sK4(X0,X1),X1)) = X2
    | k2_relat_1(sK4(X0,X3)) = sK5
    | v1_funct_1(sK4(X0,X1)) != iProver_top
    | v1_relat_1(sK4(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5985,c_1933])).

cnf(c_5998,plain,
    ( k1_funct_1(sK4(X0,X1),sK3(sK4(X0,X2),X2)) = X1
    | k2_relat_1(sK4(X0,X3)) = sK5
    | v1_funct_1(sK4(X0,X2)) != iProver_top
    | v1_relat_1(sK4(X0,X2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5994,c_13])).

cnf(c_6101,plain,
    ( k1_funct_1(sK4(k1_xboole_0,X0),sK3(sK4(k1_xboole_0,X1),X1)) = X0
    | k2_relat_1(sK4(k1_xboole_0,X2)) = sK5
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(sK4(k1_xboole_0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1833,c_5998])).

cnf(c_6116,plain,
    ( k1_funct_1(k1_xboole_0,sK3(sK4(k1_xboole_0,X0),X0)) = X1
    | k2_relat_1(sK4(k1_xboole_0,X2)) = sK5
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(sK4(k1_xboole_0,X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6101,c_1833])).

cnf(c_6117,plain,
    ( k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,X0)) = X1
    | sK5 = k1_xboole_0
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6116,c_1833,c_1981])).

cnf(c_6118,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,X0)) = X1
    | sK5 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6117])).

cnf(c_5411,plain,
    ( k2_relat_1(sK4(sK5,X0)) = sK5 ),
    inference(superposition,[status(thm)],[c_4730,c_4501])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1290,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_5428,plain,
    ( sK4(sK5,X0) = k1_xboole_0
    | sK5 != k1_xboole_0
    | v1_relat_1(sK4(sK5,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5411,c_1290])).

cnf(c_17,negated_conjecture,
    ( k1_xboole_0 = sK6
    | k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1025,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1040,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1025])).

cnf(c_1026,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1314,plain,
    ( sK5 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_1026])).

cnf(c_1315,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1314])).

cnf(c_1418,plain,
    ( v1_relat_1(sK4(sK6,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_1416])).

cnf(c_1440,plain,
    ( ~ r2_hidden(sK0(k2_relat_1(sK4(sK6,X0)),sK5),sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1439])).

cnf(c_1442,plain,
    ( ~ r2_hidden(sK0(k2_relat_1(sK4(sK6,k1_xboole_0)),sK5),sK5) ),
    inference(instantiation,[status(thm)],[c_1440])).

cnf(c_1451,plain,
    ( r2_hidden(sK0(k2_relat_1(sK4(sK6,X0)),sK5),k2_relat_1(sK4(sK6,X0))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1450])).

cnf(c_1453,plain,
    ( r2_hidden(sK0(k2_relat_1(sK4(sK6,k1_xboole_0)),sK5),k2_relat_1(sK4(sK6,k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_1451])).

cnf(c_1472,plain,
    ( k1_relat_1(sK4(sK6,X0)) = sK6 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1473,plain,
    ( k1_relat_1(sK4(sK6,k1_xboole_0)) = sK6 ),
    inference(instantiation,[status(thm)],[c_1472])).

cnf(c_1028,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1492,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK0(k2_relat_1(sK4(sK6,X2)),sK5),sK5)
    | sK0(k2_relat_1(sK4(sK6,X2)),sK5) != X0
    | sK5 != X1 ),
    inference(instantiation,[status(thm)],[c_1028])).

cnf(c_1494,plain,
    ( r2_hidden(sK0(k2_relat_1(sK4(sK6,k1_xboole_0)),sK5),sK5)
    | ~ r2_hidden(k1_xboole_0,k1_xboole_0)
    | sK0(k2_relat_1(sK4(sK6,k1_xboole_0)),sK5) != k1_xboole_0
    | sK5 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1492])).

cnf(c_1770,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK0(k2_relat_1(sK4(sK6,X2)),sK5),k2_relat_1(sK4(sK6,X2)))
    | X0 != sK0(k2_relat_1(sK4(sK6,X2)),sK5)
    | X1 != k2_relat_1(sK4(sK6,X2)) ),
    inference(instantiation,[status(thm)],[c_1028])).

cnf(c_1772,plain,
    ( ~ r2_hidden(sK0(k2_relat_1(sK4(sK6,k1_xboole_0)),sK5),k2_relat_1(sK4(sK6,k1_xboole_0)))
    | r2_hidden(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != sK0(k2_relat_1(sK4(sK6,k1_xboole_0)),sK5)
    | k1_xboole_0 != k2_relat_1(sK4(sK6,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_1770])).

cnf(c_1557,plain,
    ( k2_relat_1(X0) != X1
    | k1_xboole_0 != X1
    | k1_xboole_0 = k2_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_1026])).

cnf(c_1712,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = k2_relat_1(X0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1557])).

cnf(c_2300,plain,
    ( k2_relat_1(sK4(sK6,X0)) != k1_xboole_0
    | k1_xboole_0 = k2_relat_1(sK4(sK6,X0))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1712])).

cnf(c_2305,plain,
    ( k2_relat_1(sK4(sK6,k1_xboole_0)) != k1_xboole_0
    | k1_xboole_0 = k2_relat_1(sK4(sK6,k1_xboole_0))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2300])).

cnf(c_3180,plain,
    ( ~ v1_relat_1(sK4(sK6,X0))
    | k1_relat_1(sK4(sK6,X0)) != k1_xboole_0
    | k2_relat_1(sK4(sK6,X0)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3182,plain,
    ( ~ v1_relat_1(sK4(sK6,k1_xboole_0))
    | k1_relat_1(sK4(sK6,k1_xboole_0)) != k1_xboole_0
    | k2_relat_1(sK4(sK6,k1_xboole_0)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3180])).

cnf(c_2243,plain,
    ( X0 != X1
    | k1_relat_1(sK4(sK6,X2)) != X1
    | k1_relat_1(sK4(sK6,X2)) = X0 ),
    inference(instantiation,[status(thm)],[c_1026])).

cnf(c_3551,plain,
    ( X0 != sK6
    | k1_relat_1(sK4(sK6,X1)) = X0
    | k1_relat_1(sK4(sK6,X1)) != sK6 ),
    inference(instantiation,[status(thm)],[c_2243])).

cnf(c_3552,plain,
    ( k1_relat_1(sK4(sK6,k1_xboole_0)) != sK6
    | k1_relat_1(sK4(sK6,k1_xboole_0)) = k1_xboole_0
    | k1_xboole_0 != sK6 ),
    inference(instantiation,[status(thm)],[c_3551])).

cnf(c_3725,plain,
    ( X0 != X1
    | X0 = sK0(k2_relat_1(sK4(sK6,X2)),sK5)
    | sK0(k2_relat_1(sK4(sK6,X2)),sK5) != X1 ),
    inference(instantiation,[status(thm)],[c_1026])).

cnf(c_3726,plain,
    ( sK0(k2_relat_1(sK4(sK6,k1_xboole_0)),sK5) != k1_xboole_0
    | k1_xboole_0 = sK0(k2_relat_1(sK4(sK6,k1_xboole_0)),sK5)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3725])).

cnf(c_4487,plain,
    ( sK0(k2_relat_1(sK4(sK6,k1_xboole_0)),sK5) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4486])).

cnf(c_6304,plain,
    ( sK5 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5428,c_17,c_1040,c_1315,c_1418,c_1442,c_1453,c_1473,c_1494,c_1772,c_2305,c_3182,c_3552,c_3726,c_4487])).

cnf(c_22869,plain,
    ( k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,X0)) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3321,c_17,c_23,c_26,c_27,c_490,c_1040,c_1315,c_1346,c_1382,c_1418,c_1442,c_1453,c_1473,c_1494,c_1772,c_2305,c_3182,c_3552,c_3726,c_4487,c_6000])).

cnf(c_4500,plain,
    ( r2_hidden(X0,k2_relat_1(sK4(sK6,X0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4486,c_1450])).

cnf(c_23274,plain,
    ( r2_hidden(X0,k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_22869,c_4500])).

cnf(c_5408,plain,
    ( k2_relat_1(sK4(k1_xboole_0,X0)) = sK5
    | r2_hidden(sK2(k1_xboole_0,sK5),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1833,c_4730])).

cnf(c_5415,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK2(k1_xboole_0,sK5),k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5408,c_1833,c_1981])).

cnf(c_11422,plain,
    ( r2_hidden(sK2(k1_xboole_0,sK5),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5415,c_17,c_1040,c_1315,c_1418,c_1442,c_1453,c_1473,c_1494,c_1772,c_2305,c_3182,c_3552,c_3726,c_4487])).

cnf(c_2070,plain,
    ( k1_funct_1(X0,sK3(X0,k1_funct_1(X0,X1))) = k1_funct_1(X0,X1)
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1283,c_1282])).

cnf(c_7163,plain,
    ( k1_funct_1(sK4(X0,X1),sK3(sK4(X0,X1),k1_funct_1(sK4(X0,X1),X2))) = k1_funct_1(sK4(X0,X1),X2)
    | r2_hidden(X2,X0) != iProver_top
    | v1_funct_1(sK4(X0,X1)) != iProver_top
    | v1_relat_1(sK4(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_2070])).

cnf(c_7206,plain,
    ( k1_funct_1(sK4(X0,X1),sK3(sK4(X0,X1),k1_funct_1(sK4(X0,X1),X2))) = k1_funct_1(sK4(X0,X1),X2)
    | r2_hidden(X2,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7163,c_21,c_24])).

cnf(c_7228,plain,
    ( k1_funct_1(sK4(X0,X1),sK3(sK4(X0,X1),k1_funct_1(sK4(X0,X1),sK2(sK4(X0,X2),sK5)))) = k1_funct_1(sK4(X0,X1),sK2(sK4(X0,X2),sK5))
    | k2_relat_1(sK4(X0,X2)) = sK5 ),
    inference(superposition,[status(thm)],[c_4730,c_7206])).

cnf(c_7682,plain,
    ( k1_funct_1(sK4(X0,X1),sK3(sK4(X0,X1),X1)) = k1_funct_1(sK4(X0,X1),sK2(sK4(X0,X2),sK5))
    | k2_relat_1(sK4(X0,X2)) = sK5 ),
    inference(superposition,[status(thm)],[c_4734,c_7228])).

cnf(c_7797,plain,
    ( k1_funct_1(sK4(X0,X1),sK3(sK4(X0,X1),X1)) = X1
    | k2_relat_1(sK4(X0,X2)) = sK5 ),
    inference(superposition,[status(thm)],[c_7682,c_4734])).

cnf(c_7834,plain,
    ( k1_funct_1(sK4(X0,X1),sK3(sK4(X0,X1),X1)) = X1
    | r2_hidden(X2,k1_relat_1(sK4(X0,X3))) != iProver_top
    | r2_hidden(k1_funct_1(sK4(X0,X3),X2),sK5) = iProver_top
    | v1_funct_1(sK4(X0,X3)) != iProver_top
    | v1_relat_1(sK4(X0,X3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7797,c_1283])).

cnf(c_7911,plain,
    ( k1_funct_1(sK4(X0,X1),sK3(sK4(X0,X1),X1)) = X1
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(k1_funct_1(sK4(X0,X3),X2),sK5) = iProver_top
    | v1_funct_1(sK4(X0,X3)) != iProver_top
    | v1_relat_1(sK4(X0,X3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7834,c_13])).

cnf(c_8366,plain,
    ( k1_funct_1(sK4(X0,X1),sK3(sK4(X0,X1),X1)) = X1
    | r2_hidden(X2,X0) != iProver_top
    | v1_funct_1(sK4(X0,X3)) != iProver_top
    | v1_relat_1(sK4(X0,X3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7911,c_4501])).

cnf(c_8615,plain,
    ( k1_funct_1(sK4(X0,X1),sK3(sK4(X0,X1),X1)) = X1
    | r2_hidden(X2,X0) != iProver_top
    | v1_relat_1(sK4(X0,X3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1279,c_8366])).

cnf(c_8623,plain,
    ( k1_funct_1(sK4(X0,X1),sK3(sK4(X0,X1),X1)) = X1
    | r2_hidden(X2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1278,c_8615])).

cnf(c_11426,plain,
    ( k1_funct_1(sK4(k1_xboole_0,X0),sK3(sK4(k1_xboole_0,X0),X0)) = X0 ),
    inference(superposition,[status(thm)],[c_11422,c_8623])).

cnf(c_11438,plain,
    ( k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_11426,c_1833])).

cnf(c_23541,plain,
    ( r2_hidden(X0,X1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_23274,c_11438])).

cnf(c_23546,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_23541,c_4501])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:24:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 7.91/1.51  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.91/1.51  
% 7.91/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.91/1.51  
% 7.91/1.51  ------  iProver source info
% 7.91/1.51  
% 7.91/1.51  git: date: 2020-06-30 10:37:57 +0100
% 7.91/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.91/1.51  git: non_committed_changes: false
% 7.91/1.51  git: last_make_outside_of_git: false
% 7.91/1.51  
% 7.91/1.51  ------ 
% 7.91/1.51  
% 7.91/1.51  ------ Input Options
% 7.91/1.51  
% 7.91/1.51  --out_options                           all
% 7.91/1.51  --tptp_safe_out                         true
% 7.91/1.51  --problem_path                          ""
% 7.91/1.51  --include_path                          ""
% 7.91/1.51  --clausifier                            res/vclausify_rel
% 7.91/1.51  --clausifier_options                    ""
% 7.91/1.51  --stdin                                 false
% 7.91/1.51  --stats_out                             all
% 7.91/1.51  
% 7.91/1.51  ------ General Options
% 7.91/1.51  
% 7.91/1.51  --fof                                   false
% 7.91/1.51  --time_out_real                         305.
% 7.91/1.51  --time_out_virtual                      -1.
% 7.91/1.51  --symbol_type_check                     false
% 7.91/1.51  --clausify_out                          false
% 7.91/1.51  --sig_cnt_out                           false
% 7.91/1.51  --trig_cnt_out                          false
% 7.91/1.51  --trig_cnt_out_tolerance                1.
% 7.91/1.51  --trig_cnt_out_sk_spl                   false
% 7.91/1.51  --abstr_cl_out                          false
% 7.91/1.51  
% 7.91/1.51  ------ Global Options
% 7.91/1.51  
% 7.91/1.51  --schedule                              default
% 7.91/1.51  --add_important_lit                     false
% 7.91/1.51  --prop_solver_per_cl                    1000
% 7.91/1.51  --min_unsat_core                        false
% 7.91/1.51  --soft_assumptions                      false
% 7.91/1.51  --soft_lemma_size                       3
% 7.91/1.51  --prop_impl_unit_size                   0
% 7.91/1.51  --prop_impl_unit                        []
% 7.91/1.51  --share_sel_clauses                     true
% 7.91/1.51  --reset_solvers                         false
% 7.91/1.51  --bc_imp_inh                            [conj_cone]
% 7.91/1.51  --conj_cone_tolerance                   3.
% 7.91/1.51  --extra_neg_conj                        none
% 7.91/1.51  --large_theory_mode                     true
% 7.91/1.51  --prolific_symb_bound                   200
% 7.91/1.51  --lt_threshold                          2000
% 7.91/1.51  --clause_weak_htbl                      true
% 7.91/1.51  --gc_record_bc_elim                     false
% 7.91/1.51  
% 7.91/1.51  ------ Preprocessing Options
% 7.91/1.51  
% 7.91/1.51  --preprocessing_flag                    true
% 7.91/1.51  --time_out_prep_mult                    0.1
% 7.91/1.51  --splitting_mode                        input
% 7.91/1.51  --splitting_grd                         true
% 7.91/1.51  --splitting_cvd                         false
% 7.91/1.51  --splitting_cvd_svl                     false
% 7.91/1.51  --splitting_nvd                         32
% 7.91/1.51  --sub_typing                            true
% 7.91/1.51  --prep_gs_sim                           true
% 7.91/1.51  --prep_unflatten                        true
% 7.91/1.51  --prep_res_sim                          true
% 7.91/1.51  --prep_upred                            true
% 7.91/1.51  --prep_sem_filter                       exhaustive
% 7.91/1.51  --prep_sem_filter_out                   false
% 7.91/1.51  --pred_elim                             true
% 7.91/1.51  --res_sim_input                         true
% 7.91/1.51  --eq_ax_congr_red                       true
% 7.91/1.51  --pure_diseq_elim                       true
% 7.91/1.51  --brand_transform                       false
% 7.91/1.51  --non_eq_to_eq                          false
% 7.91/1.51  --prep_def_merge                        true
% 7.91/1.51  --prep_def_merge_prop_impl              false
% 7.91/1.51  --prep_def_merge_mbd                    true
% 7.91/1.51  --prep_def_merge_tr_red                 false
% 7.91/1.51  --prep_def_merge_tr_cl                  false
% 7.91/1.51  --smt_preprocessing                     true
% 7.91/1.51  --smt_ac_axioms                         fast
% 7.91/1.51  --preprocessed_out                      false
% 7.91/1.51  --preprocessed_stats                    false
% 7.91/1.51  
% 7.91/1.51  ------ Abstraction refinement Options
% 7.91/1.51  
% 7.91/1.51  --abstr_ref                             []
% 7.91/1.51  --abstr_ref_prep                        false
% 7.91/1.51  --abstr_ref_until_sat                   false
% 7.91/1.51  --abstr_ref_sig_restrict                funpre
% 7.91/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.91/1.51  --abstr_ref_under                       []
% 7.91/1.51  
% 7.91/1.51  ------ SAT Options
% 7.91/1.51  
% 7.91/1.51  --sat_mode                              false
% 7.91/1.51  --sat_fm_restart_options                ""
% 7.91/1.51  --sat_gr_def                            false
% 7.91/1.51  --sat_epr_types                         true
% 7.91/1.51  --sat_non_cyclic_types                  false
% 7.91/1.51  --sat_finite_models                     false
% 7.91/1.51  --sat_fm_lemmas                         false
% 7.91/1.51  --sat_fm_prep                           false
% 7.91/1.51  --sat_fm_uc_incr                        true
% 7.91/1.51  --sat_out_model                         small
% 7.91/1.51  --sat_out_clauses                       false
% 7.91/1.51  
% 7.91/1.51  ------ QBF Options
% 7.91/1.51  
% 7.91/1.51  --qbf_mode                              false
% 7.91/1.51  --qbf_elim_univ                         false
% 7.91/1.51  --qbf_dom_inst                          none
% 7.91/1.51  --qbf_dom_pre_inst                      false
% 7.91/1.51  --qbf_sk_in                             false
% 7.91/1.51  --qbf_pred_elim                         true
% 7.91/1.51  --qbf_split                             512
% 7.91/1.51  
% 7.91/1.51  ------ BMC1 Options
% 7.91/1.51  
% 7.91/1.51  --bmc1_incremental                      false
% 7.91/1.51  --bmc1_axioms                           reachable_all
% 7.91/1.51  --bmc1_min_bound                        0
% 7.91/1.51  --bmc1_max_bound                        -1
% 7.91/1.51  --bmc1_max_bound_default                -1
% 7.91/1.51  --bmc1_symbol_reachability              true
% 7.91/1.51  --bmc1_property_lemmas                  false
% 7.91/1.51  --bmc1_k_induction                      false
% 7.91/1.51  --bmc1_non_equiv_states                 false
% 7.91/1.51  --bmc1_deadlock                         false
% 7.91/1.51  --bmc1_ucm                              false
% 7.91/1.51  --bmc1_add_unsat_core                   none
% 7.91/1.51  --bmc1_unsat_core_children              false
% 7.91/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.91/1.51  --bmc1_out_stat                         full
% 7.91/1.51  --bmc1_ground_init                      false
% 7.91/1.51  --bmc1_pre_inst_next_state              false
% 7.91/1.51  --bmc1_pre_inst_state                   false
% 7.91/1.51  --bmc1_pre_inst_reach_state             false
% 7.91/1.51  --bmc1_out_unsat_core                   false
% 7.91/1.51  --bmc1_aig_witness_out                  false
% 7.91/1.51  --bmc1_verbose                          false
% 7.91/1.51  --bmc1_dump_clauses_tptp                false
% 7.91/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.91/1.51  --bmc1_dump_file                        -
% 7.91/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.91/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.91/1.51  --bmc1_ucm_extend_mode                  1
% 7.91/1.51  --bmc1_ucm_init_mode                    2
% 7.91/1.51  --bmc1_ucm_cone_mode                    none
% 7.91/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.91/1.51  --bmc1_ucm_relax_model                  4
% 7.91/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.91/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.91/1.51  --bmc1_ucm_layered_model                none
% 7.91/1.51  --bmc1_ucm_max_lemma_size               10
% 7.91/1.51  
% 7.91/1.51  ------ AIG Options
% 7.91/1.51  
% 7.91/1.51  --aig_mode                              false
% 7.91/1.51  
% 7.91/1.51  ------ Instantiation Options
% 7.91/1.51  
% 7.91/1.51  --instantiation_flag                    true
% 7.91/1.51  --inst_sos_flag                         true
% 7.91/1.51  --inst_sos_phase                        true
% 7.91/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.91/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.91/1.51  --inst_lit_sel_side                     num_symb
% 7.91/1.51  --inst_solver_per_active                1400
% 7.91/1.51  --inst_solver_calls_frac                1.
% 7.91/1.51  --inst_passive_queue_type               priority_queues
% 7.91/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.91/1.51  --inst_passive_queues_freq              [25;2]
% 7.91/1.51  --inst_dismatching                      true
% 7.91/1.51  --inst_eager_unprocessed_to_passive     true
% 7.91/1.51  --inst_prop_sim_given                   true
% 7.91/1.51  --inst_prop_sim_new                     false
% 7.91/1.51  --inst_subs_new                         false
% 7.91/1.51  --inst_eq_res_simp                      false
% 7.91/1.51  --inst_subs_given                       false
% 7.91/1.51  --inst_orphan_elimination               true
% 7.91/1.51  --inst_learning_loop_flag               true
% 7.91/1.51  --inst_learning_start                   3000
% 7.91/1.51  --inst_learning_factor                  2
% 7.91/1.51  --inst_start_prop_sim_after_learn       3
% 7.91/1.51  --inst_sel_renew                        solver
% 7.91/1.51  --inst_lit_activity_flag                true
% 7.91/1.51  --inst_restr_to_given                   false
% 7.91/1.51  --inst_activity_threshold               500
% 7.91/1.51  --inst_out_proof                        true
% 7.91/1.51  
% 7.91/1.51  ------ Resolution Options
% 7.91/1.51  
% 7.91/1.51  --resolution_flag                       true
% 7.91/1.51  --res_lit_sel                           adaptive
% 7.91/1.51  --res_lit_sel_side                      none
% 7.91/1.51  --res_ordering                          kbo
% 7.91/1.51  --res_to_prop_solver                    active
% 7.91/1.51  --res_prop_simpl_new                    false
% 7.91/1.51  --res_prop_simpl_given                  true
% 7.91/1.51  --res_passive_queue_type                priority_queues
% 7.91/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.91/1.51  --res_passive_queues_freq               [15;5]
% 7.91/1.51  --res_forward_subs                      full
% 7.91/1.51  --res_backward_subs                     full
% 7.91/1.51  --res_forward_subs_resolution           true
% 7.91/1.51  --res_backward_subs_resolution          true
% 7.91/1.51  --res_orphan_elimination                true
% 7.91/1.51  --res_time_limit                        2.
% 7.91/1.51  --res_out_proof                         true
% 7.91/1.51  
% 7.91/1.51  ------ Superposition Options
% 7.91/1.51  
% 7.91/1.51  --superposition_flag                    true
% 7.91/1.51  --sup_passive_queue_type                priority_queues
% 7.91/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.91/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.91/1.51  --demod_completeness_check              fast
% 7.91/1.51  --demod_use_ground                      true
% 7.91/1.51  --sup_to_prop_solver                    passive
% 7.91/1.51  --sup_prop_simpl_new                    true
% 7.91/1.51  --sup_prop_simpl_given                  true
% 7.91/1.51  --sup_fun_splitting                     true
% 7.91/1.51  --sup_smt_interval                      50000
% 7.91/1.51  
% 7.91/1.51  ------ Superposition Simplification Setup
% 7.91/1.51  
% 7.91/1.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.91/1.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.91/1.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.91/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.91/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.91/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.91/1.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.91/1.51  --sup_immed_triv                        [TrivRules]
% 7.91/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.91/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.91/1.51  --sup_immed_bw_main                     []
% 7.91/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.91/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.91/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.91/1.51  --sup_input_bw                          []
% 7.91/1.51  
% 7.91/1.51  ------ Combination Options
% 7.91/1.51  
% 7.91/1.51  --comb_res_mult                         3
% 7.91/1.51  --comb_sup_mult                         2
% 7.91/1.51  --comb_inst_mult                        10
% 7.91/1.51  
% 7.91/1.51  ------ Debug Options
% 7.91/1.51  
% 7.91/1.51  --dbg_backtrace                         false
% 7.91/1.51  --dbg_dump_prop_clauses                 false
% 7.91/1.51  --dbg_dump_prop_clauses_file            -
% 7.91/1.51  --dbg_out_stat                          false
% 7.91/1.51  ------ Parsing...
% 7.91/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.91/1.51  
% 7.91/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.91/1.51  
% 7.91/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.91/1.51  
% 7.91/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.91/1.51  ------ Proving...
% 7.91/1.51  ------ Problem Properties 
% 7.91/1.51  
% 7.91/1.51  
% 7.91/1.51  clauses                                 17
% 7.91/1.51  conjectures                             1
% 7.91/1.51  EPR                                     1
% 7.91/1.51  Horn                                    15
% 7.91/1.51  unary                                   3
% 7.91/1.51  binary                                  2
% 7.91/1.51  lits                                    55
% 7.91/1.51  lits eq                                 20
% 7.91/1.51  fd_pure                                 0
% 7.91/1.51  fd_pseudo                               0
% 7.91/1.51  fd_cond                                 2
% 7.91/1.51  fd_pseudo_cond                          3
% 7.91/1.51  AC symbols                              0
% 7.91/1.51  
% 7.91/1.51  ------ Schedule dynamic 5 is on 
% 7.91/1.51  
% 7.91/1.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.91/1.51  
% 7.91/1.51  
% 7.91/1.51  ------ 
% 7.91/1.51  Current options:
% 7.91/1.51  ------ 
% 7.91/1.51  
% 7.91/1.51  ------ Input Options
% 7.91/1.51  
% 7.91/1.51  --out_options                           all
% 7.91/1.51  --tptp_safe_out                         true
% 7.91/1.51  --problem_path                          ""
% 7.91/1.51  --include_path                          ""
% 7.91/1.51  --clausifier                            res/vclausify_rel
% 7.91/1.51  --clausifier_options                    ""
% 7.91/1.51  --stdin                                 false
% 7.91/1.51  --stats_out                             all
% 7.91/1.51  
% 7.91/1.51  ------ General Options
% 7.91/1.51  
% 7.91/1.51  --fof                                   false
% 7.91/1.51  --time_out_real                         305.
% 7.91/1.51  --time_out_virtual                      -1.
% 7.91/1.51  --symbol_type_check                     false
% 7.91/1.51  --clausify_out                          false
% 7.91/1.51  --sig_cnt_out                           false
% 7.91/1.51  --trig_cnt_out                          false
% 7.91/1.51  --trig_cnt_out_tolerance                1.
% 7.91/1.51  --trig_cnt_out_sk_spl                   false
% 7.91/1.51  --abstr_cl_out                          false
% 7.91/1.51  
% 7.91/1.51  ------ Global Options
% 7.91/1.51  
% 7.91/1.51  --schedule                              default
% 7.91/1.51  --add_important_lit                     false
% 7.91/1.51  --prop_solver_per_cl                    1000
% 7.91/1.51  --min_unsat_core                        false
% 7.91/1.51  --soft_assumptions                      false
% 7.91/1.51  --soft_lemma_size                       3
% 7.91/1.51  --prop_impl_unit_size                   0
% 7.91/1.51  --prop_impl_unit                        []
% 7.91/1.51  --share_sel_clauses                     true
% 7.91/1.51  --reset_solvers                         false
% 7.91/1.51  --bc_imp_inh                            [conj_cone]
% 7.91/1.51  --conj_cone_tolerance                   3.
% 7.91/1.51  --extra_neg_conj                        none
% 7.91/1.51  --large_theory_mode                     true
% 7.91/1.51  --prolific_symb_bound                   200
% 7.91/1.51  --lt_threshold                          2000
% 7.91/1.51  --clause_weak_htbl                      true
% 7.91/1.51  --gc_record_bc_elim                     false
% 7.91/1.51  
% 7.91/1.51  ------ Preprocessing Options
% 7.91/1.51  
% 7.91/1.51  --preprocessing_flag                    true
% 7.91/1.51  --time_out_prep_mult                    0.1
% 7.91/1.51  --splitting_mode                        input
% 7.91/1.51  --splitting_grd                         true
% 7.91/1.51  --splitting_cvd                         false
% 7.91/1.51  --splitting_cvd_svl                     false
% 7.91/1.51  --splitting_nvd                         32
% 7.91/1.51  --sub_typing                            true
% 7.91/1.51  --prep_gs_sim                           true
% 7.91/1.51  --prep_unflatten                        true
% 7.91/1.51  --prep_res_sim                          true
% 7.91/1.51  --prep_upred                            true
% 7.91/1.51  --prep_sem_filter                       exhaustive
% 7.91/1.51  --prep_sem_filter_out                   false
% 7.91/1.51  --pred_elim                             true
% 7.91/1.51  --res_sim_input                         true
% 7.91/1.51  --eq_ax_congr_red                       true
% 7.91/1.51  --pure_diseq_elim                       true
% 7.91/1.51  --brand_transform                       false
% 7.91/1.51  --non_eq_to_eq                          false
% 7.91/1.51  --prep_def_merge                        true
% 7.91/1.51  --prep_def_merge_prop_impl              false
% 7.91/1.51  --prep_def_merge_mbd                    true
% 7.91/1.51  --prep_def_merge_tr_red                 false
% 7.91/1.51  --prep_def_merge_tr_cl                  false
% 7.91/1.51  --smt_preprocessing                     true
% 7.91/1.51  --smt_ac_axioms                         fast
% 7.91/1.51  --preprocessed_out                      false
% 7.91/1.51  --preprocessed_stats                    false
% 7.91/1.51  
% 7.91/1.51  ------ Abstraction refinement Options
% 7.91/1.51  
% 7.91/1.51  --abstr_ref                             []
% 7.91/1.51  --abstr_ref_prep                        false
% 7.91/1.51  --abstr_ref_until_sat                   false
% 7.91/1.51  --abstr_ref_sig_restrict                funpre
% 7.91/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.91/1.51  --abstr_ref_under                       []
% 7.91/1.51  
% 7.91/1.51  ------ SAT Options
% 7.91/1.51  
% 7.91/1.51  --sat_mode                              false
% 7.91/1.51  --sat_fm_restart_options                ""
% 7.91/1.51  --sat_gr_def                            false
% 7.91/1.51  --sat_epr_types                         true
% 7.91/1.51  --sat_non_cyclic_types                  false
% 7.91/1.51  --sat_finite_models                     false
% 7.91/1.51  --sat_fm_lemmas                         false
% 7.91/1.51  --sat_fm_prep                           false
% 7.91/1.51  --sat_fm_uc_incr                        true
% 7.91/1.51  --sat_out_model                         small
% 7.91/1.51  --sat_out_clauses                       false
% 7.91/1.51  
% 7.91/1.51  ------ QBF Options
% 7.91/1.51  
% 7.91/1.51  --qbf_mode                              false
% 7.91/1.51  --qbf_elim_univ                         false
% 7.91/1.51  --qbf_dom_inst                          none
% 7.91/1.51  --qbf_dom_pre_inst                      false
% 7.91/1.51  --qbf_sk_in                             false
% 7.91/1.51  --qbf_pred_elim                         true
% 7.91/1.51  --qbf_split                             512
% 7.91/1.51  
% 7.91/1.51  ------ BMC1 Options
% 7.91/1.51  
% 7.91/1.51  --bmc1_incremental                      false
% 7.91/1.51  --bmc1_axioms                           reachable_all
% 7.91/1.51  --bmc1_min_bound                        0
% 7.91/1.51  --bmc1_max_bound                        -1
% 7.91/1.51  --bmc1_max_bound_default                -1
% 7.91/1.51  --bmc1_symbol_reachability              true
% 7.91/1.51  --bmc1_property_lemmas                  false
% 7.91/1.51  --bmc1_k_induction                      false
% 7.91/1.51  --bmc1_non_equiv_states                 false
% 7.91/1.51  --bmc1_deadlock                         false
% 7.91/1.51  --bmc1_ucm                              false
% 7.91/1.51  --bmc1_add_unsat_core                   none
% 7.91/1.51  --bmc1_unsat_core_children              false
% 7.91/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.91/1.51  --bmc1_out_stat                         full
% 7.91/1.51  --bmc1_ground_init                      false
% 7.91/1.51  --bmc1_pre_inst_next_state              false
% 7.91/1.51  --bmc1_pre_inst_state                   false
% 7.91/1.51  --bmc1_pre_inst_reach_state             false
% 7.91/1.51  --bmc1_out_unsat_core                   false
% 7.91/1.51  --bmc1_aig_witness_out                  false
% 7.91/1.51  --bmc1_verbose                          false
% 7.91/1.51  --bmc1_dump_clauses_tptp                false
% 7.91/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.91/1.51  --bmc1_dump_file                        -
% 7.91/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.91/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.91/1.51  --bmc1_ucm_extend_mode                  1
% 7.91/1.51  --bmc1_ucm_init_mode                    2
% 7.91/1.51  --bmc1_ucm_cone_mode                    none
% 7.91/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.91/1.51  --bmc1_ucm_relax_model                  4
% 7.91/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.91/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.91/1.51  --bmc1_ucm_layered_model                none
% 7.91/1.51  --bmc1_ucm_max_lemma_size               10
% 7.91/1.51  
% 7.91/1.51  ------ AIG Options
% 7.91/1.51  
% 7.91/1.51  --aig_mode                              false
% 7.91/1.51  
% 7.91/1.51  ------ Instantiation Options
% 7.91/1.51  
% 7.91/1.51  --instantiation_flag                    true
% 7.91/1.51  --inst_sos_flag                         true
% 7.91/1.51  --inst_sos_phase                        true
% 7.91/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.91/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.91/1.51  --inst_lit_sel_side                     none
% 7.91/1.51  --inst_solver_per_active                1400
% 7.91/1.51  --inst_solver_calls_frac                1.
% 7.91/1.51  --inst_passive_queue_type               priority_queues
% 7.91/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.91/1.51  --inst_passive_queues_freq              [25;2]
% 7.91/1.51  --inst_dismatching                      true
% 7.91/1.51  --inst_eager_unprocessed_to_passive     true
% 7.91/1.51  --inst_prop_sim_given                   true
% 7.91/1.51  --inst_prop_sim_new                     false
% 7.91/1.51  --inst_subs_new                         false
% 7.91/1.51  --inst_eq_res_simp                      false
% 7.91/1.51  --inst_subs_given                       false
% 7.91/1.51  --inst_orphan_elimination               true
% 7.91/1.51  --inst_learning_loop_flag               true
% 7.91/1.51  --inst_learning_start                   3000
% 7.91/1.51  --inst_learning_factor                  2
% 7.91/1.51  --inst_start_prop_sim_after_learn       3
% 7.91/1.51  --inst_sel_renew                        solver
% 7.91/1.51  --inst_lit_activity_flag                true
% 7.91/1.51  --inst_restr_to_given                   false
% 7.91/1.51  --inst_activity_threshold               500
% 7.91/1.51  --inst_out_proof                        true
% 7.91/1.51  
% 7.91/1.51  ------ Resolution Options
% 7.91/1.51  
% 7.91/1.51  --resolution_flag                       false
% 7.91/1.51  --res_lit_sel                           adaptive
% 7.91/1.51  --res_lit_sel_side                      none
% 7.91/1.51  --res_ordering                          kbo
% 7.91/1.51  --res_to_prop_solver                    active
% 7.91/1.51  --res_prop_simpl_new                    false
% 7.91/1.51  --res_prop_simpl_given                  true
% 7.91/1.51  --res_passive_queue_type                priority_queues
% 7.91/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.91/1.51  --res_passive_queues_freq               [15;5]
% 7.91/1.51  --res_forward_subs                      full
% 7.91/1.51  --res_backward_subs                     full
% 7.91/1.51  --res_forward_subs_resolution           true
% 7.91/1.51  --res_backward_subs_resolution          true
% 7.91/1.51  --res_orphan_elimination                true
% 7.91/1.51  --res_time_limit                        2.
% 7.91/1.51  --res_out_proof                         true
% 7.91/1.51  
% 7.91/1.51  ------ Superposition Options
% 7.91/1.51  
% 7.91/1.51  --superposition_flag                    true
% 7.91/1.51  --sup_passive_queue_type                priority_queues
% 7.91/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.91/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.91/1.51  --demod_completeness_check              fast
% 7.91/1.51  --demod_use_ground                      true
% 7.91/1.51  --sup_to_prop_solver                    passive
% 7.91/1.51  --sup_prop_simpl_new                    true
% 7.91/1.51  --sup_prop_simpl_given                  true
% 7.91/1.51  --sup_fun_splitting                     true
% 7.91/1.51  --sup_smt_interval                      50000
% 7.91/1.51  
% 7.91/1.51  ------ Superposition Simplification Setup
% 7.91/1.51  
% 7.91/1.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.91/1.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.91/1.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.91/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.91/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.91/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.91/1.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.91/1.51  --sup_immed_triv                        [TrivRules]
% 7.91/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.91/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.91/1.51  --sup_immed_bw_main                     []
% 7.91/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.91/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.91/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.91/1.51  --sup_input_bw                          []
% 7.91/1.51  
% 7.91/1.51  ------ Combination Options
% 7.91/1.51  
% 7.91/1.51  --comb_res_mult                         3
% 7.91/1.51  --comb_sup_mult                         2
% 7.91/1.51  --comb_inst_mult                        10
% 7.91/1.51  
% 7.91/1.51  ------ Debug Options
% 7.91/1.51  
% 7.91/1.51  --dbg_backtrace                         false
% 7.91/1.51  --dbg_dump_prop_clauses                 false
% 7.91/1.51  --dbg_dump_prop_clauses_file            -
% 7.91/1.51  --dbg_out_stat                          false
% 7.91/1.51  
% 7.91/1.51  
% 7.91/1.51  
% 7.91/1.51  
% 7.91/1.51  ------ Proving...
% 7.91/1.51  
% 7.91/1.51  
% 7.91/1.51  % SZS status Theorem for theBenchmark.p
% 7.91/1.51  
% 7.91/1.51   Resolution empty clause
% 7.91/1.51  
% 7.91/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 7.91/1.51  
% 7.91/1.51  fof(f5,axiom,(
% 7.91/1.51    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 7.91/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.91/1.51  
% 7.91/1.51  fof(f15,plain,(
% 7.91/1.51    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 7.91/1.51    inference(ennf_transformation,[],[f5])).
% 7.91/1.51  
% 7.91/1.51  fof(f27,plain,(
% 7.91/1.51    ! [X1,X0] : (? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (! [X3] : (k1_funct_1(sK4(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK4(X0,X1)) = X0 & v1_funct_1(sK4(X0,X1)) & v1_relat_1(sK4(X0,X1))))),
% 7.91/1.51    introduced(choice_axiom,[])).
% 7.91/1.51  
% 7.91/1.51  fof(f28,plain,(
% 7.91/1.51    ! [X0,X1] : (! [X3] : (k1_funct_1(sK4(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK4(X0,X1)) = X0 & v1_funct_1(sK4(X0,X1)) & v1_relat_1(sK4(X0,X1)))),
% 7.91/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f15,f27])).
% 7.91/1.51  
% 7.91/1.51  fof(f45,plain,(
% 7.91/1.51    ( ! [X0,X1] : (k1_relat_1(sK4(X0,X1)) = X0) )),
% 7.91/1.51    inference(cnf_transformation,[],[f28])).
% 7.91/1.51  
% 7.91/1.51  fof(f2,axiom,(
% 7.91/1.51    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_relat_1(X0) = k1_xboole_0) => k1_xboole_0 = X0))),
% 7.91/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.91/1.51  
% 7.91/1.51  fof(f10,plain,(
% 7.91/1.51    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_relat_1(X0) != k1_xboole_0)) | ~v1_relat_1(X0))),
% 7.91/1.51    inference(ennf_transformation,[],[f2])).
% 7.91/1.51  
% 7.91/1.51  fof(f11,plain,(
% 7.91/1.51    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_relat_1(X0) != k1_xboole_0) | ~v1_relat_1(X0))),
% 7.91/1.51    inference(flattening,[],[f10])).
% 7.91/1.51  
% 7.91/1.51  fof(f33,plain,(
% 7.91/1.51    ( ! [X0] : (k1_xboole_0 = X0 | k1_relat_1(X0) != k1_xboole_0 | ~v1_relat_1(X0)) )),
% 7.91/1.51    inference(cnf_transformation,[],[f11])).
% 7.91/1.51  
% 7.91/1.51  fof(f43,plain,(
% 7.91/1.51    ( ! [X0,X1] : (v1_relat_1(sK4(X0,X1))) )),
% 7.91/1.51    inference(cnf_transformation,[],[f28])).
% 7.91/1.51  
% 7.91/1.51  fof(f4,axiom,(
% 7.91/1.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 7.91/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.91/1.51  
% 7.91/1.51  fof(f13,plain,(
% 7.91/1.51    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.91/1.51    inference(ennf_transformation,[],[f4])).
% 7.91/1.51  
% 7.91/1.51  fof(f14,plain,(
% 7.91/1.51    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.91/1.51    inference(flattening,[],[f13])).
% 7.91/1.51  
% 7.91/1.51  fof(f21,plain,(
% 7.91/1.51    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.91/1.51    inference(nnf_transformation,[],[f14])).
% 7.91/1.51  
% 7.91/1.51  fof(f22,plain,(
% 7.91/1.51    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.91/1.51    inference(rectify,[],[f21])).
% 7.91/1.51  
% 7.91/1.51  fof(f25,plain,(
% 7.91/1.51    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))))),
% 7.91/1.51    introduced(choice_axiom,[])).
% 7.91/1.51  
% 7.91/1.51  fof(f24,plain,(
% 7.91/1.51    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X1)) = X2 & r2_hidden(sK2(X0,X1),k1_relat_1(X0))))) )),
% 7.91/1.51    introduced(choice_axiom,[])).
% 7.91/1.51  
% 7.91/1.51  fof(f23,plain,(
% 7.91/1.51    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK1(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1))))),
% 7.91/1.51    introduced(choice_axiom,[])).
% 7.91/1.51  
% 7.91/1.51  fof(f26,plain,(
% 7.91/1.51    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & ((k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.91/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f22,f25,f24,f23])).
% 7.91/1.51  
% 7.91/1.51  fof(f37,plain,(
% 7.91/1.51    ( ! [X0,X5,X1] : (r2_hidden(sK3(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.91/1.51    inference(cnf_transformation,[],[f26])).
% 7.91/1.51  
% 7.91/1.51  fof(f52,plain,(
% 7.91/1.51    ( ! [X0,X5] : (r2_hidden(sK3(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.91/1.51    inference(equality_resolution,[],[f37])).
% 7.91/1.51  
% 7.91/1.51  fof(f44,plain,(
% 7.91/1.51    ( ! [X0,X1] : (v1_funct_1(sK4(X0,X1))) )),
% 7.91/1.51    inference(cnf_transformation,[],[f28])).
% 7.91/1.51  
% 7.91/1.51  fof(f3,axiom,(
% 7.91/1.51    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k1_xboole_0 <=> k1_xboole_0 = k2_relat_1(X0)))),
% 7.91/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.91/1.51  
% 7.91/1.51  fof(f12,plain,(
% 7.91/1.51    ! [X0] : ((k1_relat_1(X0) = k1_xboole_0 <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 7.91/1.51    inference(ennf_transformation,[],[f3])).
% 7.91/1.51  
% 7.91/1.51  fof(f20,plain,(
% 7.91/1.51    ! [X0] : (((k1_relat_1(X0) = k1_xboole_0 | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_relat_1(X0) != k1_xboole_0)) | ~v1_relat_1(X0))),
% 7.91/1.51    inference(nnf_transformation,[],[f12])).
% 7.91/1.51  
% 7.91/1.51  fof(f35,plain,(
% 7.91/1.51    ( ! [X0] : (k1_xboole_0 = k2_relat_1(X0) | k1_relat_1(X0) != k1_xboole_0 | ~v1_relat_1(X0)) )),
% 7.91/1.51    inference(cnf_transformation,[],[f20])).
% 7.91/1.51  
% 7.91/1.51  fof(f46,plain,(
% 7.91/1.51    ( ! [X0,X3,X1] : (k1_funct_1(sK4(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) )),
% 7.91/1.51    inference(cnf_transformation,[],[f28])).
% 7.91/1.51  
% 7.91/1.51  fof(f40,plain,(
% 7.91/1.51    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | r2_hidden(sK2(X0,X1),k1_relat_1(X0)) | r2_hidden(sK1(X0,X1),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.91/1.51    inference(cnf_transformation,[],[f26])).
% 7.91/1.51  
% 7.91/1.51  fof(f1,axiom,(
% 7.91/1.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.91/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.91/1.51  
% 7.91/1.51  fof(f8,plain,(
% 7.91/1.51    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 7.91/1.51    inference(unused_predicate_definition_removal,[],[f1])).
% 7.91/1.51  
% 7.91/1.51  fof(f9,plain,(
% 7.91/1.51    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 7.91/1.51    inference(ennf_transformation,[],[f8])).
% 7.91/1.51  
% 7.91/1.51  fof(f18,plain,(
% 7.91/1.51    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.91/1.51    introduced(choice_axiom,[])).
% 7.91/1.51  
% 7.91/1.51  fof(f19,plain,(
% 7.91/1.51    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.91/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f18])).
% 7.91/1.51  
% 7.91/1.51  fof(f31,plain,(
% 7.91/1.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 7.91/1.51    inference(cnf_transformation,[],[f19])).
% 7.91/1.51  
% 7.91/1.51  fof(f6,conjecture,(
% 7.91/1.51    ! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 7.91/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.91/1.51  
% 7.91/1.51  fof(f7,negated_conjecture,(
% 7.91/1.51    ~! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 7.91/1.51    inference(negated_conjecture,[],[f6])).
% 7.91/1.51  
% 7.91/1.51  fof(f16,plain,(
% 7.91/1.51    ? [X0,X1] : (! [X2] : ((~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 7.91/1.51    inference(ennf_transformation,[],[f7])).
% 7.91/1.51  
% 7.91/1.51  fof(f17,plain,(
% 7.91/1.51    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 7.91/1.51    inference(flattening,[],[f16])).
% 7.91/1.51  
% 7.91/1.51  fof(f29,plain,(
% 7.91/1.51    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0)) => (! [X2] : (~r1_tarski(k2_relat_1(X2),sK5) | k1_relat_1(X2) != sK6 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = sK6 | k1_xboole_0 != sK5))),
% 7.91/1.51    introduced(choice_axiom,[])).
% 7.91/1.51  
% 7.91/1.51  fof(f30,plain,(
% 7.91/1.51    ! [X2] : (~r1_tarski(k2_relat_1(X2),sK5) | k1_relat_1(X2) != sK6 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = sK6 | k1_xboole_0 != sK5)),
% 7.91/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f17,f29])).
% 7.91/1.51  
% 7.91/1.51  fof(f48,plain,(
% 7.91/1.51    ( ! [X2] : (~r1_tarski(k2_relat_1(X2),sK5) | k1_relat_1(X2) != sK6 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 7.91/1.51    inference(cnf_transformation,[],[f30])).
% 7.91/1.51  
% 7.91/1.51  fof(f38,plain,(
% 7.91/1.51    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK3(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.91/1.51    inference(cnf_transformation,[],[f26])).
% 7.91/1.51  
% 7.91/1.51  fof(f51,plain,(
% 7.91/1.51    ( ! [X0,X5] : (k1_funct_1(X0,sK3(X0,X5)) = X5 | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.91/1.51    inference(equality_resolution,[],[f38])).
% 7.91/1.51  
% 7.91/1.51  fof(f32,plain,(
% 7.91/1.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 7.91/1.51    inference(cnf_transformation,[],[f19])).
% 7.91/1.51  
% 7.91/1.51  fof(f39,plain,(
% 7.91/1.51    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.91/1.51    inference(cnf_transformation,[],[f26])).
% 7.91/1.51  
% 7.91/1.51  fof(f49,plain,(
% 7.91/1.51    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.91/1.51    inference(equality_resolution,[],[f39])).
% 7.91/1.51  
% 7.91/1.51  fof(f50,plain,(
% 7.91/1.51    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.91/1.51    inference(equality_resolution,[],[f49])).
% 7.91/1.51  
% 7.91/1.51  fof(f34,plain,(
% 7.91/1.51    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 7.91/1.51    inference(cnf_transformation,[],[f11])).
% 7.91/1.51  
% 7.91/1.51  fof(f47,plain,(
% 7.91/1.51    k1_xboole_0 = sK6 | k1_xboole_0 != sK5),
% 7.91/1.51    inference(cnf_transformation,[],[f30])).
% 7.91/1.51  
% 7.91/1.51  cnf(c_13,plain,
% 7.91/1.51      ( k1_relat_1(sK4(X0,X1)) = X0 ),
% 7.91/1.51      inference(cnf_transformation,[],[f45]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_3,plain,
% 7.91/1.51      ( ~ v1_relat_1(X0) | k1_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = X0 ),
% 7.91/1.51      inference(cnf_transformation,[],[f33]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_1289,plain,
% 7.91/1.51      ( k1_relat_1(X0) != k1_xboole_0
% 7.91/1.51      | k1_xboole_0 = X0
% 7.91/1.51      | v1_relat_1(X0) != iProver_top ),
% 7.91/1.51      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_1573,plain,
% 7.91/1.51      ( sK4(X0,X1) = k1_xboole_0
% 7.91/1.51      | k1_xboole_0 != X0
% 7.91/1.51      | v1_relat_1(sK4(X0,X1)) != iProver_top ),
% 7.91/1.51      inference(superposition,[status(thm)],[c_13,c_1289]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_15,plain,
% 7.91/1.51      ( v1_relat_1(sK4(X0,X1)) ),
% 7.91/1.51      inference(cnf_transformation,[],[f43]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_21,plain,
% 7.91/1.51      ( v1_relat_1(sK4(X0,X1)) = iProver_top ),
% 7.91/1.51      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_1830,plain,
% 7.91/1.51      ( k1_xboole_0 != X0 | sK4(X0,X1) = k1_xboole_0 ),
% 7.91/1.51      inference(global_propositional_subsumption,[status(thm)],[c_1573,c_21]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_1831,plain,
% 7.91/1.51      ( sK4(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0 ),
% 7.91/1.51      inference(renaming,[status(thm)],[c_1830]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_1833,plain,
% 7.91/1.51      ( sK4(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.91/1.51      inference(equality_resolution,[status(thm)],[c_1831]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_1837,plain,
% 7.91/1.51      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.91/1.51      inference(superposition,[status(thm)],[c_1833,c_13]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_11,plain,
% 7.91/1.51      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 7.91/1.51      | r2_hidden(sK3(X1,X0),k1_relat_1(X1))
% 7.91/1.51      | ~ v1_funct_1(X1)
% 7.91/1.51      | ~ v1_relat_1(X1) ),
% 7.91/1.51      inference(cnf_transformation,[],[f52]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_1281,plain,
% 7.91/1.51      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 7.91/1.51      | r2_hidden(sK3(X1,X0),k1_relat_1(X1)) = iProver_top
% 7.91/1.51      | v1_funct_1(X1) != iProver_top
% 7.91/1.51      | v1_relat_1(X1) != iProver_top ),
% 7.91/1.51      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_1932,plain,
% 7.91/1.51      ( r2_hidden(X0,k2_relat_1(k1_xboole_0)) != iProver_top
% 7.91/1.51      | r2_hidden(sK3(k1_xboole_0,X0),k1_xboole_0) = iProver_top
% 7.91/1.51      | v1_funct_1(k1_xboole_0) != iProver_top
% 7.91/1.51      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.91/1.51      inference(superposition,[status(thm)],[c_1837,c_1281]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_23,plain,
% 7.91/1.51      ( v1_relat_1(sK4(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 7.91/1.51      inference(instantiation,[status(thm)],[c_21]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_14,plain,
% 7.91/1.51      ( v1_funct_1(sK4(X0,X1)) ),
% 7.91/1.51      inference(cnf_transformation,[],[f44]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_24,plain,
% 7.91/1.51      ( v1_funct_1(sK4(X0,X1)) = iProver_top ),
% 7.91/1.51      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_26,plain,
% 7.91/1.51      ( v1_funct_1(sK4(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 7.91/1.51      inference(instantiation,[status(thm)],[c_24]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_27,plain,
% 7.91/1.51      ( k1_relat_1(sK4(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
% 7.91/1.51      inference(instantiation,[status(thm)],[c_13]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_488,plain,
% 7.91/1.51      ( sK4(X0,X1) != X2 | k1_relat_1(X2) != k1_xboole_0 | k1_xboole_0 = X2 ),
% 7.91/1.51      inference(resolution_lifted,[status(thm)],[c_3,c_15]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_489,plain,
% 7.91/1.51      ( k1_relat_1(sK4(X0,X1)) != k1_xboole_0 | k1_xboole_0 = sK4(X0,X1) ),
% 7.91/1.51      inference(unflattening,[status(thm)],[c_488]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_490,plain,
% 7.91/1.51      ( k1_relat_1(sK4(k1_xboole_0,k1_xboole_0)) != k1_xboole_0
% 7.91/1.51      | k1_xboole_0 = sK4(k1_xboole_0,k1_xboole_0) ),
% 7.91/1.51      inference(instantiation,[status(thm)],[c_489]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_1032,plain,
% 7.91/1.51      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 7.91/1.51      theory(equality) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_1343,plain,
% 7.91/1.51      ( v1_funct_1(X0) | ~ v1_funct_1(sK4(X1,X2)) | X0 != sK4(X1,X2) ),
% 7.91/1.51      inference(instantiation,[status(thm)],[c_1032]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_1344,plain,
% 7.91/1.51      ( X0 != sK4(X1,X2)
% 7.91/1.51      | v1_funct_1(X0) = iProver_top
% 7.91/1.51      | v1_funct_1(sK4(X1,X2)) != iProver_top ),
% 7.91/1.51      inference(predicate_to_equality,[status(thm)],[c_1343]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_1346,plain,
% 7.91/1.51      ( k1_xboole_0 != sK4(k1_xboole_0,k1_xboole_0)
% 7.91/1.51      | v1_funct_1(sK4(k1_xboole_0,k1_xboole_0)) != iProver_top
% 7.91/1.51      | v1_funct_1(k1_xboole_0) = iProver_top ),
% 7.91/1.51      inference(instantiation,[status(thm)],[c_1344]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_1029,plain,
% 7.91/1.51      ( ~ v1_relat_1(X0) | v1_relat_1(X1) | X1 != X0 ),
% 7.91/1.51      theory(equality) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_1379,plain,
% 7.91/1.51      ( v1_relat_1(X0) | ~ v1_relat_1(sK4(X1,X2)) | X0 != sK4(X1,X2) ),
% 7.91/1.51      inference(instantiation,[status(thm)],[c_1029]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_1380,plain,
% 7.91/1.51      ( X0 != sK4(X1,X2)
% 7.91/1.51      | v1_relat_1(X0) = iProver_top
% 7.91/1.51      | v1_relat_1(sK4(X1,X2)) != iProver_top ),
% 7.91/1.51      inference(predicate_to_equality,[status(thm)],[c_1379]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_1382,plain,
% 7.91/1.51      ( k1_xboole_0 != sK4(k1_xboole_0,k1_xboole_0)
% 7.91/1.51      | v1_relat_1(sK4(k1_xboole_0,k1_xboole_0)) != iProver_top
% 7.91/1.51      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 7.91/1.51      inference(instantiation,[status(thm)],[c_1380]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_3310,plain,
% 7.91/1.51      ( r2_hidden(X0,k2_relat_1(k1_xboole_0)) != iProver_top
% 7.91/1.51      | r2_hidden(sK3(k1_xboole_0,X0),k1_xboole_0) = iProver_top ),
% 7.91/1.51      inference(global_propositional_subsumption,
% 7.91/1.51                [status(thm)],
% 7.91/1.51                [c_1932,c_23,c_26,c_27,c_490,c_1346,c_1382]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_5,plain,
% 7.91/1.51      ( ~ v1_relat_1(X0)
% 7.91/1.51      | k1_relat_1(X0) != k1_xboole_0
% 7.91/1.51      | k2_relat_1(X0) = k1_xboole_0 ),
% 7.91/1.51      inference(cnf_transformation,[],[f35]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_1287,plain,
% 7.91/1.51      ( k1_relat_1(X0) != k1_xboole_0
% 7.91/1.51      | k2_relat_1(X0) = k1_xboole_0
% 7.91/1.51      | v1_relat_1(X0) != iProver_top ),
% 7.91/1.51      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_1756,plain,
% 7.91/1.51      ( k2_relat_1(sK4(X0,X1)) = k1_xboole_0
% 7.91/1.51      | k1_xboole_0 != X0
% 7.91/1.51      | v1_relat_1(sK4(X0,X1)) != iProver_top ),
% 7.91/1.51      inference(superposition,[status(thm)],[c_13,c_1287]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_1977,plain,
% 7.91/1.51      ( k1_xboole_0 != X0 | k2_relat_1(sK4(X0,X1)) = k1_xboole_0 ),
% 7.91/1.51      inference(global_propositional_subsumption,[status(thm)],[c_1756,c_21]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_1978,plain,
% 7.91/1.51      ( k2_relat_1(sK4(X0,X1)) = k1_xboole_0 | k1_xboole_0 != X0 ),
% 7.91/1.51      inference(renaming,[status(thm)],[c_1977]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_1980,plain,
% 7.91/1.51      ( k2_relat_1(sK4(k1_xboole_0,X0)) = k1_xboole_0 ),
% 7.91/1.51      inference(equality_resolution,[status(thm)],[c_1978]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_1981,plain,
% 7.91/1.51      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.91/1.51      inference(light_normalisation,[status(thm)],[c_1980,c_1833]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_3316,plain,
% 7.91/1.51      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 7.91/1.51      | r2_hidden(sK3(k1_xboole_0,X0),k1_xboole_0) = iProver_top ),
% 7.91/1.51      inference(light_normalisation,[status(thm)],[c_3310,c_1981]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_12,plain,
% 7.91/1.51      ( ~ r2_hidden(X0,X1) | k1_funct_1(sK4(X1,X2),X0) = X2 ),
% 7.91/1.51      inference(cnf_transformation,[],[f46]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_1280,plain,
% 7.91/1.51      ( k1_funct_1(sK4(X0,X1),X2) = X1 | r2_hidden(X2,X0) != iProver_top ),
% 7.91/1.51      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_3320,plain,
% 7.91/1.51      ( k1_funct_1(sK4(k1_xboole_0,X0),sK3(k1_xboole_0,X1)) = X0
% 7.91/1.51      | r2_hidden(X1,k1_xboole_0) != iProver_top ),
% 7.91/1.51      inference(superposition,[status(thm)],[c_3316,c_1280]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_3321,plain,
% 7.91/1.51      ( k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,X0)) = X1
% 7.91/1.51      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.91/1.51      inference(light_normalisation,[status(thm)],[c_3320,c_1833]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_22,plain,
% 7.91/1.51      ( v1_relat_1(sK4(k1_xboole_0,k1_xboole_0)) ),
% 7.91/1.51      inference(instantiation,[status(thm)],[c_15]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_25,plain,
% 7.91/1.51      ( v1_funct_1(sK4(k1_xboole_0,k1_xboole_0)) ),
% 7.91/1.51      inference(instantiation,[status(thm)],[c_14]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_1345,plain,
% 7.91/1.51      ( ~ v1_funct_1(sK4(k1_xboole_0,k1_xboole_0))
% 7.91/1.51      | v1_funct_1(k1_xboole_0)
% 7.91/1.51      | k1_xboole_0 != sK4(k1_xboole_0,k1_xboole_0) ),
% 7.91/1.51      inference(instantiation,[status(thm)],[c_1343]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_1381,plain,
% 7.91/1.51      ( ~ v1_relat_1(sK4(k1_xboole_0,k1_xboole_0))
% 7.91/1.51      | v1_relat_1(k1_xboole_0)
% 7.91/1.51      | k1_xboole_0 != sK4(k1_xboole_0,k1_xboole_0) ),
% 7.91/1.51      inference(instantiation,[status(thm)],[c_1379]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_8,plain,
% 7.91/1.51      ( r2_hidden(sK2(X0,X1),k1_relat_1(X0))
% 7.91/1.51      | r2_hidden(sK1(X0,X1),X1)
% 7.91/1.51      | ~ v1_funct_1(X0)
% 7.91/1.51      | ~ v1_relat_1(X0)
% 7.91/1.51      | k2_relat_1(X0) = X1 ),
% 7.91/1.51      inference(cnf_transformation,[],[f40]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_1284,plain,
% 7.91/1.51      ( k2_relat_1(X0) = X1
% 7.91/1.51      | r2_hidden(sK2(X0,X1),k1_relat_1(X0)) = iProver_top
% 7.91/1.51      | r2_hidden(sK1(X0,X1),X1) = iProver_top
% 7.91/1.51      | v1_funct_1(X0) != iProver_top
% 7.91/1.51      | v1_relat_1(X0) != iProver_top ),
% 7.91/1.51      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_2082,plain,
% 7.91/1.51      ( k2_relat_1(sK4(X0,X1)) = X2
% 7.91/1.51      | r2_hidden(sK2(sK4(X0,X1),X2),X0) = iProver_top
% 7.91/1.51      | r2_hidden(sK1(sK4(X0,X1),X2),X2) = iProver_top
% 7.91/1.51      | v1_funct_1(sK4(X0,X1)) != iProver_top
% 7.91/1.51      | v1_relat_1(sK4(X0,X1)) != iProver_top ),
% 7.91/1.51      inference(superposition,[status(thm)],[c_13,c_1284]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_2735,plain,
% 7.91/1.51      ( k2_relat_1(sK4(X0,X1)) = X2
% 7.91/1.51      | r2_hidden(sK2(sK4(X0,X1),X2),X0) = iProver_top
% 7.91/1.51      | r2_hidden(sK1(sK4(X0,X1),X2),X2) = iProver_top ),
% 7.91/1.51      inference(global_propositional_subsumption,
% 7.91/1.51                [status(thm)],
% 7.91/1.51                [c_2082,c_21,c_24]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_2745,plain,
% 7.91/1.51      ( k1_funct_1(sK4(X0,X1),sK2(sK4(X0,X2),X3)) = X1
% 7.91/1.51      | k2_relat_1(sK4(X0,X2)) = X3
% 7.91/1.51      | r2_hidden(sK1(sK4(X0,X2),X3),X3) = iProver_top ),
% 7.91/1.51      inference(superposition,[status(thm)],[c_2735,c_1280]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_1278,plain,
% 7.91/1.51      ( v1_relat_1(sK4(X0,X1)) = iProver_top ),
% 7.91/1.51      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_1279,plain,
% 7.91/1.51      ( v1_funct_1(sK4(X0,X1)) = iProver_top ),
% 7.91/1.51      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_1,plain,
% 7.91/1.51      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 7.91/1.51      inference(cnf_transformation,[],[f31]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_16,negated_conjecture,
% 7.91/1.51      ( ~ r1_tarski(k2_relat_1(X0),sK5)
% 7.91/1.51      | ~ v1_funct_1(X0)
% 7.91/1.51      | ~ v1_relat_1(X0)
% 7.91/1.51      | k1_relat_1(X0) != sK6 ),
% 7.91/1.51      inference(cnf_transformation,[],[f48]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_191,plain,
% 7.91/1.51      ( r2_hidden(sK0(X0,X1),X0)
% 7.91/1.51      | ~ v1_funct_1(X2)
% 7.91/1.51      | ~ v1_relat_1(X2)
% 7.91/1.51      | k1_relat_1(X2) != sK6
% 7.91/1.51      | k2_relat_1(X2) != X0
% 7.91/1.51      | sK5 != X1 ),
% 7.91/1.51      inference(resolution_lifted,[status(thm)],[c_1,c_16]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_192,plain,
% 7.91/1.51      ( r2_hidden(sK0(k2_relat_1(X0),sK5),k2_relat_1(X0))
% 7.91/1.51      | ~ v1_funct_1(X0)
% 7.91/1.51      | ~ v1_relat_1(X0)
% 7.91/1.51      | k1_relat_1(X0) != sK6 ),
% 7.91/1.51      inference(unflattening,[status(thm)],[c_191]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_1277,plain,
% 7.91/1.51      ( k1_relat_1(X0) != sK6
% 7.91/1.51      | r2_hidden(sK0(k2_relat_1(X0),sK5),k2_relat_1(X0)) = iProver_top
% 7.91/1.51      | v1_funct_1(X0) != iProver_top
% 7.91/1.51      | v1_relat_1(X0) != iProver_top ),
% 7.91/1.51      inference(predicate_to_equality,[status(thm)],[c_192]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_1389,plain,
% 7.91/1.51      ( sK6 != X0
% 7.91/1.51      | r2_hidden(sK0(k2_relat_1(sK4(X0,X1)),sK5),k2_relat_1(sK4(X0,X1))) = iProver_top
% 7.91/1.51      | v1_funct_1(sK4(X0,X1)) != iProver_top
% 7.91/1.51      | v1_relat_1(sK4(X0,X1)) != iProver_top ),
% 7.91/1.51      inference(superposition,[status(thm)],[c_13,c_1277]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_1444,plain,
% 7.91/1.51      ( sK6 != X0
% 7.91/1.51      | r2_hidden(sK0(k2_relat_1(sK4(X0,X1)),sK5),k2_relat_1(sK4(X0,X1))) = iProver_top ),
% 7.91/1.51      inference(global_propositional_subsumption,
% 7.91/1.51                [status(thm)],
% 7.91/1.51                [c_1389,c_21,c_24]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_1450,plain,
% 7.91/1.51      ( r2_hidden(sK0(k2_relat_1(sK4(sK6,X0)),sK5),k2_relat_1(sK4(sK6,X0))) = iProver_top ),
% 7.91/1.51      inference(equality_resolution,[status(thm)],[c_1444]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_1933,plain,
% 7.91/1.51      ( k1_funct_1(sK4(k1_relat_1(X0),X1),sK3(X0,X2)) = X1
% 7.91/1.51      | r2_hidden(X2,k2_relat_1(X0)) != iProver_top
% 7.91/1.51      | v1_funct_1(X0) != iProver_top
% 7.91/1.51      | v1_relat_1(X0) != iProver_top ),
% 7.91/1.51      inference(superposition,[status(thm)],[c_1281,c_1280]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_3964,plain,
% 7.91/1.51      ( k1_funct_1(sK4(k1_relat_1(sK4(sK6,X0)),X1),sK3(sK4(sK6,X0),sK0(k2_relat_1(sK4(sK6,X0)),sK5))) = X1
% 7.91/1.51      | v1_funct_1(sK4(sK6,X0)) != iProver_top
% 7.91/1.51      | v1_relat_1(sK4(sK6,X0)) != iProver_top ),
% 7.91/1.51      inference(superposition,[status(thm)],[c_1450,c_1933]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_3973,plain,
% 7.91/1.51      ( k1_funct_1(sK4(sK6,X0),sK3(sK4(sK6,X1),sK0(k2_relat_1(sK4(sK6,X1)),sK5))) = X0
% 7.91/1.51      | v1_funct_1(sK4(sK6,X1)) != iProver_top
% 7.91/1.51      | v1_relat_1(sK4(sK6,X1)) != iProver_top ),
% 7.91/1.51      inference(demodulation,[status(thm)],[c_3964,c_13]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_4154,plain,
% 7.91/1.51      ( k1_funct_1(sK4(sK6,X0),sK3(sK4(sK6,X1),sK0(k2_relat_1(sK4(sK6,X1)),sK5))) = X0
% 7.91/1.51      | v1_relat_1(sK4(sK6,X1)) != iProver_top ),
% 7.91/1.51      inference(superposition,[status(thm)],[c_1279,c_3973]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_4353,plain,
% 7.91/1.51      ( k1_funct_1(sK4(sK6,X0),sK3(sK4(sK6,X1),sK0(k2_relat_1(sK4(sK6,X1)),sK5))) = X0 ),
% 7.91/1.51      inference(superposition,[status(thm)],[c_1278,c_4154]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_10,plain,
% 7.91/1.51      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 7.91/1.51      | ~ v1_funct_1(X1)
% 7.91/1.51      | ~ v1_relat_1(X1)
% 7.91/1.51      | k1_funct_1(X1,sK3(X1,X0)) = X0 ),
% 7.91/1.51      inference(cnf_transformation,[],[f51]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_1282,plain,
% 7.91/1.51      ( k1_funct_1(X0,sK3(X0,X1)) = X1
% 7.91/1.51      | r2_hidden(X1,k2_relat_1(X0)) != iProver_top
% 7.91/1.51      | v1_funct_1(X0) != iProver_top
% 7.91/1.51      | v1_relat_1(X0) != iProver_top ),
% 7.91/1.51      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_1983,plain,
% 7.91/1.51      ( k1_funct_1(sK4(sK6,X0),sK3(sK4(sK6,X0),sK0(k2_relat_1(sK4(sK6,X0)),sK5))) = sK0(k2_relat_1(sK4(sK6,X0)),sK5)
% 7.91/1.51      | v1_funct_1(sK4(sK6,X0)) != iProver_top
% 7.91/1.51      | v1_relat_1(sK4(sK6,X0)) != iProver_top ),
% 7.91/1.51      inference(superposition,[status(thm)],[c_1450,c_1282]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_1370,plain,
% 7.91/1.51      ( v1_funct_1(sK4(sK6,X0)) ),
% 7.91/1.51      inference(instantiation,[status(thm)],[c_14]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_1371,plain,
% 7.91/1.51      ( v1_funct_1(sK4(sK6,X0)) = iProver_top ),
% 7.91/1.51      inference(predicate_to_equality,[status(thm)],[c_1370]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_1416,plain,
% 7.91/1.51      ( v1_relat_1(sK4(sK6,X0)) ),
% 7.91/1.51      inference(instantiation,[status(thm)],[c_15]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_1417,plain,
% 7.91/1.51      ( v1_relat_1(sK4(sK6,X0)) = iProver_top ),
% 7.91/1.51      inference(predicate_to_equality,[status(thm)],[c_1416]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_2272,plain,
% 7.91/1.51      ( k1_funct_1(sK4(sK6,X0),sK3(sK4(sK6,X0),sK0(k2_relat_1(sK4(sK6,X0)),sK5))) = sK0(k2_relat_1(sK4(sK6,X0)),sK5) ),
% 7.91/1.51      inference(global_propositional_subsumption,
% 7.91/1.51                [status(thm)],
% 7.91/1.51                [c_1983,c_1371,c_1417]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_4486,plain,
% 7.91/1.51      ( sK0(k2_relat_1(sK4(sK6,X0)),sK5) = X0 ),
% 7.91/1.51      inference(demodulation,[status(thm)],[c_4353,c_2272]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_0,plain,
% 7.91/1.51      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 7.91/1.51      inference(cnf_transformation,[],[f32]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_209,plain,
% 7.91/1.51      ( ~ r2_hidden(sK0(X0,X1),X1)
% 7.91/1.51      | ~ v1_funct_1(X2)
% 7.91/1.51      | ~ v1_relat_1(X2)
% 7.91/1.51      | k1_relat_1(X2) != sK6
% 7.91/1.51      | k2_relat_1(X2) != X0
% 7.91/1.51      | sK5 != X1 ),
% 7.91/1.51      inference(resolution_lifted,[status(thm)],[c_0,c_16]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_210,plain,
% 7.91/1.51      ( ~ r2_hidden(sK0(k2_relat_1(X0),sK5),sK5)
% 7.91/1.51      | ~ v1_funct_1(X0)
% 7.91/1.51      | ~ v1_relat_1(X0)
% 7.91/1.51      | k1_relat_1(X0) != sK6 ),
% 7.91/1.51      inference(unflattening,[status(thm)],[c_209]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_1276,plain,
% 7.91/1.51      ( k1_relat_1(X0) != sK6
% 7.91/1.51      | r2_hidden(sK0(k2_relat_1(X0),sK5),sK5) != iProver_top
% 7.91/1.51      | v1_funct_1(X0) != iProver_top
% 7.91/1.51      | v1_relat_1(X0) != iProver_top ),
% 7.91/1.51      inference(predicate_to_equality,[status(thm)],[c_210]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_1390,plain,
% 7.91/1.51      ( sK6 != X0
% 7.91/1.51      | r2_hidden(sK0(k2_relat_1(sK4(X0,X1)),sK5),sK5) != iProver_top
% 7.91/1.51      | v1_funct_1(sK4(X0,X1)) != iProver_top
% 7.91/1.51      | v1_relat_1(sK4(X0,X1)) != iProver_top ),
% 7.91/1.51      inference(superposition,[status(thm)],[c_13,c_1276]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_1433,plain,
% 7.91/1.51      ( sK6 != X0
% 7.91/1.51      | r2_hidden(sK0(k2_relat_1(sK4(X0,X1)),sK5),sK5) != iProver_top ),
% 7.91/1.51      inference(global_propositional_subsumption,
% 7.91/1.51                [status(thm)],
% 7.91/1.51                [c_1390,c_21,c_24]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_1439,plain,
% 7.91/1.51      ( r2_hidden(sK0(k2_relat_1(sK4(sK6,X0)),sK5),sK5) != iProver_top ),
% 7.91/1.51      inference(equality_resolution,[status(thm)],[c_1433]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_4501,plain,
% 7.91/1.51      ( r2_hidden(X0,sK5) != iProver_top ),
% 7.91/1.51      inference(demodulation,[status(thm)],[c_4486,c_1439]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_4734,plain,
% 7.91/1.51      ( k1_funct_1(sK4(X0,X1),sK2(sK4(X0,X2),sK5)) = X1
% 7.91/1.51      | k2_relat_1(sK4(X0,X2)) = sK5 ),
% 7.91/1.51      inference(superposition,[status(thm)],[c_2745,c_4501]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_9,plain,
% 7.91/1.51      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 7.91/1.51      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 7.91/1.51      | ~ v1_funct_1(X1)
% 7.91/1.51      | ~ v1_relat_1(X1) ),
% 7.91/1.51      inference(cnf_transformation,[],[f50]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_1283,plain,
% 7.91/1.51      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 7.91/1.51      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
% 7.91/1.51      | v1_funct_1(X1) != iProver_top
% 7.91/1.51      | v1_relat_1(X1) != iProver_top ),
% 7.91/1.51      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_5533,plain,
% 7.91/1.51      ( k2_relat_1(sK4(X0,X1)) = sK5
% 7.91/1.51      | r2_hidden(X2,k2_relat_1(sK4(X0,X2))) = iProver_top
% 7.91/1.51      | r2_hidden(sK2(sK4(X0,X1),sK5),k1_relat_1(sK4(X0,X2))) != iProver_top
% 7.91/1.51      | v1_funct_1(sK4(X0,X2)) != iProver_top
% 7.91/1.51      | v1_relat_1(sK4(X0,X2)) != iProver_top ),
% 7.91/1.51      inference(superposition,[status(thm)],[c_4734,c_1283]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_5534,plain,
% 7.91/1.51      ( k2_relat_1(sK4(X0,X1)) = sK5
% 7.91/1.51      | r2_hidden(X2,k2_relat_1(sK4(X0,X2))) = iProver_top
% 7.91/1.51      | r2_hidden(sK2(sK4(X0,X1),sK5),X0) != iProver_top
% 7.91/1.51      | v1_funct_1(sK4(X0,X2)) != iProver_top
% 7.91/1.51      | v1_relat_1(sK4(X0,X2)) != iProver_top ),
% 7.91/1.51      inference(demodulation,[status(thm)],[c_5533,c_13]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_4730,plain,
% 7.91/1.51      ( k2_relat_1(sK4(X0,X1)) = sK5
% 7.91/1.51      | r2_hidden(sK2(sK4(X0,X1),sK5),X0) = iProver_top ),
% 7.91/1.51      inference(superposition,[status(thm)],[c_2735,c_4501]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_5984,plain,
% 7.91/1.51      ( r2_hidden(X2,k2_relat_1(sK4(X0,X2))) = iProver_top
% 7.91/1.51      | k2_relat_1(sK4(X0,X1)) = sK5
% 7.91/1.51      | v1_funct_1(sK4(X0,X2)) != iProver_top
% 7.91/1.51      | v1_relat_1(sK4(X0,X2)) != iProver_top ),
% 7.91/1.51      inference(global_propositional_subsumption,[status(thm)],[c_5534,c_4730]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_5985,plain,
% 7.91/1.51      ( k2_relat_1(sK4(X0,X1)) = sK5
% 7.91/1.51      | r2_hidden(X2,k2_relat_1(sK4(X0,X2))) = iProver_top
% 7.91/1.51      | v1_funct_1(sK4(X0,X2)) != iProver_top
% 7.91/1.51      | v1_relat_1(sK4(X0,X2)) != iProver_top ),
% 7.91/1.51      inference(renaming,[status(thm)],[c_5984]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_5994,plain,
% 7.91/1.51      ( k1_funct_1(sK4(k1_relat_1(sK4(X0,X1)),X2),sK3(sK4(X0,X1),X1)) = X2
% 7.91/1.51      | k2_relat_1(sK4(X0,X3)) = sK5
% 7.91/1.51      | v1_funct_1(sK4(X0,X1)) != iProver_top
% 7.91/1.51      | v1_relat_1(sK4(X0,X1)) != iProver_top ),
% 7.91/1.51      inference(superposition,[status(thm)],[c_5985,c_1933]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_5998,plain,
% 7.91/1.51      ( k1_funct_1(sK4(X0,X1),sK3(sK4(X0,X2),X2)) = X1
% 7.91/1.51      | k2_relat_1(sK4(X0,X3)) = sK5
% 7.91/1.51      | v1_funct_1(sK4(X0,X2)) != iProver_top
% 7.91/1.51      | v1_relat_1(sK4(X0,X2)) != iProver_top ),
% 7.91/1.51      inference(light_normalisation,[status(thm)],[c_5994,c_13]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_6101,plain,
% 7.91/1.51      ( k1_funct_1(sK4(k1_xboole_0,X0),sK3(sK4(k1_xboole_0,X1),X1)) = X0
% 7.91/1.51      | k2_relat_1(sK4(k1_xboole_0,X2)) = sK5
% 7.91/1.51      | v1_funct_1(k1_xboole_0) != iProver_top
% 7.91/1.51      | v1_relat_1(sK4(k1_xboole_0,X1)) != iProver_top ),
% 7.91/1.51      inference(superposition,[status(thm)],[c_1833,c_5998]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_6116,plain,
% 7.91/1.51      ( k1_funct_1(k1_xboole_0,sK3(sK4(k1_xboole_0,X0),X0)) = X1
% 7.91/1.51      | k2_relat_1(sK4(k1_xboole_0,X2)) = sK5
% 7.91/1.51      | v1_funct_1(k1_xboole_0) != iProver_top
% 7.91/1.51      | v1_relat_1(sK4(k1_xboole_0,X0)) != iProver_top ),
% 7.91/1.51      inference(light_normalisation,[status(thm)],[c_6101,c_1833]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_6117,plain,
% 7.91/1.51      ( k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,X0)) = X1
% 7.91/1.51      | sK5 = k1_xboole_0
% 7.91/1.51      | v1_funct_1(k1_xboole_0) != iProver_top
% 7.91/1.51      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.91/1.51      inference(demodulation,[status(thm)],[c_6116,c_1833,c_1981]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_6118,plain,
% 7.91/1.51      ( ~ v1_funct_1(k1_xboole_0)
% 7.91/1.51      | ~ v1_relat_1(k1_xboole_0)
% 7.91/1.51      | k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,X0)) = X1
% 7.91/1.51      | sK5 = k1_xboole_0 ),
% 7.91/1.51      inference(predicate_to_equality_rev,[status(thm)],[c_6117]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_5411,plain,
% 7.91/1.51      ( k2_relat_1(sK4(sK5,X0)) = sK5 ),
% 7.91/1.51      inference(superposition,[status(thm)],[c_4730,c_4501]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_2,plain,
% 7.91/1.51      ( ~ v1_relat_1(X0) | k2_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = X0 ),
% 7.91/1.51      inference(cnf_transformation,[],[f34]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_1290,plain,
% 7.91/1.51      ( k2_relat_1(X0) != k1_xboole_0
% 7.91/1.51      | k1_xboole_0 = X0
% 7.91/1.51      | v1_relat_1(X0) != iProver_top ),
% 7.91/1.51      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_5428,plain,
% 7.91/1.51      ( sK4(sK5,X0) = k1_xboole_0
% 7.91/1.51      | sK5 != k1_xboole_0
% 7.91/1.51      | v1_relat_1(sK4(sK5,X0)) != iProver_top ),
% 7.91/1.51      inference(superposition,[status(thm)],[c_5411,c_1290]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_17,negated_conjecture,
% 7.91/1.51      ( k1_xboole_0 = sK6 | k1_xboole_0 != sK5 ),
% 7.91/1.51      inference(cnf_transformation,[],[f47]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_1025,plain,( X0 = X0 ),theory(equality) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_1040,plain,
% 7.91/1.51      ( k1_xboole_0 = k1_xboole_0 ),
% 7.91/1.51      inference(instantiation,[status(thm)],[c_1025]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_1026,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_1314,plain,
% 7.91/1.51      ( sK5 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK5 ),
% 7.91/1.51      inference(instantiation,[status(thm)],[c_1026]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_1315,plain,
% 7.91/1.51      ( sK5 != k1_xboole_0 | k1_xboole_0 = sK5 | k1_xboole_0 != k1_xboole_0 ),
% 7.91/1.51      inference(instantiation,[status(thm)],[c_1314]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_1418,plain,
% 7.91/1.51      ( v1_relat_1(sK4(sK6,k1_xboole_0)) ),
% 7.91/1.51      inference(instantiation,[status(thm)],[c_1416]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_1440,plain,
% 7.91/1.51      ( ~ r2_hidden(sK0(k2_relat_1(sK4(sK6,X0)),sK5),sK5) ),
% 7.91/1.51      inference(predicate_to_equality_rev,[status(thm)],[c_1439]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_1442,plain,
% 7.91/1.51      ( ~ r2_hidden(sK0(k2_relat_1(sK4(sK6,k1_xboole_0)),sK5),sK5) ),
% 7.91/1.51      inference(instantiation,[status(thm)],[c_1440]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_1451,plain,
% 7.91/1.51      ( r2_hidden(sK0(k2_relat_1(sK4(sK6,X0)),sK5),k2_relat_1(sK4(sK6,X0))) ),
% 7.91/1.51      inference(predicate_to_equality_rev,[status(thm)],[c_1450]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_1453,plain,
% 7.91/1.51      ( r2_hidden(sK0(k2_relat_1(sK4(sK6,k1_xboole_0)),sK5),k2_relat_1(sK4(sK6,k1_xboole_0))) ),
% 7.91/1.51      inference(instantiation,[status(thm)],[c_1451]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_1472,plain,
% 7.91/1.51      ( k1_relat_1(sK4(sK6,X0)) = sK6 ),
% 7.91/1.51      inference(instantiation,[status(thm)],[c_13]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_1473,plain,
% 7.91/1.51      ( k1_relat_1(sK4(sK6,k1_xboole_0)) = sK6 ),
% 7.91/1.51      inference(instantiation,[status(thm)],[c_1472]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_1028,plain,
% 7.91/1.51      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.91/1.51      theory(equality) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_1492,plain,
% 7.91/1.51      ( ~ r2_hidden(X0,X1)
% 7.91/1.51      | r2_hidden(sK0(k2_relat_1(sK4(sK6,X2)),sK5),sK5)
% 7.91/1.51      | sK0(k2_relat_1(sK4(sK6,X2)),sK5) != X0
% 7.91/1.51      | sK5 != X1 ),
% 7.91/1.51      inference(instantiation,[status(thm)],[c_1028]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_1494,plain,
% 7.91/1.51      ( r2_hidden(sK0(k2_relat_1(sK4(sK6,k1_xboole_0)),sK5),sK5)
% 7.91/1.51      | ~ r2_hidden(k1_xboole_0,k1_xboole_0)
% 7.91/1.51      | sK0(k2_relat_1(sK4(sK6,k1_xboole_0)),sK5) != k1_xboole_0
% 7.91/1.51      | sK5 != k1_xboole_0 ),
% 7.91/1.51      inference(instantiation,[status(thm)],[c_1492]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_1770,plain,
% 7.91/1.51      ( r2_hidden(X0,X1)
% 7.91/1.51      | ~ r2_hidden(sK0(k2_relat_1(sK4(sK6,X2)),sK5),k2_relat_1(sK4(sK6,X2)))
% 7.91/1.51      | X0 != sK0(k2_relat_1(sK4(sK6,X2)),sK5)
% 7.91/1.51      | X1 != k2_relat_1(sK4(sK6,X2)) ),
% 7.91/1.51      inference(instantiation,[status(thm)],[c_1028]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_1772,plain,
% 7.91/1.51      ( ~ r2_hidden(sK0(k2_relat_1(sK4(sK6,k1_xboole_0)),sK5),k2_relat_1(sK4(sK6,k1_xboole_0)))
% 7.91/1.51      | r2_hidden(k1_xboole_0,k1_xboole_0)
% 7.91/1.51      | k1_xboole_0 != sK0(k2_relat_1(sK4(sK6,k1_xboole_0)),sK5)
% 7.91/1.51      | k1_xboole_0 != k2_relat_1(sK4(sK6,k1_xboole_0)) ),
% 7.91/1.51      inference(instantiation,[status(thm)],[c_1770]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_1557,plain,
% 7.91/1.51      ( k2_relat_1(X0) != X1
% 7.91/1.51      | k1_xboole_0 != X1
% 7.91/1.51      | k1_xboole_0 = k2_relat_1(X0) ),
% 7.91/1.51      inference(instantiation,[status(thm)],[c_1026]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_1712,plain,
% 7.91/1.51      ( k2_relat_1(X0) != k1_xboole_0
% 7.91/1.51      | k1_xboole_0 = k2_relat_1(X0)
% 7.91/1.51      | k1_xboole_0 != k1_xboole_0 ),
% 7.91/1.51      inference(instantiation,[status(thm)],[c_1557]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_2300,plain,
% 7.91/1.51      ( k2_relat_1(sK4(sK6,X0)) != k1_xboole_0
% 7.91/1.51      | k1_xboole_0 = k2_relat_1(sK4(sK6,X0))
% 7.91/1.51      | k1_xboole_0 != k1_xboole_0 ),
% 7.91/1.51      inference(instantiation,[status(thm)],[c_1712]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_2305,plain,
% 7.91/1.51      ( k2_relat_1(sK4(sK6,k1_xboole_0)) != k1_xboole_0
% 7.91/1.51      | k1_xboole_0 = k2_relat_1(sK4(sK6,k1_xboole_0))
% 7.91/1.51      | k1_xboole_0 != k1_xboole_0 ),
% 7.91/1.51      inference(instantiation,[status(thm)],[c_2300]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_3180,plain,
% 7.91/1.51      ( ~ v1_relat_1(sK4(sK6,X0))
% 7.91/1.51      | k1_relat_1(sK4(sK6,X0)) != k1_xboole_0
% 7.91/1.51      | k2_relat_1(sK4(sK6,X0)) = k1_xboole_0 ),
% 7.91/1.51      inference(instantiation,[status(thm)],[c_5]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_3182,plain,
% 7.91/1.51      ( ~ v1_relat_1(sK4(sK6,k1_xboole_0))
% 7.91/1.51      | k1_relat_1(sK4(sK6,k1_xboole_0)) != k1_xboole_0
% 7.91/1.51      | k2_relat_1(sK4(sK6,k1_xboole_0)) = k1_xboole_0 ),
% 7.91/1.51      inference(instantiation,[status(thm)],[c_3180]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_2243,plain,
% 7.91/1.51      ( X0 != X1
% 7.91/1.51      | k1_relat_1(sK4(sK6,X2)) != X1
% 7.91/1.51      | k1_relat_1(sK4(sK6,X2)) = X0 ),
% 7.91/1.51      inference(instantiation,[status(thm)],[c_1026]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_3551,plain,
% 7.91/1.51      ( X0 != sK6
% 7.91/1.51      | k1_relat_1(sK4(sK6,X1)) = X0
% 7.91/1.51      | k1_relat_1(sK4(sK6,X1)) != sK6 ),
% 7.91/1.51      inference(instantiation,[status(thm)],[c_2243]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_3552,plain,
% 7.91/1.51      ( k1_relat_1(sK4(sK6,k1_xboole_0)) != sK6
% 7.91/1.51      | k1_relat_1(sK4(sK6,k1_xboole_0)) = k1_xboole_0
% 7.91/1.51      | k1_xboole_0 != sK6 ),
% 7.91/1.51      inference(instantiation,[status(thm)],[c_3551]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_3725,plain,
% 7.91/1.51      ( X0 != X1
% 7.91/1.51      | X0 = sK0(k2_relat_1(sK4(sK6,X2)),sK5)
% 7.91/1.51      | sK0(k2_relat_1(sK4(sK6,X2)),sK5) != X1 ),
% 7.91/1.51      inference(instantiation,[status(thm)],[c_1026]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_3726,plain,
% 7.91/1.51      ( sK0(k2_relat_1(sK4(sK6,k1_xboole_0)),sK5) != k1_xboole_0
% 7.91/1.51      | k1_xboole_0 = sK0(k2_relat_1(sK4(sK6,k1_xboole_0)),sK5)
% 7.91/1.51      | k1_xboole_0 != k1_xboole_0 ),
% 7.91/1.51      inference(instantiation,[status(thm)],[c_3725]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_4487,plain,
% 7.91/1.51      ( sK0(k2_relat_1(sK4(sK6,k1_xboole_0)),sK5) = k1_xboole_0 ),
% 7.91/1.51      inference(instantiation,[status(thm)],[c_4486]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_6304,plain,
% 7.91/1.51      ( sK5 != k1_xboole_0 ),
% 7.91/1.51      inference(global_propositional_subsumption,
% 7.91/1.51                [status(thm)],
% 7.91/1.51                [c_5428,c_17,c_1040,c_1315,c_1418,c_1442,c_1453,c_1473,
% 7.91/1.51                 c_1494,c_1772,c_2305,c_3182,c_3552,c_3726,c_4487]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_22869,plain,
% 7.91/1.51      ( k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,X0)) = X1 ),
% 7.91/1.51      inference(global_propositional_subsumption,
% 7.91/1.51                [status(thm)],
% 7.91/1.51                [c_3321,c_17,c_23,c_26,c_27,c_490,c_1040,c_1315,c_1346,
% 7.91/1.51                 c_1382,c_1418,c_1442,c_1453,c_1473,c_1494,c_1772,c_2305,
% 7.91/1.51                 c_3182,c_3552,c_3726,c_4487,c_6000]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_4500,plain,
% 7.91/1.51      ( r2_hidden(X0,k2_relat_1(sK4(sK6,X0))) = iProver_top ),
% 7.91/1.51      inference(demodulation,[status(thm)],[c_4486,c_1450]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_23274,plain,
% 7.91/1.51      ( r2_hidden(X0,k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,X1))) = iProver_top ),
% 7.91/1.51      inference(superposition,[status(thm)],[c_22869,c_4500]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_5408,plain,
% 7.91/1.51      ( k2_relat_1(sK4(k1_xboole_0,X0)) = sK5
% 7.91/1.51      | r2_hidden(sK2(k1_xboole_0,sK5),k1_xboole_0) = iProver_top ),
% 7.91/1.51      inference(superposition,[status(thm)],[c_1833,c_4730]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_5415,plain,
% 7.91/1.51      ( sK5 = k1_xboole_0
% 7.91/1.51      | r2_hidden(sK2(k1_xboole_0,sK5),k1_xboole_0) = iProver_top ),
% 7.91/1.51      inference(light_normalisation,[status(thm)],[c_5408,c_1833,c_1981]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_11422,plain,
% 7.91/1.51      ( r2_hidden(sK2(k1_xboole_0,sK5),k1_xboole_0) = iProver_top ),
% 7.91/1.51      inference(global_propositional_subsumption,
% 7.91/1.51                [status(thm)],
% 7.91/1.51                [c_5415,c_17,c_1040,c_1315,c_1418,c_1442,c_1453,c_1473,
% 7.91/1.51                 c_1494,c_1772,c_2305,c_3182,c_3552,c_3726,c_4487]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_2070,plain,
% 7.91/1.51      ( k1_funct_1(X0,sK3(X0,k1_funct_1(X0,X1))) = k1_funct_1(X0,X1)
% 7.91/1.51      | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
% 7.91/1.51      | v1_funct_1(X0) != iProver_top
% 7.91/1.51      | v1_relat_1(X0) != iProver_top ),
% 7.91/1.51      inference(superposition,[status(thm)],[c_1283,c_1282]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_7163,plain,
% 7.91/1.51      ( k1_funct_1(sK4(X0,X1),sK3(sK4(X0,X1),k1_funct_1(sK4(X0,X1),X2))) = k1_funct_1(sK4(X0,X1),X2)
% 7.91/1.51      | r2_hidden(X2,X0) != iProver_top
% 7.91/1.51      | v1_funct_1(sK4(X0,X1)) != iProver_top
% 7.91/1.51      | v1_relat_1(sK4(X0,X1)) != iProver_top ),
% 7.91/1.51      inference(superposition,[status(thm)],[c_13,c_2070]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_7206,plain,
% 7.91/1.51      ( k1_funct_1(sK4(X0,X1),sK3(sK4(X0,X1),k1_funct_1(sK4(X0,X1),X2))) = k1_funct_1(sK4(X0,X1),X2)
% 7.91/1.51      | r2_hidden(X2,X0) != iProver_top ),
% 7.91/1.51      inference(global_propositional_subsumption,
% 7.91/1.51                [status(thm)],
% 7.91/1.51                [c_7163,c_21,c_24]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_7228,plain,
% 7.91/1.51      ( k1_funct_1(sK4(X0,X1),sK3(sK4(X0,X1),k1_funct_1(sK4(X0,X1),sK2(sK4(X0,X2),sK5)))) = k1_funct_1(sK4(X0,X1),sK2(sK4(X0,X2),sK5))
% 7.91/1.51      | k2_relat_1(sK4(X0,X2)) = sK5 ),
% 7.91/1.51      inference(superposition,[status(thm)],[c_4730,c_7206]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_7682,plain,
% 7.91/1.51      ( k1_funct_1(sK4(X0,X1),sK3(sK4(X0,X1),X1)) = k1_funct_1(sK4(X0,X1),sK2(sK4(X0,X2),sK5))
% 7.91/1.51      | k2_relat_1(sK4(X0,X2)) = sK5 ),
% 7.91/1.51      inference(superposition,[status(thm)],[c_4734,c_7228]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_7797,plain,
% 7.91/1.51      ( k1_funct_1(sK4(X0,X1),sK3(sK4(X0,X1),X1)) = X1
% 7.91/1.51      | k2_relat_1(sK4(X0,X2)) = sK5 ),
% 7.91/1.51      inference(superposition,[status(thm)],[c_7682,c_4734]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_7834,plain,
% 7.91/1.51      ( k1_funct_1(sK4(X0,X1),sK3(sK4(X0,X1),X1)) = X1
% 7.91/1.51      | r2_hidden(X2,k1_relat_1(sK4(X0,X3))) != iProver_top
% 7.91/1.51      | r2_hidden(k1_funct_1(sK4(X0,X3),X2),sK5) = iProver_top
% 7.91/1.51      | v1_funct_1(sK4(X0,X3)) != iProver_top
% 7.91/1.51      | v1_relat_1(sK4(X0,X3)) != iProver_top ),
% 7.91/1.51      inference(superposition,[status(thm)],[c_7797,c_1283]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_7911,plain,
% 7.91/1.51      ( k1_funct_1(sK4(X0,X1),sK3(sK4(X0,X1),X1)) = X1
% 7.91/1.51      | r2_hidden(X2,X0) != iProver_top
% 7.91/1.51      | r2_hidden(k1_funct_1(sK4(X0,X3),X2),sK5) = iProver_top
% 7.91/1.51      | v1_funct_1(sK4(X0,X3)) != iProver_top
% 7.91/1.51      | v1_relat_1(sK4(X0,X3)) != iProver_top ),
% 7.91/1.51      inference(demodulation,[status(thm)],[c_7834,c_13]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_8366,plain,
% 7.91/1.51      ( k1_funct_1(sK4(X0,X1),sK3(sK4(X0,X1),X1)) = X1
% 7.91/1.51      | r2_hidden(X2,X0) != iProver_top
% 7.91/1.51      | v1_funct_1(sK4(X0,X3)) != iProver_top
% 7.91/1.51      | v1_relat_1(sK4(X0,X3)) != iProver_top ),
% 7.91/1.51      inference(superposition,[status(thm)],[c_7911,c_4501]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_8615,plain,
% 7.91/1.51      ( k1_funct_1(sK4(X0,X1),sK3(sK4(X0,X1),X1)) = X1
% 7.91/1.51      | r2_hidden(X2,X0) != iProver_top
% 7.91/1.51      | v1_relat_1(sK4(X0,X3)) != iProver_top ),
% 7.91/1.51      inference(superposition,[status(thm)],[c_1279,c_8366]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_8623,plain,
% 7.91/1.51      ( k1_funct_1(sK4(X0,X1),sK3(sK4(X0,X1),X1)) = X1
% 7.91/1.51      | r2_hidden(X2,X0) != iProver_top ),
% 7.91/1.51      inference(superposition,[status(thm)],[c_1278,c_8615]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_11426,plain,
% 7.91/1.51      ( k1_funct_1(sK4(k1_xboole_0,X0),sK3(sK4(k1_xboole_0,X0),X0)) = X0 ),
% 7.91/1.51      inference(superposition,[status(thm)],[c_11422,c_8623]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_11438,plain,
% 7.91/1.51      ( k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,X0)) = X0 ),
% 7.91/1.51      inference(light_normalisation,[status(thm)],[c_11426,c_1833]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_23541,plain,
% 7.91/1.51      ( r2_hidden(X0,X1) = iProver_top ),
% 7.91/1.51      inference(demodulation,[status(thm)],[c_23274,c_11438]) ).
% 7.91/1.51  
% 7.91/1.51  cnf(c_23546,plain,
% 7.91/1.51      ( $false ),
% 7.91/1.51      inference(superposition,[status(thm)],[c_23541,c_4501]) ).
% 7.91/1.51  
% 7.91/1.51  
% 7.91/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.91/1.51  
% 7.91/1.51  ------                               Statistics
% 7.91/1.51  
% 7.91/1.51  ------ General
% 7.91/1.51  
% 7.91/1.51  abstr_ref_over_cycles:                  0
% 7.91/1.51  abstr_ref_under_cycles:                 0
% 7.91/1.51  gc_basic_clause_elim:                   0
% 7.91/1.51  forced_gc_time:                         0
% 7.91/1.51  parsing_time:                           0.031
% 7.91/1.51  unif_index_cands_time:                  0.
% 7.91/1.51  unif_index_add_time:                    0.
% 7.91/1.51  orderings_time:                         0.
% 7.91/1.51  out_proof_time:                         0.013
% 7.91/1.51  total_time:                             0.901
% 7.91/1.51  num_of_symbols:                         47
% 7.91/1.51  num_of_terms:                           30908
% 7.91/1.51  
% 7.91/1.51  ------ Preprocessing
% 7.91/1.51  
% 7.91/1.51  num_of_splits:                          0
% 7.91/1.51  num_of_split_atoms:                     1
% 7.91/1.51  num_of_reused_defs:                     8
% 7.91/1.51  num_eq_ax_congr_red:                    29
% 7.91/1.51  num_of_sem_filtered_clauses:            1
% 7.91/1.51  num_of_subtypes:                        0
% 7.91/1.51  monotx_restored_types:                  0
% 7.91/1.51  sat_num_of_epr_types:                   0
% 7.91/1.51  sat_num_of_non_cyclic_types:            0
% 7.91/1.51  sat_guarded_non_collapsed_types:        0
% 7.91/1.51  num_pure_diseq_elim:                    0
% 7.91/1.51  simp_replaced_by:                       0
% 7.91/1.51  res_preprocessed:                       86
% 7.91/1.51  prep_upred:                             0
% 7.91/1.51  prep_unflattend:                        44
% 7.91/1.51  smt_new_axioms:                         0
% 7.91/1.51  pred_elim_cands:                        3
% 7.91/1.51  pred_elim:                              1
% 7.91/1.51  pred_elim_cl:                           1
% 7.91/1.51  pred_elim_cycles:                       5
% 7.91/1.51  merged_defs:                            0
% 7.91/1.51  merged_defs_ncl:                        0
% 7.91/1.51  bin_hyper_res:                          0
% 7.91/1.51  prep_cycles:                            4
% 7.91/1.51  pred_elim_time:                         0.011
% 7.91/1.51  splitting_time:                         0.
% 7.91/1.51  sem_filter_time:                        0.
% 7.91/1.51  monotx_time:                            0.
% 7.91/1.51  subtype_inf_time:                       0.
% 7.91/1.51  
% 7.91/1.51  ------ Problem properties
% 7.91/1.51  
% 7.91/1.51  clauses:                                17
% 7.91/1.51  conjectures:                            1
% 7.91/1.51  epr:                                    1
% 7.91/1.51  horn:                                   15
% 7.91/1.51  ground:                                 1
% 7.91/1.51  unary:                                  3
% 7.91/1.51  binary:                                 2
% 7.91/1.51  lits:                                   55
% 7.91/1.51  lits_eq:                                20
% 7.91/1.51  fd_pure:                                0
% 7.91/1.51  fd_pseudo:                              0
% 7.91/1.51  fd_cond:                                2
% 7.91/1.51  fd_pseudo_cond:                         3
% 7.91/1.51  ac_symbols:                             0
% 7.91/1.51  
% 7.91/1.51  ------ Propositional Solver
% 7.91/1.51  
% 7.91/1.51  prop_solver_calls:                      36
% 7.91/1.51  prop_fast_solver_calls:                 2037
% 7.91/1.51  smt_solver_calls:                       0
% 7.91/1.51  smt_fast_solver_calls:                  0
% 7.91/1.51  prop_num_of_clauses:                    10032
% 7.91/1.51  prop_preprocess_simplified:             19329
% 7.91/1.51  prop_fo_subsumed:                       131
% 7.91/1.51  prop_solver_time:                       0.
% 7.91/1.51  smt_solver_time:                        0.
% 7.91/1.51  smt_fast_solver_time:                   0.
% 7.91/1.51  prop_fast_solver_time:                  0.
% 7.91/1.51  prop_unsat_core_time:                   0.
% 7.91/1.51  
% 7.91/1.51  ------ QBF
% 7.91/1.51  
% 7.91/1.51  qbf_q_res:                              0
% 7.91/1.51  qbf_num_tautologies:                    0
% 7.91/1.51  qbf_prep_cycles:                        0
% 7.91/1.51  
% 7.91/1.51  ------ BMC1
% 7.91/1.51  
% 7.91/1.51  bmc1_current_bound:                     -1
% 7.91/1.51  bmc1_last_solved_bound:                 -1
% 7.91/1.51  bmc1_unsat_core_size:                   -1
% 7.91/1.51  bmc1_unsat_core_parents_size:           -1
% 7.91/1.51  bmc1_merge_next_fun:                    0
% 7.91/1.51  bmc1_unsat_core_clauses_time:           0.
% 7.91/1.51  
% 7.91/1.51  ------ Instantiation
% 7.91/1.51  
% 7.91/1.51  inst_num_of_clauses:                    2764
% 7.91/1.51  inst_num_in_passive:                    1672
% 7.91/1.51  inst_num_in_active:                     1038
% 7.91/1.51  inst_num_in_unprocessed:                54
% 7.91/1.51  inst_num_of_loops:                      1250
% 7.91/1.51  inst_num_of_learning_restarts:          0
% 7.91/1.51  inst_num_moves_active_passive:          206
% 7.91/1.51  inst_lit_activity:                      0
% 7.91/1.51  inst_lit_activity_moves:                0
% 7.91/1.51  inst_num_tautologies:                   0
% 7.91/1.51  inst_num_prop_implied:                  0
% 7.91/1.51  inst_num_existing_simplified:           0
% 7.91/1.51  inst_num_eq_res_simplified:             0
% 7.91/1.51  inst_num_child_elim:                    0
% 7.91/1.51  inst_num_of_dismatching_blockings:      1832
% 7.91/1.51  inst_num_of_non_proper_insts:           3131
% 7.91/1.51  inst_num_of_duplicates:                 0
% 7.91/1.51  inst_inst_num_from_inst_to_res:         0
% 7.91/1.51  inst_dismatching_checking_time:         0.
% 7.91/1.51  
% 7.91/1.51  ------ Resolution
% 7.91/1.51  
% 7.91/1.51  res_num_of_clauses:                     0
% 7.91/1.51  res_num_in_passive:                     0
% 7.91/1.51  res_num_in_active:                      0
% 7.91/1.51  res_num_of_loops:                       90
% 7.91/1.51  res_forward_subset_subsumed:            163
% 7.91/1.51  res_backward_subset_subsumed:           0
% 7.91/1.51  res_forward_subsumed:                   0
% 7.91/1.51  res_backward_subsumed:                  0
% 7.91/1.51  res_forward_subsumption_resolution:     4
% 7.91/1.51  res_backward_subsumption_resolution:    0
% 7.91/1.51  res_clause_to_clause_subsumption:       5236
% 7.91/1.51  res_orphan_elimination:                 0
% 7.91/1.51  res_tautology_del:                      172
% 7.91/1.51  res_num_eq_res_simplified:              0
% 7.91/1.51  res_num_sel_changes:                    0
% 7.91/1.51  res_moves_from_active_to_pass:          0
% 7.91/1.51  
% 7.91/1.51  ------ Superposition
% 7.91/1.51  
% 7.91/1.51  sup_time_total:                         0.
% 7.91/1.51  sup_time_generating:                    0.
% 7.91/1.51  sup_time_sim_full:                      0.
% 7.91/1.51  sup_time_sim_immed:                     0.
% 7.91/1.51  
% 7.91/1.51  sup_num_of_clauses:                     578
% 7.91/1.51  sup_num_in_active:                      24
% 7.91/1.51  sup_num_in_passive:                     554
% 7.91/1.51  sup_num_of_loops:                       249
% 7.91/1.51  sup_fw_superposition:                   1288
% 7.91/1.51  sup_bw_superposition:                   996
% 7.91/1.51  sup_immediate_simplified:               1515
% 7.91/1.51  sup_given_eliminated:                   47
% 7.91/1.51  comparisons_done:                       0
% 7.91/1.51  comparisons_avoided:                    236
% 7.91/1.51  
% 7.91/1.51  ------ Simplifications
% 7.91/1.51  
% 7.91/1.51  
% 7.91/1.51  sim_fw_subset_subsumed:                 303
% 7.91/1.51  sim_bw_subset_subsumed:                 91
% 7.91/1.51  sim_fw_subsumed:                        423
% 7.91/1.51  sim_bw_subsumed:                        138
% 7.91/1.51  sim_fw_subsumption_res:                 0
% 7.91/1.51  sim_bw_subsumption_res:                 0
% 7.91/1.51  sim_tautology_del:                      23
% 7.91/1.51  sim_eq_tautology_del:                   471
% 7.91/1.51  sim_eq_res_simp:                        1
% 7.91/1.51  sim_fw_demodulated:                     752
% 7.91/1.51  sim_bw_demodulated:                     201
% 7.91/1.51  sim_light_normalised:                   501
% 7.91/1.51  sim_joinable_taut:                      0
% 7.91/1.51  sim_joinable_simp:                      0
% 7.91/1.51  sim_ac_normalised:                      0
% 7.91/1.51  sim_smt_subsumption:                    0
% 7.91/1.51  
%------------------------------------------------------------------------------
