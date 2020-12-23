%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:49:48 EST 2020

% Result     : Theorem 4.03s
% Output     : CNFRefutation 4.03s
% Verified   : 
% Statistics : Number of formulae       :  185 (3275 expanded)
%              Number of clauses        :  141 ( 936 expanded)
%              Number of leaves         :   12 ( 660 expanded)
%              Depth                    :   30
%              Number of atoms          :  645 (20686 expanded)
%              Number of equality atoms :  390 (10358 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2,X3] :
              ( ( X2 != X3
                | ~ r2_hidden(X2,X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
        & ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
                | X2 != X3
                | ~ r2_hidden(X2,X0) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2,X3] :
              ( ( X2 != X3
                | ~ r2_hidden(X2,X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
        & ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
                | X2 != X3
                | ~ r2_hidden(X2,X0) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2,X3] :
              ( ( X2 != X3
                | ~ r2_hidden(X2,X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
        & ( ! [X4,X5] :
              ( ( r2_hidden(k4_tarski(X4,X5),X1)
                | X4 != X5
                | ~ r2_hidden(X4,X0) )
              & ( ( X4 = X5
                  & r2_hidden(X4,X0) )
                | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f13])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( X2 != X3
            | ~ r2_hidden(X2,X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( ( X2 = X3
              & r2_hidden(X2,X0) )
            | r2_hidden(k4_tarski(X2,X3),X1) ) )
     => ( ( sK0(X0,X1) != sK1(X0,X1)
          | ~ r2_hidden(sK0(X0,X1),X0)
          | ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) )
        & ( ( sK0(X0,X1) = sK1(X0,X1)
            & r2_hidden(sK0(X0,X1),X0) )
          | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( ( sK0(X0,X1) != sK1(X0,X1)
              | ~ r2_hidden(sK0(X0,X1),X0)
              | ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) )
            & ( ( sK0(X0,X1) = sK1(X0,X1)
                & r2_hidden(sK0(X0,X1),X0) )
              | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) ) ) )
        & ( ! [X4,X5] :
              ( ( r2_hidden(k4_tarski(X4,X5),X1)
                | X4 != X5
                | ~ r2_hidden(X4,X0) )
              & ( ( X4 = X5
                  & r2_hidden(X4,X0) )
                | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = X1
      | sK0(X0,X1) = sK1(X0,X1)
      | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( k6_relat_1(X0) = X1
        <=> ( ! [X2] :
                ( r2_hidden(X2,X0)
               => k1_funct_1(X1,X2) = X2 )
            & k1_relat_1(X1) = X0 ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <~> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <~> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ( ? [X2] :
            ( k1_funct_1(X1,X2) != X2
            & r2_hidden(X2,X0) )
        | k1_relat_1(X1) != X0
        | k6_relat_1(X0) != X1 )
      & ( ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 )
        | k6_relat_1(X0) = X1 )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ( ? [X2] :
            ( k1_funct_1(X1,X2) != X2
            & r2_hidden(X2,X0) )
        | k1_relat_1(X1) != X0
        | k6_relat_1(X0) != X1 )
      & ( ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 )
        | k6_relat_1(X0) = X1 )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ( ? [X2] :
            ( k1_funct_1(X1,X2) != X2
            & r2_hidden(X2,X0) )
        | k1_relat_1(X1) != X0
        | k6_relat_1(X0) != X1 )
      & ( ( ! [X3] :
              ( k1_funct_1(X1,X3) = X3
              | ~ r2_hidden(X3,X0) )
          & k1_relat_1(X1) = X0 )
        | k6_relat_1(X0) = X1 )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(rectify,[],[f20])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k1_funct_1(X1,X2) != X2
          & r2_hidden(X2,X0) )
     => ( k1_funct_1(X1,sK4) != sK4
        & r2_hidden(sK4,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( ( ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0
          | k6_relat_1(X0) != X1 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) = X1 )
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ( ? [X2] :
            ( k1_funct_1(sK3,X2) != X2
            & r2_hidden(X2,sK2) )
        | k1_relat_1(sK3) != sK2
        | k6_relat_1(sK2) != sK3 )
      & ( ( ! [X3] :
              ( k1_funct_1(sK3,X3) = X3
              | ~ r2_hidden(X3,sK2) )
          & k1_relat_1(sK3) = sK2 )
        | k6_relat_1(sK2) = sK3 )
      & v1_funct_1(sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ( ( k1_funct_1(sK3,sK4) != sK4
        & r2_hidden(sK4,sK2) )
      | k1_relat_1(sK3) != sK2
      | k6_relat_1(sK2) != sK3 )
    & ( ( ! [X3] :
            ( k1_funct_1(sK3,X3) = X3
            | ~ r2_hidden(X3,sK2) )
        & k1_relat_1(sK3) = sK2 )
      | k6_relat_1(sK2) = sK3 )
    & v1_funct_1(sK3)
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f21,f23,f22])).

fof(f39,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f38,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f40,plain,
    ( k1_relat_1(sK3) = sK2
    | k6_relat_1(sK2) = sK3 ),
    inference(cnf_transformation,[],[f24])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = X1
      | r2_hidden(sK0(X0,X1),X0)
      | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f48,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f37])).

fof(f27,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | X4 != X5
      | ~ r2_hidden(X4,X0)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f44,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X5),X1)
      | ~ r2_hidden(X5,X0)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f27])).

fof(f45,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,X5),k6_relat_1(X0))
      | ~ r2_hidden(X5,X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f44])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f34,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f42,plain,
    ( r2_hidden(sK4,sK2)
    | k1_relat_1(sK3) != sK2
    | k6_relat_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f24])).

fof(f43,plain,
    ( k1_funct_1(sK3,sK4) != sK4
    | k1_relat_1(sK3) != sK2
    | k6_relat_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f24])).

fof(f41,plain,(
    ! [X3] :
      ( k1_funct_1(sK3,X3) = X3
      | ~ r2_hidden(X3,sK2)
      | k6_relat_1(sK2) = sK3 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f31,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = X1
      | sK0(X0,X1) != sK1(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X0)
      | ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_1,plain,
    ( r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)
    | ~ v1_relat_1(X1)
    | sK1(X0,X1) = sK0(X0,X1)
    | k6_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_830,plain,
    ( sK1(X0,X1) = sK0(X0,X1)
    | k6_relat_1(X0) = X1
    | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_11,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_17,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_263,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_17])).

cnf(c_264,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK3)
    | ~ v1_relat_1(sK3)
    | k1_funct_1(sK3,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_263])).

cnf(c_18,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_268,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK3)
    | k1_funct_1(sK3,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_264,c_18])).

cnf(c_816,plain,
    ( k1_funct_1(sK3,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_268])).

cnf(c_1894,plain,
    ( k1_funct_1(sK3,sK0(X0,sK3)) = sK1(X0,sK3)
    | sK1(X0,sK3) = sK0(X0,sK3)
    | k6_relat_1(X0) = sK3
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_830,c_816])).

cnf(c_1976,plain,
    ( ~ v1_relat_1(sK3)
    | k1_funct_1(sK3,sK0(X0,sK3)) = sK1(X0,sK3)
    | sK1(X0,sK3) = sK0(X0,sK3)
    | k6_relat_1(X0) = sK3 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1894])).

cnf(c_5145,plain,
    ( k6_relat_1(X0) = sK3
    | sK1(X0,sK3) = sK0(X0,sK3)
    | k1_funct_1(sK3,sK0(X0,sK3)) = sK1(X0,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1894,c_18,c_1976])).

cnf(c_5146,plain,
    ( k1_funct_1(sK3,sK0(X0,sK3)) = sK1(X0,sK3)
    | sK1(X0,sK3) = sK0(X0,sK3)
    | k6_relat_1(X0) = sK3 ),
    inference(renaming,[status(thm)],[c_5145])).

cnf(c_16,negated_conjecture,
    ( k1_relat_1(sK3) = sK2
    | k6_relat_1(sK2) = sK3 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_2,plain,
    ( r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)
    | r2_hidden(sK0(X0,X1),X0)
    | ~ v1_relat_1(X1)
    | k6_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_829,plain,
    ( k6_relat_1(X0) = X1
    | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) = iProver_top
    | r2_hidden(sK0(X0,X1),X0) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_12,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_227,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_17])).

cnf(c_228,plain,
    ( r2_hidden(X0,k1_relat_1(sK3))
    | ~ r2_hidden(k4_tarski(X0,X1),sK3)
    | ~ v1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_227])).

cnf(c_232,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK3)
    | r2_hidden(X0,k1_relat_1(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_228,c_18])).

cnf(c_233,plain,
    ( r2_hidden(X0,k1_relat_1(sK3))
    | ~ r2_hidden(k4_tarski(X0,X1),sK3) ),
    inference(renaming,[status(thm)],[c_232])).

cnf(c_818,plain,
    ( r2_hidden(X0,k1_relat_1(sK3)) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_233])).

cnf(c_1768,plain,
    ( k6_relat_1(X0) = sK3
    | r2_hidden(sK0(X0,sK3),X0) = iProver_top
    | r2_hidden(sK0(X0,sK3),k1_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_829,c_818])).

cnf(c_19,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3059,plain,
    ( r2_hidden(sK0(X0,sK3),k1_relat_1(sK3)) = iProver_top
    | r2_hidden(sK0(X0,sK3),X0) = iProver_top
    | k6_relat_1(X0) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1768,c_19])).

cnf(c_3060,plain,
    ( k6_relat_1(X0) = sK3
    | r2_hidden(sK0(X0,sK3),X0) = iProver_top
    | r2_hidden(sK0(X0,sK3),k1_relat_1(sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_3059])).

cnf(c_3068,plain,
    ( k6_relat_1(X0) = sK3
    | k6_relat_1(sK2) = sK3
    | r2_hidden(sK0(X0,sK3),X0) = iProver_top
    | r2_hidden(sK0(X0,sK3),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_16,c_3060])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_245,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_relat_1(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_17])).

cnf(c_246,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3)
    | ~ v1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_245])).

cnf(c_250,plain,
    ( r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3)
    | ~ r2_hidden(X0,k1_relat_1(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_246,c_18])).

cnf(c_251,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3) ),
    inference(renaming,[status(thm)],[c_250])).

cnf(c_817,plain,
    ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_251])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k4_tarski(X0,X0),k6_relat_1(X1))
    | ~ v1_relat_1(k6_relat_1(X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_828,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(k4_tarski(X0,X0),k6_relat_1(X1)) = iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_9,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_825,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_897,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(k4_tarski(X0,X0),k6_relat_1(X1)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_828,c_825])).

cnf(c_8,plain,
    ( v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_210,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1
    | k6_relat_1(X3) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_11])).

cnf(c_211,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),k6_relat_1(X2))
    | ~ v1_relat_1(k6_relat_1(X2))
    | k1_funct_1(k6_relat_1(X2),X0) = X1 ),
    inference(unflattening,[status(thm)],[c_210])).

cnf(c_221,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),k6_relat_1(X2))
    | k1_funct_1(k6_relat_1(X2),X0) = X1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_211,c_9])).

cnf(c_819,plain,
    ( k1_funct_1(k6_relat_1(X0),X1) = X2
    | r2_hidden(k4_tarski(X1,X2),k6_relat_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_221])).

cnf(c_1342,plain,
    ( k1_funct_1(k6_relat_1(X0),X1) = X1
    | r2_hidden(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_897,c_819])).

cnf(c_1349,plain,
    ( k1_funct_1(k6_relat_1(k6_relat_1(X0)),k4_tarski(X1,X1)) = k4_tarski(X1,X1)
    | r2_hidden(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_897,c_1342])).

cnf(c_1598,plain,
    ( k1_funct_1(k6_relat_1(k6_relat_1(sK3)),k4_tarski(k4_tarski(X0,k1_funct_1(sK3,X0)),k4_tarski(X0,k1_funct_1(sK3,X0)))) = k4_tarski(k4_tarski(X0,k1_funct_1(sK3,X0)),k4_tarski(X0,k1_funct_1(sK3,X0)))
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_817,c_1349])).

cnf(c_6235,plain,
    ( k1_funct_1(k6_relat_1(k6_relat_1(sK3)),k4_tarski(k4_tarski(sK0(k1_relat_1(sK3),sK3),k1_funct_1(sK3,sK0(k1_relat_1(sK3),sK3))),k4_tarski(sK0(k1_relat_1(sK3),sK3),k1_funct_1(sK3,sK0(k1_relat_1(sK3),sK3))))) = k4_tarski(k4_tarski(sK0(k1_relat_1(sK3),sK3),k1_funct_1(sK3,sK0(k1_relat_1(sK3),sK3))),k4_tarski(sK0(k1_relat_1(sK3),sK3),k1_funct_1(sK3,sK0(k1_relat_1(sK3),sK3))))
    | k6_relat_1(k1_relat_1(sK3)) = sK3
    | k6_relat_1(sK2) = sK3
    | r2_hidden(sK0(k1_relat_1(sK3),sK3),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3068,c_1598])).

cnf(c_6245,plain,
    ( k1_funct_1(k6_relat_1(k6_relat_1(sK3)),k4_tarski(k4_tarski(X0,k1_funct_1(sK3,X0)),k4_tarski(X0,k1_funct_1(sK3,X0)))) = k4_tarski(k4_tarski(X0,k1_funct_1(sK3,X0)),k4_tarski(X0,k1_funct_1(sK3,X0)))
    | k6_relat_1(sK2) = sK3
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_16,c_1598])).

cnf(c_6316,plain,
    ( k1_funct_1(k6_relat_1(k6_relat_1(sK3)),k4_tarski(k4_tarski(sK0(k1_relat_1(sK3),sK3),k1_funct_1(sK3,sK0(k1_relat_1(sK3),sK3))),k4_tarski(sK0(k1_relat_1(sK3),sK3),k1_funct_1(sK3,sK0(k1_relat_1(sK3),sK3))))) = k4_tarski(k4_tarski(sK0(k1_relat_1(sK3),sK3),k1_funct_1(sK3,sK0(k1_relat_1(sK3),sK3))),k4_tarski(sK0(k1_relat_1(sK3),sK3),k1_funct_1(sK3,sK0(k1_relat_1(sK3),sK3))))
    | k6_relat_1(k1_relat_1(sK3)) = sK3
    | k6_relat_1(sK2) = sK3 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6235,c_6245])).

cnf(c_13111,plain,
    ( k1_funct_1(k6_relat_1(k6_relat_1(sK3)),k4_tarski(k4_tarski(sK0(sK2,sK3),k1_funct_1(sK3,sK0(sK2,sK3))),k4_tarski(sK0(sK2,sK3),k1_funct_1(sK3,sK0(sK2,sK3))))) = k4_tarski(k4_tarski(sK0(k1_relat_1(sK3),sK3),k1_funct_1(sK3,sK0(k1_relat_1(sK3),sK3))),k4_tarski(sK0(k1_relat_1(sK3),sK3),k1_funct_1(sK3,sK0(k1_relat_1(sK3),sK3))))
    | k6_relat_1(k1_relat_1(sK3)) = sK3
    | k6_relat_1(sK2) = sK3 ),
    inference(superposition,[status(thm)],[c_16,c_6316])).

cnf(c_13515,plain,
    ( k4_tarski(k4_tarski(sK0(k1_relat_1(sK3),sK3),k1_funct_1(sK3,sK0(k1_relat_1(sK3),sK3))),k4_tarski(sK0(k1_relat_1(sK3),sK3),k1_funct_1(sK3,sK0(k1_relat_1(sK3),sK3)))) = k1_funct_1(k6_relat_1(k6_relat_1(sK3)),k4_tarski(k4_tarski(sK0(sK2,sK3),sK1(sK2,sK3)),k4_tarski(sK0(sK2,sK3),sK1(sK2,sK3))))
    | sK1(sK2,sK3) = sK0(sK2,sK3)
    | k6_relat_1(k1_relat_1(sK3)) = sK3
    | k6_relat_1(sK2) = sK3 ),
    inference(superposition,[status(thm)],[c_5146,c_13111])).

cnf(c_14,negated_conjecture,
    ( r2_hidden(sK4,sK2)
    | k1_relat_1(sK3) != sK2
    | k6_relat_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_518,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_535,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_518])).

cnf(c_519,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1124,plain,
    ( k6_relat_1(sK2) != X0
    | sK3 != X0
    | sK3 = k6_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_519])).

cnf(c_1125,plain,
    ( k6_relat_1(sK2) != sK3
    | sK3 = k6_relat_1(sK2)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1124])).

cnf(c_1213,plain,
    ( r2_hidden(k4_tarski(sK4,sK4),k6_relat_1(sK2))
    | ~ r2_hidden(sK4,sK2)
    | ~ v1_relat_1(k6_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1253,plain,
    ( v1_relat_1(k6_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_13,negated_conjecture,
    ( k1_funct_1(sK3,sK4) != sK4
    | k1_relat_1(sK3) != sK2
    | k6_relat_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_3714,plain,
    ( ~ r2_hidden(k4_tarski(sK4,sK4),sK3)
    | k1_relat_1(sK3) != sK2
    | k6_relat_1(sK2) != sK3 ),
    inference(resolution,[status(thm)],[c_268,c_13])).

cnf(c_15,negated_conjecture,
    ( ~ r2_hidden(X0,sK2)
    | k1_funct_1(sK3,X0) = X0
    | k6_relat_1(sK2) = sK3 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_823,plain,
    ( k1_funct_1(sK3,X0) = X0
    | k6_relat_1(sK2) = sK3
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3075,plain,
    ( k1_funct_1(sK3,sK0(sK2,sK3)) = sK0(sK2,sK3)
    | k6_relat_1(sK2) = sK3
    | r2_hidden(sK0(sK2,sK3),k1_relat_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3060,c_823])).

cnf(c_1205,plain,
    ( ~ r2_hidden(sK0(sK2,sK3),sK2)
    | k1_funct_1(sK3,sK0(sK2,sK3)) = sK0(sK2,sK3)
    | k6_relat_1(sK2) = sK3 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1206,plain,
    ( k1_funct_1(sK3,sK0(sK2,sK3)) = sK0(sK2,sK3)
    | k6_relat_1(sK2) = sK3
    | r2_hidden(sK0(sK2,sK3),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1205])).

cnf(c_3213,plain,
    ( k6_relat_1(sK2) = sK3
    | r2_hidden(sK0(sK2,sK3),sK2) = iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_3068])).

cnf(c_3215,plain,
    ( k6_relat_1(sK2) = sK3
    | r2_hidden(sK0(sK2,sK3),sK2) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3213])).

cnf(c_3626,plain,
    ( k6_relat_1(sK2) = sK3
    | k1_funct_1(sK3,sK0(sK2,sK3)) = sK0(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3075,c_1206,c_3215])).

cnf(c_3627,plain,
    ( k1_funct_1(sK3,sK0(sK2,sK3)) = sK0(sK2,sK3)
    | k6_relat_1(sK2) = sK3 ),
    inference(renaming,[status(thm)],[c_3626])).

cnf(c_5155,plain,
    ( sK1(sK2,sK3) = sK0(sK2,sK3)
    | k6_relat_1(sK2) = sK3 ),
    inference(superposition,[status(thm)],[c_5146,c_3627])).

cnf(c_521,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_6,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_3347,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k2_relat_1(k6_relat_1(X1)))
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_521,c_6])).

cnf(c_1998,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_519,c_518])).

cnf(c_4986,plain,
    ( k6_relat_1(sK2) = sK3
    | sK2 = k1_relat_1(sK3) ),
    inference(resolution,[status(thm)],[c_1998,c_16])).

cnf(c_9324,plain,
    ( r2_hidden(k6_relat_1(sK2),k2_relat_1(k6_relat_1(X0)))
    | ~ r2_hidden(sK3,X0)
    | sK2 = k1_relat_1(sK3) ),
    inference(resolution,[status(thm)],[c_3347,c_4986])).

cnf(c_1406,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_518])).

cnf(c_7,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_1433,plain,
    ( k1_relat_1(k6_relat_1(sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1162,plain,
    ( X0 != X1
    | sK2 != X1
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_519])).

cnf(c_1405,plain,
    ( X0 != sK2
    | sK2 = X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1162])).

cnf(c_2516,plain,
    ( k1_relat_1(k6_relat_1(sK2)) != sK2
    | sK2 = k1_relat_1(k6_relat_1(sK2))
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1405])).

cnf(c_525,plain,
    ( X0 != X1
    | k1_relat_1(X0) = k1_relat_1(X1) ),
    theory(equality)).

cnf(c_3795,plain,
    ( X0 != k6_relat_1(sK2)
    | k1_relat_1(X0) = k1_relat_1(k6_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_525])).

cnf(c_3800,plain,
    ( k1_relat_1(sK3) = k1_relat_1(k6_relat_1(sK2))
    | sK3 != k6_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_3795])).

cnf(c_5390,plain,
    ( sK2 = k1_relat_1(sK3)
    | sK3 = k6_relat_1(sK2) ),
    inference(resolution,[status(thm)],[c_4986,c_1998])).

cnf(c_2961,plain,
    ( X0 != k1_relat_1(k6_relat_1(sK2))
    | sK2 = X0
    | sK2 != k1_relat_1(k6_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_1162])).

cnf(c_10150,plain,
    ( k1_relat_1(X0) != k1_relat_1(k6_relat_1(sK2))
    | sK2 = k1_relat_1(X0)
    | sK2 != k1_relat_1(k6_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_2961])).

cnf(c_10152,plain,
    ( k1_relat_1(sK3) != k1_relat_1(k6_relat_1(sK2))
    | sK2 != k1_relat_1(k6_relat_1(sK2))
    | sK2 = k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_10150])).

cnf(c_11040,plain,
    ( sK2 = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9324,c_1406,c_1433,c_2516,c_3800,c_5390,c_10152])).

cnf(c_11047,plain,
    ( k1_relat_1(sK3) = sK2 ),
    inference(resolution,[status(thm)],[c_11040,c_1998])).

cnf(c_10181,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(sK4,sK4),k6_relat_1(sK2))
    | X0 != k4_tarski(sK4,sK4)
    | X1 != k6_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_521])).

cnf(c_15314,plain,
    ( r2_hidden(k4_tarski(sK4,sK4),X0)
    | ~ r2_hidden(k4_tarski(sK4,sK4),k6_relat_1(sK2))
    | X0 != k6_relat_1(sK2)
    | k4_tarski(sK4,sK4) != k4_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_10181])).

cnf(c_15317,plain,
    ( ~ r2_hidden(k4_tarski(sK4,sK4),k6_relat_1(sK2))
    | r2_hidden(k4_tarski(sK4,sK4),sK3)
    | k4_tarski(sK4,sK4) != k4_tarski(sK4,sK4)
    | sK3 != k6_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_15314])).

cnf(c_15315,plain,
    ( k4_tarski(sK4,sK4) = k4_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_518])).

cnf(c_15584,plain,
    ( sK1(sK2,sK3) = sK0(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13515,c_14,c_535,c_1125,c_1213,c_1253,c_3714,c_5155,c_11047,c_15317,c_15315])).

cnf(c_0,plain,
    ( ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)
    | ~ r2_hidden(sK0(X0,X1),X0)
    | ~ v1_relat_1(X1)
    | sK1(X0,X1) != sK0(X0,X1)
    | k6_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_831,plain,
    ( sK1(X0,X1) != sK0(X0,X1)
    | k6_relat_1(X0) = X1
    | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) != iProver_top
    | r2_hidden(sK0(X0,X1),X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_15587,plain,
    ( k6_relat_1(sK2) = sK3
    | r2_hidden(k4_tarski(sK0(sK2,sK3),sK1(sK2,sK3)),sK3) != iProver_top
    | r2_hidden(sK0(sK2,sK3),sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_15584,c_831])).

cnf(c_15595,plain,
    ( k6_relat_1(sK2) = sK3
    | r2_hidden(k4_tarski(sK0(sK2,sK3),sK0(sK2,sK3)),sK3) != iProver_top
    | r2_hidden(sK0(sK2,sK3),sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_15587,c_15584])).

cnf(c_1350,plain,
    ( k1_funct_1(k6_relat_1(sK3),k4_tarski(X0,k1_funct_1(sK3,X0))) = k4_tarski(X0,k1_funct_1(sK3,X0))
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_817,c_1342])).

cnf(c_3208,plain,
    ( k1_funct_1(k6_relat_1(sK3),k4_tarski(sK0(k1_relat_1(sK3),sK3),k1_funct_1(sK3,sK0(k1_relat_1(sK3),sK3)))) = k4_tarski(sK0(k1_relat_1(sK3),sK3),k1_funct_1(sK3,sK0(k1_relat_1(sK3),sK3)))
    | k6_relat_1(k1_relat_1(sK3)) = sK3
    | k6_relat_1(sK2) = sK3
    | r2_hidden(sK0(k1_relat_1(sK3),sK3),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3068,c_1350])).

cnf(c_1484,plain,
    ( k1_funct_1(k6_relat_1(sK3),k4_tarski(X0,k1_funct_1(sK3,X0))) = k4_tarski(X0,k1_funct_1(sK3,X0))
    | k6_relat_1(sK2) = sK3
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_16,c_1350])).

cnf(c_7282,plain,
    ( k1_funct_1(k6_relat_1(sK3),k4_tarski(sK0(k1_relat_1(sK3),sK3),k1_funct_1(sK3,sK0(k1_relat_1(sK3),sK3)))) = k4_tarski(sK0(k1_relat_1(sK3),sK3),k1_funct_1(sK3,sK0(k1_relat_1(sK3),sK3)))
    | k6_relat_1(k1_relat_1(sK3)) = sK3
    | k6_relat_1(sK2) = sK3 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3208,c_1484])).

cnf(c_7286,plain,
    ( k1_funct_1(k6_relat_1(sK3),k4_tarski(sK0(sK2,sK3),k1_funct_1(sK3,sK0(sK2,sK3)))) = k4_tarski(sK0(k1_relat_1(sK3),sK3),k1_funct_1(sK3,sK0(k1_relat_1(sK3),sK3)))
    | k6_relat_1(k1_relat_1(sK3)) = sK3
    | k6_relat_1(sK2) = sK3 ),
    inference(superposition,[status(thm)],[c_16,c_7282])).

cnf(c_193,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_relat_1(X1)
    | k6_relat_1(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_10])).

cnf(c_194,plain,
    ( ~ r2_hidden(X0,k1_relat_1(k6_relat_1(X1)))
    | r2_hidden(k4_tarski(X0,k1_funct_1(k6_relat_1(X1),X0)),k6_relat_1(X1))
    | ~ v1_relat_1(k6_relat_1(X1)) ),
    inference(unflattening,[status(thm)],[c_193])).

cnf(c_204,plain,
    ( ~ r2_hidden(X0,k1_relat_1(k6_relat_1(X1)))
    | r2_hidden(k4_tarski(X0,k1_funct_1(k6_relat_1(X1),X0)),k6_relat_1(X1)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_194,c_9])).

cnf(c_820,plain,
    ( r2_hidden(X0,k1_relat_1(k6_relat_1(X1))) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(k6_relat_1(X1),X0)),k6_relat_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_204])).

cnf(c_883,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(k6_relat_1(X1),X0)),k6_relat_1(X1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_820,c_7])).

cnf(c_7507,plain,
    ( k6_relat_1(k1_relat_1(sK3)) = sK3
    | k6_relat_1(sK2) = sK3
    | r2_hidden(k4_tarski(k4_tarski(sK0(sK2,sK3),k1_funct_1(sK3,sK0(sK2,sK3))),k4_tarski(sK0(k1_relat_1(sK3),sK3),k1_funct_1(sK3,sK0(k1_relat_1(sK3),sK3)))),k6_relat_1(sK3)) = iProver_top
    | r2_hidden(k4_tarski(sK0(sK2,sK3),k1_funct_1(sK3,sK0(sK2,sK3))),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7286,c_883])).

cnf(c_3081,plain,
    ( k6_relat_1(k1_relat_1(sK3)) = sK3
    | r2_hidden(sK0(k1_relat_1(sK3),sK3),k1_relat_1(sK3)) = iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_3060])).

cnf(c_3083,plain,
    ( k6_relat_1(k1_relat_1(sK3)) = sK3
    | r2_hidden(sK0(k1_relat_1(sK3),sK3),k1_relat_1(sK3)) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3081])).

cnf(c_3074,plain,
    ( k1_funct_1(k6_relat_1(sK3),k4_tarski(sK0(sK2,sK3),k1_funct_1(sK3,sK0(sK2,sK3)))) = k4_tarski(sK0(sK2,sK3),k1_funct_1(sK3,sK0(sK2,sK3)))
    | k6_relat_1(sK2) = sK3
    | r2_hidden(sK0(sK2,sK3),k1_relat_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3060,c_1484])).

cnf(c_4539,plain,
    ( k1_funct_1(k6_relat_1(sK3),k4_tarski(sK0(sK2,sK3),k1_funct_1(sK3,sK0(sK2,sK3)))) = k4_tarski(sK0(sK2,sK3),k1_funct_1(sK3,sK0(sK2,sK3)))
    | k6_relat_1(sK2) = sK3 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3074,c_1350])).

cnf(c_7509,plain,
    ( k4_tarski(sK0(k1_relat_1(sK3),sK3),k1_funct_1(sK3,sK0(k1_relat_1(sK3),sK3))) = k4_tarski(sK0(sK2,sK3),k1_funct_1(sK3,sK0(sK2,sK3)))
    | k6_relat_1(k1_relat_1(sK3)) = sK3
    | k6_relat_1(sK2) = sK3 ),
    inference(superposition,[status(thm)],[c_7286,c_4539])).

cnf(c_7556,plain,
    ( k6_relat_1(k1_relat_1(sK3)) = sK3
    | k6_relat_1(sK2) = sK3
    | r2_hidden(k4_tarski(sK0(sK2,sK3),k1_funct_1(sK3,sK0(sK2,sK3))),sK3) = iProver_top
    | r2_hidden(sK0(k1_relat_1(sK3),sK3),k1_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7509,c_817])).

cnf(c_9826,plain,
    ( r2_hidden(k4_tarski(k4_tarski(sK0(sK2,sK3),k1_funct_1(sK3,sK0(sK2,sK3))),k4_tarski(sK0(k1_relat_1(sK3),sK3),k1_funct_1(sK3,sK0(k1_relat_1(sK3),sK3)))),k6_relat_1(sK3)) = iProver_top
    | k6_relat_1(sK2) = sK3
    | k6_relat_1(k1_relat_1(sK3)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7507,c_3083,c_7556])).

cnf(c_9827,plain,
    ( k6_relat_1(k1_relat_1(sK3)) = sK3
    | k6_relat_1(sK2) = sK3
    | r2_hidden(k4_tarski(k4_tarski(sK0(sK2,sK3),k1_funct_1(sK3,sK0(sK2,sK3))),k4_tarski(sK0(k1_relat_1(sK3),sK3),k1_funct_1(sK3,sK0(k1_relat_1(sK3),sK3)))),k6_relat_1(sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_9826])).

cnf(c_9841,plain,
    ( k6_relat_1(k1_relat_1(sK3)) = sK3
    | k6_relat_1(sK2) = sK3
    | r2_hidden(k4_tarski(k4_tarski(sK0(sK2,sK3),k1_funct_1(sK3,sK0(sK2,sK3))),k4_tarski(sK0(sK2,sK3),k1_funct_1(sK3,sK0(sK2,sK3)))),k6_relat_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_16,c_9827])).

cnf(c_9950,plain,
    ( k6_relat_1(k1_relat_1(sK3)) = sK3
    | k6_relat_1(sK2) = sK3
    | r2_hidden(k4_tarski(k4_tarski(sK0(sK2,sK3),sK0(sK2,sK3)),k4_tarski(sK0(sK2,sK3),sK0(sK2,sK3))),k6_relat_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3627,c_9841])).

cnf(c_34,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_36,plain,
    ( v1_relat_1(k6_relat_1(sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_34])).

cnf(c_1288,plain,
    ( sK0(sK2,sK3) = sK0(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_518])).

cnf(c_3509,plain,
    ( r2_hidden(k4_tarski(k4_tarski(sK0(sK2,sK3),sK0(sK2,sK3)),k4_tarski(sK0(sK2,sK3),sK0(sK2,sK3))),k6_relat_1(X0))
    | ~ r2_hidden(k4_tarski(sK0(sK2,sK3),sK0(sK2,sK3)),X0)
    | ~ v1_relat_1(k6_relat_1(X0)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3510,plain,
    ( r2_hidden(k4_tarski(k4_tarski(sK0(sK2,sK3),sK0(sK2,sK3)),k4_tarski(sK0(sK2,sK3),sK0(sK2,sK3))),k6_relat_1(X0)) = iProver_top
    | r2_hidden(k4_tarski(sK0(sK2,sK3),sK0(sK2,sK3)),X0) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3509])).

cnf(c_3512,plain,
    ( r2_hidden(k4_tarski(k4_tarski(sK0(sK2,sK3),sK0(sK2,sK3)),k4_tarski(sK0(sK2,sK3),sK0(sK2,sK3))),k6_relat_1(sK3)) = iProver_top
    | r2_hidden(k4_tarski(sK0(sK2,sK3),sK0(sK2,sK3)),sK3) != iProver_top
    | v1_relat_1(k6_relat_1(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3510])).

cnf(c_3630,plain,
    ( k6_relat_1(sK2) = sK3
    | r2_hidden(k4_tarski(sK0(sK2,sK3),sK0(sK2,sK3)),sK3) = iProver_top
    | r2_hidden(sK0(sK2,sK3),k1_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3627,c_817])).

cnf(c_1197,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK0(sK2,sK3),sK2)
    | X0 != sK0(sK2,sK3)
    | X1 != sK2 ),
    inference(instantiation,[status(thm)],[c_521])).

cnf(c_1287,plain,
    ( r2_hidden(sK0(sK2,sK3),X0)
    | ~ r2_hidden(sK0(sK2,sK3),sK2)
    | X0 != sK2
    | sK0(sK2,sK3) != sK0(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1197])).

cnf(c_10165,plain,
    ( r2_hidden(sK0(sK2,sK3),k1_relat_1(sK3))
    | ~ r2_hidden(sK0(sK2,sK3),sK2)
    | sK0(sK2,sK3) != sK0(sK2,sK3)
    | k1_relat_1(sK3) != sK2 ),
    inference(instantiation,[status(thm)],[c_1287])).

cnf(c_10172,plain,
    ( sK0(sK2,sK3) != sK0(sK2,sK3)
    | k1_relat_1(sK3) != sK2
    | r2_hidden(sK0(sK2,sK3),k1_relat_1(sK3)) = iProver_top
    | r2_hidden(sK0(sK2,sK3),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10165])).

cnf(c_10270,plain,
    ( k6_relat_1(sK2) = sK3
    | r2_hidden(k4_tarski(k4_tarski(sK0(sK2,sK3),sK0(sK2,sK3)),k4_tarski(sK0(sK2,sK3),sK0(sK2,sK3))),k6_relat_1(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9950,c_16,c_36,c_1288,c_3215,c_3512,c_3630,c_10172])).

cnf(c_176,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1)
    | k6_relat_1(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_12])).

cnf(c_177,plain,
    ( r2_hidden(X0,k1_relat_1(k6_relat_1(X1)))
    | ~ r2_hidden(k4_tarski(X0,X2),k6_relat_1(X1))
    | ~ v1_relat_1(k6_relat_1(X1)) ),
    inference(unflattening,[status(thm)],[c_176])).

cnf(c_187,plain,
    ( r2_hidden(X0,k1_relat_1(k6_relat_1(X1)))
    | ~ r2_hidden(k4_tarski(X0,X2),k6_relat_1(X1)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_177,c_9])).

cnf(c_821,plain,
    ( r2_hidden(X0,k1_relat_1(k6_relat_1(X1))) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),k6_relat_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_187])).

cnf(c_860,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),k6_relat_1(X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_821,c_7])).

cnf(c_10276,plain,
    ( k6_relat_1(sK2) = sK3
    | r2_hidden(k4_tarski(sK0(sK2,sK3),sK0(sK2,sK3)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_10270,c_860])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_15595,c_15315,c_15317,c_11047,c_10276,c_3714,c_3215,c_1253,c_1213,c_1125,c_535,c_14,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:07:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 4.03/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.03/1.00  
% 4.03/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.03/1.00  
% 4.03/1.00  ------  iProver source info
% 4.03/1.00  
% 4.03/1.00  git: date: 2020-06-30 10:37:57 +0100
% 4.03/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.03/1.00  git: non_committed_changes: false
% 4.03/1.00  git: last_make_outside_of_git: false
% 4.03/1.00  
% 4.03/1.00  ------ 
% 4.03/1.00  ------ Parsing...
% 4.03/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.03/1.00  
% 4.03/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e 
% 4.03/1.00  
% 4.03/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.03/1.00  
% 4.03/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.03/1.00  ------ Proving...
% 4.03/1.00  ------ Problem Properties 
% 4.03/1.00  
% 4.03/1.00  
% 4.03/1.00  clauses                                 20
% 4.03/1.00  conjectures                             5
% 4.03/1.00  EPR                                     1
% 4.03/1.00  Horn                                    16
% 4.03/1.00  unary                                   4
% 4.03/1.00  binary                                  7
% 4.03/1.00  lits                                    49
% 4.03/1.00  lits eq                                 19
% 4.03/1.00  fd_pure                                 0
% 4.03/1.00  fd_pseudo                               0
% 4.03/1.00  fd_cond                                 0
% 4.03/1.00  fd_pseudo_cond                          6
% 4.03/1.00  AC symbols                              0
% 4.03/1.00  
% 4.03/1.00  ------ Input Options Time Limit: Unbounded
% 4.03/1.00  
% 4.03/1.00  
% 4.03/1.00  ------ 
% 4.03/1.00  Current options:
% 4.03/1.00  ------ 
% 4.03/1.00  
% 4.03/1.00  
% 4.03/1.00  
% 4.03/1.00  
% 4.03/1.00  ------ Proving...
% 4.03/1.00  
% 4.03/1.00  
% 4.03/1.00  % SZS status Theorem for theBenchmark.p
% 4.03/1.00  
% 4.03/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 4.03/1.00  
% 4.03/1.00  fof(f1,axiom,(
% 4.03/1.00    ! [X0,X1] : (v1_relat_1(X1) => (k6_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> (X2 = X3 & r2_hidden(X2,X0)))))),
% 4.03/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.03/1.00  
% 4.03/1.00  fof(f7,plain,(
% 4.03/1.00    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> (X2 = X3 & r2_hidden(X2,X0)))) | ~v1_relat_1(X1))),
% 4.03/1.00    inference(ennf_transformation,[],[f1])).
% 4.03/1.00  
% 4.03/1.00  fof(f12,plain,(
% 4.03/1.00    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2,X3] : (((X2 != X3 | ~r2_hidden(X2,X0)) | ~r2_hidden(k4_tarski(X2,X3),X1)) & ((X2 = X3 & r2_hidden(X2,X0)) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) | (X2 != X3 | ~r2_hidden(X2,X0))) & ((X2 = X3 & r2_hidden(X2,X0)) | ~r2_hidden(k4_tarski(X2,X3),X1))) | k6_relat_1(X0) != X1)) | ~v1_relat_1(X1))),
% 4.03/1.00    inference(nnf_transformation,[],[f7])).
% 4.03/1.00  
% 4.03/1.00  fof(f13,plain,(
% 4.03/1.00    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2,X3] : ((X2 != X3 | ~r2_hidden(X2,X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & ((X2 = X3 & r2_hidden(X2,X0)) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) | X2 != X3 | ~r2_hidden(X2,X0)) & ((X2 = X3 & r2_hidden(X2,X0)) | ~r2_hidden(k4_tarski(X2,X3),X1))) | k6_relat_1(X0) != X1)) | ~v1_relat_1(X1))),
% 4.03/1.00    inference(flattening,[],[f12])).
% 4.03/1.00  
% 4.03/1.00  fof(f14,plain,(
% 4.03/1.00    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2,X3] : ((X2 != X3 | ~r2_hidden(X2,X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & ((X2 = X3 & r2_hidden(X2,X0)) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X1) | X4 != X5 | ~r2_hidden(X4,X0)) & ((X4 = X5 & r2_hidden(X4,X0)) | ~r2_hidden(k4_tarski(X4,X5),X1))) | k6_relat_1(X0) != X1)) | ~v1_relat_1(X1))),
% 4.03/1.00    inference(rectify,[],[f13])).
% 4.03/1.00  
% 4.03/1.00  fof(f15,plain,(
% 4.03/1.00    ! [X1,X0] : (? [X2,X3] : ((X2 != X3 | ~r2_hidden(X2,X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & ((X2 = X3 & r2_hidden(X2,X0)) | r2_hidden(k4_tarski(X2,X3),X1))) => ((sK0(X0,X1) != sK1(X0,X1) | ~r2_hidden(sK0(X0,X1),X0) | ~r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)) & ((sK0(X0,X1) = sK1(X0,X1) & r2_hidden(sK0(X0,X1),X0)) | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1))))),
% 4.03/1.00    introduced(choice_axiom,[])).
% 4.03/1.00  
% 4.03/1.00  fof(f16,plain,(
% 4.03/1.00    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ((sK0(X0,X1) != sK1(X0,X1) | ~r2_hidden(sK0(X0,X1),X0) | ~r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)) & ((sK0(X0,X1) = sK1(X0,X1) & r2_hidden(sK0(X0,X1),X0)) | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X1) | X4 != X5 | ~r2_hidden(X4,X0)) & ((X4 = X5 & r2_hidden(X4,X0)) | ~r2_hidden(k4_tarski(X4,X5),X1))) | k6_relat_1(X0) != X1)) | ~v1_relat_1(X1))),
% 4.03/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).
% 4.03/1.00  
% 4.03/1.00  fof(f29,plain,(
% 4.03/1.00    ( ! [X0,X1] : (k6_relat_1(X0) = X1 | sK0(X0,X1) = sK1(X0,X1) | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) | ~v1_relat_1(X1)) )),
% 4.03/1.00    inference(cnf_transformation,[],[f16])).
% 4.03/1.00  
% 4.03/1.00  fof(f4,axiom,(
% 4.03/1.00    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 4.03/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.03/1.00  
% 4.03/1.00  fof(f8,plain,(
% 4.03/1.00    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 4.03/1.00    inference(ennf_transformation,[],[f4])).
% 4.03/1.00  
% 4.03/1.00  fof(f9,plain,(
% 4.03/1.00    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 4.03/1.00    inference(flattening,[],[f8])).
% 4.03/1.00  
% 4.03/1.00  fof(f17,plain,(
% 4.03/1.00    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 4.03/1.00    inference(nnf_transformation,[],[f9])).
% 4.03/1.00  
% 4.03/1.00  fof(f18,plain,(
% 4.03/1.00    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 4.03/1.00    inference(flattening,[],[f17])).
% 4.03/1.00  
% 4.03/1.00  fof(f36,plain,(
% 4.03/1.00    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 4.03/1.00    inference(cnf_transformation,[],[f18])).
% 4.03/1.00  
% 4.03/1.00  fof(f5,conjecture,(
% 4.03/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(X0) = X1 <=> (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = X2) & k1_relat_1(X1) = X0)))),
% 4.03/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.03/1.00  
% 4.03/1.00  fof(f6,negated_conjecture,(
% 4.03/1.00    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(X0) = X1 <=> (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = X2) & k1_relat_1(X1) = X0)))),
% 4.03/1.00    inference(negated_conjecture,[],[f5])).
% 4.03/1.00  
% 4.03/1.00  fof(f10,plain,(
% 4.03/1.00    ? [X0,X1] : ((k6_relat_1(X0) = X1 <~> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 4.03/1.00    inference(ennf_transformation,[],[f6])).
% 4.03/1.00  
% 4.03/1.00  fof(f11,plain,(
% 4.03/1.00    ? [X0,X1] : ((k6_relat_1(X0) = X1 <~> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 4.03/1.00    inference(flattening,[],[f10])).
% 4.03/1.00  
% 4.03/1.00  fof(f19,plain,(
% 4.03/1.00    ? [X0,X1] : ((((? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) | k6_relat_1(X0) != X1) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) = X1)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 4.03/1.00    inference(nnf_transformation,[],[f11])).
% 4.03/1.00  
% 4.03/1.00  fof(f20,plain,(
% 4.03/1.00    ? [X0,X1] : ((? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0 | k6_relat_1(X0) != X1) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) = X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 4.03/1.00    inference(flattening,[],[f19])).
% 4.03/1.00  
% 4.03/1.00  fof(f21,plain,(
% 4.03/1.00    ? [X0,X1] : ((? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0 | k6_relat_1(X0) != X1) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) = X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 4.03/1.00    inference(rectify,[],[f20])).
% 4.03/1.00  
% 4.03/1.00  fof(f23,plain,(
% 4.03/1.00    ( ! [X0,X1] : (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) => (k1_funct_1(X1,sK4) != sK4 & r2_hidden(sK4,X0))) )),
% 4.03/1.00    introduced(choice_axiom,[])).
% 4.03/1.00  
% 4.03/1.00  fof(f22,plain,(
% 4.03/1.00    ? [X0,X1] : ((? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0 | k6_relat_1(X0) != X1) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) = X1) & v1_funct_1(X1) & v1_relat_1(X1)) => ((? [X2] : (k1_funct_1(sK3,X2) != X2 & r2_hidden(X2,sK2)) | k1_relat_1(sK3) != sK2 | k6_relat_1(sK2) != sK3) & ((! [X3] : (k1_funct_1(sK3,X3) = X3 | ~r2_hidden(X3,sK2)) & k1_relat_1(sK3) = sK2) | k6_relat_1(sK2) = sK3) & v1_funct_1(sK3) & v1_relat_1(sK3))),
% 4.03/1.00    introduced(choice_axiom,[])).
% 4.03/1.00  
% 4.03/1.00  fof(f24,plain,(
% 4.03/1.00    ((k1_funct_1(sK3,sK4) != sK4 & r2_hidden(sK4,sK2)) | k1_relat_1(sK3) != sK2 | k6_relat_1(sK2) != sK3) & ((! [X3] : (k1_funct_1(sK3,X3) = X3 | ~r2_hidden(X3,sK2)) & k1_relat_1(sK3) = sK2) | k6_relat_1(sK2) = sK3) & v1_funct_1(sK3) & v1_relat_1(sK3)),
% 4.03/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f21,f23,f22])).
% 4.03/1.00  
% 4.03/1.00  fof(f39,plain,(
% 4.03/1.00    v1_funct_1(sK3)),
% 4.03/1.00    inference(cnf_transformation,[],[f24])).
% 4.03/1.00  
% 4.03/1.00  fof(f38,plain,(
% 4.03/1.00    v1_relat_1(sK3)),
% 4.03/1.00    inference(cnf_transformation,[],[f24])).
% 4.03/1.00  
% 4.03/1.00  fof(f40,plain,(
% 4.03/1.00    k1_relat_1(sK3) = sK2 | k6_relat_1(sK2) = sK3),
% 4.03/1.00    inference(cnf_transformation,[],[f24])).
% 4.03/1.00  
% 4.03/1.00  fof(f28,plain,(
% 4.03/1.00    ( ! [X0,X1] : (k6_relat_1(X0) = X1 | r2_hidden(sK0(X0,X1),X0) | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) | ~v1_relat_1(X1)) )),
% 4.03/1.00    inference(cnf_transformation,[],[f16])).
% 4.03/1.00  
% 4.03/1.00  fof(f35,plain,(
% 4.03/1.00    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 4.03/1.00    inference(cnf_transformation,[],[f18])).
% 4.03/1.00  
% 4.03/1.00  fof(f37,plain,(
% 4.03/1.00    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 4.03/1.00    inference(cnf_transformation,[],[f18])).
% 4.03/1.00  
% 4.03/1.00  fof(f48,plain,(
% 4.03/1.00    ( ! [X2,X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 4.03/1.00    inference(equality_resolution,[],[f37])).
% 4.03/1.00  
% 4.03/1.00  fof(f27,plain,(
% 4.03/1.00    ( ! [X4,X0,X5,X1] : (r2_hidden(k4_tarski(X4,X5),X1) | X4 != X5 | ~r2_hidden(X4,X0) | k6_relat_1(X0) != X1 | ~v1_relat_1(X1)) )),
% 4.03/1.00    inference(cnf_transformation,[],[f16])).
% 4.03/1.00  
% 4.03/1.00  fof(f44,plain,(
% 4.03/1.00    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,X5),X1) | ~r2_hidden(X5,X0) | k6_relat_1(X0) != X1 | ~v1_relat_1(X1)) )),
% 4.03/1.00    inference(equality_resolution,[],[f27])).
% 4.03/1.00  
% 4.03/1.00  fof(f45,plain,(
% 4.03/1.00    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,X5),k6_relat_1(X0)) | ~r2_hidden(X5,X0) | ~v1_relat_1(k6_relat_1(X0))) )),
% 4.03/1.00    inference(equality_resolution,[],[f44])).
% 4.03/1.00  
% 4.03/1.00  fof(f3,axiom,(
% 4.03/1.00    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 4.03/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.03/1.00  
% 4.03/1.00  fof(f33,plain,(
% 4.03/1.00    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 4.03/1.00    inference(cnf_transformation,[],[f3])).
% 4.03/1.00  
% 4.03/1.00  fof(f34,plain,(
% 4.03/1.00    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 4.03/1.00    inference(cnf_transformation,[],[f3])).
% 4.03/1.00  
% 4.03/1.00  fof(f42,plain,(
% 4.03/1.00    r2_hidden(sK4,sK2) | k1_relat_1(sK3) != sK2 | k6_relat_1(sK2) != sK3),
% 4.03/1.00    inference(cnf_transformation,[],[f24])).
% 4.03/1.00  
% 4.03/1.00  fof(f43,plain,(
% 4.03/1.00    k1_funct_1(sK3,sK4) != sK4 | k1_relat_1(sK3) != sK2 | k6_relat_1(sK2) != sK3),
% 4.03/1.00    inference(cnf_transformation,[],[f24])).
% 4.03/1.00  
% 4.03/1.00  fof(f41,plain,(
% 4.03/1.00    ( ! [X3] : (k1_funct_1(sK3,X3) = X3 | ~r2_hidden(X3,sK2) | k6_relat_1(sK2) = sK3) )),
% 4.03/1.00    inference(cnf_transformation,[],[f24])).
% 4.03/1.00  
% 4.03/1.00  fof(f2,axiom,(
% 4.03/1.00    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 4.03/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.03/1.00  
% 4.03/1.00  fof(f32,plain,(
% 4.03/1.00    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 4.03/1.00    inference(cnf_transformation,[],[f2])).
% 4.03/1.00  
% 4.03/1.00  fof(f31,plain,(
% 4.03/1.00    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 4.03/1.00    inference(cnf_transformation,[],[f2])).
% 4.03/1.00  
% 4.03/1.00  fof(f30,plain,(
% 4.03/1.00    ( ! [X0,X1] : (k6_relat_1(X0) = X1 | sK0(X0,X1) != sK1(X0,X1) | ~r2_hidden(sK0(X0,X1),X0) | ~r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) | ~v1_relat_1(X1)) )),
% 4.03/1.00    inference(cnf_transformation,[],[f16])).
% 4.03/1.00  
% 4.03/1.00  cnf(c_1,plain,
% 4.03/1.00      ( r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)
% 4.03/1.00      | ~ v1_relat_1(X1)
% 4.03/1.00      | sK1(X0,X1) = sK0(X0,X1)
% 4.03/1.00      | k6_relat_1(X0) = X1 ),
% 4.03/1.00      inference(cnf_transformation,[],[f29]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_830,plain,
% 4.03/1.00      ( sK1(X0,X1) = sK0(X0,X1)
% 4.03/1.00      | k6_relat_1(X0) = X1
% 4.03/1.00      | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) = iProver_top
% 4.03/1.00      | v1_relat_1(X1) != iProver_top ),
% 4.03/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_11,plain,
% 4.03/1.00      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 4.03/1.00      | ~ v1_funct_1(X2)
% 4.03/1.00      | ~ v1_relat_1(X2)
% 4.03/1.00      | k1_funct_1(X2,X0) = X1 ),
% 4.03/1.00      inference(cnf_transformation,[],[f36]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_17,negated_conjecture,
% 4.03/1.00      ( v1_funct_1(sK3) ),
% 4.03/1.00      inference(cnf_transformation,[],[f39]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_263,plain,
% 4.03/1.00      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 4.03/1.00      | ~ v1_relat_1(X2)
% 4.03/1.00      | k1_funct_1(X2,X0) = X1
% 4.03/1.00      | sK3 != X2 ),
% 4.03/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_17]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_264,plain,
% 4.03/1.00      ( ~ r2_hidden(k4_tarski(X0,X1),sK3)
% 4.03/1.00      | ~ v1_relat_1(sK3)
% 4.03/1.00      | k1_funct_1(sK3,X0) = X1 ),
% 4.03/1.00      inference(unflattening,[status(thm)],[c_263]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_18,negated_conjecture,
% 4.03/1.00      ( v1_relat_1(sK3) ),
% 4.03/1.00      inference(cnf_transformation,[],[f38]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_268,plain,
% 4.03/1.00      ( ~ r2_hidden(k4_tarski(X0,X1),sK3) | k1_funct_1(sK3,X0) = X1 ),
% 4.03/1.00      inference(global_propositional_subsumption,
% 4.03/1.00                [status(thm)],
% 4.03/1.00                [c_264,c_18]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_816,plain,
% 4.03/1.00      ( k1_funct_1(sK3,X0) = X1
% 4.03/1.00      | r2_hidden(k4_tarski(X0,X1),sK3) != iProver_top ),
% 4.03/1.00      inference(predicate_to_equality,[status(thm)],[c_268]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_1894,plain,
% 4.03/1.00      ( k1_funct_1(sK3,sK0(X0,sK3)) = sK1(X0,sK3)
% 4.03/1.00      | sK1(X0,sK3) = sK0(X0,sK3)
% 4.03/1.00      | k6_relat_1(X0) = sK3
% 4.03/1.00      | v1_relat_1(sK3) != iProver_top ),
% 4.03/1.00      inference(superposition,[status(thm)],[c_830,c_816]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_1976,plain,
% 4.03/1.00      ( ~ v1_relat_1(sK3)
% 4.03/1.00      | k1_funct_1(sK3,sK0(X0,sK3)) = sK1(X0,sK3)
% 4.03/1.00      | sK1(X0,sK3) = sK0(X0,sK3)
% 4.03/1.00      | k6_relat_1(X0) = sK3 ),
% 4.03/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1894]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_5145,plain,
% 4.03/1.00      ( k6_relat_1(X0) = sK3
% 4.03/1.00      | sK1(X0,sK3) = sK0(X0,sK3)
% 4.03/1.00      | k1_funct_1(sK3,sK0(X0,sK3)) = sK1(X0,sK3) ),
% 4.03/1.00      inference(global_propositional_subsumption,
% 4.03/1.00                [status(thm)],
% 4.03/1.00                [c_1894,c_18,c_1976]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_5146,plain,
% 4.03/1.00      ( k1_funct_1(sK3,sK0(X0,sK3)) = sK1(X0,sK3)
% 4.03/1.00      | sK1(X0,sK3) = sK0(X0,sK3)
% 4.03/1.00      | k6_relat_1(X0) = sK3 ),
% 4.03/1.00      inference(renaming,[status(thm)],[c_5145]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_16,negated_conjecture,
% 4.03/1.00      ( k1_relat_1(sK3) = sK2 | k6_relat_1(sK2) = sK3 ),
% 4.03/1.00      inference(cnf_transformation,[],[f40]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_2,plain,
% 4.03/1.00      ( r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)
% 4.03/1.00      | r2_hidden(sK0(X0,X1),X0)
% 4.03/1.00      | ~ v1_relat_1(X1)
% 4.03/1.00      | k6_relat_1(X0) = X1 ),
% 4.03/1.00      inference(cnf_transformation,[],[f28]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_829,plain,
% 4.03/1.00      ( k6_relat_1(X0) = X1
% 4.03/1.00      | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) = iProver_top
% 4.03/1.00      | r2_hidden(sK0(X0,X1),X0) = iProver_top
% 4.03/1.00      | v1_relat_1(X1) != iProver_top ),
% 4.03/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_12,plain,
% 4.03/1.00      ( r2_hidden(X0,k1_relat_1(X1))
% 4.03/1.00      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 4.03/1.00      | ~ v1_funct_1(X1)
% 4.03/1.00      | ~ v1_relat_1(X1) ),
% 4.03/1.00      inference(cnf_transformation,[],[f35]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_227,plain,
% 4.03/1.00      ( r2_hidden(X0,k1_relat_1(X1))
% 4.03/1.00      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 4.03/1.00      | ~ v1_relat_1(X1)
% 4.03/1.00      | sK3 != X1 ),
% 4.03/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_17]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_228,plain,
% 4.03/1.00      ( r2_hidden(X0,k1_relat_1(sK3))
% 4.03/1.00      | ~ r2_hidden(k4_tarski(X0,X1),sK3)
% 4.03/1.00      | ~ v1_relat_1(sK3) ),
% 4.03/1.00      inference(unflattening,[status(thm)],[c_227]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_232,plain,
% 4.03/1.00      ( ~ r2_hidden(k4_tarski(X0,X1),sK3)
% 4.03/1.00      | r2_hidden(X0,k1_relat_1(sK3)) ),
% 4.03/1.00      inference(global_propositional_subsumption,
% 4.03/1.00                [status(thm)],
% 4.03/1.00                [c_228,c_18]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_233,plain,
% 4.03/1.00      ( r2_hidden(X0,k1_relat_1(sK3))
% 4.03/1.00      | ~ r2_hidden(k4_tarski(X0,X1),sK3) ),
% 4.03/1.00      inference(renaming,[status(thm)],[c_232]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_818,plain,
% 4.03/1.00      ( r2_hidden(X0,k1_relat_1(sK3)) = iProver_top
% 4.03/1.00      | r2_hidden(k4_tarski(X0,X1),sK3) != iProver_top ),
% 4.03/1.00      inference(predicate_to_equality,[status(thm)],[c_233]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_1768,plain,
% 4.03/1.00      ( k6_relat_1(X0) = sK3
% 4.03/1.00      | r2_hidden(sK0(X0,sK3),X0) = iProver_top
% 4.03/1.00      | r2_hidden(sK0(X0,sK3),k1_relat_1(sK3)) = iProver_top
% 4.03/1.00      | v1_relat_1(sK3) != iProver_top ),
% 4.03/1.00      inference(superposition,[status(thm)],[c_829,c_818]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_19,plain,
% 4.03/1.00      ( v1_relat_1(sK3) = iProver_top ),
% 4.03/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_3059,plain,
% 4.03/1.00      ( r2_hidden(sK0(X0,sK3),k1_relat_1(sK3)) = iProver_top
% 4.03/1.00      | r2_hidden(sK0(X0,sK3),X0) = iProver_top
% 4.03/1.00      | k6_relat_1(X0) = sK3 ),
% 4.03/1.00      inference(global_propositional_subsumption,
% 4.03/1.00                [status(thm)],
% 4.03/1.00                [c_1768,c_19]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_3060,plain,
% 4.03/1.00      ( k6_relat_1(X0) = sK3
% 4.03/1.00      | r2_hidden(sK0(X0,sK3),X0) = iProver_top
% 4.03/1.00      | r2_hidden(sK0(X0,sK3),k1_relat_1(sK3)) = iProver_top ),
% 4.03/1.00      inference(renaming,[status(thm)],[c_3059]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_3068,plain,
% 4.03/1.00      ( k6_relat_1(X0) = sK3
% 4.03/1.00      | k6_relat_1(sK2) = sK3
% 4.03/1.00      | r2_hidden(sK0(X0,sK3),X0) = iProver_top
% 4.03/1.00      | r2_hidden(sK0(X0,sK3),sK2) = iProver_top ),
% 4.03/1.00      inference(superposition,[status(thm)],[c_16,c_3060]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_10,plain,
% 4.03/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 4.03/1.00      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 4.03/1.00      | ~ v1_funct_1(X1)
% 4.03/1.00      | ~ v1_relat_1(X1) ),
% 4.03/1.00      inference(cnf_transformation,[],[f48]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_245,plain,
% 4.03/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 4.03/1.00      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 4.03/1.00      | ~ v1_relat_1(X1)
% 4.03/1.00      | sK3 != X1 ),
% 4.03/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_17]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_246,plain,
% 4.03/1.00      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 4.03/1.00      | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3)
% 4.03/1.00      | ~ v1_relat_1(sK3) ),
% 4.03/1.00      inference(unflattening,[status(thm)],[c_245]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_250,plain,
% 4.03/1.00      ( r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3)
% 4.03/1.00      | ~ r2_hidden(X0,k1_relat_1(sK3)) ),
% 4.03/1.00      inference(global_propositional_subsumption,
% 4.03/1.00                [status(thm)],
% 4.03/1.00                [c_246,c_18]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_251,plain,
% 4.03/1.00      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 4.03/1.00      | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3) ),
% 4.03/1.00      inference(renaming,[status(thm)],[c_250]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_817,plain,
% 4.03/1.00      ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 4.03/1.00      | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3) = iProver_top ),
% 4.03/1.00      inference(predicate_to_equality,[status(thm)],[c_251]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_3,plain,
% 4.03/1.00      ( ~ r2_hidden(X0,X1)
% 4.03/1.00      | r2_hidden(k4_tarski(X0,X0),k6_relat_1(X1))
% 4.03/1.00      | ~ v1_relat_1(k6_relat_1(X1)) ),
% 4.03/1.00      inference(cnf_transformation,[],[f45]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_828,plain,
% 4.03/1.00      ( r2_hidden(X0,X1) != iProver_top
% 4.03/1.00      | r2_hidden(k4_tarski(X0,X0),k6_relat_1(X1)) = iProver_top
% 4.03/1.00      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 4.03/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_9,plain,
% 4.03/1.00      ( v1_relat_1(k6_relat_1(X0)) ),
% 4.03/1.00      inference(cnf_transformation,[],[f33]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_825,plain,
% 4.03/1.00      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 4.03/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_897,plain,
% 4.03/1.00      ( r2_hidden(X0,X1) != iProver_top
% 4.03/1.00      | r2_hidden(k4_tarski(X0,X0),k6_relat_1(X1)) = iProver_top ),
% 4.03/1.00      inference(forward_subsumption_resolution,
% 4.03/1.00                [status(thm)],
% 4.03/1.00                [c_828,c_825]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_8,plain,
% 4.03/1.00      ( v1_funct_1(k6_relat_1(X0)) ),
% 4.03/1.00      inference(cnf_transformation,[],[f34]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_210,plain,
% 4.03/1.00      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 4.03/1.00      | ~ v1_relat_1(X2)
% 4.03/1.00      | k1_funct_1(X2,X0) = X1
% 4.03/1.00      | k6_relat_1(X3) != X2 ),
% 4.03/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_11]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_211,plain,
% 4.03/1.00      ( ~ r2_hidden(k4_tarski(X0,X1),k6_relat_1(X2))
% 4.03/1.00      | ~ v1_relat_1(k6_relat_1(X2))
% 4.03/1.00      | k1_funct_1(k6_relat_1(X2),X0) = X1 ),
% 4.03/1.00      inference(unflattening,[status(thm)],[c_210]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_221,plain,
% 4.03/1.00      ( ~ r2_hidden(k4_tarski(X0,X1),k6_relat_1(X2))
% 4.03/1.00      | k1_funct_1(k6_relat_1(X2),X0) = X1 ),
% 4.03/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_211,c_9]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_819,plain,
% 4.03/1.00      ( k1_funct_1(k6_relat_1(X0),X1) = X2
% 4.03/1.00      | r2_hidden(k4_tarski(X1,X2),k6_relat_1(X0)) != iProver_top ),
% 4.03/1.00      inference(predicate_to_equality,[status(thm)],[c_221]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_1342,plain,
% 4.03/1.00      ( k1_funct_1(k6_relat_1(X0),X1) = X1
% 4.03/1.00      | r2_hidden(X1,X0) != iProver_top ),
% 4.03/1.00      inference(superposition,[status(thm)],[c_897,c_819]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_1349,plain,
% 4.03/1.00      ( k1_funct_1(k6_relat_1(k6_relat_1(X0)),k4_tarski(X1,X1)) = k4_tarski(X1,X1)
% 4.03/1.00      | r2_hidden(X1,X0) != iProver_top ),
% 4.03/1.00      inference(superposition,[status(thm)],[c_897,c_1342]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_1598,plain,
% 4.03/1.00      ( k1_funct_1(k6_relat_1(k6_relat_1(sK3)),k4_tarski(k4_tarski(X0,k1_funct_1(sK3,X0)),k4_tarski(X0,k1_funct_1(sK3,X0)))) = k4_tarski(k4_tarski(X0,k1_funct_1(sK3,X0)),k4_tarski(X0,k1_funct_1(sK3,X0)))
% 4.03/1.00      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top ),
% 4.03/1.00      inference(superposition,[status(thm)],[c_817,c_1349]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_6235,plain,
% 4.03/1.00      ( k1_funct_1(k6_relat_1(k6_relat_1(sK3)),k4_tarski(k4_tarski(sK0(k1_relat_1(sK3),sK3),k1_funct_1(sK3,sK0(k1_relat_1(sK3),sK3))),k4_tarski(sK0(k1_relat_1(sK3),sK3),k1_funct_1(sK3,sK0(k1_relat_1(sK3),sK3))))) = k4_tarski(k4_tarski(sK0(k1_relat_1(sK3),sK3),k1_funct_1(sK3,sK0(k1_relat_1(sK3),sK3))),k4_tarski(sK0(k1_relat_1(sK3),sK3),k1_funct_1(sK3,sK0(k1_relat_1(sK3),sK3))))
% 4.03/1.00      | k6_relat_1(k1_relat_1(sK3)) = sK3
% 4.03/1.00      | k6_relat_1(sK2) = sK3
% 4.03/1.00      | r2_hidden(sK0(k1_relat_1(sK3),sK3),sK2) = iProver_top ),
% 4.03/1.00      inference(superposition,[status(thm)],[c_3068,c_1598]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_6245,plain,
% 4.03/1.00      ( k1_funct_1(k6_relat_1(k6_relat_1(sK3)),k4_tarski(k4_tarski(X0,k1_funct_1(sK3,X0)),k4_tarski(X0,k1_funct_1(sK3,X0)))) = k4_tarski(k4_tarski(X0,k1_funct_1(sK3,X0)),k4_tarski(X0,k1_funct_1(sK3,X0)))
% 4.03/1.00      | k6_relat_1(sK2) = sK3
% 4.03/1.00      | r2_hidden(X0,sK2) != iProver_top ),
% 4.03/1.00      inference(superposition,[status(thm)],[c_16,c_1598]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_6316,plain,
% 4.03/1.00      ( k1_funct_1(k6_relat_1(k6_relat_1(sK3)),k4_tarski(k4_tarski(sK0(k1_relat_1(sK3),sK3),k1_funct_1(sK3,sK0(k1_relat_1(sK3),sK3))),k4_tarski(sK0(k1_relat_1(sK3),sK3),k1_funct_1(sK3,sK0(k1_relat_1(sK3),sK3))))) = k4_tarski(k4_tarski(sK0(k1_relat_1(sK3),sK3),k1_funct_1(sK3,sK0(k1_relat_1(sK3),sK3))),k4_tarski(sK0(k1_relat_1(sK3),sK3),k1_funct_1(sK3,sK0(k1_relat_1(sK3),sK3))))
% 4.03/1.00      | k6_relat_1(k1_relat_1(sK3)) = sK3
% 4.03/1.00      | k6_relat_1(sK2) = sK3 ),
% 4.03/1.00      inference(forward_subsumption_resolution,
% 4.03/1.00                [status(thm)],
% 4.03/1.00                [c_6235,c_6245]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_13111,plain,
% 4.03/1.00      ( k1_funct_1(k6_relat_1(k6_relat_1(sK3)),k4_tarski(k4_tarski(sK0(sK2,sK3),k1_funct_1(sK3,sK0(sK2,sK3))),k4_tarski(sK0(sK2,sK3),k1_funct_1(sK3,sK0(sK2,sK3))))) = k4_tarski(k4_tarski(sK0(k1_relat_1(sK3),sK3),k1_funct_1(sK3,sK0(k1_relat_1(sK3),sK3))),k4_tarski(sK0(k1_relat_1(sK3),sK3),k1_funct_1(sK3,sK0(k1_relat_1(sK3),sK3))))
% 4.03/1.00      | k6_relat_1(k1_relat_1(sK3)) = sK3
% 4.03/1.00      | k6_relat_1(sK2) = sK3 ),
% 4.03/1.00      inference(superposition,[status(thm)],[c_16,c_6316]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_13515,plain,
% 4.03/1.00      ( k4_tarski(k4_tarski(sK0(k1_relat_1(sK3),sK3),k1_funct_1(sK3,sK0(k1_relat_1(sK3),sK3))),k4_tarski(sK0(k1_relat_1(sK3),sK3),k1_funct_1(sK3,sK0(k1_relat_1(sK3),sK3)))) = k1_funct_1(k6_relat_1(k6_relat_1(sK3)),k4_tarski(k4_tarski(sK0(sK2,sK3),sK1(sK2,sK3)),k4_tarski(sK0(sK2,sK3),sK1(sK2,sK3))))
% 4.03/1.00      | sK1(sK2,sK3) = sK0(sK2,sK3)
% 4.03/1.00      | k6_relat_1(k1_relat_1(sK3)) = sK3
% 4.03/1.00      | k6_relat_1(sK2) = sK3 ),
% 4.03/1.00      inference(superposition,[status(thm)],[c_5146,c_13111]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_14,negated_conjecture,
% 4.03/1.00      ( r2_hidden(sK4,sK2)
% 4.03/1.00      | k1_relat_1(sK3) != sK2
% 4.03/1.00      | k6_relat_1(sK2) != sK3 ),
% 4.03/1.00      inference(cnf_transformation,[],[f42]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_518,plain,( X0 = X0 ),theory(equality) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_535,plain,
% 4.03/1.00      ( sK3 = sK3 ),
% 4.03/1.00      inference(instantiation,[status(thm)],[c_518]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_519,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_1124,plain,
% 4.03/1.00      ( k6_relat_1(sK2) != X0 | sK3 != X0 | sK3 = k6_relat_1(sK2) ),
% 4.03/1.00      inference(instantiation,[status(thm)],[c_519]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_1125,plain,
% 4.03/1.00      ( k6_relat_1(sK2) != sK3 | sK3 = k6_relat_1(sK2) | sK3 != sK3 ),
% 4.03/1.00      inference(instantiation,[status(thm)],[c_1124]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_1213,plain,
% 4.03/1.00      ( r2_hidden(k4_tarski(sK4,sK4),k6_relat_1(sK2))
% 4.03/1.00      | ~ r2_hidden(sK4,sK2)
% 4.03/1.00      | ~ v1_relat_1(k6_relat_1(sK2)) ),
% 4.03/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_1253,plain,
% 4.03/1.00      ( v1_relat_1(k6_relat_1(sK2)) ),
% 4.03/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_13,negated_conjecture,
% 4.03/1.00      ( k1_funct_1(sK3,sK4) != sK4
% 4.03/1.00      | k1_relat_1(sK3) != sK2
% 4.03/1.00      | k6_relat_1(sK2) != sK3 ),
% 4.03/1.00      inference(cnf_transformation,[],[f43]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_3714,plain,
% 4.03/1.00      ( ~ r2_hidden(k4_tarski(sK4,sK4),sK3)
% 4.03/1.00      | k1_relat_1(sK3) != sK2
% 4.03/1.00      | k6_relat_1(sK2) != sK3 ),
% 4.03/1.00      inference(resolution,[status(thm)],[c_268,c_13]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_15,negated_conjecture,
% 4.03/1.00      ( ~ r2_hidden(X0,sK2)
% 4.03/1.00      | k1_funct_1(sK3,X0) = X0
% 4.03/1.00      | k6_relat_1(sK2) = sK3 ),
% 4.03/1.00      inference(cnf_transformation,[],[f41]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_823,plain,
% 4.03/1.00      ( k1_funct_1(sK3,X0) = X0
% 4.03/1.00      | k6_relat_1(sK2) = sK3
% 4.03/1.00      | r2_hidden(X0,sK2) != iProver_top ),
% 4.03/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_3075,plain,
% 4.03/1.00      ( k1_funct_1(sK3,sK0(sK2,sK3)) = sK0(sK2,sK3)
% 4.03/1.00      | k6_relat_1(sK2) = sK3
% 4.03/1.00      | r2_hidden(sK0(sK2,sK3),k1_relat_1(sK3)) = iProver_top ),
% 4.03/1.00      inference(superposition,[status(thm)],[c_3060,c_823]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_1205,plain,
% 4.03/1.00      ( ~ r2_hidden(sK0(sK2,sK3),sK2)
% 4.03/1.00      | k1_funct_1(sK3,sK0(sK2,sK3)) = sK0(sK2,sK3)
% 4.03/1.00      | k6_relat_1(sK2) = sK3 ),
% 4.03/1.00      inference(instantiation,[status(thm)],[c_15]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_1206,plain,
% 4.03/1.00      ( k1_funct_1(sK3,sK0(sK2,sK3)) = sK0(sK2,sK3)
% 4.03/1.00      | k6_relat_1(sK2) = sK3
% 4.03/1.00      | r2_hidden(sK0(sK2,sK3),sK2) != iProver_top ),
% 4.03/1.00      inference(predicate_to_equality,[status(thm)],[c_1205]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_3213,plain,
% 4.03/1.00      ( k6_relat_1(sK2) = sK3
% 4.03/1.00      | r2_hidden(sK0(sK2,sK3),sK2) = iProver_top
% 4.03/1.00      | iProver_top != iProver_top ),
% 4.03/1.00      inference(equality_factoring,[status(thm)],[c_3068]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_3215,plain,
% 4.03/1.00      ( k6_relat_1(sK2) = sK3
% 4.03/1.00      | r2_hidden(sK0(sK2,sK3),sK2) = iProver_top ),
% 4.03/1.00      inference(equality_resolution_simp,[status(thm)],[c_3213]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_3626,plain,
% 4.03/1.00      ( k6_relat_1(sK2) = sK3
% 4.03/1.00      | k1_funct_1(sK3,sK0(sK2,sK3)) = sK0(sK2,sK3) ),
% 4.03/1.00      inference(global_propositional_subsumption,
% 4.03/1.00                [status(thm)],
% 4.03/1.00                [c_3075,c_1206,c_3215]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_3627,plain,
% 4.03/1.00      ( k1_funct_1(sK3,sK0(sK2,sK3)) = sK0(sK2,sK3)
% 4.03/1.00      | k6_relat_1(sK2) = sK3 ),
% 4.03/1.00      inference(renaming,[status(thm)],[c_3626]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_5155,plain,
% 4.03/1.00      ( sK1(sK2,sK3) = sK0(sK2,sK3) | k6_relat_1(sK2) = sK3 ),
% 4.03/1.00      inference(superposition,[status(thm)],[c_5146,c_3627]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_521,plain,
% 4.03/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 4.03/1.00      theory(equality) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_6,plain,
% 4.03/1.00      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 4.03/1.00      inference(cnf_transformation,[],[f32]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_3347,plain,
% 4.03/1.00      ( ~ r2_hidden(X0,X1)
% 4.03/1.00      | r2_hidden(X2,k2_relat_1(k6_relat_1(X1)))
% 4.03/1.00      | X2 != X0 ),
% 4.03/1.00      inference(resolution,[status(thm)],[c_521,c_6]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_1998,plain,
% 4.03/1.00      ( X0 != X1 | X1 = X0 ),
% 4.03/1.00      inference(resolution,[status(thm)],[c_519,c_518]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_4986,plain,
% 4.03/1.00      ( k6_relat_1(sK2) = sK3 | sK2 = k1_relat_1(sK3) ),
% 4.03/1.00      inference(resolution,[status(thm)],[c_1998,c_16]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_9324,plain,
% 4.03/1.00      ( r2_hidden(k6_relat_1(sK2),k2_relat_1(k6_relat_1(X0)))
% 4.03/1.00      | ~ r2_hidden(sK3,X0)
% 4.03/1.00      | sK2 = k1_relat_1(sK3) ),
% 4.03/1.00      inference(resolution,[status(thm)],[c_3347,c_4986]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_1406,plain,
% 4.03/1.00      ( sK2 = sK2 ),
% 4.03/1.00      inference(instantiation,[status(thm)],[c_518]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_7,plain,
% 4.03/1.00      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 4.03/1.00      inference(cnf_transformation,[],[f31]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_1433,plain,
% 4.03/1.00      ( k1_relat_1(k6_relat_1(sK2)) = sK2 ),
% 4.03/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_1162,plain,
% 4.03/1.00      ( X0 != X1 | sK2 != X1 | sK2 = X0 ),
% 4.03/1.00      inference(instantiation,[status(thm)],[c_519]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_1405,plain,
% 4.03/1.00      ( X0 != sK2 | sK2 = X0 | sK2 != sK2 ),
% 4.03/1.00      inference(instantiation,[status(thm)],[c_1162]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_2516,plain,
% 4.03/1.00      ( k1_relat_1(k6_relat_1(sK2)) != sK2
% 4.03/1.00      | sK2 = k1_relat_1(k6_relat_1(sK2))
% 4.03/1.00      | sK2 != sK2 ),
% 4.03/1.00      inference(instantiation,[status(thm)],[c_1405]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_525,plain,
% 4.03/1.00      ( X0 != X1 | k1_relat_1(X0) = k1_relat_1(X1) ),
% 4.03/1.00      theory(equality) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_3795,plain,
% 4.03/1.00      ( X0 != k6_relat_1(sK2)
% 4.03/1.00      | k1_relat_1(X0) = k1_relat_1(k6_relat_1(sK2)) ),
% 4.03/1.00      inference(instantiation,[status(thm)],[c_525]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_3800,plain,
% 4.03/1.00      ( k1_relat_1(sK3) = k1_relat_1(k6_relat_1(sK2))
% 4.03/1.00      | sK3 != k6_relat_1(sK2) ),
% 4.03/1.00      inference(instantiation,[status(thm)],[c_3795]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_5390,plain,
% 4.03/1.00      ( sK2 = k1_relat_1(sK3) | sK3 = k6_relat_1(sK2) ),
% 4.03/1.00      inference(resolution,[status(thm)],[c_4986,c_1998]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_2961,plain,
% 4.03/1.00      ( X0 != k1_relat_1(k6_relat_1(sK2))
% 4.03/1.00      | sK2 = X0
% 4.03/1.00      | sK2 != k1_relat_1(k6_relat_1(sK2)) ),
% 4.03/1.00      inference(instantiation,[status(thm)],[c_1162]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_10150,plain,
% 4.03/1.00      ( k1_relat_1(X0) != k1_relat_1(k6_relat_1(sK2))
% 4.03/1.00      | sK2 = k1_relat_1(X0)
% 4.03/1.00      | sK2 != k1_relat_1(k6_relat_1(sK2)) ),
% 4.03/1.00      inference(instantiation,[status(thm)],[c_2961]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_10152,plain,
% 4.03/1.00      ( k1_relat_1(sK3) != k1_relat_1(k6_relat_1(sK2))
% 4.03/1.00      | sK2 != k1_relat_1(k6_relat_1(sK2))
% 4.03/1.00      | sK2 = k1_relat_1(sK3) ),
% 4.03/1.00      inference(instantiation,[status(thm)],[c_10150]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_11040,plain,
% 4.03/1.00      ( sK2 = k1_relat_1(sK3) ),
% 4.03/1.00      inference(global_propositional_subsumption,
% 4.03/1.00                [status(thm)],
% 4.03/1.00                [c_9324,c_1406,c_1433,c_2516,c_3800,c_5390,c_10152]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_11047,plain,
% 4.03/1.00      ( k1_relat_1(sK3) = sK2 ),
% 4.03/1.00      inference(resolution,[status(thm)],[c_11040,c_1998]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_10181,plain,
% 4.03/1.00      ( r2_hidden(X0,X1)
% 4.03/1.00      | ~ r2_hidden(k4_tarski(sK4,sK4),k6_relat_1(sK2))
% 4.03/1.00      | X0 != k4_tarski(sK4,sK4)
% 4.03/1.00      | X1 != k6_relat_1(sK2) ),
% 4.03/1.00      inference(instantiation,[status(thm)],[c_521]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_15314,plain,
% 4.03/1.00      ( r2_hidden(k4_tarski(sK4,sK4),X0)
% 4.03/1.00      | ~ r2_hidden(k4_tarski(sK4,sK4),k6_relat_1(sK2))
% 4.03/1.00      | X0 != k6_relat_1(sK2)
% 4.03/1.00      | k4_tarski(sK4,sK4) != k4_tarski(sK4,sK4) ),
% 4.03/1.00      inference(instantiation,[status(thm)],[c_10181]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_15317,plain,
% 4.03/1.00      ( ~ r2_hidden(k4_tarski(sK4,sK4),k6_relat_1(sK2))
% 4.03/1.00      | r2_hidden(k4_tarski(sK4,sK4),sK3)
% 4.03/1.00      | k4_tarski(sK4,sK4) != k4_tarski(sK4,sK4)
% 4.03/1.00      | sK3 != k6_relat_1(sK2) ),
% 4.03/1.00      inference(instantiation,[status(thm)],[c_15314]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_15315,plain,
% 4.03/1.00      ( k4_tarski(sK4,sK4) = k4_tarski(sK4,sK4) ),
% 4.03/1.00      inference(instantiation,[status(thm)],[c_518]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_15584,plain,
% 4.03/1.00      ( sK1(sK2,sK3) = sK0(sK2,sK3) ),
% 4.03/1.00      inference(global_propositional_subsumption,
% 4.03/1.00                [status(thm)],
% 4.03/1.00                [c_13515,c_14,c_535,c_1125,c_1213,c_1253,c_3714,c_5155,
% 4.03/1.00                 c_11047,c_15317,c_15315]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_0,plain,
% 4.03/1.00      ( ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)
% 4.03/1.00      | ~ r2_hidden(sK0(X0,X1),X0)
% 4.03/1.00      | ~ v1_relat_1(X1)
% 4.03/1.00      | sK1(X0,X1) != sK0(X0,X1)
% 4.03/1.00      | k6_relat_1(X0) = X1 ),
% 4.03/1.00      inference(cnf_transformation,[],[f30]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_831,plain,
% 4.03/1.00      ( sK1(X0,X1) != sK0(X0,X1)
% 4.03/1.00      | k6_relat_1(X0) = X1
% 4.03/1.00      | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) != iProver_top
% 4.03/1.00      | r2_hidden(sK0(X0,X1),X0) != iProver_top
% 4.03/1.00      | v1_relat_1(X1) != iProver_top ),
% 4.03/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_15587,plain,
% 4.03/1.00      ( k6_relat_1(sK2) = sK3
% 4.03/1.00      | r2_hidden(k4_tarski(sK0(sK2,sK3),sK1(sK2,sK3)),sK3) != iProver_top
% 4.03/1.00      | r2_hidden(sK0(sK2,sK3),sK2) != iProver_top
% 4.03/1.00      | v1_relat_1(sK3) != iProver_top ),
% 4.03/1.00      inference(superposition,[status(thm)],[c_15584,c_831]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_15595,plain,
% 4.03/1.00      ( k6_relat_1(sK2) = sK3
% 4.03/1.00      | r2_hidden(k4_tarski(sK0(sK2,sK3),sK0(sK2,sK3)),sK3) != iProver_top
% 4.03/1.00      | r2_hidden(sK0(sK2,sK3),sK2) != iProver_top
% 4.03/1.00      | v1_relat_1(sK3) != iProver_top ),
% 4.03/1.00      inference(light_normalisation,[status(thm)],[c_15587,c_15584]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_1350,plain,
% 4.03/1.00      ( k1_funct_1(k6_relat_1(sK3),k4_tarski(X0,k1_funct_1(sK3,X0))) = k4_tarski(X0,k1_funct_1(sK3,X0))
% 4.03/1.00      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top ),
% 4.03/1.00      inference(superposition,[status(thm)],[c_817,c_1342]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_3208,plain,
% 4.03/1.00      ( k1_funct_1(k6_relat_1(sK3),k4_tarski(sK0(k1_relat_1(sK3),sK3),k1_funct_1(sK3,sK0(k1_relat_1(sK3),sK3)))) = k4_tarski(sK0(k1_relat_1(sK3),sK3),k1_funct_1(sK3,sK0(k1_relat_1(sK3),sK3)))
% 4.03/1.00      | k6_relat_1(k1_relat_1(sK3)) = sK3
% 4.03/1.00      | k6_relat_1(sK2) = sK3
% 4.03/1.00      | r2_hidden(sK0(k1_relat_1(sK3),sK3),sK2) = iProver_top ),
% 4.03/1.00      inference(superposition,[status(thm)],[c_3068,c_1350]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_1484,plain,
% 4.03/1.00      ( k1_funct_1(k6_relat_1(sK3),k4_tarski(X0,k1_funct_1(sK3,X0))) = k4_tarski(X0,k1_funct_1(sK3,X0))
% 4.03/1.00      | k6_relat_1(sK2) = sK3
% 4.03/1.00      | r2_hidden(X0,sK2) != iProver_top ),
% 4.03/1.00      inference(superposition,[status(thm)],[c_16,c_1350]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_7282,plain,
% 4.03/1.00      ( k1_funct_1(k6_relat_1(sK3),k4_tarski(sK0(k1_relat_1(sK3),sK3),k1_funct_1(sK3,sK0(k1_relat_1(sK3),sK3)))) = k4_tarski(sK0(k1_relat_1(sK3),sK3),k1_funct_1(sK3,sK0(k1_relat_1(sK3),sK3)))
% 4.03/1.00      | k6_relat_1(k1_relat_1(sK3)) = sK3
% 4.03/1.00      | k6_relat_1(sK2) = sK3 ),
% 4.03/1.00      inference(forward_subsumption_resolution,
% 4.03/1.00                [status(thm)],
% 4.03/1.00                [c_3208,c_1484]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_7286,plain,
% 4.03/1.00      ( k1_funct_1(k6_relat_1(sK3),k4_tarski(sK0(sK2,sK3),k1_funct_1(sK3,sK0(sK2,sK3)))) = k4_tarski(sK0(k1_relat_1(sK3),sK3),k1_funct_1(sK3,sK0(k1_relat_1(sK3),sK3)))
% 4.03/1.00      | k6_relat_1(k1_relat_1(sK3)) = sK3
% 4.03/1.00      | k6_relat_1(sK2) = sK3 ),
% 4.03/1.00      inference(superposition,[status(thm)],[c_16,c_7282]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_193,plain,
% 4.03/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 4.03/1.00      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 4.03/1.00      | ~ v1_relat_1(X1)
% 4.03/1.00      | k6_relat_1(X2) != X1 ),
% 4.03/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_10]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_194,plain,
% 4.03/1.00      ( ~ r2_hidden(X0,k1_relat_1(k6_relat_1(X1)))
% 4.03/1.00      | r2_hidden(k4_tarski(X0,k1_funct_1(k6_relat_1(X1),X0)),k6_relat_1(X1))
% 4.03/1.00      | ~ v1_relat_1(k6_relat_1(X1)) ),
% 4.03/1.00      inference(unflattening,[status(thm)],[c_193]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_204,plain,
% 4.03/1.00      ( ~ r2_hidden(X0,k1_relat_1(k6_relat_1(X1)))
% 4.03/1.00      | r2_hidden(k4_tarski(X0,k1_funct_1(k6_relat_1(X1),X0)),k6_relat_1(X1)) ),
% 4.03/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_194,c_9]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_820,plain,
% 4.03/1.00      ( r2_hidden(X0,k1_relat_1(k6_relat_1(X1))) != iProver_top
% 4.03/1.00      | r2_hidden(k4_tarski(X0,k1_funct_1(k6_relat_1(X1),X0)),k6_relat_1(X1)) = iProver_top ),
% 4.03/1.00      inference(predicate_to_equality,[status(thm)],[c_204]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_883,plain,
% 4.03/1.00      ( r2_hidden(X0,X1) != iProver_top
% 4.03/1.00      | r2_hidden(k4_tarski(X0,k1_funct_1(k6_relat_1(X1),X0)),k6_relat_1(X1)) = iProver_top ),
% 4.03/1.00      inference(demodulation,[status(thm)],[c_820,c_7]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_7507,plain,
% 4.03/1.00      ( k6_relat_1(k1_relat_1(sK3)) = sK3
% 4.03/1.00      | k6_relat_1(sK2) = sK3
% 4.03/1.00      | r2_hidden(k4_tarski(k4_tarski(sK0(sK2,sK3),k1_funct_1(sK3,sK0(sK2,sK3))),k4_tarski(sK0(k1_relat_1(sK3),sK3),k1_funct_1(sK3,sK0(k1_relat_1(sK3),sK3)))),k6_relat_1(sK3)) = iProver_top
% 4.03/1.00      | r2_hidden(k4_tarski(sK0(sK2,sK3),k1_funct_1(sK3,sK0(sK2,sK3))),sK3) != iProver_top ),
% 4.03/1.00      inference(superposition,[status(thm)],[c_7286,c_883]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_3081,plain,
% 4.03/1.00      ( k6_relat_1(k1_relat_1(sK3)) = sK3
% 4.03/1.00      | r2_hidden(sK0(k1_relat_1(sK3),sK3),k1_relat_1(sK3)) = iProver_top
% 4.03/1.00      | iProver_top != iProver_top ),
% 4.03/1.00      inference(equality_factoring,[status(thm)],[c_3060]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_3083,plain,
% 4.03/1.00      ( k6_relat_1(k1_relat_1(sK3)) = sK3
% 4.03/1.00      | r2_hidden(sK0(k1_relat_1(sK3),sK3),k1_relat_1(sK3)) = iProver_top ),
% 4.03/1.00      inference(equality_resolution_simp,[status(thm)],[c_3081]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_3074,plain,
% 4.03/1.00      ( k1_funct_1(k6_relat_1(sK3),k4_tarski(sK0(sK2,sK3),k1_funct_1(sK3,sK0(sK2,sK3)))) = k4_tarski(sK0(sK2,sK3),k1_funct_1(sK3,sK0(sK2,sK3)))
% 4.03/1.00      | k6_relat_1(sK2) = sK3
% 4.03/1.00      | r2_hidden(sK0(sK2,sK3),k1_relat_1(sK3)) = iProver_top ),
% 4.03/1.00      inference(superposition,[status(thm)],[c_3060,c_1484]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_4539,plain,
% 4.03/1.00      ( k1_funct_1(k6_relat_1(sK3),k4_tarski(sK0(sK2,sK3),k1_funct_1(sK3,sK0(sK2,sK3)))) = k4_tarski(sK0(sK2,sK3),k1_funct_1(sK3,sK0(sK2,sK3)))
% 4.03/1.00      | k6_relat_1(sK2) = sK3 ),
% 4.03/1.00      inference(forward_subsumption_resolution,
% 4.03/1.00                [status(thm)],
% 4.03/1.00                [c_3074,c_1350]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_7509,plain,
% 4.03/1.00      ( k4_tarski(sK0(k1_relat_1(sK3),sK3),k1_funct_1(sK3,sK0(k1_relat_1(sK3),sK3))) = k4_tarski(sK0(sK2,sK3),k1_funct_1(sK3,sK0(sK2,sK3)))
% 4.03/1.00      | k6_relat_1(k1_relat_1(sK3)) = sK3
% 4.03/1.00      | k6_relat_1(sK2) = sK3 ),
% 4.03/1.00      inference(superposition,[status(thm)],[c_7286,c_4539]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_7556,plain,
% 4.03/1.00      ( k6_relat_1(k1_relat_1(sK3)) = sK3
% 4.03/1.00      | k6_relat_1(sK2) = sK3
% 4.03/1.00      | r2_hidden(k4_tarski(sK0(sK2,sK3),k1_funct_1(sK3,sK0(sK2,sK3))),sK3) = iProver_top
% 4.03/1.00      | r2_hidden(sK0(k1_relat_1(sK3),sK3),k1_relat_1(sK3)) != iProver_top ),
% 4.03/1.00      inference(superposition,[status(thm)],[c_7509,c_817]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_9826,plain,
% 4.03/1.00      ( r2_hidden(k4_tarski(k4_tarski(sK0(sK2,sK3),k1_funct_1(sK3,sK0(sK2,sK3))),k4_tarski(sK0(k1_relat_1(sK3),sK3),k1_funct_1(sK3,sK0(k1_relat_1(sK3),sK3)))),k6_relat_1(sK3)) = iProver_top
% 4.03/1.00      | k6_relat_1(sK2) = sK3
% 4.03/1.00      | k6_relat_1(k1_relat_1(sK3)) = sK3 ),
% 4.03/1.00      inference(global_propositional_subsumption,
% 4.03/1.00                [status(thm)],
% 4.03/1.00                [c_7507,c_3083,c_7556]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_9827,plain,
% 4.03/1.00      ( k6_relat_1(k1_relat_1(sK3)) = sK3
% 4.03/1.00      | k6_relat_1(sK2) = sK3
% 4.03/1.00      | r2_hidden(k4_tarski(k4_tarski(sK0(sK2,sK3),k1_funct_1(sK3,sK0(sK2,sK3))),k4_tarski(sK0(k1_relat_1(sK3),sK3),k1_funct_1(sK3,sK0(k1_relat_1(sK3),sK3)))),k6_relat_1(sK3)) = iProver_top ),
% 4.03/1.00      inference(renaming,[status(thm)],[c_9826]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_9841,plain,
% 4.03/1.00      ( k6_relat_1(k1_relat_1(sK3)) = sK3
% 4.03/1.00      | k6_relat_1(sK2) = sK3
% 4.03/1.00      | r2_hidden(k4_tarski(k4_tarski(sK0(sK2,sK3),k1_funct_1(sK3,sK0(sK2,sK3))),k4_tarski(sK0(sK2,sK3),k1_funct_1(sK3,sK0(sK2,sK3)))),k6_relat_1(sK3)) = iProver_top ),
% 4.03/1.00      inference(superposition,[status(thm)],[c_16,c_9827]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_9950,plain,
% 4.03/1.00      ( k6_relat_1(k1_relat_1(sK3)) = sK3
% 4.03/1.00      | k6_relat_1(sK2) = sK3
% 4.03/1.00      | r2_hidden(k4_tarski(k4_tarski(sK0(sK2,sK3),sK0(sK2,sK3)),k4_tarski(sK0(sK2,sK3),sK0(sK2,sK3))),k6_relat_1(sK3)) = iProver_top ),
% 4.03/1.00      inference(superposition,[status(thm)],[c_3627,c_9841]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_34,plain,
% 4.03/1.00      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 4.03/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_36,plain,
% 4.03/1.00      ( v1_relat_1(k6_relat_1(sK3)) = iProver_top ),
% 4.03/1.00      inference(instantiation,[status(thm)],[c_34]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_1288,plain,
% 4.03/1.00      ( sK0(sK2,sK3) = sK0(sK2,sK3) ),
% 4.03/1.00      inference(instantiation,[status(thm)],[c_518]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_3509,plain,
% 4.03/1.00      ( r2_hidden(k4_tarski(k4_tarski(sK0(sK2,sK3),sK0(sK2,sK3)),k4_tarski(sK0(sK2,sK3),sK0(sK2,sK3))),k6_relat_1(X0))
% 4.03/1.00      | ~ r2_hidden(k4_tarski(sK0(sK2,sK3),sK0(sK2,sK3)),X0)
% 4.03/1.00      | ~ v1_relat_1(k6_relat_1(X0)) ),
% 4.03/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_3510,plain,
% 4.03/1.00      ( r2_hidden(k4_tarski(k4_tarski(sK0(sK2,sK3),sK0(sK2,sK3)),k4_tarski(sK0(sK2,sK3),sK0(sK2,sK3))),k6_relat_1(X0)) = iProver_top
% 4.03/1.00      | r2_hidden(k4_tarski(sK0(sK2,sK3),sK0(sK2,sK3)),X0) != iProver_top
% 4.03/1.00      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 4.03/1.00      inference(predicate_to_equality,[status(thm)],[c_3509]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_3512,plain,
% 4.03/1.00      ( r2_hidden(k4_tarski(k4_tarski(sK0(sK2,sK3),sK0(sK2,sK3)),k4_tarski(sK0(sK2,sK3),sK0(sK2,sK3))),k6_relat_1(sK3)) = iProver_top
% 4.03/1.00      | r2_hidden(k4_tarski(sK0(sK2,sK3),sK0(sK2,sK3)),sK3) != iProver_top
% 4.03/1.00      | v1_relat_1(k6_relat_1(sK3)) != iProver_top ),
% 4.03/1.00      inference(instantiation,[status(thm)],[c_3510]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_3630,plain,
% 4.03/1.00      ( k6_relat_1(sK2) = sK3
% 4.03/1.00      | r2_hidden(k4_tarski(sK0(sK2,sK3),sK0(sK2,sK3)),sK3) = iProver_top
% 4.03/1.00      | r2_hidden(sK0(sK2,sK3),k1_relat_1(sK3)) != iProver_top ),
% 4.03/1.00      inference(superposition,[status(thm)],[c_3627,c_817]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_1197,plain,
% 4.03/1.00      ( r2_hidden(X0,X1)
% 4.03/1.00      | ~ r2_hidden(sK0(sK2,sK3),sK2)
% 4.03/1.00      | X0 != sK0(sK2,sK3)
% 4.03/1.00      | X1 != sK2 ),
% 4.03/1.00      inference(instantiation,[status(thm)],[c_521]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_1287,plain,
% 4.03/1.00      ( r2_hidden(sK0(sK2,sK3),X0)
% 4.03/1.00      | ~ r2_hidden(sK0(sK2,sK3),sK2)
% 4.03/1.00      | X0 != sK2
% 4.03/1.00      | sK0(sK2,sK3) != sK0(sK2,sK3) ),
% 4.03/1.00      inference(instantiation,[status(thm)],[c_1197]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_10165,plain,
% 4.03/1.00      ( r2_hidden(sK0(sK2,sK3),k1_relat_1(sK3))
% 4.03/1.00      | ~ r2_hidden(sK0(sK2,sK3),sK2)
% 4.03/1.00      | sK0(sK2,sK3) != sK0(sK2,sK3)
% 4.03/1.00      | k1_relat_1(sK3) != sK2 ),
% 4.03/1.00      inference(instantiation,[status(thm)],[c_1287]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_10172,plain,
% 4.03/1.00      ( sK0(sK2,sK3) != sK0(sK2,sK3)
% 4.03/1.00      | k1_relat_1(sK3) != sK2
% 4.03/1.00      | r2_hidden(sK0(sK2,sK3),k1_relat_1(sK3)) = iProver_top
% 4.03/1.00      | r2_hidden(sK0(sK2,sK3),sK2) != iProver_top ),
% 4.03/1.00      inference(predicate_to_equality,[status(thm)],[c_10165]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_10270,plain,
% 4.03/1.00      ( k6_relat_1(sK2) = sK3
% 4.03/1.00      | r2_hidden(k4_tarski(k4_tarski(sK0(sK2,sK3),sK0(sK2,sK3)),k4_tarski(sK0(sK2,sK3),sK0(sK2,sK3))),k6_relat_1(sK3)) = iProver_top ),
% 4.03/1.00      inference(global_propositional_subsumption,
% 4.03/1.00                [status(thm)],
% 4.03/1.00                [c_9950,c_16,c_36,c_1288,c_3215,c_3512,c_3630,c_10172]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_176,plain,
% 4.03/1.00      ( r2_hidden(X0,k1_relat_1(X1))
% 4.03/1.00      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 4.03/1.00      | ~ v1_relat_1(X1)
% 4.03/1.00      | k6_relat_1(X3) != X1 ),
% 4.03/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_12]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_177,plain,
% 4.03/1.00      ( r2_hidden(X0,k1_relat_1(k6_relat_1(X1)))
% 4.03/1.00      | ~ r2_hidden(k4_tarski(X0,X2),k6_relat_1(X1))
% 4.03/1.00      | ~ v1_relat_1(k6_relat_1(X1)) ),
% 4.03/1.00      inference(unflattening,[status(thm)],[c_176]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_187,plain,
% 4.03/1.00      ( r2_hidden(X0,k1_relat_1(k6_relat_1(X1)))
% 4.03/1.00      | ~ r2_hidden(k4_tarski(X0,X2),k6_relat_1(X1)) ),
% 4.03/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_177,c_9]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_821,plain,
% 4.03/1.00      ( r2_hidden(X0,k1_relat_1(k6_relat_1(X1))) = iProver_top
% 4.03/1.00      | r2_hidden(k4_tarski(X0,X2),k6_relat_1(X1)) != iProver_top ),
% 4.03/1.00      inference(predicate_to_equality,[status(thm)],[c_187]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_860,plain,
% 4.03/1.00      ( r2_hidden(X0,X1) = iProver_top
% 4.03/1.00      | r2_hidden(k4_tarski(X0,X2),k6_relat_1(X1)) != iProver_top ),
% 4.03/1.00      inference(demodulation,[status(thm)],[c_821,c_7]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_10276,plain,
% 4.03/1.00      ( k6_relat_1(sK2) = sK3
% 4.03/1.00      | r2_hidden(k4_tarski(sK0(sK2,sK3),sK0(sK2,sK3)),sK3) = iProver_top ),
% 4.03/1.00      inference(superposition,[status(thm)],[c_10270,c_860]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(contradiction,plain,
% 4.03/1.00      ( $false ),
% 4.03/1.00      inference(minisat,
% 4.03/1.00                [status(thm)],
% 4.03/1.00                [c_15595,c_15315,c_15317,c_11047,c_10276,c_3714,c_3215,
% 4.03/1.00                 c_1253,c_1213,c_1125,c_535,c_14,c_19]) ).
% 4.03/1.00  
% 4.03/1.00  
% 4.03/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 4.03/1.00  
% 4.03/1.00  ------                               Statistics
% 4.03/1.00  
% 4.03/1.00  ------ Selected
% 4.03/1.00  
% 4.03/1.00  total_time:                             0.478
% 4.03/1.00  
%------------------------------------------------------------------------------
