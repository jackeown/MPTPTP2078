%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0617+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:44 EST 2020

% Result     : Theorem 7.19s
% Output     : CNFRefutation 7.19s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 806 expanded)
%              Number of clauses        :   66 ( 232 expanded)
%              Number of leaves         :   12 ( 227 expanded)
%              Depth                    :   20
%              Number of atoms          :  427 (5141 expanded)
%              Number of equality atoms :  188 (1933 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( X0 = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X0)
              <=> r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( X0 = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X0)
              <=> r2_hidden(k4_tarski(X2,X3),X1) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( X0 = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X2,X3),X0) )
                  & ( r2_hidden(k4_tarski(X2,X3),X1)
                    | r2_hidden(k4_tarski(X2,X3),X0) ) ) )
            & ( ! [X2,X3] :
                  ( ( r2_hidden(k4_tarski(X2,X3),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) )
                  & ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
              | X0 != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( X0 = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X2,X3),X0) )
                  & ( r2_hidden(k4_tarski(X2,X3),X1)
                    | r2_hidden(k4_tarski(X2,X3),X0) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) )
                  & ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X4,X5),X0) ) )
              | X0 != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f11])).

fof(f13,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r2_hidden(k4_tarski(X2,X3),X1)
            | ~ r2_hidden(k4_tarski(X2,X3),X0) )
          & ( r2_hidden(k4_tarski(X2,X3),X1)
            | r2_hidden(k4_tarski(X2,X3),X0) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)
          | ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0) )
        & ( r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)
          | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( X0 = X1
              | ( ( ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)
                  | ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0) )
                & ( r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)
                  | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) )
                  & ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X4,X5),X0) ) )
              | X0 != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f13])).

fof(f27,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)
      | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
              & k1_relat_1(X0) = k1_relat_1(X1) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( ! [X2] :
                    ( r2_hidden(X2,k1_relat_1(X0))
                   => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
                & k1_relat_1(X0) = k1_relat_1(X1) )
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & ! [X2] :
              ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
              | ~ r2_hidden(X2,k1_relat_1(X0)) )
          & k1_relat_1(X0) = k1_relat_1(X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & ! [X2] :
              ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
              | ~ r2_hidden(X2,k1_relat_1(X0)) )
          & k1_relat_1(X0) = k1_relat_1(X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] :
          ( X0 != X1
          & ! [X2] :
              ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
              | ~ r2_hidden(X2,k1_relat_1(X0)) )
          & k1_relat_1(X0) = k1_relat_1(X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( sK6 != X0
        & ! [X2] :
            ( k1_funct_1(sK6,X2) = k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0)) )
        & k1_relat_1(sK6) = k1_relat_1(X0)
        & v1_funct_1(sK6)
        & v1_relat_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( X0 != X1
            & ! [X2] :
                ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
                | ~ r2_hidden(X2,k1_relat_1(X0)) )
            & k1_relat_1(X0) = k1_relat_1(X1)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( sK5 != X1
          & ! [X2] :
              ( k1_funct_1(sK5,X2) = k1_funct_1(X1,X2)
              | ~ r2_hidden(X2,k1_relat_1(sK5)) )
          & k1_relat_1(sK5) = k1_relat_1(X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK5)
      & v1_relat_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( sK5 != sK6
    & ! [X2] :
        ( k1_funct_1(sK5,X2) = k1_funct_1(sK6,X2)
        | ~ r2_hidden(X2,k1_relat_1(sK5)) )
    & k1_relat_1(sK5) = k1_relat_1(sK6)
    & v1_funct_1(sK6)
    & v1_relat_1(sK6)
    & v1_funct_1(sK5)
    & v1_relat_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f10,f23,f22])).

fof(f38,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( ( k1_funct_1(X0,X1) = X2
                | k1_xboole_0 != X2 )
              & ( k1_xboole_0 = X2
                | k1_funct_1(X0,X1) != X2 ) )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( ( k1_funct_1(X0,X1) = X2
                | ~ r2_hidden(k4_tarski(X1,X2),X0) )
              & ( r2_hidden(k4_tarski(X1,X2),X0)
                | k1_funct_1(X0,X1) != X2 ) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X0,X1) = X2
      | ~ r2_hidden(k4_tarski(X1,X2),X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f17,plain,(
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
    inference(rectify,[],[f16])).

fof(f20,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK3(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK2(X0,X1),X3),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK2(X0,X1),X4),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK2(X0,X1),X3),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f17,f20,f19,f18])).

fof(f34,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f49,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f34])).

fof(f37,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f24])).

fof(f40,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f24])).

fof(f39,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f24])).

fof(f41,plain,(
    k1_relat_1(sK5) = k1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f24])).

fof(f42,plain,(
    ! [X2] :
      ( k1_funct_1(sK5,X2) = k1_funct_1(sK6,X2)
      | ~ r2_hidden(X2,k1_relat_1(sK5)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f43,plain,(
    sK5 != sK6 ),
    inference(cnf_transformation,[],[f24])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),X0)
      | k1_funct_1(X0,X1) != X2
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f29])).

fof(f28,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)
      | ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_1,plain,
    ( r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)
    | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_694,plain,
    ( X0 = X1
    | r2_hidden(k4_tarski(sK0(X1,X0),sK1(X1,X0)),X0) = iProver_top
    | r2_hidden(k4_tarski(sK0(X1,X0),sK1(X1,X0)),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_17,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,X0) = X2 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_10,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_101,plain,
    ( ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,X0) = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6,c_10])).

cnf(c_102,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(renaming,[status(thm)],[c_101])).

cnf(c_269,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_102])).

cnf(c_270,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK5)
    | ~ v1_relat_1(sK5)
    | k1_funct_1(sK5,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_269])).

cnf(c_18,negated_conjecture,
    ( v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_274,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK5)
    | k1_funct_1(sK5,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_270,c_18])).

cnf(c_681,plain,
    ( k1_funct_1(sK5,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_274])).

cnf(c_1765,plain,
    ( k1_funct_1(sK5,sK0(sK5,X0)) = sK1(sK5,X0)
    | sK5 = X0
    | r2_hidden(k4_tarski(sK0(sK5,X0),sK1(sK5,X0)),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_694,c_681])).

cnf(c_19,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_13376,plain,
    ( v1_relat_1(X0) != iProver_top
    | r2_hidden(k4_tarski(sK0(sK5,X0),sK1(sK5,X0)),X0) = iProver_top
    | sK5 = X0
    | k1_funct_1(sK5,sK0(sK5,X0)) = sK1(sK5,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1765,c_19])).

cnf(c_13377,plain,
    ( k1_funct_1(sK5,sK0(sK5,X0)) = sK1(sK5,X0)
    | sK5 = X0
    | r2_hidden(k4_tarski(sK0(sK5,X0),sK1(sK5,X0)),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_13376])).

cnf(c_15,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_251,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1
    | sK6 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_102])).

cnf(c_252,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK6)
    | ~ v1_relat_1(sK6)
    | k1_funct_1(sK6,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_251])).

cnf(c_16,negated_conjecture,
    ( v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_256,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK6)
    | k1_funct_1(sK6,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_252,c_16])).

cnf(c_682,plain,
    ( k1_funct_1(sK6,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_256])).

cnf(c_13389,plain,
    ( k1_funct_1(sK6,sK0(sK5,sK6)) = sK1(sK5,sK6)
    | k1_funct_1(sK5,sK0(sK5,sK6)) = sK1(sK5,sK6)
    | sK6 = sK5
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_13377,c_682])).

cnf(c_14,negated_conjecture,
    ( k1_relat_1(sK5) = k1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_691,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1761,plain,
    ( X0 = X1
    | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) = iProver_top
    | r2_hidden(sK0(X0,X1),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_694,c_691])).

cnf(c_10713,plain,
    ( X0 = X1
    | r2_hidden(sK0(X1,X0),k1_relat_1(X1)) = iProver_top
    | r2_hidden(sK0(X1,X0),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1761,c_691])).

cnf(c_11110,plain,
    ( sK6 = X0
    | r2_hidden(sK0(X0,sK6),k1_relat_1(X0)) = iProver_top
    | r2_hidden(sK0(X0,sK6),k1_relat_1(sK5)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_14,c_10713])).

cnf(c_21,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_11353,plain,
    ( v1_relat_1(X0) != iProver_top
    | r2_hidden(sK0(X0,sK6),k1_relat_1(sK5)) = iProver_top
    | r2_hidden(sK0(X0,sK6),k1_relat_1(X0)) = iProver_top
    | sK6 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11110,c_21])).

cnf(c_11354,plain,
    ( sK6 = X0
    | r2_hidden(sK0(X0,sK6),k1_relat_1(X0)) = iProver_top
    | r2_hidden(sK0(X0,sK6),k1_relat_1(sK5)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_11353])).

cnf(c_13,negated_conjecture,
    ( ~ r2_hidden(X0,k1_relat_1(sK5))
    | k1_funct_1(sK5,X0) = k1_funct_1(sK6,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_689,plain,
    ( k1_funct_1(sK5,X0) = k1_funct_1(sK6,X0)
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_11366,plain,
    ( k1_funct_1(sK5,sK0(X0,sK6)) = k1_funct_1(sK6,sK0(X0,sK6))
    | sK6 = X0
    | r2_hidden(sK0(X0,sK6),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_11354,c_689])).

cnf(c_12302,plain,
    ( k1_funct_1(sK6,sK0(sK5,sK6)) = k1_funct_1(sK5,sK0(sK5,sK6))
    | sK6 = sK5
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_11366,c_689])).

cnf(c_12,negated_conjecture,
    ( sK5 != sK6 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_413,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_426,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_413])).

cnf(c_414,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_840,plain,
    ( sK6 != X0
    | sK5 != X0
    | sK5 = sK6 ),
    inference(instantiation,[status(thm)],[c_414])).

cnf(c_841,plain,
    ( sK6 != sK5
    | sK5 = sK6
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_840])).

cnf(c_12361,plain,
    ( k1_funct_1(sK6,sK0(sK5,sK6)) = k1_funct_1(sK5,sK0(sK5,sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12302,c_19,c_12,c_426,c_841])).

cnf(c_13440,plain,
    ( k1_funct_1(sK5,sK0(sK5,sK6)) = sK1(sK5,sK6)
    | sK6 = sK5
    | v1_relat_1(sK6) != iProver_top ),
    inference(demodulation,[status(thm)],[c_13389,c_12361])).

cnf(c_23494,plain,
    ( k1_funct_1(sK5,sK0(sK5,sK6)) = sK1(sK5,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13440,c_21,c_12,c_426,c_841])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_215,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_relat_1(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_17])).

cnf(c_216,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK5))
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK5,X0)),sK5)
    | ~ v1_relat_1(sK5) ),
    inference(unflattening,[status(thm)],[c_215])).

cnf(c_220,plain,
    ( r2_hidden(k4_tarski(X0,k1_funct_1(sK5,X0)),sK5)
    | ~ r2_hidden(X0,k1_relat_1(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_216,c_18])).

cnf(c_221,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK5))
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK5,X0)),sK5) ),
    inference(renaming,[status(thm)],[c_220])).

cnf(c_684,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK5,X0)),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_221])).

cnf(c_23512,plain,
    ( r2_hidden(k4_tarski(sK0(sK5,sK6),sK1(sK5,sK6)),sK5) = iProver_top
    | r2_hidden(sK0(sK5,sK6),k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_23494,c_684])).

cnf(c_179,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_relat_1(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_15])).

cnf(c_180,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK6))
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6)
    | ~ v1_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_179])).

cnf(c_184,plain,
    ( r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6)
    | ~ r2_hidden(X0,k1_relat_1(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_180,c_16])).

cnf(c_185,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK6))
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6) ),
    inference(renaming,[status(thm)],[c_184])).

cnf(c_686,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_185])).

cnf(c_733,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_686,c_14])).

cnf(c_12365,plain,
    ( r2_hidden(k4_tarski(sK0(sK5,sK6),k1_funct_1(sK5,sK0(sK5,sK6))),sK6) = iProver_top
    | r2_hidden(sK0(sK5,sK6),k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12361,c_733])).

cnf(c_11311,plain,
    ( sK6 = sK5
    | r2_hidden(sK0(sK5,sK6),k1_relat_1(sK5)) = iProver_top
    | v1_relat_1(sK6) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_11110])).

cnf(c_12450,plain,
    ( r2_hidden(k4_tarski(sK0(sK5,sK6),k1_funct_1(sK5,sK0(sK5,sK6))),sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12365,c_19,c_21,c_12,c_426,c_841,c_11311])).

cnf(c_23499,plain,
    ( r2_hidden(k4_tarski(sK0(sK5,sK6),sK1(sK5,sK6)),sK6) = iProver_top ),
    inference(demodulation,[status(thm)],[c_23494,c_12450])).

cnf(c_0,plain,
    ( ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)
    | ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_873,plain,
    ( ~ r2_hidden(k4_tarski(sK0(X0,sK6),sK1(X0,sK6)),X0)
    | ~ r2_hidden(k4_tarski(sK0(X0,sK6),sK1(X0,sK6)),sK6)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK6)
    | sK6 = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_874,plain,
    ( sK6 = X0
    | r2_hidden(k4_tarski(sK0(X0,sK6),sK1(X0,sK6)),X0) != iProver_top
    | r2_hidden(k4_tarski(sK0(X0,sK6),sK1(X0,sK6)),sK6) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_873])).

cnf(c_876,plain,
    ( sK6 = sK5
    | r2_hidden(k4_tarski(sK0(sK5,sK6),sK1(sK5,sK6)),sK6) != iProver_top
    | r2_hidden(k4_tarski(sK0(sK5,sK6),sK1(sK5,sK6)),sK5) != iProver_top
    | v1_relat_1(sK6) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_874])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_23512,c_23499,c_11311,c_876,c_841,c_426,c_12,c_21,c_19])).


%------------------------------------------------------------------------------
