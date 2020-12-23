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
% DateTime   : Thu Dec  3 11:49:09 EST 2020

% Result     : Theorem 11.49s
% Output     : CNFRefutation 11.49s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 907 expanded)
%              Number of clauses        :  111 ( 286 expanded)
%              Number of leaves         :   14 ( 243 expanded)
%              Depth                    :   18
%              Number of atoms          :  556 (5489 expanded)
%              Number of equality atoms :  282 (2026 expanded)
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

fof(f28,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)
      | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

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

fof(f24,plain,(
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

fof(f23,plain,
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

fof(f25,plain,
    ( sK5 != sK6
    & ! [X2] :
        ( k1_funct_1(sK5,X2) = k1_funct_1(sK6,X2)
        | ~ r2_hidden(X2,k1_relat_1(sK5)) )
    & k1_relat_1(sK5) = k1_relat_1(sK6)
    & v1_funct_1(sK6)
    & v1_relat_1(sK6)
    & v1_funct_1(sK5)
    & v1_relat_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f10,f24,f23])).

fof(f40,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f25])).

fof(f39,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f25])).

fof(f41,plain,(
    k1_relat_1(sK5) = k1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f16,plain,(
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
    inference(rectify,[],[f15])).

fof(f19,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK3(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
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

fof(f20,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f16,f19,f18,f17])).

fof(f31,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f46,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f31])).

fof(f30,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f47,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f30])).

fof(f37,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f25])).

fof(f43,plain,(
    sK5 != sK6 ),
    inference(cnf_transformation,[],[f25])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f48,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f36])).

fof(f38,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f25])).

fof(f42,plain,(
    ! [X2] :
      ( k1_funct_1(sK5,X2) = k1_funct_1(sK6,X2)
      | ~ r2_hidden(X2,k1_relat_1(sK5)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f29,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)
      | ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_347,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_8004,plain,
    ( X0 != X1
    | k4_tarski(sK0(sK6,sK5),k1_funct_1(sK6,sK0(sK6,sK5))) != X1
    | k4_tarski(sK0(sK6,sK5),k1_funct_1(sK6,sK0(sK6,sK5))) = X0 ),
    inference(instantiation,[status(thm)],[c_347])).

cnf(c_18569,plain,
    ( X0 != k4_tarski(sK0(sK6,sK5),k1_funct_1(sK5,sK0(sK6,sK5)))
    | k4_tarski(sK0(sK6,sK5),k1_funct_1(sK6,sK0(sK6,sK5))) = X0
    | k4_tarski(sK0(sK6,sK5),k1_funct_1(sK6,sK0(sK6,sK5))) != k4_tarski(sK0(sK6,sK5),k1_funct_1(sK5,sK0(sK6,sK5))) ),
    inference(instantiation,[status(thm)],[c_8004])).

cnf(c_30019,plain,
    ( k4_tarski(sK0(sK6,sK5),k1_funct_1(sK6,sK0(sK6,sK5))) != k4_tarski(sK0(sK6,sK5),k1_funct_1(sK5,sK0(sK6,sK5)))
    | k4_tarski(sK0(sK6,sK5),k1_funct_1(sK6,sK0(sK6,sK5))) = k4_tarski(sK0(sK6,sK5),sK1(sK6,sK5))
    | k4_tarski(sK0(sK6,sK5),sK1(sK6,sK5)) != k4_tarski(sK0(sK6,sK5),k1_funct_1(sK5,sK0(sK6,sK5))) ),
    inference(instantiation,[status(thm)],[c_18569])).

cnf(c_1738,plain,
    ( X0 != X1
    | sK1(sK6,sK5) != X1
    | sK1(sK6,sK5) = X0 ),
    inference(instantiation,[status(thm)],[c_347])).

cnf(c_5143,plain,
    ( X0 != sK1(sK6,sK5)
    | sK1(sK6,sK5) = X0
    | sK1(sK6,sK5) != sK1(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_1738])).

cnf(c_22210,plain,
    ( k1_funct_1(sK5,sK0(sK6,sK5)) != sK1(sK6,sK5)
    | sK1(sK6,sK5) = k1_funct_1(sK5,sK0(sK6,sK5))
    | sK1(sK6,sK5) != sK1(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_5143])).

cnf(c_348,plain,
    ( X0 != X1
    | X2 != X3
    | k4_tarski(X0,X2) = k4_tarski(X1,X3) ),
    theory(equality)).

cnf(c_2477,plain,
    ( X0 != k1_funct_1(sK5,sK0(sK6,sK5))
    | X1 != sK0(sK6,sK5)
    | k4_tarski(X1,X0) = k4_tarski(sK0(sK6,sK5),k1_funct_1(sK5,sK0(sK6,sK5))) ),
    inference(instantiation,[status(thm)],[c_348])).

cnf(c_4207,plain,
    ( X0 != k1_funct_1(sK5,sK0(sK6,sK5))
    | k4_tarski(sK0(sK6,sK5),X0) = k4_tarski(sK0(sK6,sK5),k1_funct_1(sK5,sK0(sK6,sK5)))
    | sK0(sK6,sK5) != sK0(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_2477])).

cnf(c_16663,plain,
    ( k4_tarski(sK0(sK6,sK5),sK1(sK6,sK5)) = k4_tarski(sK0(sK6,sK5),k1_funct_1(sK5,sK0(sK6,sK5)))
    | sK1(sK6,sK5) != k1_funct_1(sK5,sK0(sK6,sK5))
    | sK0(sK6,sK5) != sK0(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_4207])).

cnf(c_349,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3663,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(sK0(sK6,sK5),k1_funct_1(sK5,sK0(sK6,sK5))),X2)
    | X1 != X2
    | X0 != k4_tarski(sK0(sK6,sK5),k1_funct_1(sK5,sK0(sK6,sK5))) ),
    inference(instantiation,[status(thm)],[c_349])).

cnf(c_15225,plain,
    ( ~ r2_hidden(k4_tarski(sK0(sK6,sK5),k1_funct_1(sK5,sK0(sK6,sK5))),X0)
    | r2_hidden(k4_tarski(sK0(sK6,sK5),sK1(sK6,sK5)),X1)
    | X1 != X0
    | k4_tarski(sK0(sK6,sK5),sK1(sK6,sK5)) != k4_tarski(sK0(sK6,sK5),k1_funct_1(sK5,sK0(sK6,sK5))) ),
    inference(instantiation,[status(thm)],[c_3663])).

cnf(c_15228,plain,
    ( X0 != X1
    | k4_tarski(sK0(sK6,sK5),sK1(sK6,sK5)) != k4_tarski(sK0(sK6,sK5),k1_funct_1(sK5,sK0(sK6,sK5)))
    | r2_hidden(k4_tarski(sK0(sK6,sK5),k1_funct_1(sK5,sK0(sK6,sK5))),X1) != iProver_top
    | r2_hidden(k4_tarski(sK0(sK6,sK5),sK1(sK6,sK5)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15225])).

cnf(c_15230,plain,
    ( k4_tarski(sK0(sK6,sK5),sK1(sK6,sK5)) != k4_tarski(sK0(sK6,sK5),k1_funct_1(sK5,sK0(sK6,sK5)))
    | sK5 != sK5
    | r2_hidden(k4_tarski(sK0(sK6,sK5),k1_funct_1(sK5,sK0(sK6,sK5))),sK5) != iProver_top
    | r2_hidden(k4_tarski(sK0(sK6,sK5),sK1(sK6,sK5)),sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_15228])).

cnf(c_1334,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(sK0(sK6,sK5),k1_funct_1(sK6,sK0(sK6,sK5))),sK6)
    | X0 != k4_tarski(sK0(sK6,sK5),k1_funct_1(sK6,sK0(sK6,sK5)))
    | X1 != sK6 ),
    inference(instantiation,[status(thm)],[c_349])).

cnf(c_2132,plain,
    ( r2_hidden(X0,sK6)
    | ~ r2_hidden(k4_tarski(sK0(sK6,sK5),k1_funct_1(sK6,sK0(sK6,sK5))),sK6)
    | X0 != k4_tarski(sK0(sK6,sK5),k1_funct_1(sK6,sK0(sK6,sK5)))
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_1334])).

cnf(c_3639,plain,
    ( r2_hidden(k4_tarski(X0,X1),sK6)
    | ~ r2_hidden(k4_tarski(sK0(sK6,sK5),k1_funct_1(sK6,sK0(sK6,sK5))),sK6)
    | k4_tarski(X0,X1) != k4_tarski(sK0(sK6,sK5),k1_funct_1(sK6,sK0(sK6,sK5)))
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_2132])).

cnf(c_13980,plain,
    ( ~ r2_hidden(k4_tarski(sK0(sK6,sK5),k1_funct_1(sK6,sK0(sK6,sK5))),sK6)
    | r2_hidden(k4_tarski(sK0(sK6,sK5),k1_funct_1(sK5,sK0(sK6,sK5))),sK6)
    | k4_tarski(sK0(sK6,sK5),k1_funct_1(sK5,sK0(sK6,sK5))) != k4_tarski(sK0(sK6,sK5),k1_funct_1(sK6,sK0(sK6,sK5)))
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_3639])).

cnf(c_1221,plain,
    ( X0 != X1
    | k4_tarski(sK0(sK6,sK5),sK1(sK6,sK5)) != X1
    | k4_tarski(sK0(sK6,sK5),sK1(sK6,sK5)) = X0 ),
    inference(instantiation,[status(thm)],[c_347])).

cnf(c_6094,plain,
    ( X0 != k4_tarski(sK0(sK6,sK5),k1_funct_1(sK6,sK0(sK6,sK5)))
    | k4_tarski(sK0(sK6,sK5),sK1(sK6,sK5)) = X0
    | k4_tarski(sK0(sK6,sK5),sK1(sK6,sK5)) != k4_tarski(sK0(sK6,sK5),k1_funct_1(sK6,sK0(sK6,sK5))) ),
    inference(instantiation,[status(thm)],[c_1221])).

cnf(c_13972,plain,
    ( k4_tarski(sK0(sK6,sK5),k1_funct_1(sK5,sK0(sK6,sK5))) != k4_tarski(sK0(sK6,sK5),k1_funct_1(sK6,sK0(sK6,sK5)))
    | k4_tarski(sK0(sK6,sK5),sK1(sK6,sK5)) != k4_tarski(sK0(sK6,sK5),k1_funct_1(sK6,sK0(sK6,sK5)))
    | k4_tarski(sK0(sK6,sK5),sK1(sK6,sK5)) = k4_tarski(sK0(sK6,sK5),k1_funct_1(sK5,sK0(sK6,sK5))) ),
    inference(instantiation,[status(thm)],[c_6094])).

cnf(c_6853,plain,
    ( k1_funct_1(X0,sK0(sK6,sK5)) != k1_funct_1(sK5,sK0(sK6,sK5))
    | k4_tarski(sK0(sK6,sK5),k1_funct_1(X0,sK0(sK6,sK5))) = k4_tarski(sK0(sK6,sK5),k1_funct_1(sK5,sK0(sK6,sK5)))
    | sK0(sK6,sK5) != sK0(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_4207])).

cnf(c_11562,plain,
    ( k1_funct_1(sK6,sK0(sK6,sK5)) != k1_funct_1(sK5,sK0(sK6,sK5))
    | k4_tarski(sK0(sK6,sK5),k1_funct_1(sK6,sK0(sK6,sK5))) = k4_tarski(sK0(sK6,sK5),k1_funct_1(sK5,sK0(sK6,sK5)))
    | sK0(sK6,sK5) != sK0(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_6853])).

cnf(c_3640,plain,
    ( X0 != k1_funct_1(sK6,sK0(sK6,sK5))
    | X1 != sK0(sK6,sK5)
    | k4_tarski(X1,X0) = k4_tarski(sK0(sK6,sK5),k1_funct_1(sK6,sK0(sK6,sK5))) ),
    inference(instantiation,[status(thm)],[c_348])).

cnf(c_8021,plain,
    ( X0 != k1_funct_1(sK6,sK0(sK6,sK5))
    | k4_tarski(sK0(sK6,sK5),X0) = k4_tarski(sK0(sK6,sK5),k1_funct_1(sK6,sK0(sK6,sK5)))
    | sK0(sK6,sK5) != sK0(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_3640])).

cnf(c_10949,plain,
    ( k4_tarski(sK0(sK6,sK5),sK1(sK6,sK5)) = k4_tarski(sK0(sK6,sK5),k1_funct_1(sK6,sK0(sK6,sK5)))
    | sK1(sK6,sK5) != k1_funct_1(sK6,sK0(sK6,sK5))
    | sK0(sK6,sK5) != sK0(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_8021])).

cnf(c_10943,plain,
    ( k1_funct_1(X0,sK0(sK6,sK5)) != k1_funct_1(sK6,sK0(sK6,sK5))
    | k4_tarski(sK0(sK6,sK5),k1_funct_1(X0,sK0(sK6,sK5))) = k4_tarski(sK0(sK6,sK5),k1_funct_1(sK6,sK0(sK6,sK5)))
    | sK0(sK6,sK5) != sK0(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_8021])).

cnf(c_10945,plain,
    ( k1_funct_1(sK5,sK0(sK6,sK5)) != k1_funct_1(sK6,sK0(sK6,sK5))
    | k4_tarski(sK0(sK6,sK5),k1_funct_1(sK5,sK0(sK6,sK5))) = k4_tarski(sK0(sK6,sK5),k1_funct_1(sK6,sK0(sK6,sK5)))
    | sK0(sK6,sK5) != sK0(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_10943])).

cnf(c_9716,plain,
    ( k1_funct_1(sK6,sK0(sK6,sK5)) != sK1(sK6,sK5)
    | sK1(sK6,sK5) = k1_funct_1(sK6,sK0(sK6,sK5))
    | sK1(sK6,sK5) != sK1(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_5143])).

cnf(c_8014,plain,
    ( ~ r2_hidden(k4_tarski(sK0(sK6,sK5),k1_funct_1(sK6,sK0(sK6,sK5))),sK6)
    | r2_hidden(k4_tarski(sK0(sK6,sK5),sK1(sK6,sK5)),sK6)
    | k4_tarski(sK0(sK6,sK5),sK1(sK6,sK5)) != k4_tarski(sK0(sK6,sK5),k1_funct_1(sK6,sK0(sK6,sK5)))
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_3639])).

cnf(c_8015,plain,
    ( k4_tarski(sK0(sK6,sK5),sK1(sK6,sK5)) != k4_tarski(sK0(sK6,sK5),k1_funct_1(sK6,sK0(sK6,sK5)))
    | sK6 != sK6
    | r2_hidden(k4_tarski(sK0(sK6,sK5),k1_funct_1(sK6,sK0(sK6,sK5))),sK6) != iProver_top
    | r2_hidden(k4_tarski(sK0(sK6,sK5),sK1(sK6,sK5)),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8014])).

cnf(c_1,plain,
    ( r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)
    | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_608,plain,
    ( X0 = X1
    | r2_hidden(k4_tarski(sK0(X1,X0),sK1(X1,X0)),X0) = iProver_top
    | r2_hidden(k4_tarski(sK0(X1,X0),sK1(X1,X0)),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_9,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_14,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_204,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1
    | sK6 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_14])).

cnf(c_205,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK6)
    | ~ v1_relat_1(sK6)
    | k1_funct_1(sK6,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_204])).

cnf(c_15,negated_conjecture,
    ( v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_209,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK6)
    | k1_funct_1(sK6,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_205,c_15])).

cnf(c_598,plain,
    ( k1_funct_1(sK6,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_209])).

cnf(c_1768,plain,
    ( k1_funct_1(sK6,sK0(sK6,X0)) = sK1(sK6,X0)
    | sK6 = X0
    | r2_hidden(k4_tarski(sK0(sK6,X0),sK1(sK6,X0)),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_608,c_598])).

cnf(c_20,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_7302,plain,
    ( v1_relat_1(X0) != iProver_top
    | r2_hidden(k4_tarski(sK0(sK6,X0),sK1(sK6,X0)),X0) = iProver_top
    | sK6 = X0
    | k1_funct_1(sK6,sK0(sK6,X0)) = sK1(sK6,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1768,c_20])).

cnf(c_7303,plain,
    ( k1_funct_1(sK6,sK0(sK6,X0)) = sK1(sK6,X0)
    | sK6 = X0
    | r2_hidden(k4_tarski(sK0(sK6,X0),sK1(sK6,X0)),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_7302])).

cnf(c_7305,plain,
    ( k1_funct_1(sK6,sK0(sK6,sK5)) = sK1(sK6,sK5)
    | sK6 = sK5
    | r2_hidden(k4_tarski(sK0(sK6,sK5),sK1(sK6,sK5)),sK5) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7303])).

cnf(c_13,negated_conjecture,
    ( k1_relat_1(sK5) = k1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_6,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_605,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1765,plain,
    ( X0 = X1
    | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) = iProver_top
    | r2_hidden(sK0(X0,X1),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_608,c_605])).

cnf(c_4260,plain,
    ( X0 = X1
    | r2_hidden(sK0(X1,X0),k1_relat_1(X1)) = iProver_top
    | r2_hidden(sK0(X1,X0),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1765,c_605])).

cnf(c_4382,plain,
    ( sK6 = X0
    | r2_hidden(sK0(sK6,X0),k1_relat_1(X0)) = iProver_top
    | r2_hidden(sK0(sK6,X0),k1_relat_1(sK5)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_4260])).

cnf(c_4729,plain,
    ( v1_relat_1(X0) != iProver_top
    | r2_hidden(sK0(sK6,X0),k1_relat_1(sK5)) = iProver_top
    | r2_hidden(sK0(sK6,X0),k1_relat_1(X0)) = iProver_top
    | sK6 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4382,c_20])).

cnf(c_4730,plain,
    ( sK6 = X0
    | r2_hidden(sK0(sK6,X0),k1_relat_1(X0)) = iProver_top
    | r2_hidden(sK0(sK6,X0),k1_relat_1(sK5)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4729])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,sK4(X1,X0)),X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_604,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK4(X1,X0)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1075,plain,
    ( k1_funct_1(sK6,X0) = sK4(sK6,X0)
    | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_604,c_598])).

cnf(c_1083,plain,
    ( k1_funct_1(sK6,X0) = sK4(sK6,X0)
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1075,c_13])).

cnf(c_4741,plain,
    ( k1_funct_1(sK6,sK0(sK6,X0)) = sK4(sK6,sK0(sK6,X0))
    | sK6 = X0
    | r2_hidden(sK0(sK6,X0),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4730,c_1083])).

cnf(c_5835,plain,
    ( k1_funct_1(sK6,sK0(sK6,sK5)) = sK4(sK6,sK0(sK6,sK5))
    | sK6 = sK5
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4741,c_1083])).

cnf(c_17,negated_conjecture,
    ( v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_18,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_11,negated_conjecture,
    ( sK5 != sK6 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_346,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_359,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_346])).

cnf(c_735,plain,
    ( sK6 != X0
    | sK5 != X0
    | sK5 = sK6 ),
    inference(instantiation,[status(thm)],[c_347])).

cnf(c_736,plain,
    ( sK6 != sK5
    | sK5 = sK6
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_735])).

cnf(c_5893,plain,
    ( k1_funct_1(sK6,sK0(sK6,sK5)) = sK4(sK6,sK0(sK6,sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5835,c_18,c_11,c_359,c_736])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_168,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_relat_1(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_14])).

cnf(c_169,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK6))
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6)
    | ~ v1_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_168])).

cnf(c_173,plain,
    ( r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6)
    | ~ r2_hidden(X0,k1_relat_1(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_169,c_15])).

cnf(c_174,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK6))
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6) ),
    inference(renaming,[status(thm)],[c_173])).

cnf(c_600,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_174])).

cnf(c_638,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_600,c_13])).

cnf(c_5896,plain,
    ( r2_hidden(k4_tarski(sK0(sK6,sK5),sK4(sK6,sK0(sK6,sK5))),sK6) = iProver_top
    | r2_hidden(sK0(sK6,sK5),k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5893,c_638])).

cnf(c_5897,plain,
    ( r2_hidden(k4_tarski(sK0(sK6,sK5),sK4(sK6,sK0(sK6,sK5))),sK6)
    | ~ r2_hidden(sK0(sK6,sK5),k1_relat_1(sK5)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5896])).

cnf(c_4540,plain,
    ( r2_hidden(sK0(sK6,X0),k1_relat_1(X0))
    | r2_hidden(sK0(sK6,X0),k1_relat_1(sK5))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK6)
    | sK6 = X0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4382])).

cnf(c_4542,plain,
    ( r2_hidden(sK0(sK6,sK5),k1_relat_1(sK5))
    | ~ v1_relat_1(sK6)
    | ~ v1_relat_1(sK5)
    | sK6 = sK5 ),
    inference(instantiation,[status(thm)],[c_4540])).

cnf(c_4541,plain,
    ( sK6 = sK5
    | r2_hidden(sK0(sK6,sK5),k1_relat_1(sK5)) = iProver_top
    | v1_relat_1(sK6) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4382])).

cnf(c_3668,plain,
    ( ~ r2_hidden(k4_tarski(sK0(sK6,sK5),k1_funct_1(sK5,sK0(sK6,sK5))),sK6)
    | k1_funct_1(sK6,sK0(sK6,sK5)) = k1_funct_1(sK5,sK0(sK6,sK5)) ),
    inference(instantiation,[status(thm)],[c_209])).

cnf(c_1728,plain,
    ( X0 != k4_tarski(sK0(sK6,sK5),sK1(sK6,sK5))
    | k4_tarski(sK0(sK6,sK5),sK1(sK6,sK5)) = X0
    | k4_tarski(sK0(sK6,sK5),sK1(sK6,sK5)) != k4_tarski(sK0(sK6,sK5),sK1(sK6,sK5)) ),
    inference(instantiation,[status(thm)],[c_1221])).

cnf(c_3367,plain,
    ( k4_tarski(sK0(sK6,sK5),k1_funct_1(sK6,sK0(sK6,sK5))) != k4_tarski(sK0(sK6,sK5),sK1(sK6,sK5))
    | k4_tarski(sK0(sK6,sK5),sK1(sK6,sK5)) = k4_tarski(sK0(sK6,sK5),k1_funct_1(sK6,sK0(sK6,sK5)))
    | k4_tarski(sK0(sK6,sK5),sK1(sK6,sK5)) != k4_tarski(sK0(sK6,sK5),sK1(sK6,sK5)) ),
    inference(instantiation,[status(thm)],[c_1728])).

cnf(c_1736,plain,
    ( sK1(sK6,sK5) = sK1(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_346])).

cnf(c_1340,plain,
    ( ~ r2_hidden(k4_tarski(sK0(sK6,sK5),sK4(sK6,sK0(sK6,sK5))),sK6)
    | r2_hidden(sK0(sK6,sK5),k1_relat_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1341,plain,
    ( r2_hidden(k4_tarski(sK0(sK6,sK5),sK4(sK6,sK0(sK6,sK5))),sK6) != iProver_top
    | r2_hidden(sK0(sK6,sK5),k1_relat_1(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1340])).

cnf(c_1191,plain,
    ( sK0(sK6,sK5) = sK0(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_346])).

cnf(c_933,plain,
    ( k4_tarski(sK0(sK6,sK5),sK1(sK6,sK5)) = k4_tarski(sK0(sK6,sK5),sK1(sK6,sK5)) ),
    inference(instantiation,[status(thm)],[c_346])).

cnf(c_16,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_186,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_relat_1(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_16])).

cnf(c_187,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK5))
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK5,X0)),sK5)
    | ~ v1_relat_1(sK5) ),
    inference(unflattening,[status(thm)],[c_186])).

cnf(c_191,plain,
    ( r2_hidden(k4_tarski(X0,k1_funct_1(sK5,X0)),sK5)
    | ~ r2_hidden(X0,k1_relat_1(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_187,c_17])).

cnf(c_192,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK5))
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK5,X0)),sK5) ),
    inference(renaming,[status(thm)],[c_191])).

cnf(c_906,plain,
    ( r2_hidden(k4_tarski(sK0(sK6,sK5),k1_funct_1(sK5,sK0(sK6,sK5))),sK5)
    | ~ r2_hidden(sK0(sK6,sK5),k1_relat_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_192])).

cnf(c_910,plain,
    ( r2_hidden(k4_tarski(sK0(sK6,sK5),k1_funct_1(sK5,sK0(sK6,sK5))),sK5) = iProver_top
    | r2_hidden(sK0(sK6,sK5),k1_relat_1(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_906])).

cnf(c_12,negated_conjecture,
    ( ~ r2_hidden(X0,k1_relat_1(sK5))
    | k1_funct_1(sK5,X0) = k1_funct_1(sK6,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_907,plain,
    ( ~ r2_hidden(sK0(sK6,sK5),k1_relat_1(sK5))
    | k1_funct_1(sK5,sK0(sK6,sK5)) = k1_funct_1(sK6,sK0(sK6,sK5)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_908,plain,
    ( k1_funct_1(sK5,sK0(sK6,sK5)) = k1_funct_1(sK6,sK0(sK6,sK5))
    | r2_hidden(sK0(sK6,sK5),k1_relat_1(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_907])).

cnf(c_834,plain,
    ( r2_hidden(k4_tarski(sK0(sK6,sK5),k1_funct_1(sK6,sK0(sK6,sK5))),sK6)
    | ~ r2_hidden(sK0(sK6,sK5),k1_relat_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_174])).

cnf(c_835,plain,
    ( r2_hidden(k4_tarski(sK0(sK6,sK5),k1_funct_1(sK6,sK0(sK6,sK5))),sK6) = iProver_top
    | r2_hidden(sK0(sK6,sK5),k1_relat_1(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_834])).

cnf(c_794,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_346])).

cnf(c_0,plain,
    ( ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)
    | ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_780,plain,
    ( ~ r2_hidden(k4_tarski(sK0(sK6,sK5),sK1(sK6,sK5)),sK6)
    | ~ r2_hidden(k4_tarski(sK0(sK6,sK5),sK1(sK6,sK5)),sK5)
    | ~ v1_relat_1(sK6)
    | ~ v1_relat_1(sK5)
    | sK5 = sK6 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_781,plain,
    ( sK5 = sK6
    | r2_hidden(k4_tarski(sK0(sK6,sK5),sK1(sK6,sK5)),sK6) != iProver_top
    | r2_hidden(k4_tarski(sK0(sK6,sK5),sK1(sK6,sK5)),sK5) != iProver_top
    | v1_relat_1(sK6) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_780])).

cnf(c_222,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_16])).

cnf(c_223,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK5)
    | ~ v1_relat_1(sK5)
    | k1_funct_1(sK5,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_222])).

cnf(c_227,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK5)
    | k1_funct_1(sK5,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_223,c_17])).

cnf(c_770,plain,
    ( ~ r2_hidden(k4_tarski(sK0(sK6,sK5),sK1(sK6,sK5)),sK5)
    | k1_funct_1(sK5,sK0(sK6,sK5)) = sK1(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_227])).

cnf(c_771,plain,
    ( k1_funct_1(sK5,sK0(sK6,sK5)) = sK1(sK6,sK5)
    | r2_hidden(k4_tarski(sK0(sK6,sK5),sK1(sK6,sK5)),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_770])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_30019,c_22210,c_16663,c_15230,c_13980,c_13972,c_11562,c_10949,c_10945,c_9716,c_8015,c_7305,c_5897,c_5896,c_4542,c_4541,c_3668,c_3367,c_1736,c_1341,c_1340,c_1191,c_933,c_910,c_908,c_835,c_834,c_794,c_781,c_771,c_736,c_359,c_11,c_20,c_15,c_18,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n023.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 16:58:51 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 11.49/1.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.49/1.98  
% 11.49/1.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.49/1.98  
% 11.49/1.98  ------  iProver source info
% 11.49/1.98  
% 11.49/1.98  git: date: 2020-06-30 10:37:57 +0100
% 11.49/1.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.49/1.98  git: non_committed_changes: false
% 11.49/1.98  git: last_make_outside_of_git: false
% 11.49/1.98  
% 11.49/1.98  ------ 
% 11.49/1.98  ------ Parsing...
% 11.49/1.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.49/1.98  
% 11.49/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 11.49/1.98  
% 11.49/1.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.49/1.98  
% 11.49/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.49/1.98  ------ Proving...
% 11.49/1.98  ------ Problem Properties 
% 11.49/1.98  
% 11.49/1.98  
% 11.49/1.98  clauses                                 15
% 11.49/1.98  conjectures                             5
% 11.49/1.98  EPR                                     3
% 11.49/1.98  Horn                                    13
% 11.49/1.98  unary                                   4
% 11.49/1.98  binary                                  7
% 11.49/1.98  lits                                    34
% 11.49/1.98  lits eq                                 9
% 11.49/1.98  fd_pure                                 0
% 11.49/1.98  fd_pseudo                               0
% 11.49/1.98  fd_cond                                 0
% 11.49/1.98  fd_pseudo_cond                          6
% 11.49/1.98  AC symbols                              0
% 11.49/1.98  
% 11.49/1.98  ------ Input Options Time Limit: Unbounded
% 11.49/1.98  
% 11.49/1.98  
% 11.49/1.98  ------ 
% 11.49/1.98  Current options:
% 11.49/1.98  ------ 
% 11.49/1.98  
% 11.49/1.98  
% 11.49/1.98  
% 11.49/1.98  
% 11.49/1.98  ------ Proving...
% 11.49/1.98  
% 11.49/1.98  
% 11.49/1.98  % SZS status Theorem for theBenchmark.p
% 11.49/1.98  
% 11.49/1.98  % SZS output start CNFRefutation for theBenchmark.p
% 11.49/1.98  
% 11.49/1.98  fof(f1,axiom,(
% 11.49/1.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (X0 = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) <=> r2_hidden(k4_tarski(X2,X3),X1)))))),
% 11.49/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.49/1.98  
% 11.49/1.98  fof(f6,plain,(
% 11.49/1.98    ! [X0] : (! [X1] : ((X0 = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) <=> r2_hidden(k4_tarski(X2,X3),X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 11.49/1.98    inference(ennf_transformation,[],[f1])).
% 11.49/1.98  
% 11.49/1.98  fof(f11,plain,(
% 11.49/1.98    ! [X0] : (! [X1] : (((X0 = X1 | ? [X2,X3] : ((~r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0)) & (r2_hidden(k4_tarski(X2,X3),X1) | r2_hidden(k4_tarski(X2,X3),X0)))) & (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0))) | X0 != X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 11.49/1.98    inference(nnf_transformation,[],[f6])).
% 11.49/1.98  
% 11.49/1.98  fof(f12,plain,(
% 11.49/1.98    ! [X0] : (! [X1] : (((X0 = X1 | ? [X2,X3] : ((~r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0)) & (r2_hidden(k4_tarski(X2,X3),X1) | r2_hidden(k4_tarski(X2,X3),X0)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X0) | ~r2_hidden(k4_tarski(X4,X5),X1)) & (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0))) | X0 != X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 11.49/1.98    inference(rectify,[],[f11])).
% 11.49/1.98  
% 11.49/1.98  fof(f13,plain,(
% 11.49/1.98    ! [X1,X0] : (? [X2,X3] : ((~r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0)) & (r2_hidden(k4_tarski(X2,X3),X1) | r2_hidden(k4_tarski(X2,X3),X0))) => ((~r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) | ~r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0)) & (r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0))))),
% 11.49/1.98    introduced(choice_axiom,[])).
% 11.49/1.98  
% 11.49/1.98  fof(f14,plain,(
% 11.49/1.98    ! [X0] : (! [X1] : (((X0 = X1 | ((~r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) | ~r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0)) & (r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X0) | ~r2_hidden(k4_tarski(X4,X5),X1)) & (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0))) | X0 != X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 11.49/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f13])).
% 11.49/1.98  
% 11.49/1.98  fof(f28,plain,(
% 11.49/1.98    ( ! [X0,X1] : (X0 = X1 | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 11.49/1.98    inference(cnf_transformation,[],[f14])).
% 11.49/1.98  
% 11.49/1.98  fof(f3,axiom,(
% 11.49/1.98    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 11.49/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.49/1.98  
% 11.49/1.98  fof(f7,plain,(
% 11.49/1.98    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 11.49/1.98    inference(ennf_transformation,[],[f3])).
% 11.49/1.98  
% 11.49/1.98  fof(f8,plain,(
% 11.49/1.98    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 11.49/1.98    inference(flattening,[],[f7])).
% 11.49/1.98  
% 11.49/1.98  fof(f21,plain,(
% 11.49/1.98    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 11.49/1.98    inference(nnf_transformation,[],[f8])).
% 11.49/1.98  
% 11.49/1.98  fof(f22,plain,(
% 11.49/1.98    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 11.49/1.98    inference(flattening,[],[f21])).
% 11.49/1.98  
% 11.49/1.98  fof(f35,plain,(
% 11.49/1.98    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 11.49/1.98    inference(cnf_transformation,[],[f22])).
% 11.49/1.98  
% 11.49/1.98  fof(f4,conjecture,(
% 11.49/1.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 11.49/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.49/1.98  
% 11.49/1.98  fof(f5,negated_conjecture,(
% 11.49/1.98    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 11.49/1.98    inference(negated_conjecture,[],[f4])).
% 11.49/1.98  
% 11.49/1.98  fof(f9,plain,(
% 11.49/1.98    ? [X0] : (? [X1] : ((X0 != X1 & (! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0))) & k1_relat_1(X0) = k1_relat_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 11.49/1.98    inference(ennf_transformation,[],[f5])).
% 11.49/1.98  
% 11.49/1.98  fof(f10,plain,(
% 11.49/1.98    ? [X0] : (? [X1] : (X0 != X1 & ! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0))) & k1_relat_1(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 11.49/1.98    inference(flattening,[],[f9])).
% 11.49/1.98  
% 11.49/1.98  fof(f24,plain,(
% 11.49/1.98    ( ! [X0] : (? [X1] : (X0 != X1 & ! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0))) & k1_relat_1(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (sK6 != X0 & ! [X2] : (k1_funct_1(sK6,X2) = k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0))) & k1_relat_1(sK6) = k1_relat_1(X0) & v1_funct_1(sK6) & v1_relat_1(sK6))) )),
% 11.49/1.98    introduced(choice_axiom,[])).
% 11.49/1.98  
% 11.49/1.98  fof(f23,plain,(
% 11.49/1.98    ? [X0] : (? [X1] : (X0 != X1 & ! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0))) & k1_relat_1(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (sK5 != X1 & ! [X2] : (k1_funct_1(sK5,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(sK5))) & k1_relat_1(sK5) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK5) & v1_relat_1(sK5))),
% 11.49/1.98    introduced(choice_axiom,[])).
% 11.49/1.98  
% 11.49/1.98  fof(f25,plain,(
% 11.49/1.98    (sK5 != sK6 & ! [X2] : (k1_funct_1(sK5,X2) = k1_funct_1(sK6,X2) | ~r2_hidden(X2,k1_relat_1(sK5))) & k1_relat_1(sK5) = k1_relat_1(sK6) & v1_funct_1(sK6) & v1_relat_1(sK6)) & v1_funct_1(sK5) & v1_relat_1(sK5)),
% 11.49/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f10,f24,f23])).
% 11.49/1.98  
% 11.49/1.98  fof(f40,plain,(
% 11.49/1.98    v1_funct_1(sK6)),
% 11.49/1.98    inference(cnf_transformation,[],[f25])).
% 11.49/1.98  
% 11.49/1.98  fof(f39,plain,(
% 11.49/1.98    v1_relat_1(sK6)),
% 11.49/1.98    inference(cnf_transformation,[],[f25])).
% 11.49/1.98  
% 11.49/1.98  fof(f41,plain,(
% 11.49/1.98    k1_relat_1(sK5) = k1_relat_1(sK6)),
% 11.49/1.98    inference(cnf_transformation,[],[f25])).
% 11.49/1.98  
% 11.49/1.98  fof(f2,axiom,(
% 11.49/1.98    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 11.49/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.49/1.98  
% 11.49/1.98  fof(f15,plain,(
% 11.49/1.98    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 11.49/1.98    inference(nnf_transformation,[],[f2])).
% 11.49/1.98  
% 11.49/1.98  fof(f16,plain,(
% 11.49/1.98    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 11.49/1.98    inference(rectify,[],[f15])).
% 11.49/1.98  
% 11.49/1.98  fof(f19,plain,(
% 11.49/1.98    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0))),
% 11.49/1.98    introduced(choice_axiom,[])).
% 11.49/1.98  
% 11.49/1.98  fof(f18,plain,(
% 11.49/1.98    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) => r2_hidden(k4_tarski(X2,sK3(X0,X1)),X0))) )),
% 11.49/1.98    introduced(choice_axiom,[])).
% 11.49/1.98  
% 11.49/1.98  fof(f17,plain,(
% 11.49/1.98    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK2(X0,X1),X3),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK2(X0,X1),X4),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 11.49/1.98    introduced(choice_axiom,[])).
% 11.49/1.98  
% 11.49/1.98  fof(f20,plain,(
% 11.49/1.98    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK2(X0,X1),X3),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 11.49/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f16,f19,f18,f17])).
% 11.49/1.98  
% 11.49/1.98  fof(f31,plain,(
% 11.49/1.98    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 11.49/1.98    inference(cnf_transformation,[],[f20])).
% 11.49/1.98  
% 11.49/1.98  fof(f46,plain,(
% 11.49/1.98    ( ! [X6,X0,X5] : (r2_hidden(X5,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X5,X6),X0)) )),
% 11.49/1.98    inference(equality_resolution,[],[f31])).
% 11.49/1.98  
% 11.49/1.98  fof(f30,plain,(
% 11.49/1.98    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 11.49/1.98    inference(cnf_transformation,[],[f20])).
% 11.49/1.98  
% 11.49/1.98  fof(f47,plain,(
% 11.49/1.98    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 11.49/1.98    inference(equality_resolution,[],[f30])).
% 11.49/1.98  
% 11.49/1.98  fof(f37,plain,(
% 11.49/1.98    v1_relat_1(sK5)),
% 11.49/1.98    inference(cnf_transformation,[],[f25])).
% 11.49/1.98  
% 11.49/1.98  fof(f43,plain,(
% 11.49/1.98    sK5 != sK6),
% 11.49/1.98    inference(cnf_transformation,[],[f25])).
% 11.49/1.98  
% 11.49/1.98  fof(f36,plain,(
% 11.49/1.98    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 11.49/1.98    inference(cnf_transformation,[],[f22])).
% 11.49/1.98  
% 11.49/1.98  fof(f48,plain,(
% 11.49/1.98    ( ! [X2,X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 11.49/1.98    inference(equality_resolution,[],[f36])).
% 11.49/1.98  
% 11.49/1.98  fof(f38,plain,(
% 11.49/1.98    v1_funct_1(sK5)),
% 11.49/1.98    inference(cnf_transformation,[],[f25])).
% 11.49/1.98  
% 11.49/1.98  fof(f42,plain,(
% 11.49/1.98    ( ! [X2] : (k1_funct_1(sK5,X2) = k1_funct_1(sK6,X2) | ~r2_hidden(X2,k1_relat_1(sK5))) )),
% 11.49/1.98    inference(cnf_transformation,[],[f25])).
% 11.49/1.98  
% 11.49/1.98  fof(f29,plain,(
% 11.49/1.98    ( ! [X0,X1] : (X0 = X1 | ~r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) | ~r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 11.49/1.98    inference(cnf_transformation,[],[f14])).
% 11.49/1.98  
% 11.49/1.98  cnf(c_347,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_8004,plain,
% 11.49/1.98      ( X0 != X1
% 11.49/1.98      | k4_tarski(sK0(sK6,sK5),k1_funct_1(sK6,sK0(sK6,sK5))) != X1
% 11.49/1.98      | k4_tarski(sK0(sK6,sK5),k1_funct_1(sK6,sK0(sK6,sK5))) = X0 ),
% 11.49/1.98      inference(instantiation,[status(thm)],[c_347]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_18569,plain,
% 11.49/1.98      ( X0 != k4_tarski(sK0(sK6,sK5),k1_funct_1(sK5,sK0(sK6,sK5)))
% 11.49/1.98      | k4_tarski(sK0(sK6,sK5),k1_funct_1(sK6,sK0(sK6,sK5))) = X0
% 11.49/1.98      | k4_tarski(sK0(sK6,sK5),k1_funct_1(sK6,sK0(sK6,sK5))) != k4_tarski(sK0(sK6,sK5),k1_funct_1(sK5,sK0(sK6,sK5))) ),
% 11.49/1.98      inference(instantiation,[status(thm)],[c_8004]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_30019,plain,
% 11.49/1.98      ( k4_tarski(sK0(sK6,sK5),k1_funct_1(sK6,sK0(sK6,sK5))) != k4_tarski(sK0(sK6,sK5),k1_funct_1(sK5,sK0(sK6,sK5)))
% 11.49/1.98      | k4_tarski(sK0(sK6,sK5),k1_funct_1(sK6,sK0(sK6,sK5))) = k4_tarski(sK0(sK6,sK5),sK1(sK6,sK5))
% 11.49/1.98      | k4_tarski(sK0(sK6,sK5),sK1(sK6,sK5)) != k4_tarski(sK0(sK6,sK5),k1_funct_1(sK5,sK0(sK6,sK5))) ),
% 11.49/1.98      inference(instantiation,[status(thm)],[c_18569]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_1738,plain,
% 11.49/1.98      ( X0 != X1 | sK1(sK6,sK5) != X1 | sK1(sK6,sK5) = X0 ),
% 11.49/1.98      inference(instantiation,[status(thm)],[c_347]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_5143,plain,
% 11.49/1.98      ( X0 != sK1(sK6,sK5)
% 11.49/1.98      | sK1(sK6,sK5) = X0
% 11.49/1.98      | sK1(sK6,sK5) != sK1(sK6,sK5) ),
% 11.49/1.98      inference(instantiation,[status(thm)],[c_1738]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_22210,plain,
% 11.49/1.98      ( k1_funct_1(sK5,sK0(sK6,sK5)) != sK1(sK6,sK5)
% 11.49/1.98      | sK1(sK6,sK5) = k1_funct_1(sK5,sK0(sK6,sK5))
% 11.49/1.98      | sK1(sK6,sK5) != sK1(sK6,sK5) ),
% 11.49/1.98      inference(instantiation,[status(thm)],[c_5143]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_348,plain,
% 11.49/1.98      ( X0 != X1 | X2 != X3 | k4_tarski(X0,X2) = k4_tarski(X1,X3) ),
% 11.49/1.98      theory(equality) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_2477,plain,
% 11.49/1.98      ( X0 != k1_funct_1(sK5,sK0(sK6,sK5))
% 11.49/1.98      | X1 != sK0(sK6,sK5)
% 11.49/1.98      | k4_tarski(X1,X0) = k4_tarski(sK0(sK6,sK5),k1_funct_1(sK5,sK0(sK6,sK5))) ),
% 11.49/1.98      inference(instantiation,[status(thm)],[c_348]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_4207,plain,
% 11.49/1.98      ( X0 != k1_funct_1(sK5,sK0(sK6,sK5))
% 11.49/1.98      | k4_tarski(sK0(sK6,sK5),X0) = k4_tarski(sK0(sK6,sK5),k1_funct_1(sK5,sK0(sK6,sK5)))
% 11.49/1.98      | sK0(sK6,sK5) != sK0(sK6,sK5) ),
% 11.49/1.98      inference(instantiation,[status(thm)],[c_2477]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_16663,plain,
% 11.49/1.98      ( k4_tarski(sK0(sK6,sK5),sK1(sK6,sK5)) = k4_tarski(sK0(sK6,sK5),k1_funct_1(sK5,sK0(sK6,sK5)))
% 11.49/1.98      | sK1(sK6,sK5) != k1_funct_1(sK5,sK0(sK6,sK5))
% 11.49/1.98      | sK0(sK6,sK5) != sK0(sK6,sK5) ),
% 11.49/1.98      inference(instantiation,[status(thm)],[c_4207]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_349,plain,
% 11.49/1.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.49/1.98      theory(equality) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_3663,plain,
% 11.49/1.98      ( r2_hidden(X0,X1)
% 11.49/1.98      | ~ r2_hidden(k4_tarski(sK0(sK6,sK5),k1_funct_1(sK5,sK0(sK6,sK5))),X2)
% 11.49/1.98      | X1 != X2
% 11.49/1.98      | X0 != k4_tarski(sK0(sK6,sK5),k1_funct_1(sK5,sK0(sK6,sK5))) ),
% 11.49/1.98      inference(instantiation,[status(thm)],[c_349]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_15225,plain,
% 11.49/1.98      ( ~ r2_hidden(k4_tarski(sK0(sK6,sK5),k1_funct_1(sK5,sK0(sK6,sK5))),X0)
% 11.49/1.98      | r2_hidden(k4_tarski(sK0(sK6,sK5),sK1(sK6,sK5)),X1)
% 11.49/1.98      | X1 != X0
% 11.49/1.98      | k4_tarski(sK0(sK6,sK5),sK1(sK6,sK5)) != k4_tarski(sK0(sK6,sK5),k1_funct_1(sK5,sK0(sK6,sK5))) ),
% 11.49/1.98      inference(instantiation,[status(thm)],[c_3663]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_15228,plain,
% 11.49/1.98      ( X0 != X1
% 11.49/1.98      | k4_tarski(sK0(sK6,sK5),sK1(sK6,sK5)) != k4_tarski(sK0(sK6,sK5),k1_funct_1(sK5,sK0(sK6,sK5)))
% 11.49/1.98      | r2_hidden(k4_tarski(sK0(sK6,sK5),k1_funct_1(sK5,sK0(sK6,sK5))),X1) != iProver_top
% 11.49/1.98      | r2_hidden(k4_tarski(sK0(sK6,sK5),sK1(sK6,sK5)),X0) = iProver_top ),
% 11.49/1.98      inference(predicate_to_equality,[status(thm)],[c_15225]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_15230,plain,
% 11.49/1.98      ( k4_tarski(sK0(sK6,sK5),sK1(sK6,sK5)) != k4_tarski(sK0(sK6,sK5),k1_funct_1(sK5,sK0(sK6,sK5)))
% 11.49/1.98      | sK5 != sK5
% 11.49/1.98      | r2_hidden(k4_tarski(sK0(sK6,sK5),k1_funct_1(sK5,sK0(sK6,sK5))),sK5) != iProver_top
% 11.49/1.98      | r2_hidden(k4_tarski(sK0(sK6,sK5),sK1(sK6,sK5)),sK5) = iProver_top ),
% 11.49/1.98      inference(instantiation,[status(thm)],[c_15228]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_1334,plain,
% 11.49/1.98      ( r2_hidden(X0,X1)
% 11.49/1.98      | ~ r2_hidden(k4_tarski(sK0(sK6,sK5),k1_funct_1(sK6,sK0(sK6,sK5))),sK6)
% 11.49/1.98      | X0 != k4_tarski(sK0(sK6,sK5),k1_funct_1(sK6,sK0(sK6,sK5)))
% 11.49/1.98      | X1 != sK6 ),
% 11.49/1.98      inference(instantiation,[status(thm)],[c_349]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_2132,plain,
% 11.49/1.98      ( r2_hidden(X0,sK6)
% 11.49/1.98      | ~ r2_hidden(k4_tarski(sK0(sK6,sK5),k1_funct_1(sK6,sK0(sK6,sK5))),sK6)
% 11.49/1.98      | X0 != k4_tarski(sK0(sK6,sK5),k1_funct_1(sK6,sK0(sK6,sK5)))
% 11.49/1.98      | sK6 != sK6 ),
% 11.49/1.98      inference(instantiation,[status(thm)],[c_1334]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_3639,plain,
% 11.49/1.98      ( r2_hidden(k4_tarski(X0,X1),sK6)
% 11.49/1.98      | ~ r2_hidden(k4_tarski(sK0(sK6,sK5),k1_funct_1(sK6,sK0(sK6,sK5))),sK6)
% 11.49/1.98      | k4_tarski(X0,X1) != k4_tarski(sK0(sK6,sK5),k1_funct_1(sK6,sK0(sK6,sK5)))
% 11.49/1.98      | sK6 != sK6 ),
% 11.49/1.98      inference(instantiation,[status(thm)],[c_2132]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_13980,plain,
% 11.49/1.98      ( ~ r2_hidden(k4_tarski(sK0(sK6,sK5),k1_funct_1(sK6,sK0(sK6,sK5))),sK6)
% 11.49/1.98      | r2_hidden(k4_tarski(sK0(sK6,sK5),k1_funct_1(sK5,sK0(sK6,sK5))),sK6)
% 11.49/1.98      | k4_tarski(sK0(sK6,sK5),k1_funct_1(sK5,sK0(sK6,sK5))) != k4_tarski(sK0(sK6,sK5),k1_funct_1(sK6,sK0(sK6,sK5)))
% 11.49/1.98      | sK6 != sK6 ),
% 11.49/1.98      inference(instantiation,[status(thm)],[c_3639]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_1221,plain,
% 11.49/1.98      ( X0 != X1
% 11.49/1.98      | k4_tarski(sK0(sK6,sK5),sK1(sK6,sK5)) != X1
% 11.49/1.98      | k4_tarski(sK0(sK6,sK5),sK1(sK6,sK5)) = X0 ),
% 11.49/1.98      inference(instantiation,[status(thm)],[c_347]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_6094,plain,
% 11.49/1.98      ( X0 != k4_tarski(sK0(sK6,sK5),k1_funct_1(sK6,sK0(sK6,sK5)))
% 11.49/1.98      | k4_tarski(sK0(sK6,sK5),sK1(sK6,sK5)) = X0
% 11.49/1.98      | k4_tarski(sK0(sK6,sK5),sK1(sK6,sK5)) != k4_tarski(sK0(sK6,sK5),k1_funct_1(sK6,sK0(sK6,sK5))) ),
% 11.49/1.98      inference(instantiation,[status(thm)],[c_1221]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_13972,plain,
% 11.49/1.98      ( k4_tarski(sK0(sK6,sK5),k1_funct_1(sK5,sK0(sK6,sK5))) != k4_tarski(sK0(sK6,sK5),k1_funct_1(sK6,sK0(sK6,sK5)))
% 11.49/1.98      | k4_tarski(sK0(sK6,sK5),sK1(sK6,sK5)) != k4_tarski(sK0(sK6,sK5),k1_funct_1(sK6,sK0(sK6,sK5)))
% 11.49/1.98      | k4_tarski(sK0(sK6,sK5),sK1(sK6,sK5)) = k4_tarski(sK0(sK6,sK5),k1_funct_1(sK5,sK0(sK6,sK5))) ),
% 11.49/1.98      inference(instantiation,[status(thm)],[c_6094]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_6853,plain,
% 11.49/1.98      ( k1_funct_1(X0,sK0(sK6,sK5)) != k1_funct_1(sK5,sK0(sK6,sK5))
% 11.49/1.98      | k4_tarski(sK0(sK6,sK5),k1_funct_1(X0,sK0(sK6,sK5))) = k4_tarski(sK0(sK6,sK5),k1_funct_1(sK5,sK0(sK6,sK5)))
% 11.49/1.98      | sK0(sK6,sK5) != sK0(sK6,sK5) ),
% 11.49/1.98      inference(instantiation,[status(thm)],[c_4207]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_11562,plain,
% 11.49/1.98      ( k1_funct_1(sK6,sK0(sK6,sK5)) != k1_funct_1(sK5,sK0(sK6,sK5))
% 11.49/1.98      | k4_tarski(sK0(sK6,sK5),k1_funct_1(sK6,sK0(sK6,sK5))) = k4_tarski(sK0(sK6,sK5),k1_funct_1(sK5,sK0(sK6,sK5)))
% 11.49/1.98      | sK0(sK6,sK5) != sK0(sK6,sK5) ),
% 11.49/1.98      inference(instantiation,[status(thm)],[c_6853]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_3640,plain,
% 11.49/1.98      ( X0 != k1_funct_1(sK6,sK0(sK6,sK5))
% 11.49/1.98      | X1 != sK0(sK6,sK5)
% 11.49/1.98      | k4_tarski(X1,X0) = k4_tarski(sK0(sK6,sK5),k1_funct_1(sK6,sK0(sK6,sK5))) ),
% 11.49/1.98      inference(instantiation,[status(thm)],[c_348]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_8021,plain,
% 11.49/1.98      ( X0 != k1_funct_1(sK6,sK0(sK6,sK5))
% 11.49/1.98      | k4_tarski(sK0(sK6,sK5),X0) = k4_tarski(sK0(sK6,sK5),k1_funct_1(sK6,sK0(sK6,sK5)))
% 11.49/1.98      | sK0(sK6,sK5) != sK0(sK6,sK5) ),
% 11.49/1.98      inference(instantiation,[status(thm)],[c_3640]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_10949,plain,
% 11.49/1.98      ( k4_tarski(sK0(sK6,sK5),sK1(sK6,sK5)) = k4_tarski(sK0(sK6,sK5),k1_funct_1(sK6,sK0(sK6,sK5)))
% 11.49/1.98      | sK1(sK6,sK5) != k1_funct_1(sK6,sK0(sK6,sK5))
% 11.49/1.98      | sK0(sK6,sK5) != sK0(sK6,sK5) ),
% 11.49/1.98      inference(instantiation,[status(thm)],[c_8021]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_10943,plain,
% 11.49/1.98      ( k1_funct_1(X0,sK0(sK6,sK5)) != k1_funct_1(sK6,sK0(sK6,sK5))
% 11.49/1.98      | k4_tarski(sK0(sK6,sK5),k1_funct_1(X0,sK0(sK6,sK5))) = k4_tarski(sK0(sK6,sK5),k1_funct_1(sK6,sK0(sK6,sK5)))
% 11.49/1.98      | sK0(sK6,sK5) != sK0(sK6,sK5) ),
% 11.49/1.98      inference(instantiation,[status(thm)],[c_8021]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_10945,plain,
% 11.49/1.98      ( k1_funct_1(sK5,sK0(sK6,sK5)) != k1_funct_1(sK6,sK0(sK6,sK5))
% 11.49/1.98      | k4_tarski(sK0(sK6,sK5),k1_funct_1(sK5,sK0(sK6,sK5))) = k4_tarski(sK0(sK6,sK5),k1_funct_1(sK6,sK0(sK6,sK5)))
% 11.49/1.98      | sK0(sK6,sK5) != sK0(sK6,sK5) ),
% 11.49/1.98      inference(instantiation,[status(thm)],[c_10943]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_9716,plain,
% 11.49/1.98      ( k1_funct_1(sK6,sK0(sK6,sK5)) != sK1(sK6,sK5)
% 11.49/1.98      | sK1(sK6,sK5) = k1_funct_1(sK6,sK0(sK6,sK5))
% 11.49/1.98      | sK1(sK6,sK5) != sK1(sK6,sK5) ),
% 11.49/1.98      inference(instantiation,[status(thm)],[c_5143]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_8014,plain,
% 11.49/1.98      ( ~ r2_hidden(k4_tarski(sK0(sK6,sK5),k1_funct_1(sK6,sK0(sK6,sK5))),sK6)
% 11.49/1.98      | r2_hidden(k4_tarski(sK0(sK6,sK5),sK1(sK6,sK5)),sK6)
% 11.49/1.98      | k4_tarski(sK0(sK6,sK5),sK1(sK6,sK5)) != k4_tarski(sK0(sK6,sK5),k1_funct_1(sK6,sK0(sK6,sK5)))
% 11.49/1.98      | sK6 != sK6 ),
% 11.49/1.98      inference(instantiation,[status(thm)],[c_3639]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_8015,plain,
% 11.49/1.98      ( k4_tarski(sK0(sK6,sK5),sK1(sK6,sK5)) != k4_tarski(sK0(sK6,sK5),k1_funct_1(sK6,sK0(sK6,sK5)))
% 11.49/1.98      | sK6 != sK6
% 11.49/1.98      | r2_hidden(k4_tarski(sK0(sK6,sK5),k1_funct_1(sK6,sK0(sK6,sK5))),sK6) != iProver_top
% 11.49/1.98      | r2_hidden(k4_tarski(sK0(sK6,sK5),sK1(sK6,sK5)),sK6) = iProver_top ),
% 11.49/1.98      inference(predicate_to_equality,[status(thm)],[c_8014]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_1,plain,
% 11.49/1.98      ( r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)
% 11.49/1.98      | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0)
% 11.49/1.98      | ~ v1_relat_1(X1)
% 11.49/1.98      | ~ v1_relat_1(X0)
% 11.49/1.98      | X1 = X0 ),
% 11.49/1.98      inference(cnf_transformation,[],[f28]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_608,plain,
% 11.49/1.98      ( X0 = X1
% 11.49/1.98      | r2_hidden(k4_tarski(sK0(X1,X0),sK1(X1,X0)),X0) = iProver_top
% 11.49/1.98      | r2_hidden(k4_tarski(sK0(X1,X0),sK1(X1,X0)),X1) = iProver_top
% 11.49/1.98      | v1_relat_1(X0) != iProver_top
% 11.49/1.98      | v1_relat_1(X1) != iProver_top ),
% 11.49/1.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_9,plain,
% 11.49/1.98      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 11.49/1.98      | ~ v1_funct_1(X2)
% 11.49/1.98      | ~ v1_relat_1(X2)
% 11.49/1.98      | k1_funct_1(X2,X0) = X1 ),
% 11.49/1.98      inference(cnf_transformation,[],[f35]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_14,negated_conjecture,
% 11.49/1.98      ( v1_funct_1(sK6) ),
% 11.49/1.98      inference(cnf_transformation,[],[f40]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_204,plain,
% 11.49/1.98      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 11.49/1.98      | ~ v1_relat_1(X2)
% 11.49/1.98      | k1_funct_1(X2,X0) = X1
% 11.49/1.98      | sK6 != X2 ),
% 11.49/1.98      inference(resolution_lifted,[status(thm)],[c_9,c_14]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_205,plain,
% 11.49/1.98      ( ~ r2_hidden(k4_tarski(X0,X1),sK6)
% 11.49/1.98      | ~ v1_relat_1(sK6)
% 11.49/1.98      | k1_funct_1(sK6,X0) = X1 ),
% 11.49/1.98      inference(unflattening,[status(thm)],[c_204]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_15,negated_conjecture,
% 11.49/1.98      ( v1_relat_1(sK6) ),
% 11.49/1.98      inference(cnf_transformation,[],[f39]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_209,plain,
% 11.49/1.98      ( ~ r2_hidden(k4_tarski(X0,X1),sK6) | k1_funct_1(sK6,X0) = X1 ),
% 11.49/1.98      inference(global_propositional_subsumption,
% 11.49/1.98                [status(thm)],
% 11.49/1.98                [c_205,c_15]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_598,plain,
% 11.49/1.98      ( k1_funct_1(sK6,X0) = X1
% 11.49/1.98      | r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top ),
% 11.49/1.98      inference(predicate_to_equality,[status(thm)],[c_209]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_1768,plain,
% 11.49/1.98      ( k1_funct_1(sK6,sK0(sK6,X0)) = sK1(sK6,X0)
% 11.49/1.98      | sK6 = X0
% 11.49/1.98      | r2_hidden(k4_tarski(sK0(sK6,X0),sK1(sK6,X0)),X0) = iProver_top
% 11.49/1.98      | v1_relat_1(X0) != iProver_top
% 11.49/1.98      | v1_relat_1(sK6) != iProver_top ),
% 11.49/1.98      inference(superposition,[status(thm)],[c_608,c_598]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_20,plain,
% 11.49/1.98      ( v1_relat_1(sK6) = iProver_top ),
% 11.49/1.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_7302,plain,
% 11.49/1.98      ( v1_relat_1(X0) != iProver_top
% 11.49/1.98      | r2_hidden(k4_tarski(sK0(sK6,X0),sK1(sK6,X0)),X0) = iProver_top
% 11.49/1.98      | sK6 = X0
% 11.49/1.98      | k1_funct_1(sK6,sK0(sK6,X0)) = sK1(sK6,X0) ),
% 11.49/1.98      inference(global_propositional_subsumption,
% 11.49/1.98                [status(thm)],
% 11.49/1.98                [c_1768,c_20]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_7303,plain,
% 11.49/1.98      ( k1_funct_1(sK6,sK0(sK6,X0)) = sK1(sK6,X0)
% 11.49/1.98      | sK6 = X0
% 11.49/1.98      | r2_hidden(k4_tarski(sK0(sK6,X0),sK1(sK6,X0)),X0) = iProver_top
% 11.49/1.98      | v1_relat_1(X0) != iProver_top ),
% 11.49/1.98      inference(renaming,[status(thm)],[c_7302]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_7305,plain,
% 11.49/1.98      ( k1_funct_1(sK6,sK0(sK6,sK5)) = sK1(sK6,sK5)
% 11.49/1.98      | sK6 = sK5
% 11.49/1.98      | r2_hidden(k4_tarski(sK0(sK6,sK5),sK1(sK6,sK5)),sK5) = iProver_top
% 11.49/1.98      | v1_relat_1(sK5) != iProver_top ),
% 11.49/1.98      inference(instantiation,[status(thm)],[c_7303]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_13,negated_conjecture,
% 11.49/1.98      ( k1_relat_1(sK5) = k1_relat_1(sK6) ),
% 11.49/1.98      inference(cnf_transformation,[],[f41]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_6,plain,
% 11.49/1.98      ( r2_hidden(X0,k1_relat_1(X1)) | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
% 11.49/1.98      inference(cnf_transformation,[],[f46]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_605,plain,
% 11.49/1.98      ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
% 11.49/1.98      | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top ),
% 11.49/1.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_1765,plain,
% 11.49/1.98      ( X0 = X1
% 11.49/1.98      | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) = iProver_top
% 11.49/1.98      | r2_hidden(sK0(X0,X1),k1_relat_1(X0)) = iProver_top
% 11.49/1.98      | v1_relat_1(X0) != iProver_top
% 11.49/1.98      | v1_relat_1(X1) != iProver_top ),
% 11.49/1.98      inference(superposition,[status(thm)],[c_608,c_605]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_4260,plain,
% 11.49/1.98      ( X0 = X1
% 11.49/1.98      | r2_hidden(sK0(X1,X0),k1_relat_1(X1)) = iProver_top
% 11.49/1.98      | r2_hidden(sK0(X1,X0),k1_relat_1(X0)) = iProver_top
% 11.49/1.98      | v1_relat_1(X0) != iProver_top
% 11.49/1.98      | v1_relat_1(X1) != iProver_top ),
% 11.49/1.98      inference(superposition,[status(thm)],[c_1765,c_605]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_4382,plain,
% 11.49/1.98      ( sK6 = X0
% 11.49/1.98      | r2_hidden(sK0(sK6,X0),k1_relat_1(X0)) = iProver_top
% 11.49/1.98      | r2_hidden(sK0(sK6,X0),k1_relat_1(sK5)) = iProver_top
% 11.49/1.98      | v1_relat_1(X0) != iProver_top
% 11.49/1.98      | v1_relat_1(sK6) != iProver_top ),
% 11.49/1.98      inference(superposition,[status(thm)],[c_13,c_4260]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_4729,plain,
% 11.49/1.98      ( v1_relat_1(X0) != iProver_top
% 11.49/1.98      | r2_hidden(sK0(sK6,X0),k1_relat_1(sK5)) = iProver_top
% 11.49/1.98      | r2_hidden(sK0(sK6,X0),k1_relat_1(X0)) = iProver_top
% 11.49/1.98      | sK6 = X0 ),
% 11.49/1.98      inference(global_propositional_subsumption,
% 11.49/1.98                [status(thm)],
% 11.49/1.98                [c_4382,c_20]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_4730,plain,
% 11.49/1.98      ( sK6 = X0
% 11.49/1.98      | r2_hidden(sK0(sK6,X0),k1_relat_1(X0)) = iProver_top
% 11.49/1.98      | r2_hidden(sK0(sK6,X0),k1_relat_1(sK5)) = iProver_top
% 11.49/1.98      | v1_relat_1(X0) != iProver_top ),
% 11.49/1.98      inference(renaming,[status(thm)],[c_4729]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_7,plain,
% 11.49/1.98      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 11.49/1.98      | r2_hidden(k4_tarski(X0,sK4(X1,X0)),X1) ),
% 11.49/1.98      inference(cnf_transformation,[],[f47]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_604,plain,
% 11.49/1.98      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 11.49/1.98      | r2_hidden(k4_tarski(X0,sK4(X1,X0)),X1) = iProver_top ),
% 11.49/1.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_1075,plain,
% 11.49/1.98      ( k1_funct_1(sK6,X0) = sK4(sK6,X0)
% 11.49/1.98      | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
% 11.49/1.98      inference(superposition,[status(thm)],[c_604,c_598]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_1083,plain,
% 11.49/1.98      ( k1_funct_1(sK6,X0) = sK4(sK6,X0)
% 11.49/1.98      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 11.49/1.98      inference(light_normalisation,[status(thm)],[c_1075,c_13]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_4741,plain,
% 11.49/1.98      ( k1_funct_1(sK6,sK0(sK6,X0)) = sK4(sK6,sK0(sK6,X0))
% 11.49/1.98      | sK6 = X0
% 11.49/1.98      | r2_hidden(sK0(sK6,X0),k1_relat_1(X0)) = iProver_top
% 11.49/1.98      | v1_relat_1(X0) != iProver_top ),
% 11.49/1.98      inference(superposition,[status(thm)],[c_4730,c_1083]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_5835,plain,
% 11.49/1.98      ( k1_funct_1(sK6,sK0(sK6,sK5)) = sK4(sK6,sK0(sK6,sK5))
% 11.49/1.98      | sK6 = sK5
% 11.49/1.98      | v1_relat_1(sK5) != iProver_top ),
% 11.49/1.98      inference(superposition,[status(thm)],[c_4741,c_1083]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_17,negated_conjecture,
% 11.49/1.98      ( v1_relat_1(sK5) ),
% 11.49/1.98      inference(cnf_transformation,[],[f37]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_18,plain,
% 11.49/1.98      ( v1_relat_1(sK5) = iProver_top ),
% 11.49/1.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_11,negated_conjecture,
% 11.49/1.98      ( sK5 != sK6 ),
% 11.49/1.98      inference(cnf_transformation,[],[f43]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_346,plain,( X0 = X0 ),theory(equality) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_359,plain,
% 11.49/1.98      ( sK5 = sK5 ),
% 11.49/1.98      inference(instantiation,[status(thm)],[c_346]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_735,plain,
% 11.49/1.98      ( sK6 != X0 | sK5 != X0 | sK5 = sK6 ),
% 11.49/1.98      inference(instantiation,[status(thm)],[c_347]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_736,plain,
% 11.49/1.98      ( sK6 != sK5 | sK5 = sK6 | sK5 != sK5 ),
% 11.49/1.98      inference(instantiation,[status(thm)],[c_735]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_5893,plain,
% 11.49/1.98      ( k1_funct_1(sK6,sK0(sK6,sK5)) = sK4(sK6,sK0(sK6,sK5)) ),
% 11.49/1.98      inference(global_propositional_subsumption,
% 11.49/1.98                [status(thm)],
% 11.49/1.98                [c_5835,c_18,c_11,c_359,c_736]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_8,plain,
% 11.49/1.98      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 11.49/1.98      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 11.49/1.98      | ~ v1_funct_1(X1)
% 11.49/1.98      | ~ v1_relat_1(X1) ),
% 11.49/1.98      inference(cnf_transformation,[],[f48]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_168,plain,
% 11.49/1.98      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 11.49/1.98      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 11.49/1.98      | ~ v1_relat_1(X1)
% 11.49/1.98      | sK6 != X1 ),
% 11.49/1.98      inference(resolution_lifted,[status(thm)],[c_8,c_14]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_169,plain,
% 11.49/1.98      ( ~ r2_hidden(X0,k1_relat_1(sK6))
% 11.49/1.98      | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6)
% 11.49/1.98      | ~ v1_relat_1(sK6) ),
% 11.49/1.98      inference(unflattening,[status(thm)],[c_168]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_173,plain,
% 11.49/1.98      ( r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6)
% 11.49/1.98      | ~ r2_hidden(X0,k1_relat_1(sK6)) ),
% 11.49/1.98      inference(global_propositional_subsumption,
% 11.49/1.98                [status(thm)],
% 11.49/1.98                [c_169,c_15]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_174,plain,
% 11.49/1.98      ( ~ r2_hidden(X0,k1_relat_1(sK6))
% 11.49/1.98      | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6) ),
% 11.49/1.98      inference(renaming,[status(thm)],[c_173]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_600,plain,
% 11.49/1.98      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 11.49/1.98      | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6) = iProver_top ),
% 11.49/1.98      inference(predicate_to_equality,[status(thm)],[c_174]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_638,plain,
% 11.49/1.98      ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 11.49/1.98      | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6) = iProver_top ),
% 11.49/1.98      inference(light_normalisation,[status(thm)],[c_600,c_13]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_5896,plain,
% 11.49/1.98      ( r2_hidden(k4_tarski(sK0(sK6,sK5),sK4(sK6,sK0(sK6,sK5))),sK6) = iProver_top
% 11.49/1.98      | r2_hidden(sK0(sK6,sK5),k1_relat_1(sK5)) != iProver_top ),
% 11.49/1.98      inference(superposition,[status(thm)],[c_5893,c_638]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_5897,plain,
% 11.49/1.98      ( r2_hidden(k4_tarski(sK0(sK6,sK5),sK4(sK6,sK0(sK6,sK5))),sK6)
% 11.49/1.98      | ~ r2_hidden(sK0(sK6,sK5),k1_relat_1(sK5)) ),
% 11.49/1.98      inference(predicate_to_equality_rev,[status(thm)],[c_5896]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_4540,plain,
% 11.49/1.98      ( r2_hidden(sK0(sK6,X0),k1_relat_1(X0))
% 11.49/1.98      | r2_hidden(sK0(sK6,X0),k1_relat_1(sK5))
% 11.49/1.98      | ~ v1_relat_1(X0)
% 11.49/1.98      | ~ v1_relat_1(sK6)
% 11.49/1.98      | sK6 = X0 ),
% 11.49/1.98      inference(predicate_to_equality_rev,[status(thm)],[c_4382]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_4542,plain,
% 11.49/1.98      ( r2_hidden(sK0(sK6,sK5),k1_relat_1(sK5))
% 11.49/1.98      | ~ v1_relat_1(sK6)
% 11.49/1.98      | ~ v1_relat_1(sK5)
% 11.49/1.98      | sK6 = sK5 ),
% 11.49/1.98      inference(instantiation,[status(thm)],[c_4540]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_4541,plain,
% 11.49/1.98      ( sK6 = sK5
% 11.49/1.98      | r2_hidden(sK0(sK6,sK5),k1_relat_1(sK5)) = iProver_top
% 11.49/1.98      | v1_relat_1(sK6) != iProver_top
% 11.49/1.98      | v1_relat_1(sK5) != iProver_top ),
% 11.49/1.98      inference(instantiation,[status(thm)],[c_4382]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_3668,plain,
% 11.49/1.98      ( ~ r2_hidden(k4_tarski(sK0(sK6,sK5),k1_funct_1(sK5,sK0(sK6,sK5))),sK6)
% 11.49/1.98      | k1_funct_1(sK6,sK0(sK6,sK5)) = k1_funct_1(sK5,sK0(sK6,sK5)) ),
% 11.49/1.98      inference(instantiation,[status(thm)],[c_209]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_1728,plain,
% 11.49/1.98      ( X0 != k4_tarski(sK0(sK6,sK5),sK1(sK6,sK5))
% 11.49/1.98      | k4_tarski(sK0(sK6,sK5),sK1(sK6,sK5)) = X0
% 11.49/1.98      | k4_tarski(sK0(sK6,sK5),sK1(sK6,sK5)) != k4_tarski(sK0(sK6,sK5),sK1(sK6,sK5)) ),
% 11.49/1.98      inference(instantiation,[status(thm)],[c_1221]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_3367,plain,
% 11.49/1.98      ( k4_tarski(sK0(sK6,sK5),k1_funct_1(sK6,sK0(sK6,sK5))) != k4_tarski(sK0(sK6,sK5),sK1(sK6,sK5))
% 11.49/1.98      | k4_tarski(sK0(sK6,sK5),sK1(sK6,sK5)) = k4_tarski(sK0(sK6,sK5),k1_funct_1(sK6,sK0(sK6,sK5)))
% 11.49/1.98      | k4_tarski(sK0(sK6,sK5),sK1(sK6,sK5)) != k4_tarski(sK0(sK6,sK5),sK1(sK6,sK5)) ),
% 11.49/1.98      inference(instantiation,[status(thm)],[c_1728]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_1736,plain,
% 11.49/1.98      ( sK1(sK6,sK5) = sK1(sK6,sK5) ),
% 11.49/1.98      inference(instantiation,[status(thm)],[c_346]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_1340,plain,
% 11.49/1.98      ( ~ r2_hidden(k4_tarski(sK0(sK6,sK5),sK4(sK6,sK0(sK6,sK5))),sK6)
% 11.49/1.98      | r2_hidden(sK0(sK6,sK5),k1_relat_1(sK6)) ),
% 11.49/1.98      inference(instantiation,[status(thm)],[c_6]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_1341,plain,
% 11.49/1.98      ( r2_hidden(k4_tarski(sK0(sK6,sK5),sK4(sK6,sK0(sK6,sK5))),sK6) != iProver_top
% 11.49/1.98      | r2_hidden(sK0(sK6,sK5),k1_relat_1(sK6)) = iProver_top ),
% 11.49/1.98      inference(predicate_to_equality,[status(thm)],[c_1340]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_1191,plain,
% 11.49/1.98      ( sK0(sK6,sK5) = sK0(sK6,sK5) ),
% 11.49/1.98      inference(instantiation,[status(thm)],[c_346]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_933,plain,
% 11.49/1.98      ( k4_tarski(sK0(sK6,sK5),sK1(sK6,sK5)) = k4_tarski(sK0(sK6,sK5),sK1(sK6,sK5)) ),
% 11.49/1.98      inference(instantiation,[status(thm)],[c_346]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_16,negated_conjecture,
% 11.49/1.98      ( v1_funct_1(sK5) ),
% 11.49/1.98      inference(cnf_transformation,[],[f38]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_186,plain,
% 11.49/1.98      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 11.49/1.98      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 11.49/1.98      | ~ v1_relat_1(X1)
% 11.49/1.98      | sK5 != X1 ),
% 11.49/1.98      inference(resolution_lifted,[status(thm)],[c_8,c_16]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_187,plain,
% 11.49/1.98      ( ~ r2_hidden(X0,k1_relat_1(sK5))
% 11.49/1.98      | r2_hidden(k4_tarski(X0,k1_funct_1(sK5,X0)),sK5)
% 11.49/1.98      | ~ v1_relat_1(sK5) ),
% 11.49/1.98      inference(unflattening,[status(thm)],[c_186]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_191,plain,
% 11.49/1.98      ( r2_hidden(k4_tarski(X0,k1_funct_1(sK5,X0)),sK5)
% 11.49/1.98      | ~ r2_hidden(X0,k1_relat_1(sK5)) ),
% 11.49/1.98      inference(global_propositional_subsumption,
% 11.49/1.98                [status(thm)],
% 11.49/1.98                [c_187,c_17]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_192,plain,
% 11.49/1.98      ( ~ r2_hidden(X0,k1_relat_1(sK5))
% 11.49/1.98      | r2_hidden(k4_tarski(X0,k1_funct_1(sK5,X0)),sK5) ),
% 11.49/1.98      inference(renaming,[status(thm)],[c_191]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_906,plain,
% 11.49/1.98      ( r2_hidden(k4_tarski(sK0(sK6,sK5),k1_funct_1(sK5,sK0(sK6,sK5))),sK5)
% 11.49/1.98      | ~ r2_hidden(sK0(sK6,sK5),k1_relat_1(sK5)) ),
% 11.49/1.98      inference(instantiation,[status(thm)],[c_192]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_910,plain,
% 11.49/1.98      ( r2_hidden(k4_tarski(sK0(sK6,sK5),k1_funct_1(sK5,sK0(sK6,sK5))),sK5) = iProver_top
% 11.49/1.98      | r2_hidden(sK0(sK6,sK5),k1_relat_1(sK5)) != iProver_top ),
% 11.49/1.98      inference(predicate_to_equality,[status(thm)],[c_906]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_12,negated_conjecture,
% 11.49/1.98      ( ~ r2_hidden(X0,k1_relat_1(sK5))
% 11.49/1.98      | k1_funct_1(sK5,X0) = k1_funct_1(sK6,X0) ),
% 11.49/1.98      inference(cnf_transformation,[],[f42]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_907,plain,
% 11.49/1.98      ( ~ r2_hidden(sK0(sK6,sK5),k1_relat_1(sK5))
% 11.49/1.98      | k1_funct_1(sK5,sK0(sK6,sK5)) = k1_funct_1(sK6,sK0(sK6,sK5)) ),
% 11.49/1.98      inference(instantiation,[status(thm)],[c_12]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_908,plain,
% 11.49/1.98      ( k1_funct_1(sK5,sK0(sK6,sK5)) = k1_funct_1(sK6,sK0(sK6,sK5))
% 11.49/1.98      | r2_hidden(sK0(sK6,sK5),k1_relat_1(sK5)) != iProver_top ),
% 11.49/1.98      inference(predicate_to_equality,[status(thm)],[c_907]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_834,plain,
% 11.49/1.98      ( r2_hidden(k4_tarski(sK0(sK6,sK5),k1_funct_1(sK6,sK0(sK6,sK5))),sK6)
% 11.49/1.98      | ~ r2_hidden(sK0(sK6,sK5),k1_relat_1(sK6)) ),
% 11.49/1.98      inference(instantiation,[status(thm)],[c_174]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_835,plain,
% 11.49/1.98      ( r2_hidden(k4_tarski(sK0(sK6,sK5),k1_funct_1(sK6,sK0(sK6,sK5))),sK6) = iProver_top
% 11.49/1.98      | r2_hidden(sK0(sK6,sK5),k1_relat_1(sK6)) != iProver_top ),
% 11.49/1.98      inference(predicate_to_equality,[status(thm)],[c_834]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_794,plain,
% 11.49/1.98      ( sK6 = sK6 ),
% 11.49/1.98      inference(instantiation,[status(thm)],[c_346]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_0,plain,
% 11.49/1.98      ( ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)
% 11.49/1.98      | ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0)
% 11.49/1.98      | ~ v1_relat_1(X1)
% 11.49/1.98      | ~ v1_relat_1(X0)
% 11.49/1.98      | X1 = X0 ),
% 11.49/1.98      inference(cnf_transformation,[],[f29]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_780,plain,
% 11.49/1.98      ( ~ r2_hidden(k4_tarski(sK0(sK6,sK5),sK1(sK6,sK5)),sK6)
% 11.49/1.98      | ~ r2_hidden(k4_tarski(sK0(sK6,sK5),sK1(sK6,sK5)),sK5)
% 11.49/1.98      | ~ v1_relat_1(sK6)
% 11.49/1.98      | ~ v1_relat_1(sK5)
% 11.49/1.98      | sK5 = sK6 ),
% 11.49/1.98      inference(instantiation,[status(thm)],[c_0]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_781,plain,
% 11.49/1.98      ( sK5 = sK6
% 11.49/1.98      | r2_hidden(k4_tarski(sK0(sK6,sK5),sK1(sK6,sK5)),sK6) != iProver_top
% 11.49/1.98      | r2_hidden(k4_tarski(sK0(sK6,sK5),sK1(sK6,sK5)),sK5) != iProver_top
% 11.49/1.98      | v1_relat_1(sK6) != iProver_top
% 11.49/1.98      | v1_relat_1(sK5) != iProver_top ),
% 11.49/1.98      inference(predicate_to_equality,[status(thm)],[c_780]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_222,plain,
% 11.49/1.98      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 11.49/1.98      | ~ v1_relat_1(X2)
% 11.49/1.98      | k1_funct_1(X2,X0) = X1
% 11.49/1.98      | sK5 != X2 ),
% 11.49/1.98      inference(resolution_lifted,[status(thm)],[c_9,c_16]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_223,plain,
% 11.49/1.98      ( ~ r2_hidden(k4_tarski(X0,X1),sK5)
% 11.49/1.98      | ~ v1_relat_1(sK5)
% 11.49/1.98      | k1_funct_1(sK5,X0) = X1 ),
% 11.49/1.98      inference(unflattening,[status(thm)],[c_222]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_227,plain,
% 11.49/1.98      ( ~ r2_hidden(k4_tarski(X0,X1),sK5) | k1_funct_1(sK5,X0) = X1 ),
% 11.49/1.98      inference(global_propositional_subsumption,
% 11.49/1.98                [status(thm)],
% 11.49/1.98                [c_223,c_17]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_770,plain,
% 11.49/1.98      ( ~ r2_hidden(k4_tarski(sK0(sK6,sK5),sK1(sK6,sK5)),sK5)
% 11.49/1.98      | k1_funct_1(sK5,sK0(sK6,sK5)) = sK1(sK6,sK5) ),
% 11.49/1.98      inference(instantiation,[status(thm)],[c_227]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(c_771,plain,
% 11.49/1.98      ( k1_funct_1(sK5,sK0(sK6,sK5)) = sK1(sK6,sK5)
% 11.49/1.98      | r2_hidden(k4_tarski(sK0(sK6,sK5),sK1(sK6,sK5)),sK5) != iProver_top ),
% 11.49/1.98      inference(predicate_to_equality,[status(thm)],[c_770]) ).
% 11.49/1.98  
% 11.49/1.98  cnf(contradiction,plain,
% 11.49/1.98      ( $false ),
% 11.49/1.98      inference(minisat,
% 11.49/1.98                [status(thm)],
% 11.49/1.98                [c_30019,c_22210,c_16663,c_15230,c_13980,c_13972,c_11562,
% 11.49/1.98                 c_10949,c_10945,c_9716,c_8015,c_7305,c_5897,c_5896,
% 11.49/1.98                 c_4542,c_4541,c_3668,c_3367,c_1736,c_1341,c_1340,c_1191,
% 11.49/1.98                 c_933,c_910,c_908,c_835,c_834,c_794,c_781,c_771,c_736,
% 11.49/1.98                 c_359,c_11,c_20,c_15,c_18,c_17]) ).
% 11.49/1.98  
% 11.49/1.98  
% 11.49/1.98  % SZS output end CNFRefutation for theBenchmark.p
% 11.49/1.98  
% 11.49/1.98  ------                               Statistics
% 11.49/1.98  
% 11.49/1.98  ------ Selected
% 11.49/1.98  
% 11.49/1.98  total_time:                             1.206
% 11.49/1.98  
%------------------------------------------------------------------------------
