%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0541+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:31 EST 2020

% Result     : Theorem 1.04s
% Output     : CNFRefutation 1.04s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 177 expanded)
%              Number of clauses        :   30 (  38 expanded)
%              Number of leaves         :   11 (  47 expanded)
%              Depth                    :   14
%              Number of atoms          :  308 (1170 expanded)
%              Number of equality atoms :   40 (  66 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X4,X3),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) ) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( r2_hidden(X5,X1)
                      & r2_hidden(k4_tarski(X5,X3),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X7,X6),X0) ) )
                & ( ? [X8] :
                      ( r2_hidden(X8,X1)
                      & r2_hidden(k4_tarski(X8,X6),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f7])).

fof(f11,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X8,X6),X0) )
     => ( r2_hidden(sK2(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(sK2(X0,X1,X6),X6),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X5,X3),X0) )
     => ( r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK1(X0,X1,X2),X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X1)
                | ~ r2_hidden(k4_tarski(X4,X3),X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X5,X3),X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X1)
              | ~ r2_hidden(k4_tarski(X4,sK0(X0,X1,X2)),X0) )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(X5,sK0(X0,X1,X2)),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(X4,sK0(X0,X1,X2)),X0) )
                | ~ r2_hidden(sK0(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK1(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK1(X0,X1,X2),sK0(X0,X1,X2)),X0) )
                | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X7,X6),X0) ) )
                & ( ( r2_hidden(sK2(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(sK2(X0,X1,X6),X6),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f11,f10,f9])).

fof(f27,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X7,X6),X0)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f40,plain,(
    ! [X6,X0,X7,X1] :
      ( r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X7,X6),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f27])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(X0,k9_relat_1(X2,X1))
        <=> ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <~> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X3,X0),X2)
            | ~ r2_hidden(X3,k1_relat_1(X2)) )
        | ~ r2_hidden(X0,k9_relat_1(X2,X1)) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) )
        | r2_hidden(X0,k9_relat_1(X2,X1)) )
      & v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X3,X0),X2)
            | ~ r2_hidden(X3,k1_relat_1(X2)) )
        | ~ r2_hidden(X0,k9_relat_1(X2,X1)) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) )
        | r2_hidden(X0,k9_relat_1(X2,X1)) )
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X3,X0),X2)
            | ~ r2_hidden(X3,k1_relat_1(X2)) )
        | ~ r2_hidden(X0,k9_relat_1(X2,X1)) )
      & ( ? [X4] :
            ( r2_hidden(X4,X1)
            & r2_hidden(k4_tarski(X4,X0),X2)
            & r2_hidden(X4,k1_relat_1(X2)) )
        | r2_hidden(X0,k9_relat_1(X2,X1)) )
      & v1_relat_1(X2) ) ),
    inference(rectify,[],[f20])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK9,X1)
        & r2_hidden(k4_tarski(sK9,X0),X2)
        & r2_hidden(sK9,k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X0,X1,X2] :
        ( ( ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | r2_hidden(X0,k9_relat_1(X2,X1)) )
        & v1_relat_1(X2) )
   => ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK7)
            | ~ r2_hidden(k4_tarski(X3,sK6),sK8)
            | ~ r2_hidden(X3,k1_relat_1(sK8)) )
        | ~ r2_hidden(sK6,k9_relat_1(sK8,sK7)) )
      & ( ? [X4] :
            ( r2_hidden(X4,sK7)
            & r2_hidden(k4_tarski(X4,sK6),sK8)
            & r2_hidden(X4,k1_relat_1(sK8)) )
        | r2_hidden(sK6,k9_relat_1(sK8,sK7)) )
      & v1_relat_1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ( ! [X3] :
          ( ~ r2_hidden(X3,sK7)
          | ~ r2_hidden(k4_tarski(X3,sK6),sK8)
          | ~ r2_hidden(X3,k1_relat_1(sK8)) )
      | ~ r2_hidden(sK6,k9_relat_1(sK8,sK7)) )
    & ( ( r2_hidden(sK9,sK7)
        & r2_hidden(k4_tarski(sK9,sK6),sK8)
        & r2_hidden(sK9,k1_relat_1(sK8)) )
      | r2_hidden(sK6,k9_relat_1(sK8,sK7)) )
    & v1_relat_1(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f21,f23,f22])).

fof(f35,plain,(
    v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f24])).

fof(f39,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK7)
      | ~ r2_hidden(k4_tarski(X3,sK6),sK8)
      | ~ r2_hidden(X3,k1_relat_1(sK8))
      | ~ r2_hidden(sK6,k9_relat_1(sK8,sK7)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
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

fof(f14,plain,(
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
    inference(rectify,[],[f13])).

fof(f17,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK4(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK3(X0,X1),X3),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK3(X0,X1),X3),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f14,f17,f16,f15])).

fof(f32,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f43,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f32])).

fof(f26,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f41,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f26])).

fof(f25,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK2(X0,X1,X6),X6),X0)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f42,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k4_tarski(sK2(X0,X1,X6),X6),X0)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f25])).

fof(f38,plain,
    ( r2_hidden(sK9,sK7)
    | r2_hidden(sK6,k9_relat_1(sK8,sK7)) ),
    inference(cnf_transformation,[],[f24])).

fof(f37,plain,
    ( r2_hidden(k4_tarski(sK9,sK6),sK8)
    | r2_hidden(sK6,k9_relat_1(sK8,sK7)) ),
    inference(cnf_transformation,[],[f24])).

fof(f36,plain,
    ( r2_hidden(sK9,k1_relat_1(sK8))
    | r2_hidden(sK6,k9_relat_1(sK8,sK7)) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k9_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_14,negated_conjecture,
    ( v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_218,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k9_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X3)
    | sK8 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_14])).

cnf(c_219,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k9_relat_1(sK8,X1))
    | ~ r2_hidden(k4_tarski(X0,X2),sK8) ),
    inference(unflattening,[status(thm)],[c_218])).

cnf(c_10,negated_conjecture,
    ( ~ r2_hidden(X0,k1_relat_1(sK8))
    | ~ r2_hidden(X0,sK7)
    | ~ r2_hidden(k4_tarski(X0,sK6),sK8)
    | ~ r2_hidden(sK6,k9_relat_1(sK8,sK7)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_272,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK8))
    | ~ r2_hidden(X0,sK7)
    | ~ r2_hidden(k4_tarski(X0,sK6),sK8) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_219,c_10])).

cnf(c_808,plain,
    ( ~ r2_hidden(k4_tarski(sK9,sK6),sK8)
    | ~ r2_hidden(sK9,k1_relat_1(sK8))
    | ~ r2_hidden(sK9,sK7) ),
    inference(instantiation,[status(thm)],[c_272])).

cnf(c_809,plain,
    ( r2_hidden(k4_tarski(sK9,sK6),sK8) != iProver_top
    | r2_hidden(sK9,k1_relat_1(sK8)) != iProver_top
    | r2_hidden(sK9,sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_808])).

cnf(c_795,plain,
    ( ~ r2_hidden(sK2(sK8,sK7,sK6),k1_relat_1(sK8))
    | ~ r2_hidden(sK2(sK8,sK7,sK6),sK7)
    | ~ r2_hidden(k4_tarski(sK2(sK8,sK7,sK6),sK6),sK8) ),
    inference(instantiation,[status(thm)],[c_272])).

cnf(c_796,plain,
    ( r2_hidden(sK2(sK8,sK7,sK6),k1_relat_1(sK8)) != iProver_top
    | r2_hidden(sK2(sK8,sK7,sK6),sK7) != iProver_top
    | r2_hidden(k4_tarski(sK2(sK8,sK7,sK6),sK6),sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_795])).

cnf(c_8,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_782,plain,
    ( r2_hidden(sK2(sK8,sK7,sK6),k1_relat_1(sK8))
    | ~ r2_hidden(k4_tarski(sK2(sK8,sK7,sK6),sK6),sK8) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_783,plain,
    ( r2_hidden(sK2(sK8,sK7,sK6),k1_relat_1(sK8)) = iProver_top
    | r2_hidden(k4_tarski(sK2(sK8,sK7,sK6),sK6),sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_782])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK2(X1,X2,X0),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_245,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK2(X1,X2,X0),X2)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_14])).

cnf(c_246,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK8,X1))
    | r2_hidden(sK2(sK8,X1,X0),X1) ),
    inference(unflattening,[status(thm)],[c_245])).

cnf(c_747,plain,
    ( r2_hidden(sK2(sK8,sK7,sK6),sK7)
    | ~ r2_hidden(sK6,k9_relat_1(sK8,sK7)) ),
    inference(instantiation,[status(thm)],[c_246])).

cnf(c_748,plain,
    ( r2_hidden(sK2(sK8,sK7,sK6),sK7) = iProver_top
    | r2_hidden(sK6,k9_relat_1(sK8,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_747])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK2(X1,X2,X0),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_233,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK2(X1,X2,X0),X0),X1)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_14])).

cnf(c_234,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK8,X1))
    | r2_hidden(k4_tarski(sK2(sK8,X1,X0),X0),sK8) ),
    inference(unflattening,[status(thm)],[c_233])).

cnf(c_744,plain,
    ( r2_hidden(k4_tarski(sK2(sK8,sK7,sK6),sK6),sK8)
    | ~ r2_hidden(sK6,k9_relat_1(sK8,sK7)) ),
    inference(instantiation,[status(thm)],[c_234])).

cnf(c_745,plain,
    ( r2_hidden(k4_tarski(sK2(sK8,sK7,sK6),sK6),sK8) = iProver_top
    | r2_hidden(sK6,k9_relat_1(sK8,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_744])).

cnf(c_11,negated_conjecture,
    ( r2_hidden(sK9,sK7)
    | r2_hidden(sK6,k9_relat_1(sK8,sK7)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_18,plain,
    ( r2_hidden(sK9,sK7) = iProver_top
    | r2_hidden(sK6,k9_relat_1(sK8,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_12,negated_conjecture,
    ( r2_hidden(k4_tarski(sK9,sK6),sK8)
    | r2_hidden(sK6,k9_relat_1(sK8,sK7)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_17,plain,
    ( r2_hidden(k4_tarski(sK9,sK6),sK8) = iProver_top
    | r2_hidden(sK6,k9_relat_1(sK8,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_13,negated_conjecture,
    ( r2_hidden(sK9,k1_relat_1(sK8))
    | r2_hidden(sK6,k9_relat_1(sK8,sK7)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_16,plain,
    ( r2_hidden(sK9,k1_relat_1(sK8)) = iProver_top
    | r2_hidden(sK6,k9_relat_1(sK8,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_809,c_796,c_783,c_748,c_745,c_18,c_17,c_16])).


%------------------------------------------------------------------------------
