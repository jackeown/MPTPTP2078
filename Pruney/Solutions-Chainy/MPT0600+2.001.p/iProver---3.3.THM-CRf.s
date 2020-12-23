%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:48:17 EST 2020

% Result     : Theorem 3.10s
% Output     : CNFRefutation 3.10s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 318 expanded)
%              Number of clauses        :   48 (  93 expanded)
%              Number of leaves         :   11 (  69 expanded)
%              Depth                    :   19
%              Number of atoms          :  303 (1443 expanded)
%              Number of equality atoms :  103 ( 280 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(k4_tarski(X0,X1),X2)
        <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <~> r2_hidden(X1,k11_relat_1(X2,X0)) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,k11_relat_1(X2,X0))
        | ~ r2_hidden(k4_tarski(X0,X1),X2) )
      & ( r2_hidden(X1,k11_relat_1(X2,X0))
        | r2_hidden(k4_tarski(X0,X1),X2) )
      & v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,k11_relat_1(X2,X0))
        | ~ r2_hidden(k4_tarski(X0,X1),X2) )
      & ( r2_hidden(X1,k11_relat_1(X2,X0))
        | r2_hidden(k4_tarski(X0,X1),X2) )
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f27,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(X1,k11_relat_1(X2,X0))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) )
        & ( r2_hidden(X1,k11_relat_1(X2,X0))
          | r2_hidden(k4_tarski(X0,X1),X2) )
        & v1_relat_1(X2) )
   => ( ( ~ r2_hidden(sK6,k11_relat_1(sK7,sK5))
        | ~ r2_hidden(k4_tarski(sK5,sK6),sK7) )
      & ( r2_hidden(sK6,k11_relat_1(sK7,sK5))
        | r2_hidden(k4_tarski(sK5,sK6),sK7) )
      & v1_relat_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ( ~ r2_hidden(sK6,k11_relat_1(sK7,sK5))
      | ~ r2_hidden(k4_tarski(sK5,sK6),sK7) )
    & ( r2_hidden(sK6,k11_relat_1(sK7,sK5))
      | r2_hidden(k4_tarski(sK5,sK6),sK7) )
    & v1_relat_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f26,f27])).

fof(f45,plain,
    ( r2_hidden(sK6,k11_relat_1(sK7,sK5))
    | r2_hidden(k4_tarski(sK5,sK6),sK7) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f15,plain,(
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
    inference(nnf_transformation,[],[f7])).

fof(f16,plain,(
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
    inference(rectify,[],[f15])).

fof(f19,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X8,X6),X0) )
     => ( r2_hidden(sK3(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(sK3(X0,X1,X6),X6),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X5,X3),X0) )
     => ( r2_hidden(sK2(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK2(X0,X1,X2),X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
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
              | ~ r2_hidden(k4_tarski(X4,sK1(X0,X1,X2)),X0) )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(X5,sK1(X0,X1,X2)),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(X4,sK1(X0,X1,X2)),X0) )
                | ~ r2_hidden(sK1(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK2(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK1(X0,X1,X2)),X0) )
                | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X7,X6),X0) ) )
                & ( ( r2_hidden(sK3(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(sK3(X0,X1,X6),X6),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f16,f19,f18,f17])).

fof(f35,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X7,X6),X0)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f50,plain,(
    ! [X6,X0,X7,X1] :
      ( r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X7,X6),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f35])).

fof(f44,plain,(
    v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f28])).

fof(f34,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f51,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f34])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f12,plain,(
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
    inference(rectify,[],[f11])).

fof(f13,plain,(
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

fof(f14,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f13])).

fof(f29,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f49,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f29])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k9_relat_1(X0,k1_tarski(X1)) = k11_relat_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] : k9_relat_1(X0,k1_tarski(X1)) = k11_relat_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X0,k1_tarski(X1)) = k11_relat_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f30,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f47,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f30])).

fof(f48,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f47])).

fof(f33,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X1,X6),X6),X0)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f52,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X1,X6),X6),X0)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f46,plain,
    ( ~ r2_hidden(sK6,k11_relat_1(sK7,sK5))
    | ~ r2_hidden(k4_tarski(sK5,sK6),sK7) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_16,negated_conjecture,
    ( r2_hidden(k4_tarski(sK5,sK6),sK7)
    | r2_hidden(sK6,k11_relat_1(sK7,sK5)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_925,plain,
    ( r2_hidden(k4_tarski(sK5,sK6),sK7) = iProver_top
    | r2_hidden(sK6,k11_relat_1(sK7,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k9_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_17,negated_conjecture,
    ( v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_298,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k9_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X3)
    | sK7 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_17])).

cnf(c_299,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k9_relat_1(sK7,X1))
    | ~ r2_hidden(k4_tarski(X0,X2),sK7) ),
    inference(unflattening,[status(thm)],[c_298])).

cnf(c_921,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,k9_relat_1(sK7,X1)) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_299])).

cnf(c_1725,plain,
    ( r2_hidden(sK5,X0) != iProver_top
    | r2_hidden(sK6,k11_relat_1(sK7,sK5)) = iProver_top
    | r2_hidden(sK6,k9_relat_1(sK7,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_925,c_921])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK3(X1,X2,X0),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_361,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK3(X1,X2,X0),X2)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_17])).

cnf(c_362,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK7,X1))
    | r2_hidden(sK3(sK7,X1,X0),X1) ),
    inference(unflattening,[status(thm)],[c_361])).

cnf(c_916,plain,
    ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(sK3(sK7,X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_362])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_927,plain,
    ( X0 = X1
    | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1247,plain,
    ( sK3(sK7,k1_tarski(X0),X1) = X0
    | r2_hidden(X1,k9_relat_1(sK7,k1_tarski(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_916,c_927])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_tarski(X1)) = k11_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_244,plain,
    ( k9_relat_1(X0,k1_tarski(X1)) = k11_relat_1(X0,X1)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_17])).

cnf(c_245,plain,
    ( k9_relat_1(sK7,k1_tarski(X0)) = k11_relat_1(sK7,X0) ),
    inference(unflattening,[status(thm)],[c_244])).

cnf(c_1250,plain,
    ( sK3(sK7,k1_tarski(X0),X1) = X0
    | r2_hidden(X1,k11_relat_1(sK7,X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1247,c_245])).

cnf(c_1901,plain,
    ( sK3(sK7,k1_tarski(sK5),sK6) = sK5
    | r2_hidden(sK5,X0) != iProver_top
    | r2_hidden(sK6,k9_relat_1(sK7,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1725,c_1250])).

cnf(c_1159,plain,
    ( r2_hidden(sK3(sK7,k1_tarski(sK5),sK6),k1_tarski(sK5))
    | ~ r2_hidden(sK6,k9_relat_1(sK7,k1_tarski(sK5))) ),
    inference(instantiation,[status(thm)],[c_362])).

cnf(c_2,plain,
    ( r2_hidden(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1182,plain,
    ( r2_hidden(sK5,k1_tarski(sK5)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_552,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1428,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_552])).

cnf(c_554,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1192,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK6,k11_relat_1(sK7,sK5))
    | X1 != k11_relat_1(sK7,sK5)
    | X0 != sK6 ),
    inference(instantiation,[status(thm)],[c_554])).

cnf(c_1427,plain,
    ( r2_hidden(sK6,X0)
    | ~ r2_hidden(sK6,k11_relat_1(sK7,sK5))
    | X0 != k11_relat_1(sK7,sK5)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_1192])).

cnf(c_1870,plain,
    ( ~ r2_hidden(sK6,k11_relat_1(sK7,sK5))
    | r2_hidden(sK6,k9_relat_1(sK7,k1_tarski(sK5)))
    | k9_relat_1(sK7,k1_tarski(sK5)) != k11_relat_1(sK7,sK5)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_1427])).

cnf(c_1871,plain,
    ( k9_relat_1(sK7,k1_tarski(sK5)) = k11_relat_1(sK7,sK5) ),
    inference(instantiation,[status(thm)],[c_245])).

cnf(c_1900,plain,
    ( r2_hidden(sK5,k1_tarski(X0)) != iProver_top
    | r2_hidden(sK6,k11_relat_1(sK7,X0)) = iProver_top
    | r2_hidden(sK6,k11_relat_1(sK7,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_245,c_1725])).

cnf(c_2086,plain,
    ( r2_hidden(sK5,k1_tarski(sK5)) != iProver_top
    | r2_hidden(sK6,k11_relat_1(sK7,sK5)) = iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_1900])).

cnf(c_2088,plain,
    ( r2_hidden(sK5,k1_tarski(sK5)) != iProver_top
    | r2_hidden(sK6,k11_relat_1(sK7,sK5)) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2086])).

cnf(c_2129,plain,
    ( ~ r2_hidden(sK5,k1_tarski(sK5))
    | r2_hidden(sK6,k11_relat_1(sK7,sK5)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2088])).

cnf(c_1224,plain,
    ( ~ r2_hidden(X0,k1_tarski(sK5))
    | X0 = sK5 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2212,plain,
    ( ~ r2_hidden(sK3(sK7,k1_tarski(sK5),X0),k1_tarski(sK5))
    | sK3(sK7,k1_tarski(sK5),X0) = sK5 ),
    inference(instantiation,[status(thm)],[c_1224])).

cnf(c_3157,plain,
    ( ~ r2_hidden(sK3(sK7,k1_tarski(sK5),sK6),k1_tarski(sK5))
    | sK3(sK7,k1_tarski(sK5),sK6) = sK5 ),
    inference(instantiation,[status(thm)],[c_2212])).

cnf(c_8253,plain,
    ( sK3(sK7,k1_tarski(sK5),sK6) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1901,c_1159,c_1182,c_1428,c_1870,c_1871,c_2129,c_3157])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK3(X1,X2,X0),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_349,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK3(X1,X2,X0),X0),X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_17])).

cnf(c_350,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK7,X1))
    | r2_hidden(k4_tarski(sK3(sK7,X1,X0),X0),sK7) ),
    inference(unflattening,[status(thm)],[c_349])).

cnf(c_917,plain,
    ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(k4_tarski(sK3(sK7,X1,X0),X0),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_350])).

cnf(c_8258,plain,
    ( r2_hidden(k4_tarski(sK5,sK6),sK7) = iProver_top
    | r2_hidden(sK6,k9_relat_1(sK7,k1_tarski(sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8253,c_917])).

cnf(c_8265,plain,
    ( r2_hidden(k4_tarski(sK5,sK6),sK7) = iProver_top
    | r2_hidden(sK6,k11_relat_1(sK7,sK5)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8258,c_245])).

cnf(c_1183,plain,
    ( r2_hidden(sK5,k1_tarski(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1182])).

cnf(c_15,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(sK5,sK6),sK7)
    | ~ r2_hidden(sK6,k11_relat_1(sK7,sK5)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_20,plain,
    ( r2_hidden(k4_tarski(sK5,sK6),sK7) != iProver_top
    | r2_hidden(sK6,k11_relat_1(sK7,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8265,c_2088,c_1183,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:26:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.10/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/1.01  
% 3.10/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.10/1.01  
% 3.10/1.01  ------  iProver source info
% 3.10/1.01  
% 3.10/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.10/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.10/1.01  git: non_committed_changes: false
% 3.10/1.01  git: last_make_outside_of_git: false
% 3.10/1.01  
% 3.10/1.01  ------ 
% 3.10/1.01  
% 3.10/1.01  ------ Input Options
% 3.10/1.01  
% 3.10/1.01  --out_options                           all
% 3.10/1.01  --tptp_safe_out                         true
% 3.10/1.01  --problem_path                          ""
% 3.10/1.01  --include_path                          ""
% 3.10/1.01  --clausifier                            res/vclausify_rel
% 3.10/1.01  --clausifier_options                    --mode clausify
% 3.10/1.01  --stdin                                 false
% 3.10/1.01  --stats_out                             all
% 3.10/1.01  
% 3.10/1.01  ------ General Options
% 3.10/1.01  
% 3.10/1.01  --fof                                   false
% 3.10/1.01  --time_out_real                         305.
% 3.10/1.01  --time_out_virtual                      -1.
% 3.10/1.01  --symbol_type_check                     false
% 3.10/1.01  --clausify_out                          false
% 3.10/1.01  --sig_cnt_out                           false
% 3.10/1.01  --trig_cnt_out                          false
% 3.10/1.01  --trig_cnt_out_tolerance                1.
% 3.10/1.01  --trig_cnt_out_sk_spl                   false
% 3.10/1.01  --abstr_cl_out                          false
% 3.10/1.01  
% 3.10/1.01  ------ Global Options
% 3.10/1.01  
% 3.10/1.01  --schedule                              default
% 3.10/1.01  --add_important_lit                     false
% 3.10/1.01  --prop_solver_per_cl                    1000
% 3.10/1.01  --min_unsat_core                        false
% 3.10/1.01  --soft_assumptions                      false
% 3.10/1.01  --soft_lemma_size                       3
% 3.10/1.01  --prop_impl_unit_size                   0
% 3.10/1.01  --prop_impl_unit                        []
% 3.10/1.01  --share_sel_clauses                     true
% 3.10/1.01  --reset_solvers                         false
% 3.10/1.01  --bc_imp_inh                            [conj_cone]
% 3.10/1.01  --conj_cone_tolerance                   3.
% 3.10/1.01  --extra_neg_conj                        none
% 3.10/1.01  --large_theory_mode                     true
% 3.10/1.01  --prolific_symb_bound                   200
% 3.10/1.01  --lt_threshold                          2000
% 3.10/1.01  --clause_weak_htbl                      true
% 3.10/1.01  --gc_record_bc_elim                     false
% 3.10/1.01  
% 3.10/1.01  ------ Preprocessing Options
% 3.10/1.01  
% 3.10/1.01  --preprocessing_flag                    true
% 3.10/1.01  --time_out_prep_mult                    0.1
% 3.10/1.01  --splitting_mode                        input
% 3.10/1.01  --splitting_grd                         true
% 3.10/1.01  --splitting_cvd                         false
% 3.10/1.01  --splitting_cvd_svl                     false
% 3.10/1.01  --splitting_nvd                         32
% 3.10/1.01  --sub_typing                            true
% 3.10/1.01  --prep_gs_sim                           true
% 3.10/1.01  --prep_unflatten                        true
% 3.10/1.01  --prep_res_sim                          true
% 3.10/1.01  --prep_upred                            true
% 3.10/1.01  --prep_sem_filter                       exhaustive
% 3.10/1.01  --prep_sem_filter_out                   false
% 3.10/1.01  --pred_elim                             true
% 3.10/1.01  --res_sim_input                         true
% 3.10/1.01  --eq_ax_congr_red                       true
% 3.10/1.01  --pure_diseq_elim                       true
% 3.10/1.01  --brand_transform                       false
% 3.10/1.01  --non_eq_to_eq                          false
% 3.10/1.01  --prep_def_merge                        true
% 3.10/1.01  --prep_def_merge_prop_impl              false
% 3.10/1.01  --prep_def_merge_mbd                    true
% 3.10/1.01  --prep_def_merge_tr_red                 false
% 3.10/1.01  --prep_def_merge_tr_cl                  false
% 3.10/1.01  --smt_preprocessing                     true
% 3.10/1.01  --smt_ac_axioms                         fast
% 3.10/1.01  --preprocessed_out                      false
% 3.10/1.01  --preprocessed_stats                    false
% 3.10/1.01  
% 3.10/1.01  ------ Abstraction refinement Options
% 3.10/1.01  
% 3.10/1.01  --abstr_ref                             []
% 3.10/1.01  --abstr_ref_prep                        false
% 3.10/1.01  --abstr_ref_until_sat                   false
% 3.10/1.01  --abstr_ref_sig_restrict                funpre
% 3.10/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.10/1.01  --abstr_ref_under                       []
% 3.10/1.01  
% 3.10/1.01  ------ SAT Options
% 3.10/1.01  
% 3.10/1.01  --sat_mode                              false
% 3.10/1.01  --sat_fm_restart_options                ""
% 3.10/1.01  --sat_gr_def                            false
% 3.10/1.01  --sat_epr_types                         true
% 3.10/1.01  --sat_non_cyclic_types                  false
% 3.10/1.01  --sat_finite_models                     false
% 3.10/1.01  --sat_fm_lemmas                         false
% 3.10/1.01  --sat_fm_prep                           false
% 3.10/1.01  --sat_fm_uc_incr                        true
% 3.10/1.01  --sat_out_model                         small
% 3.10/1.01  --sat_out_clauses                       false
% 3.10/1.01  
% 3.10/1.01  ------ QBF Options
% 3.10/1.01  
% 3.10/1.01  --qbf_mode                              false
% 3.10/1.01  --qbf_elim_univ                         false
% 3.10/1.01  --qbf_dom_inst                          none
% 3.10/1.01  --qbf_dom_pre_inst                      false
% 3.10/1.01  --qbf_sk_in                             false
% 3.10/1.01  --qbf_pred_elim                         true
% 3.10/1.01  --qbf_split                             512
% 3.10/1.01  
% 3.10/1.01  ------ BMC1 Options
% 3.10/1.01  
% 3.10/1.01  --bmc1_incremental                      false
% 3.10/1.01  --bmc1_axioms                           reachable_all
% 3.10/1.01  --bmc1_min_bound                        0
% 3.10/1.01  --bmc1_max_bound                        -1
% 3.10/1.01  --bmc1_max_bound_default                -1
% 3.10/1.01  --bmc1_symbol_reachability              true
% 3.10/1.01  --bmc1_property_lemmas                  false
% 3.10/1.01  --bmc1_k_induction                      false
% 3.10/1.01  --bmc1_non_equiv_states                 false
% 3.10/1.01  --bmc1_deadlock                         false
% 3.10/1.01  --bmc1_ucm                              false
% 3.10/1.01  --bmc1_add_unsat_core                   none
% 3.10/1.01  --bmc1_unsat_core_children              false
% 3.10/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.10/1.01  --bmc1_out_stat                         full
% 3.10/1.01  --bmc1_ground_init                      false
% 3.10/1.01  --bmc1_pre_inst_next_state              false
% 3.10/1.01  --bmc1_pre_inst_state                   false
% 3.10/1.01  --bmc1_pre_inst_reach_state             false
% 3.10/1.01  --bmc1_out_unsat_core                   false
% 3.10/1.01  --bmc1_aig_witness_out                  false
% 3.10/1.01  --bmc1_verbose                          false
% 3.10/1.01  --bmc1_dump_clauses_tptp                false
% 3.10/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.10/1.01  --bmc1_dump_file                        -
% 3.10/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.10/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.10/1.01  --bmc1_ucm_extend_mode                  1
% 3.10/1.01  --bmc1_ucm_init_mode                    2
% 3.10/1.01  --bmc1_ucm_cone_mode                    none
% 3.10/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.10/1.01  --bmc1_ucm_relax_model                  4
% 3.10/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.10/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.10/1.01  --bmc1_ucm_layered_model                none
% 3.10/1.01  --bmc1_ucm_max_lemma_size               10
% 3.10/1.01  
% 3.10/1.01  ------ AIG Options
% 3.10/1.01  
% 3.10/1.01  --aig_mode                              false
% 3.10/1.01  
% 3.10/1.01  ------ Instantiation Options
% 3.10/1.01  
% 3.10/1.01  --instantiation_flag                    true
% 3.10/1.01  --inst_sos_flag                         false
% 3.10/1.01  --inst_sos_phase                        true
% 3.10/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.10/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.10/1.01  --inst_lit_sel_side                     num_symb
% 3.10/1.01  --inst_solver_per_active                1400
% 3.10/1.01  --inst_solver_calls_frac                1.
% 3.10/1.01  --inst_passive_queue_type               priority_queues
% 3.10/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.10/1.01  --inst_passive_queues_freq              [25;2]
% 3.10/1.01  --inst_dismatching                      true
% 3.10/1.01  --inst_eager_unprocessed_to_passive     true
% 3.10/1.01  --inst_prop_sim_given                   true
% 3.10/1.01  --inst_prop_sim_new                     false
% 3.10/1.01  --inst_subs_new                         false
% 3.10/1.01  --inst_eq_res_simp                      false
% 3.10/1.01  --inst_subs_given                       false
% 3.10/1.01  --inst_orphan_elimination               true
% 3.10/1.01  --inst_learning_loop_flag               true
% 3.10/1.01  --inst_learning_start                   3000
% 3.10/1.01  --inst_learning_factor                  2
% 3.10/1.01  --inst_start_prop_sim_after_learn       3
% 3.10/1.01  --inst_sel_renew                        solver
% 3.10/1.01  --inst_lit_activity_flag                true
% 3.10/1.01  --inst_restr_to_given                   false
% 3.10/1.01  --inst_activity_threshold               500
% 3.10/1.01  --inst_out_proof                        true
% 3.10/1.01  
% 3.10/1.01  ------ Resolution Options
% 3.10/1.01  
% 3.10/1.01  --resolution_flag                       true
% 3.10/1.01  --res_lit_sel                           adaptive
% 3.10/1.01  --res_lit_sel_side                      none
% 3.10/1.01  --res_ordering                          kbo
% 3.10/1.01  --res_to_prop_solver                    active
% 3.10/1.01  --res_prop_simpl_new                    false
% 3.10/1.01  --res_prop_simpl_given                  true
% 3.10/1.01  --res_passive_queue_type                priority_queues
% 3.10/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.10/1.01  --res_passive_queues_freq               [15;5]
% 3.10/1.01  --res_forward_subs                      full
% 3.10/1.01  --res_backward_subs                     full
% 3.10/1.01  --res_forward_subs_resolution           true
% 3.10/1.01  --res_backward_subs_resolution          true
% 3.10/1.01  --res_orphan_elimination                true
% 3.10/1.01  --res_time_limit                        2.
% 3.10/1.01  --res_out_proof                         true
% 3.10/1.01  
% 3.10/1.01  ------ Superposition Options
% 3.10/1.01  
% 3.10/1.01  --superposition_flag                    true
% 3.10/1.01  --sup_passive_queue_type                priority_queues
% 3.10/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.10/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.10/1.01  --demod_completeness_check              fast
% 3.10/1.01  --demod_use_ground                      true
% 3.10/1.01  --sup_to_prop_solver                    passive
% 3.10/1.01  --sup_prop_simpl_new                    true
% 3.10/1.01  --sup_prop_simpl_given                  true
% 3.10/1.01  --sup_fun_splitting                     false
% 3.10/1.01  --sup_smt_interval                      50000
% 3.10/1.01  
% 3.10/1.01  ------ Superposition Simplification Setup
% 3.10/1.01  
% 3.10/1.01  --sup_indices_passive                   []
% 3.10/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.10/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/1.01  --sup_full_bw                           [BwDemod]
% 3.10/1.01  --sup_immed_triv                        [TrivRules]
% 3.10/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.10/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/1.01  --sup_immed_bw_main                     []
% 3.10/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.10/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.10/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.10/1.01  
% 3.10/1.01  ------ Combination Options
% 3.10/1.01  
% 3.10/1.01  --comb_res_mult                         3
% 3.10/1.01  --comb_sup_mult                         2
% 3.10/1.01  --comb_inst_mult                        10
% 3.10/1.01  
% 3.10/1.01  ------ Debug Options
% 3.10/1.01  
% 3.10/1.01  --dbg_backtrace                         false
% 3.10/1.01  --dbg_dump_prop_clauses                 false
% 3.10/1.01  --dbg_dump_prop_clauses_file            -
% 3.10/1.01  --dbg_out_stat                          false
% 3.10/1.01  ------ Parsing...
% 3.10/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.10/1.01  
% 3.10/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.10/1.01  
% 3.10/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.10/1.01  
% 3.10/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.10/1.01  ------ Proving...
% 3.10/1.01  ------ Problem Properties 
% 3.10/1.01  
% 3.10/1.01  
% 3.10/1.01  clauses                                 16
% 3.10/1.01  conjectures                             2
% 3.10/1.01  EPR                                     0
% 3.10/1.01  Horn                                    12
% 3.10/1.01  unary                                   2
% 3.10/1.01  binary                                  8
% 3.10/1.01  lits                                    37
% 3.10/1.01  lits eq                                 9
% 3.10/1.01  fd_pure                                 0
% 3.10/1.01  fd_pseudo                               0
% 3.10/1.01  fd_cond                                 0
% 3.10/1.01  fd_pseudo_cond                          5
% 3.10/1.01  AC symbols                              0
% 3.10/1.01  
% 3.10/1.01  ------ Schedule dynamic 5 is on 
% 3.10/1.01  
% 3.10/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.10/1.01  
% 3.10/1.01  
% 3.10/1.01  ------ 
% 3.10/1.01  Current options:
% 3.10/1.01  ------ 
% 3.10/1.01  
% 3.10/1.01  ------ Input Options
% 3.10/1.01  
% 3.10/1.01  --out_options                           all
% 3.10/1.01  --tptp_safe_out                         true
% 3.10/1.01  --problem_path                          ""
% 3.10/1.01  --include_path                          ""
% 3.10/1.01  --clausifier                            res/vclausify_rel
% 3.10/1.01  --clausifier_options                    --mode clausify
% 3.10/1.01  --stdin                                 false
% 3.10/1.01  --stats_out                             all
% 3.10/1.01  
% 3.10/1.01  ------ General Options
% 3.10/1.01  
% 3.10/1.01  --fof                                   false
% 3.10/1.01  --time_out_real                         305.
% 3.10/1.01  --time_out_virtual                      -1.
% 3.10/1.01  --symbol_type_check                     false
% 3.10/1.01  --clausify_out                          false
% 3.10/1.01  --sig_cnt_out                           false
% 3.10/1.01  --trig_cnt_out                          false
% 3.10/1.01  --trig_cnt_out_tolerance                1.
% 3.10/1.01  --trig_cnt_out_sk_spl                   false
% 3.10/1.01  --abstr_cl_out                          false
% 3.10/1.01  
% 3.10/1.01  ------ Global Options
% 3.10/1.01  
% 3.10/1.01  --schedule                              default
% 3.10/1.01  --add_important_lit                     false
% 3.10/1.01  --prop_solver_per_cl                    1000
% 3.10/1.01  --min_unsat_core                        false
% 3.10/1.01  --soft_assumptions                      false
% 3.10/1.01  --soft_lemma_size                       3
% 3.10/1.01  --prop_impl_unit_size                   0
% 3.10/1.01  --prop_impl_unit                        []
% 3.10/1.01  --share_sel_clauses                     true
% 3.10/1.01  --reset_solvers                         false
% 3.10/1.01  --bc_imp_inh                            [conj_cone]
% 3.10/1.01  --conj_cone_tolerance                   3.
% 3.10/1.01  --extra_neg_conj                        none
% 3.10/1.01  --large_theory_mode                     true
% 3.10/1.01  --prolific_symb_bound                   200
% 3.10/1.01  --lt_threshold                          2000
% 3.10/1.01  --clause_weak_htbl                      true
% 3.10/1.01  --gc_record_bc_elim                     false
% 3.10/1.01  
% 3.10/1.01  ------ Preprocessing Options
% 3.10/1.01  
% 3.10/1.01  --preprocessing_flag                    true
% 3.10/1.01  --time_out_prep_mult                    0.1
% 3.10/1.01  --splitting_mode                        input
% 3.10/1.01  --splitting_grd                         true
% 3.10/1.01  --splitting_cvd                         false
% 3.10/1.01  --splitting_cvd_svl                     false
% 3.10/1.01  --splitting_nvd                         32
% 3.10/1.01  --sub_typing                            true
% 3.10/1.01  --prep_gs_sim                           true
% 3.10/1.01  --prep_unflatten                        true
% 3.10/1.01  --prep_res_sim                          true
% 3.10/1.01  --prep_upred                            true
% 3.10/1.01  --prep_sem_filter                       exhaustive
% 3.10/1.01  --prep_sem_filter_out                   false
% 3.10/1.01  --pred_elim                             true
% 3.10/1.01  --res_sim_input                         true
% 3.10/1.01  --eq_ax_congr_red                       true
% 3.10/1.01  --pure_diseq_elim                       true
% 3.10/1.01  --brand_transform                       false
% 3.10/1.01  --non_eq_to_eq                          false
% 3.10/1.01  --prep_def_merge                        true
% 3.10/1.01  --prep_def_merge_prop_impl              false
% 3.10/1.01  --prep_def_merge_mbd                    true
% 3.10/1.01  --prep_def_merge_tr_red                 false
% 3.10/1.01  --prep_def_merge_tr_cl                  false
% 3.10/1.01  --smt_preprocessing                     true
% 3.10/1.01  --smt_ac_axioms                         fast
% 3.10/1.01  --preprocessed_out                      false
% 3.10/1.01  --preprocessed_stats                    false
% 3.10/1.01  
% 3.10/1.01  ------ Abstraction refinement Options
% 3.10/1.01  
% 3.10/1.01  --abstr_ref                             []
% 3.10/1.01  --abstr_ref_prep                        false
% 3.10/1.01  --abstr_ref_until_sat                   false
% 3.10/1.01  --abstr_ref_sig_restrict                funpre
% 3.10/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.10/1.01  --abstr_ref_under                       []
% 3.10/1.01  
% 3.10/1.01  ------ SAT Options
% 3.10/1.01  
% 3.10/1.01  --sat_mode                              false
% 3.10/1.01  --sat_fm_restart_options                ""
% 3.10/1.01  --sat_gr_def                            false
% 3.10/1.01  --sat_epr_types                         true
% 3.10/1.01  --sat_non_cyclic_types                  false
% 3.10/1.01  --sat_finite_models                     false
% 3.10/1.01  --sat_fm_lemmas                         false
% 3.10/1.01  --sat_fm_prep                           false
% 3.10/1.01  --sat_fm_uc_incr                        true
% 3.10/1.01  --sat_out_model                         small
% 3.10/1.01  --sat_out_clauses                       false
% 3.10/1.01  
% 3.10/1.01  ------ QBF Options
% 3.10/1.01  
% 3.10/1.01  --qbf_mode                              false
% 3.10/1.01  --qbf_elim_univ                         false
% 3.10/1.01  --qbf_dom_inst                          none
% 3.10/1.01  --qbf_dom_pre_inst                      false
% 3.10/1.01  --qbf_sk_in                             false
% 3.10/1.01  --qbf_pred_elim                         true
% 3.10/1.01  --qbf_split                             512
% 3.10/1.01  
% 3.10/1.01  ------ BMC1 Options
% 3.10/1.01  
% 3.10/1.01  --bmc1_incremental                      false
% 3.10/1.01  --bmc1_axioms                           reachable_all
% 3.10/1.01  --bmc1_min_bound                        0
% 3.10/1.01  --bmc1_max_bound                        -1
% 3.10/1.01  --bmc1_max_bound_default                -1
% 3.10/1.01  --bmc1_symbol_reachability              true
% 3.10/1.01  --bmc1_property_lemmas                  false
% 3.10/1.01  --bmc1_k_induction                      false
% 3.10/1.01  --bmc1_non_equiv_states                 false
% 3.10/1.01  --bmc1_deadlock                         false
% 3.10/1.01  --bmc1_ucm                              false
% 3.10/1.01  --bmc1_add_unsat_core                   none
% 3.10/1.01  --bmc1_unsat_core_children              false
% 3.10/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.10/1.01  --bmc1_out_stat                         full
% 3.10/1.01  --bmc1_ground_init                      false
% 3.10/1.01  --bmc1_pre_inst_next_state              false
% 3.10/1.01  --bmc1_pre_inst_state                   false
% 3.10/1.01  --bmc1_pre_inst_reach_state             false
% 3.10/1.01  --bmc1_out_unsat_core                   false
% 3.10/1.01  --bmc1_aig_witness_out                  false
% 3.10/1.01  --bmc1_verbose                          false
% 3.10/1.01  --bmc1_dump_clauses_tptp                false
% 3.10/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.10/1.01  --bmc1_dump_file                        -
% 3.10/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.10/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.10/1.01  --bmc1_ucm_extend_mode                  1
% 3.10/1.01  --bmc1_ucm_init_mode                    2
% 3.10/1.01  --bmc1_ucm_cone_mode                    none
% 3.10/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.10/1.01  --bmc1_ucm_relax_model                  4
% 3.10/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.10/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.10/1.01  --bmc1_ucm_layered_model                none
% 3.10/1.01  --bmc1_ucm_max_lemma_size               10
% 3.10/1.01  
% 3.10/1.01  ------ AIG Options
% 3.10/1.01  
% 3.10/1.01  --aig_mode                              false
% 3.10/1.01  
% 3.10/1.01  ------ Instantiation Options
% 3.10/1.01  
% 3.10/1.01  --instantiation_flag                    true
% 3.10/1.01  --inst_sos_flag                         false
% 3.10/1.01  --inst_sos_phase                        true
% 3.10/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.10/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.10/1.01  --inst_lit_sel_side                     none
% 3.10/1.01  --inst_solver_per_active                1400
% 3.10/1.01  --inst_solver_calls_frac                1.
% 3.10/1.01  --inst_passive_queue_type               priority_queues
% 3.10/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.10/1.01  --inst_passive_queues_freq              [25;2]
% 3.10/1.01  --inst_dismatching                      true
% 3.10/1.01  --inst_eager_unprocessed_to_passive     true
% 3.10/1.01  --inst_prop_sim_given                   true
% 3.10/1.01  --inst_prop_sim_new                     false
% 3.10/1.01  --inst_subs_new                         false
% 3.10/1.01  --inst_eq_res_simp                      false
% 3.10/1.01  --inst_subs_given                       false
% 3.10/1.01  --inst_orphan_elimination               true
% 3.10/1.01  --inst_learning_loop_flag               true
% 3.10/1.01  --inst_learning_start                   3000
% 3.10/1.01  --inst_learning_factor                  2
% 3.10/1.01  --inst_start_prop_sim_after_learn       3
% 3.10/1.01  --inst_sel_renew                        solver
% 3.10/1.01  --inst_lit_activity_flag                true
% 3.10/1.01  --inst_restr_to_given                   false
% 3.10/1.01  --inst_activity_threshold               500
% 3.10/1.01  --inst_out_proof                        true
% 3.10/1.01  
% 3.10/1.01  ------ Resolution Options
% 3.10/1.01  
% 3.10/1.01  --resolution_flag                       false
% 3.10/1.01  --res_lit_sel                           adaptive
% 3.10/1.01  --res_lit_sel_side                      none
% 3.10/1.01  --res_ordering                          kbo
% 3.10/1.01  --res_to_prop_solver                    active
% 3.10/1.01  --res_prop_simpl_new                    false
% 3.10/1.01  --res_prop_simpl_given                  true
% 3.10/1.01  --res_passive_queue_type                priority_queues
% 3.10/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.10/1.01  --res_passive_queues_freq               [15;5]
% 3.10/1.01  --res_forward_subs                      full
% 3.10/1.01  --res_backward_subs                     full
% 3.10/1.01  --res_forward_subs_resolution           true
% 3.10/1.01  --res_backward_subs_resolution          true
% 3.10/1.01  --res_orphan_elimination                true
% 3.10/1.01  --res_time_limit                        2.
% 3.10/1.01  --res_out_proof                         true
% 3.10/1.01  
% 3.10/1.01  ------ Superposition Options
% 3.10/1.01  
% 3.10/1.01  --superposition_flag                    true
% 3.10/1.01  --sup_passive_queue_type                priority_queues
% 3.10/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.10/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.10/1.01  --demod_completeness_check              fast
% 3.10/1.01  --demod_use_ground                      true
% 3.10/1.01  --sup_to_prop_solver                    passive
% 3.10/1.01  --sup_prop_simpl_new                    true
% 3.10/1.01  --sup_prop_simpl_given                  true
% 3.10/1.01  --sup_fun_splitting                     false
% 3.10/1.01  --sup_smt_interval                      50000
% 3.10/1.01  
% 3.10/1.01  ------ Superposition Simplification Setup
% 3.10/1.01  
% 3.10/1.01  --sup_indices_passive                   []
% 3.10/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.10/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/1.01  --sup_full_bw                           [BwDemod]
% 3.10/1.01  --sup_immed_triv                        [TrivRules]
% 3.10/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.10/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/1.01  --sup_immed_bw_main                     []
% 3.10/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.10/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.10/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.10/1.01  
% 3.10/1.01  ------ Combination Options
% 3.10/1.01  
% 3.10/1.01  --comb_res_mult                         3
% 3.10/1.01  --comb_sup_mult                         2
% 3.10/1.01  --comb_inst_mult                        10
% 3.10/1.01  
% 3.10/1.01  ------ Debug Options
% 3.10/1.01  
% 3.10/1.01  --dbg_backtrace                         false
% 3.10/1.01  --dbg_dump_prop_clauses                 false
% 3.10/1.01  --dbg_dump_prop_clauses_file            -
% 3.10/1.01  --dbg_out_stat                          false
% 3.10/1.01  
% 3.10/1.01  
% 3.10/1.01  
% 3.10/1.01  
% 3.10/1.01  ------ Proving...
% 3.10/1.01  
% 3.10/1.01  
% 3.10/1.01  % SZS status Theorem for theBenchmark.p
% 3.10/1.01  
% 3.10/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.10/1.01  
% 3.10/1.01  fof(f5,conjecture,(
% 3.10/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 3.10/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/1.01  
% 3.10/1.01  fof(f6,negated_conjecture,(
% 3.10/1.01    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 3.10/1.01    inference(negated_conjecture,[],[f5])).
% 3.10/1.01  
% 3.10/1.01  fof(f10,plain,(
% 3.10/1.01    ? [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <~> r2_hidden(X1,k11_relat_1(X2,X0))) & v1_relat_1(X2))),
% 3.10/1.01    inference(ennf_transformation,[],[f6])).
% 3.10/1.01  
% 3.10/1.01  fof(f25,plain,(
% 3.10/1.01    ? [X0,X1,X2] : (((~r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2)) & (r2_hidden(X1,k11_relat_1(X2,X0)) | r2_hidden(k4_tarski(X0,X1),X2))) & v1_relat_1(X2))),
% 3.10/1.01    inference(nnf_transformation,[],[f10])).
% 3.10/1.01  
% 3.10/1.01  fof(f26,plain,(
% 3.10/1.01    ? [X0,X1,X2] : ((~r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2)) & (r2_hidden(X1,k11_relat_1(X2,X0)) | r2_hidden(k4_tarski(X0,X1),X2)) & v1_relat_1(X2))),
% 3.10/1.01    inference(flattening,[],[f25])).
% 3.10/1.01  
% 3.10/1.01  fof(f27,plain,(
% 3.10/1.01    ? [X0,X1,X2] : ((~r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2)) & (r2_hidden(X1,k11_relat_1(X2,X0)) | r2_hidden(k4_tarski(X0,X1),X2)) & v1_relat_1(X2)) => ((~r2_hidden(sK6,k11_relat_1(sK7,sK5)) | ~r2_hidden(k4_tarski(sK5,sK6),sK7)) & (r2_hidden(sK6,k11_relat_1(sK7,sK5)) | r2_hidden(k4_tarski(sK5,sK6),sK7)) & v1_relat_1(sK7))),
% 3.10/1.01    introduced(choice_axiom,[])).
% 3.10/1.01  
% 3.10/1.01  fof(f28,plain,(
% 3.10/1.01    (~r2_hidden(sK6,k11_relat_1(sK7,sK5)) | ~r2_hidden(k4_tarski(sK5,sK6),sK7)) & (r2_hidden(sK6,k11_relat_1(sK7,sK5)) | r2_hidden(k4_tarski(sK5,sK6),sK7)) & v1_relat_1(sK7)),
% 3.10/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f26,f27])).
% 3.10/1.01  
% 3.10/1.01  fof(f45,plain,(
% 3.10/1.01    r2_hidden(sK6,k11_relat_1(sK7,sK5)) | r2_hidden(k4_tarski(sK5,sK6),sK7)),
% 3.10/1.01    inference(cnf_transformation,[],[f28])).
% 3.10/1.01  
% 3.10/1.01  fof(f2,axiom,(
% 3.10/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)))))),
% 3.10/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/1.01  
% 3.10/1.01  fof(f7,plain,(
% 3.10/1.01    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)))) | ~v1_relat_1(X0))),
% 3.10/1.01    inference(ennf_transformation,[],[f2])).
% 3.10/1.01  
% 3.10/1.01  fof(f15,plain,(
% 3.10/1.01    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2)) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 3.10/1.01    inference(nnf_transformation,[],[f7])).
% 3.10/1.01  
% 3.10/1.01  fof(f16,plain,(
% 3.10/1.01    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X3),X0)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0))) & (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X8,X6),X0)) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 3.10/1.01    inference(rectify,[],[f15])).
% 3.10/1.01  
% 3.10/1.01  fof(f19,plain,(
% 3.10/1.01    ! [X6,X1,X0] : (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X8,X6),X0)) => (r2_hidden(sK3(X0,X1,X6),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X6),X6),X0)))),
% 3.10/1.01    introduced(choice_axiom,[])).
% 3.10/1.01  
% 3.10/1.01  fof(f18,plain,(
% 3.10/1.01    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X3),X0)) => (r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),X3),X0)))) )),
% 3.10/1.01    introduced(choice_axiom,[])).
% 3.10/1.01  
% 3.10/1.01  fof(f17,plain,(
% 3.10/1.01    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X3),X0)) | r2_hidden(X3,X2))) => ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,sK1(X0,X1,X2)),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,sK1(X0,X1,X2)),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.10/1.01    introduced(choice_axiom,[])).
% 3.10/1.01  
% 3.10/1.01  fof(f20,plain,(
% 3.10/1.01    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,sK1(X0,X1,X2)),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK1(X0,X1,X2)),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0))) & ((r2_hidden(sK3(X0,X1,X6),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X6),X6),X0)) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 3.10/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f16,f19,f18,f17])).
% 3.10/1.01  
% 3.10/1.01  fof(f35,plain,(
% 3.10/1.01    ( ! [X6,X2,X0,X7,X1] : (r2_hidden(X6,X2) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0) | k9_relat_1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 3.10/1.01    inference(cnf_transformation,[],[f20])).
% 3.10/1.01  
% 3.10/1.01  fof(f50,plain,(
% 3.10/1.01    ( ! [X6,X0,X7,X1] : (r2_hidden(X6,k9_relat_1(X0,X1)) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0) | ~v1_relat_1(X0)) )),
% 3.10/1.01    inference(equality_resolution,[],[f35])).
% 3.10/1.01  
% 3.10/1.01  fof(f44,plain,(
% 3.10/1.01    v1_relat_1(sK7)),
% 3.10/1.01    inference(cnf_transformation,[],[f28])).
% 3.10/1.01  
% 3.10/1.01  fof(f34,plain,(
% 3.10/1.01    ( ! [X6,X2,X0,X1] : (r2_hidden(sK3(X0,X1,X6),X1) | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 3.10/1.01    inference(cnf_transformation,[],[f20])).
% 3.10/1.01  
% 3.10/1.01  fof(f51,plain,(
% 3.10/1.01    ( ! [X6,X0,X1] : (r2_hidden(sK3(X0,X1,X6),X1) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 3.10/1.01    inference(equality_resolution,[],[f34])).
% 3.10/1.01  
% 3.10/1.01  fof(f1,axiom,(
% 3.10/1.01    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 3.10/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/1.01  
% 3.10/1.01  fof(f11,plain,(
% 3.10/1.01    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 3.10/1.01    inference(nnf_transformation,[],[f1])).
% 3.10/1.01  
% 3.10/1.01  fof(f12,plain,(
% 3.10/1.01    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.10/1.01    inference(rectify,[],[f11])).
% 3.10/1.01  
% 3.10/1.01  fof(f13,plain,(
% 3.10/1.01    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1))))),
% 3.10/1.01    introduced(choice_axiom,[])).
% 3.10/1.01  
% 3.10/1.01  fof(f14,plain,(
% 3.10/1.01    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.10/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f13])).
% 3.10/1.01  
% 3.10/1.01  fof(f29,plain,(
% 3.10/1.01    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 3.10/1.01    inference(cnf_transformation,[],[f14])).
% 3.10/1.01  
% 3.10/1.01  fof(f49,plain,(
% 3.10/1.01    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_tarski(X0))) )),
% 3.10/1.01    inference(equality_resolution,[],[f29])).
% 3.10/1.01  
% 3.10/1.01  fof(f3,axiom,(
% 3.10/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : k9_relat_1(X0,k1_tarski(X1)) = k11_relat_1(X0,X1))),
% 3.10/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/1.01  
% 3.10/1.01  fof(f8,plain,(
% 3.10/1.01    ! [X0] : (! [X1] : k9_relat_1(X0,k1_tarski(X1)) = k11_relat_1(X0,X1) | ~v1_relat_1(X0))),
% 3.10/1.01    inference(ennf_transformation,[],[f3])).
% 3.10/1.01  
% 3.10/1.01  fof(f39,plain,(
% 3.10/1.01    ( ! [X0,X1] : (k9_relat_1(X0,k1_tarski(X1)) = k11_relat_1(X0,X1) | ~v1_relat_1(X0)) )),
% 3.10/1.01    inference(cnf_transformation,[],[f8])).
% 3.10/1.01  
% 3.10/1.01  fof(f30,plain,(
% 3.10/1.01    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 3.10/1.01    inference(cnf_transformation,[],[f14])).
% 3.10/1.01  
% 3.10/1.01  fof(f47,plain,(
% 3.10/1.01    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 3.10/1.01    inference(equality_resolution,[],[f30])).
% 3.10/1.01  
% 3.10/1.01  fof(f48,plain,(
% 3.10/1.01    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 3.10/1.01    inference(equality_resolution,[],[f47])).
% 3.10/1.01  
% 3.10/1.01  fof(f33,plain,(
% 3.10/1.01    ( ! [X6,X2,X0,X1] : (r2_hidden(k4_tarski(sK3(X0,X1,X6),X6),X0) | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 3.10/1.01    inference(cnf_transformation,[],[f20])).
% 3.10/1.01  
% 3.10/1.01  fof(f52,plain,(
% 3.10/1.01    ( ! [X6,X0,X1] : (r2_hidden(k4_tarski(sK3(X0,X1,X6),X6),X0) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 3.10/1.01    inference(equality_resolution,[],[f33])).
% 3.10/1.01  
% 3.10/1.01  fof(f46,plain,(
% 3.10/1.01    ~r2_hidden(sK6,k11_relat_1(sK7,sK5)) | ~r2_hidden(k4_tarski(sK5,sK6),sK7)),
% 3.10/1.01    inference(cnf_transformation,[],[f28])).
% 3.10/1.01  
% 3.10/1.01  cnf(c_16,negated_conjecture,
% 3.10/1.01      ( r2_hidden(k4_tarski(sK5,sK6),sK7)
% 3.10/1.01      | r2_hidden(sK6,k11_relat_1(sK7,sK5)) ),
% 3.10/1.01      inference(cnf_transformation,[],[f45]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_925,plain,
% 3.10/1.01      ( r2_hidden(k4_tarski(sK5,sK6),sK7) = iProver_top
% 3.10/1.01      | r2_hidden(sK6,k11_relat_1(sK7,sK5)) = iProver_top ),
% 3.10/1.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_7,plain,
% 3.10/1.01      ( ~ r2_hidden(X0,X1)
% 3.10/1.01      | r2_hidden(X2,k9_relat_1(X3,X1))
% 3.10/1.01      | ~ r2_hidden(k4_tarski(X0,X2),X3)
% 3.10/1.01      | ~ v1_relat_1(X3) ),
% 3.10/1.01      inference(cnf_transformation,[],[f50]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_17,negated_conjecture,
% 3.10/1.01      ( v1_relat_1(sK7) ),
% 3.10/1.01      inference(cnf_transformation,[],[f44]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_298,plain,
% 3.10/1.01      ( ~ r2_hidden(X0,X1)
% 3.10/1.01      | r2_hidden(X2,k9_relat_1(X3,X1))
% 3.10/1.01      | ~ r2_hidden(k4_tarski(X0,X2),X3)
% 3.10/1.01      | sK7 != X3 ),
% 3.10/1.01      inference(resolution_lifted,[status(thm)],[c_7,c_17]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_299,plain,
% 3.10/1.01      ( ~ r2_hidden(X0,X1)
% 3.10/1.01      | r2_hidden(X2,k9_relat_1(sK7,X1))
% 3.10/1.01      | ~ r2_hidden(k4_tarski(X0,X2),sK7) ),
% 3.10/1.01      inference(unflattening,[status(thm)],[c_298]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_921,plain,
% 3.10/1.01      ( r2_hidden(X0,X1) != iProver_top
% 3.10/1.01      | r2_hidden(X2,k9_relat_1(sK7,X1)) = iProver_top
% 3.10/1.01      | r2_hidden(k4_tarski(X0,X2),sK7) != iProver_top ),
% 3.10/1.01      inference(predicate_to_equality,[status(thm)],[c_299]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_1725,plain,
% 3.10/1.01      ( r2_hidden(sK5,X0) != iProver_top
% 3.10/1.01      | r2_hidden(sK6,k11_relat_1(sK7,sK5)) = iProver_top
% 3.10/1.01      | r2_hidden(sK6,k9_relat_1(sK7,X0)) = iProver_top ),
% 3.10/1.01      inference(superposition,[status(thm)],[c_925,c_921]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_8,plain,
% 3.10/1.01      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.10/1.01      | r2_hidden(sK3(X1,X2,X0),X2)
% 3.10/1.01      | ~ v1_relat_1(X1) ),
% 3.10/1.01      inference(cnf_transformation,[],[f51]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_361,plain,
% 3.10/1.01      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.10/1.01      | r2_hidden(sK3(X1,X2,X0),X2)
% 3.10/1.01      | sK7 != X1 ),
% 3.10/1.01      inference(resolution_lifted,[status(thm)],[c_8,c_17]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_362,plain,
% 3.10/1.01      ( ~ r2_hidden(X0,k9_relat_1(sK7,X1))
% 3.10/1.01      | r2_hidden(sK3(sK7,X1,X0),X1) ),
% 3.10/1.01      inference(unflattening,[status(thm)],[c_361]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_916,plain,
% 3.10/1.01      ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 3.10/1.01      | r2_hidden(sK3(sK7,X1,X0),X1) = iProver_top ),
% 3.10/1.01      inference(predicate_to_equality,[status(thm)],[c_362]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_3,plain,
% 3.10/1.01      ( ~ r2_hidden(X0,k1_tarski(X1)) | X0 = X1 ),
% 3.10/1.01      inference(cnf_transformation,[],[f49]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_927,plain,
% 3.10/1.01      ( X0 = X1 | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
% 3.10/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_1247,plain,
% 3.10/1.01      ( sK3(sK7,k1_tarski(X0),X1) = X0
% 3.10/1.01      | r2_hidden(X1,k9_relat_1(sK7,k1_tarski(X0))) != iProver_top ),
% 3.10/1.01      inference(superposition,[status(thm)],[c_916,c_927]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_10,plain,
% 3.10/1.01      ( ~ v1_relat_1(X0)
% 3.10/1.01      | k9_relat_1(X0,k1_tarski(X1)) = k11_relat_1(X0,X1) ),
% 3.10/1.01      inference(cnf_transformation,[],[f39]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_244,plain,
% 3.10/1.01      ( k9_relat_1(X0,k1_tarski(X1)) = k11_relat_1(X0,X1) | sK7 != X0 ),
% 3.10/1.01      inference(resolution_lifted,[status(thm)],[c_10,c_17]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_245,plain,
% 3.10/1.01      ( k9_relat_1(sK7,k1_tarski(X0)) = k11_relat_1(sK7,X0) ),
% 3.10/1.01      inference(unflattening,[status(thm)],[c_244]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_1250,plain,
% 3.10/1.01      ( sK3(sK7,k1_tarski(X0),X1) = X0
% 3.10/1.01      | r2_hidden(X1,k11_relat_1(sK7,X0)) != iProver_top ),
% 3.10/1.01      inference(light_normalisation,[status(thm)],[c_1247,c_245]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_1901,plain,
% 3.10/1.01      ( sK3(sK7,k1_tarski(sK5),sK6) = sK5
% 3.10/1.01      | r2_hidden(sK5,X0) != iProver_top
% 3.10/1.01      | r2_hidden(sK6,k9_relat_1(sK7,X0)) = iProver_top ),
% 3.10/1.01      inference(superposition,[status(thm)],[c_1725,c_1250]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_1159,plain,
% 3.10/1.01      ( r2_hidden(sK3(sK7,k1_tarski(sK5),sK6),k1_tarski(sK5))
% 3.10/1.01      | ~ r2_hidden(sK6,k9_relat_1(sK7,k1_tarski(sK5))) ),
% 3.10/1.01      inference(instantiation,[status(thm)],[c_362]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_2,plain,
% 3.10/1.01      ( r2_hidden(X0,k1_tarski(X0)) ),
% 3.10/1.01      inference(cnf_transformation,[],[f48]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_1182,plain,
% 3.10/1.01      ( r2_hidden(sK5,k1_tarski(sK5)) ),
% 3.10/1.01      inference(instantiation,[status(thm)],[c_2]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_552,plain,( X0 = X0 ),theory(equality) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_1428,plain,
% 3.10/1.01      ( sK6 = sK6 ),
% 3.10/1.01      inference(instantiation,[status(thm)],[c_552]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_554,plain,
% 3.10/1.01      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.10/1.01      theory(equality) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_1192,plain,
% 3.10/1.01      ( r2_hidden(X0,X1)
% 3.10/1.01      | ~ r2_hidden(sK6,k11_relat_1(sK7,sK5))
% 3.10/1.01      | X1 != k11_relat_1(sK7,sK5)
% 3.10/1.01      | X0 != sK6 ),
% 3.10/1.01      inference(instantiation,[status(thm)],[c_554]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_1427,plain,
% 3.10/1.01      ( r2_hidden(sK6,X0)
% 3.10/1.01      | ~ r2_hidden(sK6,k11_relat_1(sK7,sK5))
% 3.10/1.01      | X0 != k11_relat_1(sK7,sK5)
% 3.10/1.01      | sK6 != sK6 ),
% 3.10/1.01      inference(instantiation,[status(thm)],[c_1192]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_1870,plain,
% 3.10/1.01      ( ~ r2_hidden(sK6,k11_relat_1(sK7,sK5))
% 3.10/1.01      | r2_hidden(sK6,k9_relat_1(sK7,k1_tarski(sK5)))
% 3.10/1.01      | k9_relat_1(sK7,k1_tarski(sK5)) != k11_relat_1(sK7,sK5)
% 3.10/1.01      | sK6 != sK6 ),
% 3.10/1.01      inference(instantiation,[status(thm)],[c_1427]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_1871,plain,
% 3.10/1.01      ( k9_relat_1(sK7,k1_tarski(sK5)) = k11_relat_1(sK7,sK5) ),
% 3.10/1.01      inference(instantiation,[status(thm)],[c_245]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_1900,plain,
% 3.10/1.01      ( r2_hidden(sK5,k1_tarski(X0)) != iProver_top
% 3.10/1.01      | r2_hidden(sK6,k11_relat_1(sK7,X0)) = iProver_top
% 3.10/1.01      | r2_hidden(sK6,k11_relat_1(sK7,sK5)) = iProver_top ),
% 3.10/1.01      inference(superposition,[status(thm)],[c_245,c_1725]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_2086,plain,
% 3.10/1.01      ( r2_hidden(sK5,k1_tarski(sK5)) != iProver_top
% 3.10/1.01      | r2_hidden(sK6,k11_relat_1(sK7,sK5)) = iProver_top
% 3.10/1.01      | iProver_top != iProver_top ),
% 3.10/1.01      inference(equality_factoring,[status(thm)],[c_1900]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_2088,plain,
% 3.10/1.01      ( r2_hidden(sK5,k1_tarski(sK5)) != iProver_top
% 3.10/1.01      | r2_hidden(sK6,k11_relat_1(sK7,sK5)) = iProver_top ),
% 3.10/1.01      inference(equality_resolution_simp,[status(thm)],[c_2086]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_2129,plain,
% 3.10/1.01      ( ~ r2_hidden(sK5,k1_tarski(sK5))
% 3.10/1.01      | r2_hidden(sK6,k11_relat_1(sK7,sK5)) ),
% 3.10/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_2088]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_1224,plain,
% 3.10/1.01      ( ~ r2_hidden(X0,k1_tarski(sK5)) | X0 = sK5 ),
% 3.10/1.01      inference(instantiation,[status(thm)],[c_3]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_2212,plain,
% 3.10/1.01      ( ~ r2_hidden(sK3(sK7,k1_tarski(sK5),X0),k1_tarski(sK5))
% 3.10/1.01      | sK3(sK7,k1_tarski(sK5),X0) = sK5 ),
% 3.10/1.01      inference(instantiation,[status(thm)],[c_1224]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_3157,plain,
% 3.10/1.01      ( ~ r2_hidden(sK3(sK7,k1_tarski(sK5),sK6),k1_tarski(sK5))
% 3.10/1.01      | sK3(sK7,k1_tarski(sK5),sK6) = sK5 ),
% 3.10/1.01      inference(instantiation,[status(thm)],[c_2212]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_8253,plain,
% 3.10/1.01      ( sK3(sK7,k1_tarski(sK5),sK6) = sK5 ),
% 3.10/1.01      inference(global_propositional_subsumption,
% 3.10/1.01                [status(thm)],
% 3.10/1.01                [c_1901,c_1159,c_1182,c_1428,c_1870,c_1871,c_2129,c_3157]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_9,plain,
% 3.10/1.01      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.10/1.01      | r2_hidden(k4_tarski(sK3(X1,X2,X0),X0),X1)
% 3.10/1.01      | ~ v1_relat_1(X1) ),
% 3.10/1.01      inference(cnf_transformation,[],[f52]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_349,plain,
% 3.10/1.01      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.10/1.01      | r2_hidden(k4_tarski(sK3(X1,X2,X0),X0),X1)
% 3.10/1.01      | sK7 != X1 ),
% 3.10/1.01      inference(resolution_lifted,[status(thm)],[c_9,c_17]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_350,plain,
% 3.10/1.01      ( ~ r2_hidden(X0,k9_relat_1(sK7,X1))
% 3.10/1.01      | r2_hidden(k4_tarski(sK3(sK7,X1,X0),X0),sK7) ),
% 3.10/1.01      inference(unflattening,[status(thm)],[c_349]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_917,plain,
% 3.10/1.01      ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 3.10/1.01      | r2_hidden(k4_tarski(sK3(sK7,X1,X0),X0),sK7) = iProver_top ),
% 3.10/1.01      inference(predicate_to_equality,[status(thm)],[c_350]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_8258,plain,
% 3.10/1.01      ( r2_hidden(k4_tarski(sK5,sK6),sK7) = iProver_top
% 3.10/1.01      | r2_hidden(sK6,k9_relat_1(sK7,k1_tarski(sK5))) != iProver_top ),
% 3.10/1.01      inference(superposition,[status(thm)],[c_8253,c_917]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_8265,plain,
% 3.10/1.01      ( r2_hidden(k4_tarski(sK5,sK6),sK7) = iProver_top
% 3.10/1.01      | r2_hidden(sK6,k11_relat_1(sK7,sK5)) != iProver_top ),
% 3.10/1.01      inference(demodulation,[status(thm)],[c_8258,c_245]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_1183,plain,
% 3.10/1.01      ( r2_hidden(sK5,k1_tarski(sK5)) = iProver_top ),
% 3.10/1.01      inference(predicate_to_equality,[status(thm)],[c_1182]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_15,negated_conjecture,
% 3.10/1.01      ( ~ r2_hidden(k4_tarski(sK5,sK6),sK7)
% 3.10/1.01      | ~ r2_hidden(sK6,k11_relat_1(sK7,sK5)) ),
% 3.10/1.01      inference(cnf_transformation,[],[f46]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_20,plain,
% 3.10/1.01      ( r2_hidden(k4_tarski(sK5,sK6),sK7) != iProver_top
% 3.10/1.01      | r2_hidden(sK6,k11_relat_1(sK7,sK5)) != iProver_top ),
% 3.10/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(contradiction,plain,
% 3.10/1.01      ( $false ),
% 3.10/1.01      inference(minisat,[status(thm)],[c_8265,c_2088,c_1183,c_20]) ).
% 3.10/1.01  
% 3.10/1.01  
% 3.10/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.10/1.01  
% 3.10/1.01  ------                               Statistics
% 3.10/1.01  
% 3.10/1.01  ------ General
% 3.10/1.01  
% 3.10/1.01  abstr_ref_over_cycles:                  0
% 3.10/1.01  abstr_ref_under_cycles:                 0
% 3.10/1.01  gc_basic_clause_elim:                   0
% 3.10/1.01  forced_gc_time:                         0
% 3.10/1.01  parsing_time:                           0.01
% 3.10/1.01  unif_index_cands_time:                  0.
% 3.10/1.01  unif_index_add_time:                    0.
% 3.10/1.01  orderings_time:                         0.
% 3.10/1.01  out_proof_time:                         0.006
% 3.10/1.01  total_time:                             0.295
% 3.10/1.01  num_of_symbols:                         46
% 3.10/1.01  num_of_terms:                           11371
% 3.10/1.01  
% 3.10/1.01  ------ Preprocessing
% 3.10/1.01  
% 3.10/1.01  num_of_splits:                          0
% 3.10/1.01  num_of_split_atoms:                     0
% 3.10/1.01  num_of_reused_defs:                     0
% 3.10/1.01  num_eq_ax_congr_red:                    39
% 3.10/1.01  num_of_sem_filtered_clauses:            1
% 3.10/1.01  num_of_subtypes:                        0
% 3.10/1.01  monotx_restored_types:                  0
% 3.10/1.01  sat_num_of_epr_types:                   0
% 3.10/1.01  sat_num_of_non_cyclic_types:            0
% 3.10/1.01  sat_guarded_non_collapsed_types:        0
% 3.10/1.01  num_pure_diseq_elim:                    0
% 3.10/1.01  simp_replaced_by:                       0
% 3.10/1.01  res_preprocessed:                       88
% 3.10/1.01  prep_upred:                             0
% 3.10/1.01  prep_unflattend:                        10
% 3.10/1.01  smt_new_axioms:                         0
% 3.10/1.01  pred_elim_cands:                        1
% 3.10/1.01  pred_elim:                              1
% 3.10/1.01  pred_elim_cl:                           1
% 3.10/1.01  pred_elim_cycles:                       3
% 3.10/1.01  merged_defs:                            8
% 3.10/1.01  merged_defs_ncl:                        0
% 3.10/1.01  bin_hyper_res:                          8
% 3.10/1.01  prep_cycles:                            4
% 3.10/1.01  pred_elim_time:                         0.004
% 3.10/1.01  splitting_time:                         0.
% 3.10/1.01  sem_filter_time:                        0.
% 3.10/1.01  monotx_time:                            0.001
% 3.10/1.01  subtype_inf_time:                       0.
% 3.10/1.01  
% 3.10/1.01  ------ Problem properties
% 3.10/1.01  
% 3.10/1.01  clauses:                                16
% 3.10/1.01  conjectures:                            2
% 3.10/1.01  epr:                                    0
% 3.10/1.01  horn:                                   12
% 3.10/1.01  ground:                                 2
% 3.10/1.01  unary:                                  2
% 3.10/1.01  binary:                                 8
% 3.10/1.01  lits:                                   37
% 3.10/1.01  lits_eq:                                9
% 3.10/1.01  fd_pure:                                0
% 3.10/1.01  fd_pseudo:                              0
% 3.10/1.01  fd_cond:                                0
% 3.10/1.01  fd_pseudo_cond:                         5
% 3.10/1.01  ac_symbols:                             0
% 3.10/1.01  
% 3.10/1.01  ------ Propositional Solver
% 3.10/1.01  
% 3.10/1.01  prop_solver_calls:                      28
% 3.10/1.01  prop_fast_solver_calls:                 731
% 3.10/1.01  smt_solver_calls:                       0
% 3.10/1.01  smt_fast_solver_calls:                  0
% 3.10/1.01  prop_num_of_clauses:                    3329
% 3.10/1.01  prop_preprocess_simplified:             6686
% 3.10/1.01  prop_fo_subsumed:                       7
% 3.10/1.01  prop_solver_time:                       0.
% 3.10/1.01  smt_solver_time:                        0.
% 3.10/1.01  smt_fast_solver_time:                   0.
% 3.10/1.01  prop_fast_solver_time:                  0.
% 3.10/1.01  prop_unsat_core_time:                   0.
% 3.10/1.01  
% 3.10/1.01  ------ QBF
% 3.10/1.01  
% 3.10/1.01  qbf_q_res:                              0
% 3.10/1.01  qbf_num_tautologies:                    0
% 3.10/1.01  qbf_prep_cycles:                        0
% 3.10/1.01  
% 3.10/1.01  ------ BMC1
% 3.10/1.01  
% 3.10/1.01  bmc1_current_bound:                     -1
% 3.10/1.01  bmc1_last_solved_bound:                 -1
% 3.10/1.01  bmc1_unsat_core_size:                   -1
% 3.10/1.01  bmc1_unsat_core_parents_size:           -1
% 3.10/1.01  bmc1_merge_next_fun:                    0
% 3.10/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.10/1.01  
% 3.10/1.01  ------ Instantiation
% 3.10/1.01  
% 3.10/1.01  inst_num_of_clauses:                    783
% 3.10/1.01  inst_num_in_passive:                    134
% 3.10/1.01  inst_num_in_active:                     368
% 3.10/1.01  inst_num_in_unprocessed:                281
% 3.10/1.01  inst_num_of_loops:                      420
% 3.10/1.01  inst_num_of_learning_restarts:          0
% 3.10/1.01  inst_num_moves_active_passive:          49
% 3.10/1.01  inst_lit_activity:                      0
% 3.10/1.01  inst_lit_activity_moves:                0
% 3.10/1.01  inst_num_tautologies:                   0
% 3.10/1.01  inst_num_prop_implied:                  0
% 3.10/1.01  inst_num_existing_simplified:           0
% 3.10/1.01  inst_num_eq_res_simplified:             0
% 3.10/1.01  inst_num_child_elim:                    0
% 3.10/1.01  inst_num_of_dismatching_blockings:      476
% 3.10/1.01  inst_num_of_non_proper_insts:           648
% 3.10/1.01  inst_num_of_duplicates:                 0
% 3.10/1.01  inst_inst_num_from_inst_to_res:         0
% 3.10/1.01  inst_dismatching_checking_time:         0.
% 3.10/1.01  
% 3.10/1.01  ------ Resolution
% 3.10/1.01  
% 3.10/1.01  res_num_of_clauses:                     0
% 3.10/1.01  res_num_in_passive:                     0
% 3.10/1.01  res_num_in_active:                      0
% 3.10/1.01  res_num_of_loops:                       92
% 3.10/1.01  res_forward_subset_subsumed:            36
% 3.10/1.01  res_backward_subset_subsumed:           0
% 3.10/1.01  res_forward_subsumed:                   0
% 3.10/1.01  res_backward_subsumed:                  0
% 3.10/1.01  res_forward_subsumption_resolution:     0
% 3.10/1.01  res_backward_subsumption_resolution:    0
% 3.10/1.01  res_clause_to_clause_subsumption:       619
% 3.10/1.01  res_orphan_elimination:                 0
% 3.10/1.01  res_tautology_del:                      44
% 3.10/1.01  res_num_eq_res_simplified:              0
% 3.10/1.01  res_num_sel_changes:                    0
% 3.10/1.01  res_moves_from_active_to_pass:          0
% 3.10/1.01  
% 3.10/1.01  ------ Superposition
% 3.10/1.01  
% 3.10/1.01  sup_time_total:                         0.
% 3.10/1.01  sup_time_generating:                    0.
% 3.10/1.01  sup_time_sim_full:                      0.
% 3.10/1.01  sup_time_sim_immed:                     0.
% 3.10/1.01  
% 3.10/1.01  sup_num_of_clauses:                     247
% 3.10/1.01  sup_num_in_active:                      82
% 3.10/1.01  sup_num_in_passive:                     165
% 3.10/1.01  sup_num_of_loops:                       83
% 3.10/1.01  sup_fw_superposition:                   223
% 3.10/1.01  sup_bw_superposition:                   98
% 3.10/1.01  sup_immediate_simplified:               79
% 3.10/1.01  sup_given_eliminated:                   0
% 3.10/1.01  comparisons_done:                       0
% 3.10/1.01  comparisons_avoided:                    68
% 3.10/1.01  
% 3.10/1.01  ------ Simplifications
% 3.10/1.01  
% 3.10/1.01  
% 3.10/1.01  sim_fw_subset_subsumed:                 7
% 3.10/1.01  sim_bw_subset_subsumed:                 5
% 3.10/1.01  sim_fw_subsumed:                        17
% 3.10/1.01  sim_bw_subsumed:                        1
% 3.10/1.01  sim_fw_subsumption_res:                 4
% 3.10/1.01  sim_bw_subsumption_res:                 0
% 3.10/1.01  sim_tautology_del:                      11
% 3.10/1.01  sim_eq_tautology_del:                   1
% 3.10/1.01  sim_eq_res_simp:                        1
% 3.10/1.01  sim_fw_demodulated:                     38
% 3.10/1.01  sim_bw_demodulated:                     0
% 3.10/1.01  sim_light_normalised:                   25
% 3.10/1.01  sim_joinable_taut:                      0
% 3.10/1.01  sim_joinable_simp:                      0
% 3.10/1.01  sim_ac_normalised:                      0
% 3.10/1.01  sim_smt_subsumption:                    0
% 3.10/1.01  
%------------------------------------------------------------------------------
