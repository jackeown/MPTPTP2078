%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:46:49 EST 2020

% Result     : Theorem 38.46s
% Output     : CNFRefutation 38.46s
% Verified   : 
% Statistics : Number of formulae       :  171 ( 504 expanded)
%              Number of clauses        :  116 ( 235 expanded)
%              Number of leaves         :   22 ( 117 expanded)
%              Depth                    :   24
%              Number of atoms          :  502 (1363 expanded)
%              Number of equality atoms :  268 ( 571 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) != k9_relat_1(X1,k2_relat_1(X0))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) != k9_relat_1(X1,k2_relat_1(X0))
          & v1_relat_1(X1) )
     => ( k2_relat_1(k5_relat_1(X0,sK7)) != k9_relat_1(sK7,k2_relat_1(X0))
        & v1_relat_1(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_relat_1(k5_relat_1(X0,X1)) != k9_relat_1(X1,k2_relat_1(X0))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k2_relat_1(k5_relat_1(sK6,X1)) != k9_relat_1(X1,k2_relat_1(sK6))
          & v1_relat_1(X1) )
      & v1_relat_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( k2_relat_1(k5_relat_1(sK6,sK7)) != k9_relat_1(sK7,k2_relat_1(sK6))
    & v1_relat_1(sK7)
    & v1_relat_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f23,f38,f37])).

fof(f59,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f39])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f24])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
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

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

fof(f35,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK4(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
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

fof(f36,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f32,f35,f34,f33])).

fof(f48,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f66,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f48])).

fof(f4,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f57,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( v1_relat_1(X2)
         => ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X0)
                    | ~ r2_hidden(X5,X1) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                      & r2_hidden(X5,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0)
            & r2_hidden(sK1(X0,X1,X2),X1) )
          | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0)
                  | ~ r2_hidden(sK1(X0,X1,X2),X1)
                  | ~ r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2) )
                & ( ( r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0)
                    & r2_hidden(sK1(X0,X1,X2),X1) )
                  | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X0)
                    | ~ r2_hidden(X5,X1) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                      & r2_hidden(X5,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f28,f29])).

fof(f42,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f64,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
      | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f60,plain,(
    v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f39])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f61,plain,(
    k2_relat_1(k5_relat_1(sK6,sK7)) != k9_relat_1(sK7,k2_relat_1(sK6)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_293,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1199,plain,
    ( X0 != X1
    | k5_relat_1(sK6,sK7) != X1
    | k5_relat_1(sK6,sK7) = X0 ),
    inference(instantiation,[status(thm)],[c_293])).

cnf(c_1570,plain,
    ( X0 != k5_relat_1(sK6,sK7)
    | k5_relat_1(sK6,sK7) = X0
    | k5_relat_1(sK6,sK7) != k5_relat_1(sK6,sK7) ),
    inference(instantiation,[status(thm)],[c_1199])).

cnf(c_20429,plain,
    ( k5_relat_1(X0,k7_relat_1(X1,X2)) != k5_relat_1(sK6,sK7)
    | k5_relat_1(sK6,sK7) = k5_relat_1(X0,k7_relat_1(X1,X2))
    | k5_relat_1(sK6,sK7) != k5_relat_1(sK6,sK7) ),
    inference(instantiation,[status(thm)],[c_1570])).

cnf(c_91864,plain,
    ( k5_relat_1(X0,k7_relat_1(sK7,X1)) != k5_relat_1(sK6,sK7)
    | k5_relat_1(sK6,sK7) = k5_relat_1(X0,k7_relat_1(sK7,X1))
    | k5_relat_1(sK6,sK7) != k5_relat_1(sK6,sK7) ),
    inference(instantiation,[status(thm)],[c_20429])).

cnf(c_122686,plain,
    ( k5_relat_1(X0,k7_relat_1(sK7,k2_relat_1(sK6))) != k5_relat_1(sK6,sK7)
    | k5_relat_1(sK6,sK7) = k5_relat_1(X0,k7_relat_1(sK7,k2_relat_1(sK6)))
    | k5_relat_1(sK6,sK7) != k5_relat_1(sK6,sK7) ),
    inference(instantiation,[status(thm)],[c_91864])).

cnf(c_122687,plain,
    ( k5_relat_1(sK6,k7_relat_1(sK7,k2_relat_1(sK6))) != k5_relat_1(sK6,sK7)
    | k5_relat_1(sK6,sK7) = k5_relat_1(sK6,k7_relat_1(sK7,k2_relat_1(sK6)))
    | k5_relat_1(sK6,sK7) != k5_relat_1(sK6,sK7) ),
    inference(instantiation,[status(thm)],[c_122686])).

cnf(c_1193,plain,
    ( k9_relat_1(sK7,k2_relat_1(sK6)) != X0
    | k9_relat_1(sK7,k2_relat_1(sK6)) = k2_relat_1(k5_relat_1(sK6,sK7))
    | k2_relat_1(k5_relat_1(sK6,sK7)) != X0 ),
    inference(instantiation,[status(thm)],[c_293])).

cnf(c_12140,plain,
    ( k9_relat_1(sK7,k2_relat_1(sK6)) != k2_relat_1(X0)
    | k9_relat_1(sK7,k2_relat_1(sK6)) = k2_relat_1(k5_relat_1(sK6,sK7))
    | k2_relat_1(k5_relat_1(sK6,sK7)) != k2_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_1193])).

cnf(c_121470,plain,
    ( k9_relat_1(sK7,k2_relat_1(sK6)) != k2_relat_1(k5_relat_1(X0,k5_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)),k6_relat_1(k2_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)))))))
    | k9_relat_1(sK7,k2_relat_1(sK6)) = k2_relat_1(k5_relat_1(sK6,sK7))
    | k2_relat_1(k5_relat_1(sK6,sK7)) != k2_relat_1(k5_relat_1(X0,k5_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)),k6_relat_1(k2_relat_1(k7_relat_1(sK7,k2_relat_1(sK6))))))) ),
    inference(instantiation,[status(thm)],[c_12140])).

cnf(c_121471,plain,
    ( k9_relat_1(sK7,k2_relat_1(sK6)) != k2_relat_1(k5_relat_1(sK6,k5_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)),k6_relat_1(k2_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)))))))
    | k9_relat_1(sK7,k2_relat_1(sK6)) = k2_relat_1(k5_relat_1(sK6,sK7))
    | k2_relat_1(k5_relat_1(sK6,sK7)) != k2_relat_1(k5_relat_1(sK6,k5_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)),k6_relat_1(k2_relat_1(k7_relat_1(sK7,k2_relat_1(sK6))))))) ),
    inference(instantiation,[status(thm)],[c_121470])).

cnf(c_299,plain,
    ( X0 != X1
    | k2_relat_1(X0) = k2_relat_1(X1) ),
    theory(equality)).

cnf(c_1027,plain,
    ( k5_relat_1(sK6,sK7) != X0
    | k2_relat_1(k5_relat_1(sK6,sK7)) = k2_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_299])).

cnf(c_1200,plain,
    ( k5_relat_1(sK6,sK7) != k5_relat_1(X0,X1)
    | k2_relat_1(k5_relat_1(sK6,sK7)) = k2_relat_1(k5_relat_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_1027])).

cnf(c_110865,plain,
    ( k5_relat_1(sK6,sK7) != k5_relat_1(X0,k5_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)),k6_relat_1(k2_relat_1(k7_relat_1(sK7,k2_relat_1(sK6))))))
    | k2_relat_1(k5_relat_1(sK6,sK7)) = k2_relat_1(k5_relat_1(X0,k5_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)),k6_relat_1(k2_relat_1(k7_relat_1(sK7,k2_relat_1(sK6))))))) ),
    inference(instantiation,[status(thm)],[c_1200])).

cnf(c_110866,plain,
    ( k5_relat_1(sK6,sK7) != k5_relat_1(sK6,k5_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)),k6_relat_1(k2_relat_1(k7_relat_1(sK7,k2_relat_1(sK6))))))
    | k2_relat_1(k5_relat_1(sK6,sK7)) = k2_relat_1(k5_relat_1(sK6,k5_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)),k6_relat_1(k2_relat_1(k7_relat_1(sK7,k2_relat_1(sK6))))))) ),
    inference(instantiation,[status(thm)],[c_110865])).

cnf(c_21,negated_conjecture,
    ( v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_685,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_704,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,sK5(X1,X0)),X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_694,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK5(X1,X0)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_12,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_693,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_17,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_688,plain,
    ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_968,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(k2_relat_1(k6_relat_1(X0)))) = k6_relat_1(X0) ),
    inference(superposition,[status(thm)],[c_693,c_688])).

cnf(c_18,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_687,plain,
    ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1223,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[status(thm)],[c_693,c_687])).

cnf(c_1823,plain,
    ( k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(X0))),X0) = k6_relat_1(X0) ),
    inference(superposition,[status(thm)],[c_968,c_1223])).

cnf(c_7,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k7_relat_1(X3,X1))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(k7_relat_1(X3,X1)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_698,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),k7_relat_1(X3,X1)) != iProver_top
    | v1_relat_1(X3) != iProver_top
    | v1_relat_1(k7_relat_1(X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_692,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_778,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),k7_relat_1(X3,X1)) != iProver_top
    | v1_relat_1(X3) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_698,c_692])).

cnf(c_3842,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),k6_relat_1(X1)) != iProver_top
    | v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(X1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1823,c_778])).

cnf(c_35909,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),k6_relat_1(X1)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3842,c_693])).

cnf(c_35919,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_relat_1(k6_relat_1(X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_694,c_35909])).

cnf(c_36209,plain,
    ( r2_hidden(sK0(k1_relat_1(k6_relat_1(X0)),X1),X0) = iProver_top
    | r1_tarski(k1_relat_1(k6_relat_1(X0)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_704,c_35919])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_705,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_36423,plain,
    ( r1_tarski(k1_relat_1(k6_relat_1(X0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_36209,c_705])).

cnf(c_15,plain,
    ( ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_690,plain,
    ( k2_relat_1(k5_relat_1(X0,X1)) = k2_relat_1(X1)
    | r1_tarski(k1_relat_1(X1),k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_36674,plain,
    ( k2_relat_1(k5_relat_1(X0,k6_relat_1(k2_relat_1(X0)))) = k2_relat_1(k6_relat_1(k2_relat_1(X0)))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k6_relat_1(k2_relat_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_36423,c_690])).

cnf(c_51748,plain,
    ( k2_relat_1(k5_relat_1(X0,k6_relat_1(k2_relat_1(X0)))) = k2_relat_1(k6_relat_1(k2_relat_1(X0)))
    | v1_relat_1(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_36674,c_693])).

cnf(c_51755,plain,
    ( k2_relat_1(k5_relat_1(sK6,k6_relat_1(k2_relat_1(sK6)))) = k2_relat_1(k6_relat_1(k2_relat_1(sK6))) ),
    inference(superposition,[status(thm)],[c_685,c_51748])).

cnf(c_970,plain,
    ( k5_relat_1(sK6,k6_relat_1(k2_relat_1(sK6))) = sK6 ),
    inference(superposition,[status(thm)],[c_685,c_688])).

cnf(c_51757,plain,
    ( k2_relat_1(k6_relat_1(k2_relat_1(sK6))) = k2_relat_1(sK6) ),
    inference(light_normalisation,[status(thm)],[c_51755,c_970])).

cnf(c_52468,plain,
    ( k7_relat_1(k6_relat_1(k2_relat_1(sK6)),k2_relat_1(sK6)) = k6_relat_1(k2_relat_1(sK6)) ),
    inference(superposition,[status(thm)],[c_51757,c_1823])).

cnf(c_20,negated_conjecture,
    ( v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_686,plain,
    ( v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_16,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k5_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(X1,k5_relat_1(X2,X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_689,plain,
    ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1942,plain,
    ( k5_relat_1(k7_relat_1(X0,X1),k5_relat_1(X2,X3)) = k5_relat_1(k5_relat_1(k7_relat_1(X0,X1),X2),X3)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X3) != iProver_top ),
    inference(superposition,[status(thm)],[c_692,c_689])).

cnf(c_8873,plain,
    ( k5_relat_1(k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),X3) = k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k5_relat_1(X2,X3))
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X3) != iProver_top ),
    inference(superposition,[status(thm)],[c_693,c_1942])).

cnf(c_90167,plain,
    ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k5_relat_1(k6_relat_1(X2),X3)) = k5_relat_1(k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2)),X3)
    | v1_relat_1(X3) != iProver_top ),
    inference(superposition,[status(thm)],[c_693,c_8873])).

cnf(c_96968,plain,
    ( k5_relat_1(k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2)),sK7) = k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k5_relat_1(k6_relat_1(X2),sK7)) ),
    inference(superposition,[status(thm)],[c_686,c_90167])).

cnf(c_1224,plain,
    ( k5_relat_1(k6_relat_1(X0),sK7) = k7_relat_1(sK7,X0) ),
    inference(superposition,[status(thm)],[c_686,c_687])).

cnf(c_96974,plain,
    ( k5_relat_1(k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2)),sK7) = k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k7_relat_1(sK7,X2)) ),
    inference(demodulation,[status(thm)],[c_96968,c_1224])).

cnf(c_104943,plain,
    ( k5_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(X0))),X0),k7_relat_1(sK7,X1)) = k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),sK7) ),
    inference(superposition,[status(thm)],[c_1823,c_96974])).

cnf(c_1222,plain,
    ( k5_relat_1(k6_relat_1(X0),k7_relat_1(X1,X2)) = k7_relat_1(k7_relat_1(X1,X2),X0)
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_692,c_687])).

cnf(c_4056,plain,
    ( k5_relat_1(k6_relat_1(X0),k7_relat_1(sK7,X1)) = k7_relat_1(k7_relat_1(sK7,X1),X0) ),
    inference(superposition,[status(thm)],[c_686,c_1222])).

cnf(c_104955,plain,
    ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),sK7) = k7_relat_1(k7_relat_1(sK7,X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_104943,c_1223,c_1823,c_4056])).

cnf(c_105998,plain,
    ( k7_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)),k2_relat_1(sK6)) = k5_relat_1(k6_relat_1(k2_relat_1(sK6)),sK7) ),
    inference(superposition,[status(thm)],[c_52468,c_104955])).

cnf(c_106004,plain,
    ( k7_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)),k2_relat_1(sK6)) = k7_relat_1(sK7,k2_relat_1(sK6)) ),
    inference(demodulation,[status(thm)],[c_105998,c_1224])).

cnf(c_3841,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_694,c_778])).

cnf(c_9385,plain,
    ( r2_hidden(sK0(k1_relat_1(k7_relat_1(X0,X1)),X2),X1) = iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_704,c_3841])).

cnf(c_46402,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9385,c_705])).

cnf(c_107621,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK7,k2_relat_1(sK6))),k2_relat_1(sK6)) = iProver_top
    | v1_relat_1(k7_relat_1(sK7,k2_relat_1(sK6))) != iProver_top ),
    inference(superposition,[status(thm)],[c_106004,c_46402])).

cnf(c_1196,plain,
    ( k9_relat_1(sK7,k2_relat_1(sK6)) != X0
    | k9_relat_1(sK7,k2_relat_1(sK6)) = k2_relat_1(X1)
    | k2_relat_1(X1) != X0 ),
    inference(instantiation,[status(thm)],[c_293])).

cnf(c_12139,plain,
    ( k9_relat_1(sK7,k2_relat_1(sK6)) != k2_relat_1(X0)
    | k9_relat_1(sK7,k2_relat_1(sK6)) = k2_relat_1(X1)
    | k2_relat_1(X1) != k2_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_1196])).

cnf(c_34495,plain,
    ( k9_relat_1(sK7,k2_relat_1(sK6)) = k2_relat_1(X0)
    | k9_relat_1(sK7,k2_relat_1(sK6)) != k2_relat_1(k5_relat_1(X1,k7_relat_1(sK7,k2_relat_1(X2))))
    | k2_relat_1(X0) != k2_relat_1(k5_relat_1(X1,k7_relat_1(sK7,k2_relat_1(X2)))) ),
    inference(instantiation,[status(thm)],[c_12139])).

cnf(c_68297,plain,
    ( k9_relat_1(sK7,k2_relat_1(sK6)) = k2_relat_1(k5_relat_1(X0,k5_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)),k6_relat_1(k2_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)))))))
    | k9_relat_1(sK7,k2_relat_1(sK6)) != k2_relat_1(k5_relat_1(X1,k7_relat_1(sK7,k2_relat_1(sK6))))
    | k2_relat_1(k5_relat_1(X0,k5_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)),k6_relat_1(k2_relat_1(k7_relat_1(sK7,k2_relat_1(sK6))))))) != k2_relat_1(k5_relat_1(X1,k7_relat_1(sK7,k2_relat_1(sK6)))) ),
    inference(instantiation,[status(thm)],[c_34495])).

cnf(c_68298,plain,
    ( k9_relat_1(sK7,k2_relat_1(sK6)) = k2_relat_1(k5_relat_1(sK6,k5_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)),k6_relat_1(k2_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)))))))
    | k9_relat_1(sK7,k2_relat_1(sK6)) != k2_relat_1(k5_relat_1(sK6,k7_relat_1(sK7,k2_relat_1(sK6))))
    | k2_relat_1(k5_relat_1(sK6,k5_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)),k6_relat_1(k2_relat_1(k7_relat_1(sK7,k2_relat_1(sK6))))))) != k2_relat_1(k5_relat_1(sK6,k7_relat_1(sK7,k2_relat_1(sK6)))) ),
    inference(instantiation,[status(thm)],[c_68297])).

cnf(c_5775,plain,
    ( X0 != k5_relat_1(X1,k7_relat_1(X2,X3))
    | k5_relat_1(sK6,sK7) = X0
    | k5_relat_1(sK6,sK7) != k5_relat_1(X1,k7_relat_1(X2,X3)) ),
    inference(instantiation,[status(thm)],[c_1199])).

cnf(c_14845,plain,
    ( k5_relat_1(X0,X1) != k5_relat_1(X2,k7_relat_1(X3,X4))
    | k5_relat_1(sK6,sK7) = k5_relat_1(X0,X1)
    | k5_relat_1(sK6,sK7) != k5_relat_1(X2,k7_relat_1(X3,X4)) ),
    inference(instantiation,[status(thm)],[c_5775])).

cnf(c_37310,plain,
    ( k5_relat_1(X0,k5_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)),k6_relat_1(k2_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)))))) != k5_relat_1(X1,k7_relat_1(sK7,k2_relat_1(sK6)))
    | k5_relat_1(sK6,sK7) = k5_relat_1(X0,k5_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)),k6_relat_1(k2_relat_1(k7_relat_1(sK7,k2_relat_1(sK6))))))
    | k5_relat_1(sK6,sK7) != k5_relat_1(X1,k7_relat_1(sK7,k2_relat_1(sK6))) ),
    inference(instantiation,[status(thm)],[c_14845])).

cnf(c_37311,plain,
    ( k5_relat_1(sK6,k5_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)),k6_relat_1(k2_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)))))) != k5_relat_1(sK6,k7_relat_1(sK7,k2_relat_1(sK6)))
    | k5_relat_1(sK6,sK7) = k5_relat_1(sK6,k5_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)),k6_relat_1(k2_relat_1(k7_relat_1(sK7,k2_relat_1(sK6))))))
    | k5_relat_1(sK6,sK7) != k5_relat_1(sK6,k7_relat_1(sK7,k2_relat_1(sK6))) ),
    inference(instantiation,[status(thm)],[c_37310])).

cnf(c_15845,plain,
    ( X0 != k5_relat_1(X1,k7_relat_1(X2,X3))
    | k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,k7_relat_1(X2,X3))) ),
    inference(instantiation,[status(thm)],[c_299])).

cnf(c_37305,plain,
    ( k5_relat_1(X0,k5_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)),k6_relat_1(k2_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)))))) != k5_relat_1(X1,k7_relat_1(sK7,k2_relat_1(sK6)))
    | k2_relat_1(k5_relat_1(X0,k5_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)),k6_relat_1(k2_relat_1(k7_relat_1(sK7,k2_relat_1(sK6))))))) = k2_relat_1(k5_relat_1(X1,k7_relat_1(sK7,k2_relat_1(sK6)))) ),
    inference(instantiation,[status(thm)],[c_15845])).

cnf(c_37309,plain,
    ( k5_relat_1(sK6,k5_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)),k6_relat_1(k2_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)))))) != k5_relat_1(sK6,k7_relat_1(sK7,k2_relat_1(sK6)))
    | k2_relat_1(k5_relat_1(sK6,k5_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)),k6_relat_1(k2_relat_1(k7_relat_1(sK7,k2_relat_1(sK6))))))) = k2_relat_1(k5_relat_1(sK6,k7_relat_1(sK7,k2_relat_1(sK6)))) ),
    inference(instantiation,[status(thm)],[c_37305])).

cnf(c_301,plain,
    ( X0 != X1
    | X2 != X3
    | k5_relat_1(X0,X2) = k5_relat_1(X1,X3) ),
    theory(equality)).

cnf(c_14846,plain,
    ( X0 != X1
    | X2 != k7_relat_1(X3,X4)
    | k5_relat_1(X0,X2) = k5_relat_1(X1,k7_relat_1(X3,X4)) ),
    inference(instantiation,[status(thm)],[c_301])).

cnf(c_17414,plain,
    ( X0 != X1
    | k5_relat_1(X0,k5_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)),k6_relat_1(k2_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)))))) = k5_relat_1(X1,k7_relat_1(sK7,k2_relat_1(sK6)))
    | k5_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)),k6_relat_1(k2_relat_1(k7_relat_1(sK7,k2_relat_1(sK6))))) != k7_relat_1(sK7,k2_relat_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_14846])).

cnf(c_17415,plain,
    ( k5_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)),k6_relat_1(k2_relat_1(k7_relat_1(sK7,k2_relat_1(sK6))))) != k7_relat_1(sK7,k2_relat_1(sK6))
    | k5_relat_1(sK6,k5_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)),k6_relat_1(k2_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)))))) = k5_relat_1(sK6,k7_relat_1(sK7,k2_relat_1(sK6)))
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_17414])).

cnf(c_7742,plain,
    ( v1_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)))
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_7743,plain,
    ( v1_relat_1(k7_relat_1(sK7,k2_relat_1(sK6))) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7742])).

cnf(c_2695,plain,
    ( k9_relat_1(sK7,k2_relat_1(sK6)) = k2_relat_1(X0)
    | k9_relat_1(sK7,k2_relat_1(sK6)) != k2_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)))
    | k2_relat_1(X0) != k2_relat_1(k7_relat_1(sK7,k2_relat_1(sK6))) ),
    inference(instantiation,[status(thm)],[c_1196])).

cnf(c_7265,plain,
    ( k9_relat_1(sK7,k2_relat_1(sK6)) = k2_relat_1(k5_relat_1(X0,k7_relat_1(sK7,k2_relat_1(sK6))))
    | k9_relat_1(sK7,k2_relat_1(sK6)) != k2_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)))
    | k2_relat_1(k5_relat_1(X0,k7_relat_1(sK7,k2_relat_1(sK6)))) != k2_relat_1(k7_relat_1(sK7,k2_relat_1(sK6))) ),
    inference(instantiation,[status(thm)],[c_2695])).

cnf(c_7270,plain,
    ( k9_relat_1(sK7,k2_relat_1(sK6)) = k2_relat_1(k5_relat_1(sK6,k7_relat_1(sK7,k2_relat_1(sK6))))
    | k9_relat_1(sK7,k2_relat_1(sK6)) != k2_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)))
    | k2_relat_1(k5_relat_1(sK6,k7_relat_1(sK7,k2_relat_1(sK6)))) != k2_relat_1(k7_relat_1(sK7,k2_relat_1(sK6))) ),
    inference(instantiation,[status(thm)],[c_7265])).

cnf(c_7263,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK7,k2_relat_1(sK6))),k2_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)))
    | k2_relat_1(k5_relat_1(X0,k7_relat_1(sK7,k2_relat_1(sK6)))) = k2_relat_1(k7_relat_1(sK7,k2_relat_1(sK6))) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_7266,plain,
    ( k2_relat_1(k5_relat_1(X0,k7_relat_1(sK7,k2_relat_1(sK6)))) = k2_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)))
    | r1_tarski(k1_relat_1(k7_relat_1(sK7,k2_relat_1(sK6))),k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK7,k2_relat_1(sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7263])).

cnf(c_7268,plain,
    ( k2_relat_1(k5_relat_1(sK6,k7_relat_1(sK7,k2_relat_1(sK6)))) = k2_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)))
    | r1_tarski(k1_relat_1(k7_relat_1(sK7,k2_relat_1(sK6))),k2_relat_1(sK6)) != iProver_top
    | v1_relat_1(k7_relat_1(sK7,k2_relat_1(sK6))) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7266])).

cnf(c_5948,plain,
    ( ~ v1_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)))
    | k5_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)),k6_relat_1(k2_relat_1(k7_relat_1(sK7,k2_relat_1(sK6))))) = k7_relat_1(sK7,k2_relat_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1945,plain,
    ( k5_relat_1(sK6,k5_relat_1(X0,X1)) = k5_relat_1(k5_relat_1(sK6,X0),X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_685,c_689])).

cnf(c_2837,plain,
    ( k5_relat_1(k5_relat_1(sK6,k6_relat_1(X0)),X1) = k5_relat_1(sK6,k5_relat_1(k6_relat_1(X0),X1))
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_693,c_1945])).

cnf(c_4723,plain,
    ( k5_relat_1(sK6,k5_relat_1(k6_relat_1(X0),sK7)) = k5_relat_1(k5_relat_1(sK6,k6_relat_1(X0)),sK7) ),
    inference(superposition,[status(thm)],[c_686,c_2837])).

cnf(c_4729,plain,
    ( k5_relat_1(k5_relat_1(sK6,k6_relat_1(X0)),sK7) = k5_relat_1(sK6,k7_relat_1(sK7,X0)) ),
    inference(light_normalisation,[status(thm)],[c_4723,c_1224])).

cnf(c_5669,plain,
    ( k5_relat_1(sK6,k7_relat_1(sK7,k2_relat_1(sK6))) = k5_relat_1(sK6,sK7) ),
    inference(superposition,[status(thm)],[c_970,c_4729])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1802,plain,
    ( ~ v1_relat_1(sK7)
    | k2_relat_1(k7_relat_1(sK7,k2_relat_1(sK6))) = k9_relat_1(sK7,k2_relat_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1564,plain,
    ( k9_relat_1(sK7,k2_relat_1(sK6)) != k9_relat_1(sK7,k2_relat_1(sK6))
    | k9_relat_1(sK7,k2_relat_1(sK6)) = k2_relat_1(X0)
    | k2_relat_1(X0) != k9_relat_1(sK7,k2_relat_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_1196])).

cnf(c_1801,plain,
    ( k9_relat_1(sK7,k2_relat_1(sK6)) != k9_relat_1(sK7,k2_relat_1(sK6))
    | k9_relat_1(sK7,k2_relat_1(sK6)) = k2_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)))
    | k2_relat_1(k7_relat_1(sK7,k2_relat_1(sK6))) != k9_relat_1(sK7,k2_relat_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_1564])).

cnf(c_292,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1571,plain,
    ( k5_relat_1(sK6,sK7) = k5_relat_1(sK6,sK7) ),
    inference(instantiation,[status(thm)],[c_292])).

cnf(c_1565,plain,
    ( k9_relat_1(sK7,k2_relat_1(sK6)) = k9_relat_1(sK7,k2_relat_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_292])).

cnf(c_1024,plain,
    ( k2_relat_1(k5_relat_1(sK6,sK7)) = k2_relat_1(k5_relat_1(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_292])).

cnf(c_904,plain,
    ( k9_relat_1(sK7,k2_relat_1(sK6)) != X0
    | k2_relat_1(k5_relat_1(sK6,sK7)) != X0
    | k2_relat_1(k5_relat_1(sK6,sK7)) = k9_relat_1(sK7,k2_relat_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_293])).

cnf(c_1023,plain,
    ( k9_relat_1(sK7,k2_relat_1(sK6)) != k2_relat_1(k5_relat_1(sK6,sK7))
    | k2_relat_1(k5_relat_1(sK6,sK7)) = k9_relat_1(sK7,k2_relat_1(sK6))
    | k2_relat_1(k5_relat_1(sK6,sK7)) != k2_relat_1(k5_relat_1(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_904])).

cnf(c_311,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_292])).

cnf(c_19,negated_conjecture,
    ( k2_relat_1(k5_relat_1(sK6,sK7)) != k9_relat_1(sK7,k2_relat_1(sK6)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_23,plain,
    ( v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_22,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_122687,c_121471,c_110866,c_107621,c_68298,c_37311,c_37309,c_17415,c_7743,c_7742,c_7270,c_7268,c_5948,c_5669,c_1802,c_1801,c_1571,c_1565,c_1024,c_1023,c_311,c_19,c_23,c_20,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:12:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 38.46/5.53  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 38.46/5.53  
% 38.46/5.53  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 38.46/5.53  
% 38.46/5.53  ------  iProver source info
% 38.46/5.53  
% 38.46/5.53  git: date: 2020-06-30 10:37:57 +0100
% 38.46/5.53  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 38.46/5.53  git: non_committed_changes: false
% 38.46/5.53  git: last_make_outside_of_git: false
% 38.46/5.53  
% 38.46/5.53  ------ 
% 38.46/5.53  ------ Parsing...
% 38.46/5.53  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 38.46/5.53  
% 38.46/5.53  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 38.46/5.53  
% 38.46/5.53  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 38.46/5.53  
% 38.46/5.53  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 38.46/5.53  ------ Proving...
% 38.46/5.53  ------ Problem Properties 
% 38.46/5.53  
% 38.46/5.53  
% 38.46/5.53  clauses                                 22
% 38.46/5.53  conjectures                             3
% 38.46/5.53  EPR                                     2
% 38.46/5.53  Horn                                    18
% 38.46/5.53  unary                                   4
% 38.46/5.53  binary                                  8
% 38.46/5.53  lits                                    63
% 38.46/5.53  lits eq                                 11
% 38.46/5.53  fd_pure                                 0
% 38.46/5.53  fd_pseudo                               0
% 38.46/5.53  fd_cond                                 0
% 38.46/5.53  fd_pseudo_cond                          5
% 38.46/5.53  AC symbols                              0
% 38.46/5.53  
% 38.46/5.53  ------ Input Options Time Limit: Unbounded
% 38.46/5.53  
% 38.46/5.53  
% 38.46/5.53  ------ 
% 38.46/5.53  Current options:
% 38.46/5.53  ------ 
% 38.46/5.53  
% 38.46/5.53  
% 38.46/5.53  
% 38.46/5.53  
% 38.46/5.53  ------ Proving...
% 38.46/5.53  
% 38.46/5.53  
% 38.46/5.53  % SZS status Theorem for theBenchmark.p
% 38.46/5.53  
% 38.46/5.53  % SZS output start CNFRefutation for theBenchmark.p
% 38.46/5.53  
% 38.46/5.53  fof(f11,conjecture,(
% 38.46/5.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 38.46/5.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 38.46/5.53  
% 38.46/5.53  fof(f12,negated_conjecture,(
% 38.46/5.53    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 38.46/5.53    inference(negated_conjecture,[],[f11])).
% 38.46/5.53  
% 38.46/5.53  fof(f23,plain,(
% 38.46/5.53    ? [X0] : (? [X1] : (k2_relat_1(k5_relat_1(X0,X1)) != k9_relat_1(X1,k2_relat_1(X0)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 38.46/5.53    inference(ennf_transformation,[],[f12])).
% 38.46/5.53  
% 38.46/5.53  fof(f38,plain,(
% 38.46/5.53    ( ! [X0] : (? [X1] : (k2_relat_1(k5_relat_1(X0,X1)) != k9_relat_1(X1,k2_relat_1(X0)) & v1_relat_1(X1)) => (k2_relat_1(k5_relat_1(X0,sK7)) != k9_relat_1(sK7,k2_relat_1(X0)) & v1_relat_1(sK7))) )),
% 38.46/5.53    introduced(choice_axiom,[])).
% 38.46/5.53  
% 38.46/5.53  fof(f37,plain,(
% 38.46/5.53    ? [X0] : (? [X1] : (k2_relat_1(k5_relat_1(X0,X1)) != k9_relat_1(X1,k2_relat_1(X0)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (k2_relat_1(k5_relat_1(sK6,X1)) != k9_relat_1(X1,k2_relat_1(sK6)) & v1_relat_1(X1)) & v1_relat_1(sK6))),
% 38.46/5.53    introduced(choice_axiom,[])).
% 38.46/5.53  
% 38.46/5.53  fof(f39,plain,(
% 38.46/5.53    (k2_relat_1(k5_relat_1(sK6,sK7)) != k9_relat_1(sK7,k2_relat_1(sK6)) & v1_relat_1(sK7)) & v1_relat_1(sK6)),
% 38.46/5.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f23,f38,f37])).
% 38.46/5.53  
% 38.46/5.53  fof(f59,plain,(
% 38.46/5.53    v1_relat_1(sK6)),
% 38.46/5.53    inference(cnf_transformation,[],[f39])).
% 38.46/5.53  
% 38.46/5.53  fof(f1,axiom,(
% 38.46/5.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 38.46/5.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 38.46/5.53  
% 38.46/5.53  fof(f13,plain,(
% 38.46/5.53    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 38.46/5.53    inference(unused_predicate_definition_removal,[],[f1])).
% 38.46/5.53  
% 38.46/5.53  fof(f14,plain,(
% 38.46/5.53    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 38.46/5.53    inference(ennf_transformation,[],[f13])).
% 38.46/5.53  
% 38.46/5.53  fof(f24,plain,(
% 38.46/5.53    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 38.46/5.53    introduced(choice_axiom,[])).
% 38.46/5.53  
% 38.46/5.53  fof(f25,plain,(
% 38.46/5.53    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 38.46/5.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f24])).
% 38.46/5.53  
% 38.46/5.53  fof(f40,plain,(
% 38.46/5.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 38.46/5.53    inference(cnf_transformation,[],[f25])).
% 38.46/5.53  
% 38.46/5.53  fof(f3,axiom,(
% 38.46/5.53    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 38.46/5.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 38.46/5.53  
% 38.46/5.53  fof(f31,plain,(
% 38.46/5.53    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 38.46/5.53    inference(nnf_transformation,[],[f3])).
% 38.46/5.53  
% 38.46/5.53  fof(f32,plain,(
% 38.46/5.53    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 38.46/5.53    inference(rectify,[],[f31])).
% 38.46/5.53  
% 38.46/5.53  fof(f35,plain,(
% 38.46/5.53    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0))),
% 38.46/5.53    introduced(choice_axiom,[])).
% 38.46/5.53  
% 38.46/5.53  fof(f34,plain,(
% 38.46/5.53    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) => r2_hidden(k4_tarski(X2,sK4(X0,X1)),X0))) )),
% 38.46/5.53    introduced(choice_axiom,[])).
% 38.46/5.53  
% 38.46/5.53  fof(f33,plain,(
% 38.46/5.53    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK3(X0,X1),X3),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 38.46/5.53    introduced(choice_axiom,[])).
% 38.46/5.53  
% 38.46/5.53  fof(f36,plain,(
% 38.46/5.53    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK3(X0,X1),X3),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 38.46/5.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f32,f35,f34,f33])).
% 38.46/5.53  
% 38.46/5.53  fof(f48,plain,(
% 38.46/5.53    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 38.46/5.53    inference(cnf_transformation,[],[f36])).
% 38.46/5.53  
% 38.46/5.53  fof(f66,plain,(
% 38.46/5.53    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 38.46/5.53    inference(equality_resolution,[],[f48])).
% 38.46/5.53  
% 38.46/5.53  fof(f4,axiom,(
% 38.46/5.53    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 38.46/5.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 38.46/5.53  
% 38.46/5.53  fof(f52,plain,(
% 38.46/5.53    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 38.46/5.53    inference(cnf_transformation,[],[f4])).
% 38.46/5.53  
% 38.46/5.53  fof(f9,axiom,(
% 38.46/5.53    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 38.46/5.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 38.46/5.53  
% 38.46/5.53  fof(f21,plain,(
% 38.46/5.53    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 38.46/5.53    inference(ennf_transformation,[],[f9])).
% 38.46/5.53  
% 38.46/5.53  fof(f57,plain,(
% 38.46/5.53    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 38.46/5.53    inference(cnf_transformation,[],[f21])).
% 38.46/5.53  
% 38.46/5.53  fof(f10,axiom,(
% 38.46/5.53    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 38.46/5.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 38.46/5.53  
% 38.46/5.53  fof(f22,plain,(
% 38.46/5.53    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 38.46/5.53    inference(ennf_transformation,[],[f10])).
% 38.46/5.53  
% 38.46/5.53  fof(f58,plain,(
% 38.46/5.53    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 38.46/5.53    inference(cnf_transformation,[],[f22])).
% 38.46/5.53  
% 38.46/5.53  fof(f2,axiom,(
% 38.46/5.53    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (v1_relat_1(X2) => (k7_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1))))))),
% 38.46/5.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 38.46/5.53  
% 38.46/5.53  fof(f15,plain,(
% 38.46/5.53    ! [X0] : (! [X1,X2] : ((k7_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 38.46/5.53    inference(ennf_transformation,[],[f2])).
% 38.46/5.53  
% 38.46/5.53  fof(f26,plain,(
% 38.46/5.53    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ? [X3,X4] : (((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | (~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1))) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 38.46/5.53    inference(nnf_transformation,[],[f15])).
% 38.46/5.53  
% 38.46/5.53  fof(f27,plain,(
% 38.46/5.53    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 38.46/5.53    inference(flattening,[],[f26])).
% 38.46/5.53  
% 38.46/5.53  fof(f28,plain,(
% 38.46/5.53    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X5,X1)) & ((r2_hidden(k4_tarski(X5,X6),X0) & r2_hidden(X5,X1)) | ~r2_hidden(k4_tarski(X5,X6),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 38.46/5.53    inference(rectify,[],[f27])).
% 38.46/5.53  
% 38.46/5.53  fof(f29,plain,(
% 38.46/5.53    ! [X2,X1,X0] : (? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((~r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0) | ~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0) & r2_hidden(sK1(X0,X1,X2),X1)) | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2))))),
% 38.46/5.53    introduced(choice_axiom,[])).
% 38.46/5.53  
% 38.46/5.53  fof(f30,plain,(
% 38.46/5.53    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ((~r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0) | ~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0) & r2_hidden(sK1(X0,X1,X2),X1)) | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2)))) & (! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X5,X1)) & ((r2_hidden(k4_tarski(X5,X6),X0) & r2_hidden(X5,X1)) | ~r2_hidden(k4_tarski(X5,X6),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 38.46/5.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f28,f29])).
% 38.46/5.53  
% 38.46/5.53  fof(f42,plain,(
% 38.46/5.53    ( ! [X6,X2,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X2) | k7_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 38.46/5.53    inference(cnf_transformation,[],[f30])).
% 38.46/5.53  
% 38.46/5.53  fof(f64,plain,(
% 38.46/5.53    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1)) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 38.46/5.53    inference(equality_resolution,[],[f42])).
% 38.46/5.53  
% 38.46/5.53  fof(f5,axiom,(
% 38.46/5.53    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 38.46/5.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 38.46/5.53  
% 38.46/5.53  fof(f16,plain,(
% 38.46/5.53    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 38.46/5.53    inference(ennf_transformation,[],[f5])).
% 38.46/5.53  
% 38.46/5.53  fof(f53,plain,(
% 38.46/5.53    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 38.46/5.53    inference(cnf_transformation,[],[f16])).
% 38.46/5.53  
% 38.46/5.53  fof(f41,plain,(
% 38.46/5.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 38.46/5.53    inference(cnf_transformation,[],[f25])).
% 38.46/5.53  
% 38.46/5.53  fof(f7,axiom,(
% 38.46/5.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)))))),
% 38.46/5.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 38.46/5.53  
% 38.46/5.53  fof(f18,plain,(
% 38.46/5.53    ! [X0] : (! [X1] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 38.46/5.53    inference(ennf_transformation,[],[f7])).
% 38.46/5.53  
% 38.46/5.53  fof(f19,plain,(
% 38.46/5.53    ! [X0] : (! [X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 38.46/5.53    inference(flattening,[],[f18])).
% 38.46/5.53  
% 38.46/5.53  fof(f55,plain,(
% 38.46/5.53    ( ! [X0,X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 38.46/5.53    inference(cnf_transformation,[],[f19])).
% 38.46/5.53  
% 38.46/5.53  fof(f60,plain,(
% 38.46/5.53    v1_relat_1(sK7)),
% 38.46/5.53    inference(cnf_transformation,[],[f39])).
% 38.46/5.53  
% 38.46/5.53  fof(f8,axiom,(
% 38.46/5.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2))))),
% 38.46/5.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 38.46/5.53  
% 38.46/5.53  fof(f20,plain,(
% 38.46/5.53    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 38.46/5.53    inference(ennf_transformation,[],[f8])).
% 38.46/5.53  
% 38.46/5.53  fof(f56,plain,(
% 38.46/5.53    ( ! [X2,X0,X1] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 38.46/5.53    inference(cnf_transformation,[],[f20])).
% 38.46/5.53  
% 38.46/5.53  fof(f6,axiom,(
% 38.46/5.53    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 38.46/5.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 38.46/5.53  
% 38.46/5.53  fof(f17,plain,(
% 38.46/5.53    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 38.46/5.53    inference(ennf_transformation,[],[f6])).
% 38.46/5.53  
% 38.46/5.53  fof(f54,plain,(
% 38.46/5.53    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 38.46/5.53    inference(cnf_transformation,[],[f17])).
% 38.46/5.53  
% 38.46/5.53  fof(f61,plain,(
% 38.46/5.53    k2_relat_1(k5_relat_1(sK6,sK7)) != k9_relat_1(sK7,k2_relat_1(sK6))),
% 38.46/5.53    inference(cnf_transformation,[],[f39])).
% 38.46/5.53  
% 38.46/5.53  cnf(c_293,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_1199,plain,
% 38.46/5.53      ( X0 != X1 | k5_relat_1(sK6,sK7) != X1 | k5_relat_1(sK6,sK7) = X0 ),
% 38.46/5.53      inference(instantiation,[status(thm)],[c_293]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_1570,plain,
% 38.46/5.53      ( X0 != k5_relat_1(sK6,sK7)
% 38.46/5.53      | k5_relat_1(sK6,sK7) = X0
% 38.46/5.53      | k5_relat_1(sK6,sK7) != k5_relat_1(sK6,sK7) ),
% 38.46/5.53      inference(instantiation,[status(thm)],[c_1199]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_20429,plain,
% 38.46/5.53      ( k5_relat_1(X0,k7_relat_1(X1,X2)) != k5_relat_1(sK6,sK7)
% 38.46/5.53      | k5_relat_1(sK6,sK7) = k5_relat_1(X0,k7_relat_1(X1,X2))
% 38.46/5.53      | k5_relat_1(sK6,sK7) != k5_relat_1(sK6,sK7) ),
% 38.46/5.53      inference(instantiation,[status(thm)],[c_1570]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_91864,plain,
% 38.46/5.53      ( k5_relat_1(X0,k7_relat_1(sK7,X1)) != k5_relat_1(sK6,sK7)
% 38.46/5.53      | k5_relat_1(sK6,sK7) = k5_relat_1(X0,k7_relat_1(sK7,X1))
% 38.46/5.53      | k5_relat_1(sK6,sK7) != k5_relat_1(sK6,sK7) ),
% 38.46/5.53      inference(instantiation,[status(thm)],[c_20429]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_122686,plain,
% 38.46/5.53      ( k5_relat_1(X0,k7_relat_1(sK7,k2_relat_1(sK6))) != k5_relat_1(sK6,sK7)
% 38.46/5.53      | k5_relat_1(sK6,sK7) = k5_relat_1(X0,k7_relat_1(sK7,k2_relat_1(sK6)))
% 38.46/5.53      | k5_relat_1(sK6,sK7) != k5_relat_1(sK6,sK7) ),
% 38.46/5.53      inference(instantiation,[status(thm)],[c_91864]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_122687,plain,
% 38.46/5.53      ( k5_relat_1(sK6,k7_relat_1(sK7,k2_relat_1(sK6))) != k5_relat_1(sK6,sK7)
% 38.46/5.53      | k5_relat_1(sK6,sK7) = k5_relat_1(sK6,k7_relat_1(sK7,k2_relat_1(sK6)))
% 38.46/5.53      | k5_relat_1(sK6,sK7) != k5_relat_1(sK6,sK7) ),
% 38.46/5.53      inference(instantiation,[status(thm)],[c_122686]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_1193,plain,
% 38.46/5.53      ( k9_relat_1(sK7,k2_relat_1(sK6)) != X0
% 38.46/5.53      | k9_relat_1(sK7,k2_relat_1(sK6)) = k2_relat_1(k5_relat_1(sK6,sK7))
% 38.46/5.53      | k2_relat_1(k5_relat_1(sK6,sK7)) != X0 ),
% 38.46/5.53      inference(instantiation,[status(thm)],[c_293]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_12140,plain,
% 38.46/5.53      ( k9_relat_1(sK7,k2_relat_1(sK6)) != k2_relat_1(X0)
% 38.46/5.53      | k9_relat_1(sK7,k2_relat_1(sK6)) = k2_relat_1(k5_relat_1(sK6,sK7))
% 38.46/5.53      | k2_relat_1(k5_relat_1(sK6,sK7)) != k2_relat_1(X0) ),
% 38.46/5.53      inference(instantiation,[status(thm)],[c_1193]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_121470,plain,
% 38.46/5.53      ( k9_relat_1(sK7,k2_relat_1(sK6)) != k2_relat_1(k5_relat_1(X0,k5_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)),k6_relat_1(k2_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)))))))
% 38.46/5.53      | k9_relat_1(sK7,k2_relat_1(sK6)) = k2_relat_1(k5_relat_1(sK6,sK7))
% 38.46/5.53      | k2_relat_1(k5_relat_1(sK6,sK7)) != k2_relat_1(k5_relat_1(X0,k5_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)),k6_relat_1(k2_relat_1(k7_relat_1(sK7,k2_relat_1(sK6))))))) ),
% 38.46/5.53      inference(instantiation,[status(thm)],[c_12140]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_121471,plain,
% 38.46/5.53      ( k9_relat_1(sK7,k2_relat_1(sK6)) != k2_relat_1(k5_relat_1(sK6,k5_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)),k6_relat_1(k2_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)))))))
% 38.46/5.53      | k9_relat_1(sK7,k2_relat_1(sK6)) = k2_relat_1(k5_relat_1(sK6,sK7))
% 38.46/5.53      | k2_relat_1(k5_relat_1(sK6,sK7)) != k2_relat_1(k5_relat_1(sK6,k5_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)),k6_relat_1(k2_relat_1(k7_relat_1(sK7,k2_relat_1(sK6))))))) ),
% 38.46/5.53      inference(instantiation,[status(thm)],[c_121470]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_299,plain,
% 38.46/5.53      ( X0 != X1 | k2_relat_1(X0) = k2_relat_1(X1) ),
% 38.46/5.53      theory(equality) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_1027,plain,
% 38.46/5.53      ( k5_relat_1(sK6,sK7) != X0
% 38.46/5.53      | k2_relat_1(k5_relat_1(sK6,sK7)) = k2_relat_1(X0) ),
% 38.46/5.53      inference(instantiation,[status(thm)],[c_299]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_1200,plain,
% 38.46/5.53      ( k5_relat_1(sK6,sK7) != k5_relat_1(X0,X1)
% 38.46/5.53      | k2_relat_1(k5_relat_1(sK6,sK7)) = k2_relat_1(k5_relat_1(X0,X1)) ),
% 38.46/5.53      inference(instantiation,[status(thm)],[c_1027]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_110865,plain,
% 38.46/5.53      ( k5_relat_1(sK6,sK7) != k5_relat_1(X0,k5_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)),k6_relat_1(k2_relat_1(k7_relat_1(sK7,k2_relat_1(sK6))))))
% 38.46/5.53      | k2_relat_1(k5_relat_1(sK6,sK7)) = k2_relat_1(k5_relat_1(X0,k5_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)),k6_relat_1(k2_relat_1(k7_relat_1(sK7,k2_relat_1(sK6))))))) ),
% 38.46/5.53      inference(instantiation,[status(thm)],[c_1200]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_110866,plain,
% 38.46/5.53      ( k5_relat_1(sK6,sK7) != k5_relat_1(sK6,k5_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)),k6_relat_1(k2_relat_1(k7_relat_1(sK7,k2_relat_1(sK6))))))
% 38.46/5.53      | k2_relat_1(k5_relat_1(sK6,sK7)) = k2_relat_1(k5_relat_1(sK6,k5_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)),k6_relat_1(k2_relat_1(k7_relat_1(sK7,k2_relat_1(sK6))))))) ),
% 38.46/5.53      inference(instantiation,[status(thm)],[c_110865]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_21,negated_conjecture,
% 38.46/5.53      ( v1_relat_1(sK6) ),
% 38.46/5.53      inference(cnf_transformation,[],[f59]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_685,plain,
% 38.46/5.53      ( v1_relat_1(sK6) = iProver_top ),
% 38.46/5.53      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_1,plain,
% 38.46/5.53      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 38.46/5.53      inference(cnf_transformation,[],[f40]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_704,plain,
% 38.46/5.53      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 38.46/5.53      | r1_tarski(X0,X1) = iProver_top ),
% 38.46/5.53      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_11,plain,
% 38.46/5.53      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 38.46/5.53      | r2_hidden(k4_tarski(X0,sK5(X1,X0)),X1) ),
% 38.46/5.53      inference(cnf_transformation,[],[f66]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_694,plain,
% 38.46/5.53      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 38.46/5.53      | r2_hidden(k4_tarski(X0,sK5(X1,X0)),X1) = iProver_top ),
% 38.46/5.53      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_12,plain,
% 38.46/5.53      ( v1_relat_1(k6_relat_1(X0)) ),
% 38.46/5.53      inference(cnf_transformation,[],[f52]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_693,plain,
% 38.46/5.53      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 38.46/5.53      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_17,plain,
% 38.46/5.53      ( ~ v1_relat_1(X0)
% 38.46/5.53      | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ),
% 38.46/5.53      inference(cnf_transformation,[],[f57]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_688,plain,
% 38.46/5.53      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
% 38.46/5.53      | v1_relat_1(X0) != iProver_top ),
% 38.46/5.53      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_968,plain,
% 38.46/5.53      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(k2_relat_1(k6_relat_1(X0)))) = k6_relat_1(X0) ),
% 38.46/5.53      inference(superposition,[status(thm)],[c_693,c_688]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_18,plain,
% 38.46/5.53      ( ~ v1_relat_1(X0)
% 38.46/5.53      | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
% 38.46/5.53      inference(cnf_transformation,[],[f58]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_687,plain,
% 38.46/5.53      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
% 38.46/5.53      | v1_relat_1(X1) != iProver_top ),
% 38.46/5.53      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_1223,plain,
% 38.46/5.53      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
% 38.46/5.53      inference(superposition,[status(thm)],[c_693,c_687]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_1823,plain,
% 38.46/5.53      ( k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(X0))),X0) = k6_relat_1(X0) ),
% 38.46/5.53      inference(superposition,[status(thm)],[c_968,c_1223]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_7,plain,
% 38.46/5.53      ( r2_hidden(X0,X1)
% 38.46/5.53      | ~ r2_hidden(k4_tarski(X0,X2),k7_relat_1(X3,X1))
% 38.46/5.53      | ~ v1_relat_1(X3)
% 38.46/5.53      | ~ v1_relat_1(k7_relat_1(X3,X1)) ),
% 38.46/5.53      inference(cnf_transformation,[],[f64]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_698,plain,
% 38.46/5.53      ( r2_hidden(X0,X1) = iProver_top
% 38.46/5.53      | r2_hidden(k4_tarski(X0,X2),k7_relat_1(X3,X1)) != iProver_top
% 38.46/5.53      | v1_relat_1(X3) != iProver_top
% 38.46/5.53      | v1_relat_1(k7_relat_1(X3,X1)) != iProver_top ),
% 38.46/5.53      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_13,plain,
% 38.46/5.53      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 38.46/5.53      inference(cnf_transformation,[],[f53]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_692,plain,
% 38.46/5.53      ( v1_relat_1(X0) != iProver_top
% 38.46/5.53      | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
% 38.46/5.53      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_778,plain,
% 38.46/5.53      ( r2_hidden(X0,X1) = iProver_top
% 38.46/5.53      | r2_hidden(k4_tarski(X0,X2),k7_relat_1(X3,X1)) != iProver_top
% 38.46/5.53      | v1_relat_1(X3) != iProver_top ),
% 38.46/5.53      inference(forward_subsumption_resolution,
% 38.46/5.53                [status(thm)],
% 38.46/5.53                [c_698,c_692]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_3842,plain,
% 38.46/5.53      ( r2_hidden(X0,X1) = iProver_top
% 38.46/5.53      | r2_hidden(k4_tarski(X0,X2),k6_relat_1(X1)) != iProver_top
% 38.46/5.53      | v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(X1)))) != iProver_top ),
% 38.46/5.53      inference(superposition,[status(thm)],[c_1823,c_778]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_35909,plain,
% 38.46/5.53      ( r2_hidden(X0,X1) = iProver_top
% 38.46/5.53      | r2_hidden(k4_tarski(X0,X2),k6_relat_1(X1)) != iProver_top ),
% 38.46/5.53      inference(forward_subsumption_resolution,
% 38.46/5.53                [status(thm)],
% 38.46/5.53                [c_3842,c_693]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_35919,plain,
% 38.46/5.53      ( r2_hidden(X0,X1) = iProver_top
% 38.46/5.53      | r2_hidden(X0,k1_relat_1(k6_relat_1(X1))) != iProver_top ),
% 38.46/5.53      inference(superposition,[status(thm)],[c_694,c_35909]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_36209,plain,
% 38.46/5.53      ( r2_hidden(sK0(k1_relat_1(k6_relat_1(X0)),X1),X0) = iProver_top
% 38.46/5.53      | r1_tarski(k1_relat_1(k6_relat_1(X0)),X1) = iProver_top ),
% 38.46/5.53      inference(superposition,[status(thm)],[c_704,c_35919]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_0,plain,
% 38.46/5.53      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 38.46/5.53      inference(cnf_transformation,[],[f41]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_705,plain,
% 38.46/5.53      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 38.46/5.53      | r1_tarski(X0,X1) = iProver_top ),
% 38.46/5.53      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_36423,plain,
% 38.46/5.53      ( r1_tarski(k1_relat_1(k6_relat_1(X0)),X0) = iProver_top ),
% 38.46/5.53      inference(superposition,[status(thm)],[c_36209,c_705]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_15,plain,
% 38.46/5.53      ( ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
% 38.46/5.53      | ~ v1_relat_1(X0)
% 38.46/5.53      | ~ v1_relat_1(X1)
% 38.46/5.53      | k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) ),
% 38.46/5.53      inference(cnf_transformation,[],[f55]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_690,plain,
% 38.46/5.53      ( k2_relat_1(k5_relat_1(X0,X1)) = k2_relat_1(X1)
% 38.46/5.53      | r1_tarski(k1_relat_1(X1),k2_relat_1(X0)) != iProver_top
% 38.46/5.53      | v1_relat_1(X1) != iProver_top
% 38.46/5.53      | v1_relat_1(X0) != iProver_top ),
% 38.46/5.53      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_36674,plain,
% 38.46/5.53      ( k2_relat_1(k5_relat_1(X0,k6_relat_1(k2_relat_1(X0)))) = k2_relat_1(k6_relat_1(k2_relat_1(X0)))
% 38.46/5.53      | v1_relat_1(X0) != iProver_top
% 38.46/5.53      | v1_relat_1(k6_relat_1(k2_relat_1(X0))) != iProver_top ),
% 38.46/5.53      inference(superposition,[status(thm)],[c_36423,c_690]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_51748,plain,
% 38.46/5.53      ( k2_relat_1(k5_relat_1(X0,k6_relat_1(k2_relat_1(X0)))) = k2_relat_1(k6_relat_1(k2_relat_1(X0)))
% 38.46/5.53      | v1_relat_1(X0) != iProver_top ),
% 38.46/5.53      inference(forward_subsumption_resolution,
% 38.46/5.53                [status(thm)],
% 38.46/5.53                [c_36674,c_693]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_51755,plain,
% 38.46/5.53      ( k2_relat_1(k5_relat_1(sK6,k6_relat_1(k2_relat_1(sK6)))) = k2_relat_1(k6_relat_1(k2_relat_1(sK6))) ),
% 38.46/5.53      inference(superposition,[status(thm)],[c_685,c_51748]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_970,plain,
% 38.46/5.53      ( k5_relat_1(sK6,k6_relat_1(k2_relat_1(sK6))) = sK6 ),
% 38.46/5.53      inference(superposition,[status(thm)],[c_685,c_688]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_51757,plain,
% 38.46/5.53      ( k2_relat_1(k6_relat_1(k2_relat_1(sK6))) = k2_relat_1(sK6) ),
% 38.46/5.53      inference(light_normalisation,[status(thm)],[c_51755,c_970]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_52468,plain,
% 38.46/5.53      ( k7_relat_1(k6_relat_1(k2_relat_1(sK6)),k2_relat_1(sK6)) = k6_relat_1(k2_relat_1(sK6)) ),
% 38.46/5.53      inference(superposition,[status(thm)],[c_51757,c_1823]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_20,negated_conjecture,
% 38.46/5.53      ( v1_relat_1(sK7) ),
% 38.46/5.53      inference(cnf_transformation,[],[f60]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_686,plain,
% 38.46/5.53      ( v1_relat_1(sK7) = iProver_top ),
% 38.46/5.53      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_16,plain,
% 38.46/5.53      ( ~ v1_relat_1(X0)
% 38.46/5.53      | ~ v1_relat_1(X1)
% 38.46/5.53      | ~ v1_relat_1(X2)
% 38.46/5.53      | k5_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(X1,k5_relat_1(X2,X0)) ),
% 38.46/5.53      inference(cnf_transformation,[],[f56]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_689,plain,
% 38.46/5.53      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
% 38.46/5.53      | v1_relat_1(X2) != iProver_top
% 38.46/5.53      | v1_relat_1(X0) != iProver_top
% 38.46/5.53      | v1_relat_1(X1) != iProver_top ),
% 38.46/5.53      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_1942,plain,
% 38.46/5.53      ( k5_relat_1(k7_relat_1(X0,X1),k5_relat_1(X2,X3)) = k5_relat_1(k5_relat_1(k7_relat_1(X0,X1),X2),X3)
% 38.46/5.53      | v1_relat_1(X0) != iProver_top
% 38.46/5.53      | v1_relat_1(X2) != iProver_top
% 38.46/5.53      | v1_relat_1(X3) != iProver_top ),
% 38.46/5.53      inference(superposition,[status(thm)],[c_692,c_689]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_8873,plain,
% 38.46/5.53      ( k5_relat_1(k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),X3) = k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k5_relat_1(X2,X3))
% 38.46/5.53      | v1_relat_1(X2) != iProver_top
% 38.46/5.53      | v1_relat_1(X3) != iProver_top ),
% 38.46/5.53      inference(superposition,[status(thm)],[c_693,c_1942]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_90167,plain,
% 38.46/5.53      ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k5_relat_1(k6_relat_1(X2),X3)) = k5_relat_1(k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2)),X3)
% 38.46/5.53      | v1_relat_1(X3) != iProver_top ),
% 38.46/5.53      inference(superposition,[status(thm)],[c_693,c_8873]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_96968,plain,
% 38.46/5.53      ( k5_relat_1(k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2)),sK7) = k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k5_relat_1(k6_relat_1(X2),sK7)) ),
% 38.46/5.53      inference(superposition,[status(thm)],[c_686,c_90167]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_1224,plain,
% 38.46/5.53      ( k5_relat_1(k6_relat_1(X0),sK7) = k7_relat_1(sK7,X0) ),
% 38.46/5.53      inference(superposition,[status(thm)],[c_686,c_687]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_96974,plain,
% 38.46/5.53      ( k5_relat_1(k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2)),sK7) = k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k7_relat_1(sK7,X2)) ),
% 38.46/5.53      inference(demodulation,[status(thm)],[c_96968,c_1224]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_104943,plain,
% 38.46/5.53      ( k5_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(X0))),X0),k7_relat_1(sK7,X1)) = k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),sK7) ),
% 38.46/5.53      inference(superposition,[status(thm)],[c_1823,c_96974]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_1222,plain,
% 38.46/5.53      ( k5_relat_1(k6_relat_1(X0),k7_relat_1(X1,X2)) = k7_relat_1(k7_relat_1(X1,X2),X0)
% 38.46/5.53      | v1_relat_1(X1) != iProver_top ),
% 38.46/5.53      inference(superposition,[status(thm)],[c_692,c_687]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_4056,plain,
% 38.46/5.53      ( k5_relat_1(k6_relat_1(X0),k7_relat_1(sK7,X1)) = k7_relat_1(k7_relat_1(sK7,X1),X0) ),
% 38.46/5.53      inference(superposition,[status(thm)],[c_686,c_1222]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_104955,plain,
% 38.46/5.53      ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),sK7) = k7_relat_1(k7_relat_1(sK7,X0),X1) ),
% 38.46/5.53      inference(light_normalisation,
% 38.46/5.53                [status(thm)],
% 38.46/5.53                [c_104943,c_1223,c_1823,c_4056]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_105998,plain,
% 38.46/5.53      ( k7_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)),k2_relat_1(sK6)) = k5_relat_1(k6_relat_1(k2_relat_1(sK6)),sK7) ),
% 38.46/5.53      inference(superposition,[status(thm)],[c_52468,c_104955]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_106004,plain,
% 38.46/5.53      ( k7_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)),k2_relat_1(sK6)) = k7_relat_1(sK7,k2_relat_1(sK6)) ),
% 38.46/5.53      inference(demodulation,[status(thm)],[c_105998,c_1224]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_3841,plain,
% 38.46/5.53      ( r2_hidden(X0,X1) = iProver_top
% 38.46/5.53      | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) != iProver_top
% 38.46/5.53      | v1_relat_1(X2) != iProver_top ),
% 38.46/5.53      inference(superposition,[status(thm)],[c_694,c_778]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_9385,plain,
% 38.46/5.53      ( r2_hidden(sK0(k1_relat_1(k7_relat_1(X0,X1)),X2),X1) = iProver_top
% 38.46/5.53      | r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X2) = iProver_top
% 38.46/5.53      | v1_relat_1(X0) != iProver_top ),
% 38.46/5.53      inference(superposition,[status(thm)],[c_704,c_3841]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_46402,plain,
% 38.46/5.53      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
% 38.46/5.53      | v1_relat_1(X0) != iProver_top ),
% 38.46/5.53      inference(superposition,[status(thm)],[c_9385,c_705]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_107621,plain,
% 38.46/5.53      ( r1_tarski(k1_relat_1(k7_relat_1(sK7,k2_relat_1(sK6))),k2_relat_1(sK6)) = iProver_top
% 38.46/5.53      | v1_relat_1(k7_relat_1(sK7,k2_relat_1(sK6))) != iProver_top ),
% 38.46/5.53      inference(superposition,[status(thm)],[c_106004,c_46402]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_1196,plain,
% 38.46/5.53      ( k9_relat_1(sK7,k2_relat_1(sK6)) != X0
% 38.46/5.53      | k9_relat_1(sK7,k2_relat_1(sK6)) = k2_relat_1(X1)
% 38.46/5.53      | k2_relat_1(X1) != X0 ),
% 38.46/5.53      inference(instantiation,[status(thm)],[c_293]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_12139,plain,
% 38.46/5.53      ( k9_relat_1(sK7,k2_relat_1(sK6)) != k2_relat_1(X0)
% 38.46/5.53      | k9_relat_1(sK7,k2_relat_1(sK6)) = k2_relat_1(X1)
% 38.46/5.53      | k2_relat_1(X1) != k2_relat_1(X0) ),
% 38.46/5.53      inference(instantiation,[status(thm)],[c_1196]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_34495,plain,
% 38.46/5.53      ( k9_relat_1(sK7,k2_relat_1(sK6)) = k2_relat_1(X0)
% 38.46/5.53      | k9_relat_1(sK7,k2_relat_1(sK6)) != k2_relat_1(k5_relat_1(X1,k7_relat_1(sK7,k2_relat_1(X2))))
% 38.46/5.53      | k2_relat_1(X0) != k2_relat_1(k5_relat_1(X1,k7_relat_1(sK7,k2_relat_1(X2)))) ),
% 38.46/5.53      inference(instantiation,[status(thm)],[c_12139]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_68297,plain,
% 38.46/5.53      ( k9_relat_1(sK7,k2_relat_1(sK6)) = k2_relat_1(k5_relat_1(X0,k5_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)),k6_relat_1(k2_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)))))))
% 38.46/5.53      | k9_relat_1(sK7,k2_relat_1(sK6)) != k2_relat_1(k5_relat_1(X1,k7_relat_1(sK7,k2_relat_1(sK6))))
% 38.46/5.53      | k2_relat_1(k5_relat_1(X0,k5_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)),k6_relat_1(k2_relat_1(k7_relat_1(sK7,k2_relat_1(sK6))))))) != k2_relat_1(k5_relat_1(X1,k7_relat_1(sK7,k2_relat_1(sK6)))) ),
% 38.46/5.53      inference(instantiation,[status(thm)],[c_34495]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_68298,plain,
% 38.46/5.53      ( k9_relat_1(sK7,k2_relat_1(sK6)) = k2_relat_1(k5_relat_1(sK6,k5_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)),k6_relat_1(k2_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)))))))
% 38.46/5.53      | k9_relat_1(sK7,k2_relat_1(sK6)) != k2_relat_1(k5_relat_1(sK6,k7_relat_1(sK7,k2_relat_1(sK6))))
% 38.46/5.53      | k2_relat_1(k5_relat_1(sK6,k5_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)),k6_relat_1(k2_relat_1(k7_relat_1(sK7,k2_relat_1(sK6))))))) != k2_relat_1(k5_relat_1(sK6,k7_relat_1(sK7,k2_relat_1(sK6)))) ),
% 38.46/5.53      inference(instantiation,[status(thm)],[c_68297]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_5775,plain,
% 38.46/5.53      ( X0 != k5_relat_1(X1,k7_relat_1(X2,X3))
% 38.46/5.53      | k5_relat_1(sK6,sK7) = X0
% 38.46/5.53      | k5_relat_1(sK6,sK7) != k5_relat_1(X1,k7_relat_1(X2,X3)) ),
% 38.46/5.53      inference(instantiation,[status(thm)],[c_1199]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_14845,plain,
% 38.46/5.53      ( k5_relat_1(X0,X1) != k5_relat_1(X2,k7_relat_1(X3,X4))
% 38.46/5.53      | k5_relat_1(sK6,sK7) = k5_relat_1(X0,X1)
% 38.46/5.53      | k5_relat_1(sK6,sK7) != k5_relat_1(X2,k7_relat_1(X3,X4)) ),
% 38.46/5.53      inference(instantiation,[status(thm)],[c_5775]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_37310,plain,
% 38.46/5.53      ( k5_relat_1(X0,k5_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)),k6_relat_1(k2_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)))))) != k5_relat_1(X1,k7_relat_1(sK7,k2_relat_1(sK6)))
% 38.46/5.53      | k5_relat_1(sK6,sK7) = k5_relat_1(X0,k5_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)),k6_relat_1(k2_relat_1(k7_relat_1(sK7,k2_relat_1(sK6))))))
% 38.46/5.53      | k5_relat_1(sK6,sK7) != k5_relat_1(X1,k7_relat_1(sK7,k2_relat_1(sK6))) ),
% 38.46/5.53      inference(instantiation,[status(thm)],[c_14845]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_37311,plain,
% 38.46/5.53      ( k5_relat_1(sK6,k5_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)),k6_relat_1(k2_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)))))) != k5_relat_1(sK6,k7_relat_1(sK7,k2_relat_1(sK6)))
% 38.46/5.53      | k5_relat_1(sK6,sK7) = k5_relat_1(sK6,k5_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)),k6_relat_1(k2_relat_1(k7_relat_1(sK7,k2_relat_1(sK6))))))
% 38.46/5.53      | k5_relat_1(sK6,sK7) != k5_relat_1(sK6,k7_relat_1(sK7,k2_relat_1(sK6))) ),
% 38.46/5.53      inference(instantiation,[status(thm)],[c_37310]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_15845,plain,
% 38.46/5.53      ( X0 != k5_relat_1(X1,k7_relat_1(X2,X3))
% 38.46/5.53      | k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,k7_relat_1(X2,X3))) ),
% 38.46/5.53      inference(instantiation,[status(thm)],[c_299]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_37305,plain,
% 38.46/5.53      ( k5_relat_1(X0,k5_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)),k6_relat_1(k2_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)))))) != k5_relat_1(X1,k7_relat_1(sK7,k2_relat_1(sK6)))
% 38.46/5.53      | k2_relat_1(k5_relat_1(X0,k5_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)),k6_relat_1(k2_relat_1(k7_relat_1(sK7,k2_relat_1(sK6))))))) = k2_relat_1(k5_relat_1(X1,k7_relat_1(sK7,k2_relat_1(sK6)))) ),
% 38.46/5.53      inference(instantiation,[status(thm)],[c_15845]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_37309,plain,
% 38.46/5.53      ( k5_relat_1(sK6,k5_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)),k6_relat_1(k2_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)))))) != k5_relat_1(sK6,k7_relat_1(sK7,k2_relat_1(sK6)))
% 38.46/5.53      | k2_relat_1(k5_relat_1(sK6,k5_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)),k6_relat_1(k2_relat_1(k7_relat_1(sK7,k2_relat_1(sK6))))))) = k2_relat_1(k5_relat_1(sK6,k7_relat_1(sK7,k2_relat_1(sK6)))) ),
% 38.46/5.53      inference(instantiation,[status(thm)],[c_37305]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_301,plain,
% 38.46/5.53      ( X0 != X1 | X2 != X3 | k5_relat_1(X0,X2) = k5_relat_1(X1,X3) ),
% 38.46/5.53      theory(equality) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_14846,plain,
% 38.46/5.53      ( X0 != X1
% 38.46/5.53      | X2 != k7_relat_1(X3,X4)
% 38.46/5.53      | k5_relat_1(X0,X2) = k5_relat_1(X1,k7_relat_1(X3,X4)) ),
% 38.46/5.53      inference(instantiation,[status(thm)],[c_301]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_17414,plain,
% 38.46/5.53      ( X0 != X1
% 38.46/5.53      | k5_relat_1(X0,k5_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)),k6_relat_1(k2_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)))))) = k5_relat_1(X1,k7_relat_1(sK7,k2_relat_1(sK6)))
% 38.46/5.53      | k5_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)),k6_relat_1(k2_relat_1(k7_relat_1(sK7,k2_relat_1(sK6))))) != k7_relat_1(sK7,k2_relat_1(sK6)) ),
% 38.46/5.53      inference(instantiation,[status(thm)],[c_14846]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_17415,plain,
% 38.46/5.53      ( k5_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)),k6_relat_1(k2_relat_1(k7_relat_1(sK7,k2_relat_1(sK6))))) != k7_relat_1(sK7,k2_relat_1(sK6))
% 38.46/5.53      | k5_relat_1(sK6,k5_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)),k6_relat_1(k2_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)))))) = k5_relat_1(sK6,k7_relat_1(sK7,k2_relat_1(sK6)))
% 38.46/5.53      | sK6 != sK6 ),
% 38.46/5.53      inference(instantiation,[status(thm)],[c_17414]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_7742,plain,
% 38.46/5.53      ( v1_relat_1(k7_relat_1(sK7,k2_relat_1(sK6))) | ~ v1_relat_1(sK7) ),
% 38.46/5.53      inference(instantiation,[status(thm)],[c_13]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_7743,plain,
% 38.46/5.53      ( v1_relat_1(k7_relat_1(sK7,k2_relat_1(sK6))) = iProver_top
% 38.46/5.53      | v1_relat_1(sK7) != iProver_top ),
% 38.46/5.53      inference(predicate_to_equality,[status(thm)],[c_7742]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_2695,plain,
% 38.46/5.53      ( k9_relat_1(sK7,k2_relat_1(sK6)) = k2_relat_1(X0)
% 38.46/5.53      | k9_relat_1(sK7,k2_relat_1(sK6)) != k2_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)))
% 38.46/5.53      | k2_relat_1(X0) != k2_relat_1(k7_relat_1(sK7,k2_relat_1(sK6))) ),
% 38.46/5.53      inference(instantiation,[status(thm)],[c_1196]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_7265,plain,
% 38.46/5.53      ( k9_relat_1(sK7,k2_relat_1(sK6)) = k2_relat_1(k5_relat_1(X0,k7_relat_1(sK7,k2_relat_1(sK6))))
% 38.46/5.53      | k9_relat_1(sK7,k2_relat_1(sK6)) != k2_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)))
% 38.46/5.53      | k2_relat_1(k5_relat_1(X0,k7_relat_1(sK7,k2_relat_1(sK6)))) != k2_relat_1(k7_relat_1(sK7,k2_relat_1(sK6))) ),
% 38.46/5.53      inference(instantiation,[status(thm)],[c_2695]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_7270,plain,
% 38.46/5.53      ( k9_relat_1(sK7,k2_relat_1(sK6)) = k2_relat_1(k5_relat_1(sK6,k7_relat_1(sK7,k2_relat_1(sK6))))
% 38.46/5.53      | k9_relat_1(sK7,k2_relat_1(sK6)) != k2_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)))
% 38.46/5.53      | k2_relat_1(k5_relat_1(sK6,k7_relat_1(sK7,k2_relat_1(sK6)))) != k2_relat_1(k7_relat_1(sK7,k2_relat_1(sK6))) ),
% 38.46/5.53      inference(instantiation,[status(thm)],[c_7265]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_7263,plain,
% 38.46/5.53      ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK7,k2_relat_1(sK6))),k2_relat_1(X0))
% 38.46/5.53      | ~ v1_relat_1(X0)
% 38.46/5.53      | ~ v1_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)))
% 38.46/5.53      | k2_relat_1(k5_relat_1(X0,k7_relat_1(sK7,k2_relat_1(sK6)))) = k2_relat_1(k7_relat_1(sK7,k2_relat_1(sK6))) ),
% 38.46/5.53      inference(instantiation,[status(thm)],[c_15]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_7266,plain,
% 38.46/5.53      ( k2_relat_1(k5_relat_1(X0,k7_relat_1(sK7,k2_relat_1(sK6)))) = k2_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)))
% 38.46/5.53      | r1_tarski(k1_relat_1(k7_relat_1(sK7,k2_relat_1(sK6))),k2_relat_1(X0)) != iProver_top
% 38.46/5.53      | v1_relat_1(X0) != iProver_top
% 38.46/5.53      | v1_relat_1(k7_relat_1(sK7,k2_relat_1(sK6))) != iProver_top ),
% 38.46/5.53      inference(predicate_to_equality,[status(thm)],[c_7263]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_7268,plain,
% 38.46/5.53      ( k2_relat_1(k5_relat_1(sK6,k7_relat_1(sK7,k2_relat_1(sK6)))) = k2_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)))
% 38.46/5.53      | r1_tarski(k1_relat_1(k7_relat_1(sK7,k2_relat_1(sK6))),k2_relat_1(sK6)) != iProver_top
% 38.46/5.53      | v1_relat_1(k7_relat_1(sK7,k2_relat_1(sK6))) != iProver_top
% 38.46/5.53      | v1_relat_1(sK6) != iProver_top ),
% 38.46/5.53      inference(instantiation,[status(thm)],[c_7266]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_5948,plain,
% 38.46/5.53      ( ~ v1_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)))
% 38.46/5.53      | k5_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)),k6_relat_1(k2_relat_1(k7_relat_1(sK7,k2_relat_1(sK6))))) = k7_relat_1(sK7,k2_relat_1(sK6)) ),
% 38.46/5.53      inference(instantiation,[status(thm)],[c_17]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_1945,plain,
% 38.46/5.53      ( k5_relat_1(sK6,k5_relat_1(X0,X1)) = k5_relat_1(k5_relat_1(sK6,X0),X1)
% 38.46/5.53      | v1_relat_1(X0) != iProver_top
% 38.46/5.53      | v1_relat_1(X1) != iProver_top ),
% 38.46/5.53      inference(superposition,[status(thm)],[c_685,c_689]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_2837,plain,
% 38.46/5.53      ( k5_relat_1(k5_relat_1(sK6,k6_relat_1(X0)),X1) = k5_relat_1(sK6,k5_relat_1(k6_relat_1(X0),X1))
% 38.46/5.53      | v1_relat_1(X1) != iProver_top ),
% 38.46/5.53      inference(superposition,[status(thm)],[c_693,c_1945]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_4723,plain,
% 38.46/5.53      ( k5_relat_1(sK6,k5_relat_1(k6_relat_1(X0),sK7)) = k5_relat_1(k5_relat_1(sK6,k6_relat_1(X0)),sK7) ),
% 38.46/5.53      inference(superposition,[status(thm)],[c_686,c_2837]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_4729,plain,
% 38.46/5.53      ( k5_relat_1(k5_relat_1(sK6,k6_relat_1(X0)),sK7) = k5_relat_1(sK6,k7_relat_1(sK7,X0)) ),
% 38.46/5.53      inference(light_normalisation,[status(thm)],[c_4723,c_1224]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_5669,plain,
% 38.46/5.53      ( k5_relat_1(sK6,k7_relat_1(sK7,k2_relat_1(sK6))) = k5_relat_1(sK6,sK7) ),
% 38.46/5.53      inference(superposition,[status(thm)],[c_970,c_4729]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_14,plain,
% 38.46/5.53      ( ~ v1_relat_1(X0)
% 38.46/5.53      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 38.46/5.53      inference(cnf_transformation,[],[f54]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_1802,plain,
% 38.46/5.53      ( ~ v1_relat_1(sK7)
% 38.46/5.53      | k2_relat_1(k7_relat_1(sK7,k2_relat_1(sK6))) = k9_relat_1(sK7,k2_relat_1(sK6)) ),
% 38.46/5.53      inference(instantiation,[status(thm)],[c_14]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_1564,plain,
% 38.46/5.53      ( k9_relat_1(sK7,k2_relat_1(sK6)) != k9_relat_1(sK7,k2_relat_1(sK6))
% 38.46/5.53      | k9_relat_1(sK7,k2_relat_1(sK6)) = k2_relat_1(X0)
% 38.46/5.53      | k2_relat_1(X0) != k9_relat_1(sK7,k2_relat_1(sK6)) ),
% 38.46/5.53      inference(instantiation,[status(thm)],[c_1196]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_1801,plain,
% 38.46/5.53      ( k9_relat_1(sK7,k2_relat_1(sK6)) != k9_relat_1(sK7,k2_relat_1(sK6))
% 38.46/5.53      | k9_relat_1(sK7,k2_relat_1(sK6)) = k2_relat_1(k7_relat_1(sK7,k2_relat_1(sK6)))
% 38.46/5.53      | k2_relat_1(k7_relat_1(sK7,k2_relat_1(sK6))) != k9_relat_1(sK7,k2_relat_1(sK6)) ),
% 38.46/5.53      inference(instantiation,[status(thm)],[c_1564]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_292,plain,( X0 = X0 ),theory(equality) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_1571,plain,
% 38.46/5.53      ( k5_relat_1(sK6,sK7) = k5_relat_1(sK6,sK7) ),
% 38.46/5.53      inference(instantiation,[status(thm)],[c_292]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_1565,plain,
% 38.46/5.53      ( k9_relat_1(sK7,k2_relat_1(sK6)) = k9_relat_1(sK7,k2_relat_1(sK6)) ),
% 38.46/5.53      inference(instantiation,[status(thm)],[c_292]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_1024,plain,
% 38.46/5.53      ( k2_relat_1(k5_relat_1(sK6,sK7)) = k2_relat_1(k5_relat_1(sK6,sK7)) ),
% 38.46/5.53      inference(instantiation,[status(thm)],[c_292]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_904,plain,
% 38.46/5.53      ( k9_relat_1(sK7,k2_relat_1(sK6)) != X0
% 38.46/5.53      | k2_relat_1(k5_relat_1(sK6,sK7)) != X0
% 38.46/5.53      | k2_relat_1(k5_relat_1(sK6,sK7)) = k9_relat_1(sK7,k2_relat_1(sK6)) ),
% 38.46/5.53      inference(instantiation,[status(thm)],[c_293]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_1023,plain,
% 38.46/5.53      ( k9_relat_1(sK7,k2_relat_1(sK6)) != k2_relat_1(k5_relat_1(sK6,sK7))
% 38.46/5.53      | k2_relat_1(k5_relat_1(sK6,sK7)) = k9_relat_1(sK7,k2_relat_1(sK6))
% 38.46/5.53      | k2_relat_1(k5_relat_1(sK6,sK7)) != k2_relat_1(k5_relat_1(sK6,sK7)) ),
% 38.46/5.53      inference(instantiation,[status(thm)],[c_904]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_311,plain,
% 38.46/5.53      ( sK6 = sK6 ),
% 38.46/5.53      inference(instantiation,[status(thm)],[c_292]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_19,negated_conjecture,
% 38.46/5.53      ( k2_relat_1(k5_relat_1(sK6,sK7)) != k9_relat_1(sK7,k2_relat_1(sK6)) ),
% 38.46/5.53      inference(cnf_transformation,[],[f61]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_23,plain,
% 38.46/5.53      ( v1_relat_1(sK7) = iProver_top ),
% 38.46/5.53      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(c_22,plain,
% 38.46/5.53      ( v1_relat_1(sK6) = iProver_top ),
% 38.46/5.53      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 38.46/5.53  
% 38.46/5.53  cnf(contradiction,plain,
% 38.46/5.53      ( $false ),
% 38.46/5.53      inference(minisat,
% 38.46/5.53                [status(thm)],
% 38.46/5.53                [c_122687,c_121471,c_110866,c_107621,c_68298,c_37311,
% 38.46/5.53                 c_37309,c_17415,c_7743,c_7742,c_7270,c_7268,c_5948,
% 38.46/5.53                 c_5669,c_1802,c_1801,c_1571,c_1565,c_1024,c_1023,c_311,
% 38.46/5.53                 c_19,c_23,c_20,c_22]) ).
% 38.46/5.53  
% 38.46/5.53  
% 38.46/5.53  % SZS output end CNFRefutation for theBenchmark.p
% 38.46/5.53  
% 38.46/5.53  ------                               Statistics
% 38.46/5.53  
% 38.46/5.53  ------ Selected
% 38.46/5.53  
% 38.46/5.53  total_time:                             4.718
% 38.46/5.53  
%------------------------------------------------------------------------------
