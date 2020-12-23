%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0467+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:22 EST 2020

% Result     : Theorem 7.90s
% Output     : CNFRefutation 7.90s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 323 expanded)
%              Number of clauses        :   53 (  98 expanded)
%              Number of leaves         :    9 (  89 expanded)
%              Depth                    :   14
%              Number of atoms          :  434 (2226 expanded)
%              Number of equality atoms :   38 ( 198 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal clause size      :   17 (   5 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ? [X3,X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                      & ( ? [X5] :
                            ( r2_hidden(k4_tarski(X5,X4),X1)
                            & r2_hidden(k4_tarski(X3,X5),X0) )
                        | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
                & ( ! [X3,X4] :
                      ( ( r2_hidden(k4_tarski(X3,X4),X2)
                        | ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) ) )
                      & ( ? [X5] :
                            ( r2_hidden(k4_tarski(X5,X4),X1)
                            & r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ? [X3,X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                      & ( ? [X6] :
                            ( r2_hidden(k4_tarski(X6,X4),X1)
                            & r2_hidden(k4_tarski(X3,X6),X0) )
                        | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ? [X10] :
                            ( r2_hidden(k4_tarski(X10,X8),X1)
                            & r2_hidden(k4_tarski(X7,X10),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f9])).

fof(f13,plain,(
    ! [X8,X7,X1,X0] :
      ( ? [X10] :
          ( r2_hidden(k4_tarski(X10,X8),X1)
          & r2_hidden(k4_tarski(X7,X10),X0) )
     => ( r2_hidden(k4_tarski(sK3(X0,X1,X7,X8),X8),X1)
        & r2_hidden(k4_tarski(X7,sK3(X0,X1,X7,X8)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,X4),X1)
          & r2_hidden(k4_tarski(X3,X6),X0) )
     => ( r2_hidden(k4_tarski(sK2(X0,X1,X2),X4),X1)
        & r2_hidden(k4_tarski(X3,sK2(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ! [X5] :
                ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                | ~ r2_hidden(k4_tarski(X3,X5),X0) )
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ? [X6] :
                ( r2_hidden(k4_tarski(X6,X4),X1)
                & r2_hidden(k4_tarski(X3,X6),X0) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ! [X5] :
              ( ~ r2_hidden(k4_tarski(X5,sK1(X0,X1,X2)),X1)
              | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),X5),X0) )
          | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) )
        & ( ? [X6] :
              ( r2_hidden(k4_tarski(X6,sK1(X0,X1,X2)),X1)
              & r2_hidden(k4_tarski(sK0(X0,X1,X2),X6),X0) )
          | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ( ( ! [X5] :
                          ( ~ r2_hidden(k4_tarski(X5,sK1(X0,X1,X2)),X1)
                          | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),X5),X0) )
                      | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) )
                    & ( ( r2_hidden(k4_tarski(sK2(X0,X1,X2),sK1(X0,X1,X2)),X1)
                        & r2_hidden(k4_tarski(sK0(X0,X1,X2),sK2(X0,X1,X2)),X0) )
                      | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ( r2_hidden(k4_tarski(sK3(X0,X1,X7,X8),X8),X1)
                          & r2_hidden(k4_tarski(X7,sK3(X0,X1,X7,X8)),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f13,f12,f11])).

fof(f21,plain,(
    ! [X2,X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),X2)
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f30,plain,(
    ! [X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f21])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f7,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f6])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X2,X0,X5,X1] :
      ( k5_relat_1(X0,X1) = X2
      | ~ r2_hidden(k4_tarski(X5,sK1(X0,X1,X2)),X1)
      | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),X5),X0)
      | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f20,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f31,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f20])).

fof(f19,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK3(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f32,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK3(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f19])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK1(X0,X1,X2)),X1)
      | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK2(X0,X1,X2)),X0)
      | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f3,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( v1_relat_1(X2)
               => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k5_relat_1(X0,k5_relat_1(X1,X2)) != k5_relat_1(k5_relat_1(X0,X1),X2)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k5_relat_1(X0,k5_relat_1(X1,X2)) != k5_relat_1(k5_relat_1(X0,X1),X2)
          & v1_relat_1(X2) )
     => ( k5_relat_1(X0,k5_relat_1(X1,sK6)) != k5_relat_1(k5_relat_1(X0,X1),sK6)
        & v1_relat_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k5_relat_1(X0,k5_relat_1(X1,X2)) != k5_relat_1(k5_relat_1(X0,X1),X2)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
     => ( ? [X2] :
            ( k5_relat_1(X0,k5_relat_1(sK5,X2)) != k5_relat_1(k5_relat_1(X0,sK5),X2)
            & v1_relat_1(X2) )
        & v1_relat_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k5_relat_1(X0,k5_relat_1(X1,X2)) != k5_relat_1(k5_relat_1(X0,X1),X2)
                & v1_relat_1(X2) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k5_relat_1(k5_relat_1(sK4,X1),X2) != k5_relat_1(sK4,k5_relat_1(X1,X2))
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( k5_relat_1(k5_relat_1(sK4,sK5),sK6) != k5_relat_1(sK4,k5_relat_1(sK5,sK6))
    & v1_relat_1(sK6)
    & v1_relat_1(sK5)
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f8,f17,f16,f15])).

fof(f29,plain,(
    k5_relat_1(k5_relat_1(sK4,sK5),sK6) != k5_relat_1(sK4,k5_relat_1(sK5,sK6)) ),
    inference(cnf_transformation,[],[f18])).

fof(f28,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f18])).

fof(f27,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f18])).

fof(f26,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_3,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X3,X0),X4)
    | r2_hidden(k4_tarski(X3,X1),k5_relat_1(X4,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(k5_relat_1(X4,X2)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_119,plain,
    ( ~ r2_hidden(k4_tarski(X0_41,X1_41),X0_39)
    | ~ r2_hidden(k4_tarski(X2_41,X0_41),X1_39)
    | r2_hidden(k4_tarski(X2_41,X1_41),k5_relat_1(X1_39,X0_39))
    | ~ v1_relat_1(X0_39)
    | ~ v1_relat_1(X1_39)
    | ~ v1_relat_1(k5_relat_1(X1_39,X0_39)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_116,plain,
    ( ~ v1_relat_1(X0_39)
    | ~ v1_relat_1(X1_39)
    | v1_relat_1(k5_relat_1(X1_39,X0_39)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_180,plain,
    ( ~ v1_relat_1(X1_39)
    | ~ v1_relat_1(X0_39)
    | r2_hidden(k4_tarski(X2_41,X1_41),k5_relat_1(X1_39,X0_39))
    | ~ r2_hidden(k4_tarski(X2_41,X0_41),X1_39)
    | ~ r2_hidden(k4_tarski(X0_41,X1_41),X0_39) ),
    inference(global_propositional_subsumption,[status(thm)],[c_119,c_116])).

cnf(c_181,plain,
    ( ~ r2_hidden(k4_tarski(X0_41,X1_41),X0_39)
    | ~ r2_hidden(k4_tarski(X2_41,X0_41),X1_39)
    | r2_hidden(k4_tarski(X2_41,X1_41),k5_relat_1(X1_39,X0_39))
    | ~ v1_relat_1(X0_39)
    | ~ v1_relat_1(X1_39) ),
    inference(renaming,[status(thm)],[c_180])).

cnf(c_3597,plain,
    ( ~ r2_hidden(k4_tarski(X0_41,sK3(sK4,sK5,sK0(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6))),sK2(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6))))),X0_39)
    | r2_hidden(k4_tarski(X0_41,sK1(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6)))),k5_relat_1(X0_39,k5_relat_1(sK5,sK6)))
    | ~ r2_hidden(k4_tarski(sK3(sK4,sK5,sK0(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6))),sK2(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6)))),sK1(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6)))),k5_relat_1(sK5,sK6))
    | ~ v1_relat_1(X0_39)
    | ~ v1_relat_1(k5_relat_1(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_181])).

cnf(c_35708,plain,
    ( ~ r2_hidden(k4_tarski(sK3(sK4,sK5,sK0(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6))),sK2(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6)))),sK1(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6)))),k5_relat_1(sK5,sK6))
    | ~ r2_hidden(k4_tarski(sK0(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6))),sK3(sK4,sK5,sK0(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6))),sK2(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6))))),sK4)
    | r2_hidden(k4_tarski(sK0(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6))),sK1(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6)))),k5_relat_1(sK4,k5_relat_1(sK5,sK6)))
    | ~ v1_relat_1(k5_relat_1(sK5,sK6))
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_3597])).

cnf(c_0,plain,
    ( ~ r2_hidden(k4_tarski(X0,sK1(X1,X2,X3)),X2)
    | ~ r2_hidden(k4_tarski(sK0(X1,X2,X3),X0),X1)
    | ~ r2_hidden(k4_tarski(sK0(X1,X2,X3),sK1(X1,X2,X3)),X3)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | k5_relat_1(X1,X2) = X3 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_122,plain,
    ( ~ r2_hidden(k4_tarski(X0_41,sK1(X0_39,X1_39,X2_39)),X1_39)
    | ~ r2_hidden(k4_tarski(sK0(X0_39,X1_39,X2_39),X0_41),X0_39)
    | ~ r2_hidden(k4_tarski(sK0(X0_39,X1_39,X2_39),sK1(X0_39,X1_39,X2_39)),X2_39)
    | ~ v1_relat_1(X0_39)
    | ~ v1_relat_1(X1_39)
    | ~ v1_relat_1(X2_39)
    | k5_relat_1(X0_39,X1_39) = X2_39 ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_28536,plain,
    ( ~ r2_hidden(k4_tarski(sK3(k5_relat_1(sK4,sK5),sK6,sK0(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6))),sK1(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6)))),sK1(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6)))),sK6)
    | ~ r2_hidden(k4_tarski(sK0(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6))),sK3(k5_relat_1(sK4,sK5),sK6,sK0(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6))),sK1(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6))))),k5_relat_1(sK4,sK5))
    | ~ r2_hidden(k4_tarski(sK0(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6))),sK1(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6)))),k5_relat_1(sK4,k5_relat_1(sK5,sK6)))
    | ~ v1_relat_1(k5_relat_1(sK4,k5_relat_1(sK5,sK6)))
    | ~ v1_relat_1(k5_relat_1(sK4,sK5))
    | ~ v1_relat_1(sK6)
    | k5_relat_1(k5_relat_1(sK4,sK5),sK6) = k5_relat_1(sK4,k5_relat_1(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_122])).

cnf(c_3608,plain,
    ( ~ r2_hidden(k4_tarski(X0_41,X1_41),X0_39)
    | r2_hidden(k4_tarski(X0_41,X2_41),k5_relat_1(X0_39,sK6))
    | ~ r2_hidden(k4_tarski(X1_41,X2_41),sK6)
    | ~ v1_relat_1(X0_39)
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_181])).

cnf(c_9224,plain,
    ( ~ r2_hidden(k4_tarski(X0_41,sK3(sK5,sK6,sK3(sK4,k5_relat_1(sK5,sK6),sK0(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6))),sK1(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6)))),sK1(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6))))),X0_39)
    | r2_hidden(k4_tarski(X0_41,sK1(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6)))),k5_relat_1(X0_39,sK6))
    | ~ r2_hidden(k4_tarski(sK3(sK5,sK6,sK3(sK4,k5_relat_1(sK5,sK6),sK0(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6))),sK1(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6)))),sK1(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6)))),sK1(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6)))),sK6)
    | ~ v1_relat_1(X0_39)
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_3608])).

cnf(c_26911,plain,
    ( ~ r2_hidden(k4_tarski(sK3(sK5,sK6,sK3(sK4,k5_relat_1(sK5,sK6),sK0(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6))),sK1(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6)))),sK1(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6)))),sK1(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6)))),sK6)
    | ~ r2_hidden(k4_tarski(sK0(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6))),sK3(sK5,sK6,sK3(sK4,k5_relat_1(sK5,sK6),sK0(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6))),sK1(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6)))),sK1(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6))))),k5_relat_1(sK4,sK5))
    | r2_hidden(k4_tarski(sK0(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6))),sK1(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6)))),k5_relat_1(k5_relat_1(sK4,sK5),sK6))
    | ~ v1_relat_1(k5_relat_1(sK4,sK5))
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_9224])).

cnf(c_4633,plain,
    ( r2_hidden(k4_tarski(X0_41,sK3(sK5,sK6,sK3(sK4,k5_relat_1(sK5,sK6),sK0(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6))),sK1(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6)))),sK1(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6))))),k5_relat_1(X0_39,sK5))
    | ~ r2_hidden(k4_tarski(X0_41,sK3(sK4,k5_relat_1(sK5,sK6),sK0(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6))),sK1(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6))))),X0_39)
    | ~ r2_hidden(k4_tarski(sK3(sK4,k5_relat_1(sK5,sK6),sK0(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6))),sK1(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6)))),sK3(sK5,sK6,sK3(sK4,k5_relat_1(sK5,sK6),sK0(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6))),sK1(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6)))),sK1(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6))))),sK5)
    | ~ v1_relat_1(X0_39)
    | ~ v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_181])).

cnf(c_18320,plain,
    ( ~ r2_hidden(k4_tarski(sK3(sK4,k5_relat_1(sK5,sK6),sK0(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6))),sK1(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6)))),sK3(sK5,sK6,sK3(sK4,k5_relat_1(sK5,sK6),sK0(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6))),sK1(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6)))),sK1(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6))))),sK5)
    | r2_hidden(k4_tarski(sK0(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6))),sK3(sK5,sK6,sK3(sK4,k5_relat_1(sK5,sK6),sK0(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6))),sK1(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6)))),sK1(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6))))),k5_relat_1(sK4,sK5))
    | ~ r2_hidden(k4_tarski(sK0(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6))),sK3(sK4,k5_relat_1(sK5,sK6),sK0(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6))),sK1(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6))))),sK4)
    | ~ v1_relat_1(sK5)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_4633])).

cnf(c_4,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
    | r2_hidden(k4_tarski(sK3(X2,X3,X0,X1),X1),X3)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(k5_relat_1(X2,X3)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_118,plain,
    ( ~ r2_hidden(k4_tarski(X0_41,X1_41),k5_relat_1(X0_39,X1_39))
    | r2_hidden(k4_tarski(sK3(X0_39,X1_39,X0_41,X1_41),X1_41),X1_39)
    | ~ v1_relat_1(X0_39)
    | ~ v1_relat_1(X1_39)
    | ~ v1_relat_1(k5_relat_1(X0_39,X1_39)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_669,plain,
    ( r2_hidden(k4_tarski(sK3(X0_39,X1_39,sK0(X2_39,X3_39,X4_39),sK1(X2_39,X3_39,X4_39)),sK1(X2_39,X3_39,X4_39)),X1_39)
    | ~ r2_hidden(k4_tarski(sK0(X2_39,X3_39,X4_39),sK1(X2_39,X3_39,X4_39)),k5_relat_1(X0_39,X1_39))
    | ~ v1_relat_1(X0_39)
    | ~ v1_relat_1(X1_39)
    | ~ v1_relat_1(k5_relat_1(X0_39,X1_39)) ),
    inference(instantiation,[status(thm)],[c_118])).

cnf(c_3582,plain,
    ( r2_hidden(k4_tarski(sK3(k5_relat_1(sK4,sK5),sK6,sK0(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6))),sK1(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6)))),sK1(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6)))),sK6)
    | ~ r2_hidden(k4_tarski(sK0(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6))),sK1(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6)))),k5_relat_1(k5_relat_1(sK4,sK5),sK6))
    | ~ v1_relat_1(k5_relat_1(k5_relat_1(sK4,sK5),sK6))
    | ~ v1_relat_1(k5_relat_1(sK4,sK5))
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_669])).

cnf(c_5,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
    | r2_hidden(k4_tarski(X0,sK3(X2,X3,X0,X1)),X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(k5_relat_1(X2,X3)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_117,plain,
    ( ~ r2_hidden(k4_tarski(X0_41,X1_41),k5_relat_1(X0_39,X1_39))
    | r2_hidden(k4_tarski(X0_41,sK3(X0_39,X1_39,X0_41,X1_41)),X0_39)
    | ~ v1_relat_1(X0_39)
    | ~ v1_relat_1(X1_39)
    | ~ v1_relat_1(k5_relat_1(X0_39,X1_39)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_670,plain,
    ( r2_hidden(k4_tarski(sK0(X0_39,X1_39,X2_39),sK3(X3_39,X4_39,sK0(X0_39,X1_39,X2_39),sK1(X0_39,X1_39,X2_39))),X3_39)
    | ~ r2_hidden(k4_tarski(sK0(X0_39,X1_39,X2_39),sK1(X0_39,X1_39,X2_39)),k5_relat_1(X3_39,X4_39))
    | ~ v1_relat_1(X3_39)
    | ~ v1_relat_1(X4_39)
    | ~ v1_relat_1(k5_relat_1(X3_39,X4_39)) ),
    inference(instantiation,[status(thm)],[c_117])).

cnf(c_3579,plain,
    ( r2_hidden(k4_tarski(sK0(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6))),sK3(k5_relat_1(sK4,sK5),sK6,sK0(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6))),sK1(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6))))),k5_relat_1(sK4,sK5))
    | ~ r2_hidden(k4_tarski(sK0(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6))),sK1(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6)))),k5_relat_1(k5_relat_1(sK4,sK5),sK6))
    | ~ v1_relat_1(k5_relat_1(k5_relat_1(sK4,sK5),sK6))
    | ~ v1_relat_1(k5_relat_1(sK4,sK5))
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_670])).

cnf(c_694,plain,
    ( ~ r2_hidden(k4_tarski(X0_41,sK2(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6)))),X0_39)
    | r2_hidden(k4_tarski(X0_41,sK1(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6)))),k5_relat_1(X0_39,sK6))
    | ~ r2_hidden(k4_tarski(sK2(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6))),sK1(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6)))),sK6)
    | ~ v1_relat_1(X0_39)
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_181])).

cnf(c_3186,plain,
    ( ~ r2_hidden(k4_tarski(sK3(sK4,sK5,sK0(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6))),sK2(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6)))),sK2(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6)))),sK5)
    | r2_hidden(k4_tarski(sK3(sK4,sK5,sK0(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6))),sK2(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6)))),sK1(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6)))),k5_relat_1(sK5,sK6))
    | ~ r2_hidden(k4_tarski(sK2(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6))),sK1(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6)))),sK6)
    | ~ v1_relat_1(sK6)
    | ~ v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_694])).

cnf(c_3183,plain,
    ( ~ r2_hidden(k4_tarski(sK2(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6))),sK1(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6)))),sK6)
    | ~ r2_hidden(k4_tarski(sK0(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6))),sK2(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6)))),k5_relat_1(sK4,sK5))
    | r2_hidden(k4_tarski(sK0(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6))),sK1(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6)))),k5_relat_1(k5_relat_1(sK4,sK5),sK6))
    | ~ v1_relat_1(k5_relat_1(sK4,sK5))
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_694])).

cnf(c_1929,plain,
    ( r2_hidden(k4_tarski(sK3(sK5,sK6,sK3(sK4,k5_relat_1(sK5,sK6),sK0(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6))),sK1(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6)))),sK1(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6)))),sK1(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6)))),sK6)
    | ~ r2_hidden(k4_tarski(sK3(sK4,k5_relat_1(sK5,sK6),sK0(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6))),sK1(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6)))),sK1(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6)))),k5_relat_1(sK5,sK6))
    | ~ v1_relat_1(k5_relat_1(sK5,sK6))
    | ~ v1_relat_1(sK6)
    | ~ v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_118])).

cnf(c_1930,plain,
    ( r2_hidden(k4_tarski(sK3(sK4,k5_relat_1(sK5,sK6),sK0(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6))),sK1(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6)))),sK3(sK5,sK6,sK3(sK4,k5_relat_1(sK5,sK6),sK0(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6))),sK1(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6)))),sK1(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6))))),sK5)
    | ~ r2_hidden(k4_tarski(sK3(sK4,k5_relat_1(sK5,sK6),sK0(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6))),sK1(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6)))),sK1(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6)))),k5_relat_1(sK5,sK6))
    | ~ v1_relat_1(k5_relat_1(sK5,sK6))
    | ~ v1_relat_1(sK6)
    | ~ v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_117])).

cnf(c_1051,plain,
    ( v1_relat_1(k5_relat_1(k5_relat_1(sK4,sK5),sK6))
    | ~ v1_relat_1(k5_relat_1(sK4,sK5))
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_116])).

cnf(c_451,plain,
    ( r2_hidden(k4_tarski(sK3(X0_39,X1_39,sK0(X2_39,X3_39,k5_relat_1(X0_39,X1_39)),sK1(X2_39,X3_39,k5_relat_1(X0_39,X1_39))),sK1(X2_39,X3_39,k5_relat_1(X0_39,X1_39))),X1_39)
    | ~ r2_hidden(k4_tarski(sK0(X2_39,X3_39,k5_relat_1(X0_39,X1_39)),sK1(X2_39,X3_39,k5_relat_1(X0_39,X1_39))),k5_relat_1(X0_39,X1_39))
    | ~ v1_relat_1(X1_39)
    | ~ v1_relat_1(X0_39)
    | ~ v1_relat_1(k5_relat_1(X0_39,X1_39)) ),
    inference(instantiation,[status(thm)],[c_118])).

cnf(c_989,plain,
    ( r2_hidden(k4_tarski(sK3(sK4,k5_relat_1(sK5,sK6),sK0(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6))),sK1(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6)))),sK1(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6)))),k5_relat_1(sK5,sK6))
    | ~ r2_hidden(k4_tarski(sK0(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6))),sK1(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6)))),k5_relat_1(sK4,k5_relat_1(sK5,sK6)))
    | ~ v1_relat_1(k5_relat_1(sK5,sK6))
    | ~ v1_relat_1(k5_relat_1(sK4,k5_relat_1(sK5,sK6)))
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_451])).

cnf(c_452,plain,
    ( r2_hidden(k4_tarski(sK0(X0_39,X1_39,k5_relat_1(X2_39,X3_39)),sK3(X2_39,X3_39,sK0(X0_39,X1_39,k5_relat_1(X2_39,X3_39)),sK1(X0_39,X1_39,k5_relat_1(X2_39,X3_39)))),X2_39)
    | ~ r2_hidden(k4_tarski(sK0(X0_39,X1_39,k5_relat_1(X2_39,X3_39)),sK1(X0_39,X1_39,k5_relat_1(X2_39,X3_39))),k5_relat_1(X2_39,X3_39))
    | ~ v1_relat_1(X3_39)
    | ~ v1_relat_1(X2_39)
    | ~ v1_relat_1(k5_relat_1(X2_39,X3_39)) ),
    inference(instantiation,[status(thm)],[c_117])).

cnf(c_986,plain,
    ( r2_hidden(k4_tarski(sK0(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6))),sK3(sK4,k5_relat_1(sK5,sK6),sK0(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6))),sK1(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6))))),sK4)
    | ~ r2_hidden(k4_tarski(sK0(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6))),sK1(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6)))),k5_relat_1(sK4,k5_relat_1(sK5,sK6)))
    | ~ v1_relat_1(k5_relat_1(sK5,sK6))
    | ~ v1_relat_1(k5_relat_1(sK4,k5_relat_1(sK5,sK6)))
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_452])).

cnf(c_808,plain,
    ( v1_relat_1(k5_relat_1(sK5,sK6))
    | ~ v1_relat_1(sK6)
    | ~ v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_116])).

cnf(c_797,plain,
    ( ~ v1_relat_1(k5_relat_1(sK5,sK6))
    | v1_relat_1(k5_relat_1(sK4,k5_relat_1(sK5,sK6)))
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_116])).

cnf(c_1,plain,
    ( r2_hidden(k4_tarski(sK2(X0,X1,X2),sK1(X0,X1,X2)),X1)
    | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_121,plain,
    ( r2_hidden(k4_tarski(sK2(X0_39,X1_39,X2_39),sK1(X0_39,X1_39,X2_39)),X1_39)
    | r2_hidden(k4_tarski(sK0(X0_39,X1_39,X2_39),sK1(X0_39,X1_39,X2_39)),X2_39)
    | ~ v1_relat_1(X0_39)
    | ~ v1_relat_1(X1_39)
    | ~ v1_relat_1(X2_39)
    | k5_relat_1(X0_39,X1_39) = X2_39 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_514,plain,
    ( r2_hidden(k4_tarski(sK2(X0_39,X1_39,k5_relat_1(X2_39,X3_39)),sK1(X0_39,X1_39,k5_relat_1(X2_39,X3_39))),X1_39)
    | r2_hidden(k4_tarski(sK0(X0_39,X1_39,k5_relat_1(X2_39,X3_39)),sK1(X0_39,X1_39,k5_relat_1(X2_39,X3_39))),k5_relat_1(X2_39,X3_39))
    | ~ v1_relat_1(X0_39)
    | ~ v1_relat_1(X1_39)
    | ~ v1_relat_1(k5_relat_1(X2_39,X3_39))
    | k5_relat_1(X0_39,X1_39) = k5_relat_1(X2_39,X3_39) ),
    inference(instantiation,[status(thm)],[c_121])).

cnf(c_651,plain,
    ( r2_hidden(k4_tarski(sK2(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6))),sK1(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6)))),sK6)
    | r2_hidden(k4_tarski(sK0(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6))),sK1(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6)))),k5_relat_1(sK4,k5_relat_1(sK5,sK6)))
    | ~ v1_relat_1(k5_relat_1(sK4,k5_relat_1(sK5,sK6)))
    | ~ v1_relat_1(k5_relat_1(sK4,sK5))
    | ~ v1_relat_1(sK6)
    | k5_relat_1(k5_relat_1(sK4,sK5),sK6) = k5_relat_1(sK4,k5_relat_1(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_514])).

cnf(c_563,plain,
    ( v1_relat_1(k5_relat_1(sK4,sK5))
    | ~ v1_relat_1(sK5)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_116])).

cnf(c_522,plain,
    ( r2_hidden(k4_tarski(sK3(sK4,sK5,sK0(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6))),sK2(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6)))),sK2(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6)))),sK5)
    | ~ r2_hidden(k4_tarski(sK0(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6))),sK2(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6)))),k5_relat_1(sK4,sK5))
    | ~ v1_relat_1(k5_relat_1(sK4,sK5))
    | ~ v1_relat_1(sK5)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_118])).

cnf(c_523,plain,
    ( r2_hidden(k4_tarski(sK0(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6))),sK3(sK4,sK5,sK0(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6))),sK2(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6))))),sK4)
    | ~ r2_hidden(k4_tarski(sK0(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6))),sK2(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6)))),k5_relat_1(sK4,sK5))
    | ~ v1_relat_1(k5_relat_1(sK4,sK5))
    | ~ v1_relat_1(sK5)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_117])).

cnf(c_2,plain,
    ( r2_hidden(k4_tarski(sK0(X0,X1,X2),sK2(X0,X1,X2)),X0)
    | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_120,plain,
    ( r2_hidden(k4_tarski(sK0(X0_39,X1_39,X2_39),sK2(X0_39,X1_39,X2_39)),X0_39)
    | r2_hidden(k4_tarski(sK0(X0_39,X1_39,X2_39),sK1(X0_39,X1_39,X2_39)),X2_39)
    | ~ v1_relat_1(X0_39)
    | ~ v1_relat_1(X1_39)
    | ~ v1_relat_1(X2_39)
    | k5_relat_1(X0_39,X1_39) = X2_39 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_450,plain,
    ( r2_hidden(k4_tarski(sK0(X0_39,X1_39,k5_relat_1(X2_39,X3_39)),sK2(X0_39,X1_39,k5_relat_1(X2_39,X3_39))),X0_39)
    | r2_hidden(k4_tarski(sK0(X0_39,X1_39,k5_relat_1(X2_39,X3_39)),sK1(X0_39,X1_39,k5_relat_1(X2_39,X3_39))),k5_relat_1(X2_39,X3_39))
    | ~ v1_relat_1(X0_39)
    | ~ v1_relat_1(X1_39)
    | ~ v1_relat_1(k5_relat_1(X2_39,X3_39))
    | k5_relat_1(X0_39,X1_39) = k5_relat_1(X2_39,X3_39) ),
    inference(instantiation,[status(thm)],[c_120])).

cnf(c_509,plain,
    ( r2_hidden(k4_tarski(sK0(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6))),sK2(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6)))),k5_relat_1(sK4,sK5))
    | r2_hidden(k4_tarski(sK0(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6))),sK1(k5_relat_1(sK4,sK5),sK6,k5_relat_1(sK4,k5_relat_1(sK5,sK6)))),k5_relat_1(sK4,k5_relat_1(sK5,sK6)))
    | ~ v1_relat_1(k5_relat_1(sK4,k5_relat_1(sK5,sK6)))
    | ~ v1_relat_1(k5_relat_1(sK4,sK5))
    | ~ v1_relat_1(sK6)
    | k5_relat_1(k5_relat_1(sK4,sK5),sK6) = k5_relat_1(sK4,k5_relat_1(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_450])).

cnf(c_7,negated_conjecture,
    ( k5_relat_1(k5_relat_1(sK4,sK5),sK6) != k5_relat_1(sK4,k5_relat_1(sK5,sK6)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_115,negated_conjecture,
    ( k5_relat_1(k5_relat_1(sK4,sK5),sK6) != k5_relat_1(sK4,k5_relat_1(sK5,sK6)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_8,negated_conjecture,
    ( v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_9,negated_conjecture,
    ( v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_10,negated_conjecture,
    ( v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f26])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_35708,c_28536,c_26911,c_18320,c_3582,c_3579,c_3186,c_3183,c_1929,c_1930,c_1051,c_989,c_986,c_808,c_797,c_651,c_563,c_522,c_523,c_509,c_115,c_8,c_9,c_10])).


%------------------------------------------------------------------------------
