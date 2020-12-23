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
% DateTime   : Thu Dec  3 11:54:34 EST 2020

% Result     : Theorem 2.72s
% Output     : CNFRefutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 776 expanded)
%              Number of clauses        :   63 ( 168 expanded)
%              Number of leaves         :   10 ( 278 expanded)
%              Depth                    :   20
%              Number of atoms          :  468 (6763 expanded)
%              Number of equality atoms :  130 (1575 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   24 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( r3_wellord1(X0,X1,X2)
              <=> ( ! [X3,X4] :
                      ( r2_hidden(k4_tarski(X3,X4),X0)
                    <=> ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                        & r2_hidden(X4,k3_relat_1(X0))
                        & r2_hidden(X3,k3_relat_1(X0)) ) )
                  & v2_funct_1(X2)
                  & k3_relat_1(X1) = k2_relat_1(X2)
                  & k1_relat_1(X2) = k3_relat_1(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_wellord1(X0,X1,X2)
              <=> ( ! [X3,X4] :
                      ( r2_hidden(k4_tarski(X3,X4),X0)
                    <=> ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                        & r2_hidden(X4,k3_relat_1(X0))
                        & r2_hidden(X3,k3_relat_1(X0)) ) )
                  & v2_funct_1(X2)
                  & k3_relat_1(X1) = k2_relat_1(X2)
                  & k1_relat_1(X2) = k3_relat_1(X0) ) )
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_wellord1(X0,X1,X2)
              <=> ( ! [X3,X4] :
                      ( r2_hidden(k4_tarski(X3,X4),X0)
                    <=> ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                        & r2_hidden(X4,k3_relat_1(X0))
                        & r2_hidden(X3,k3_relat_1(X0)) ) )
                  & v2_funct_1(X2)
                  & k3_relat_1(X1) = k2_relat_1(X2)
                  & k1_relat_1(X2) = k3_relat_1(X0) ) )
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f12,plain,(
    ! [X0,X2,X1] :
      ( ( r3_wellord1(X0,X1,X2)
      <=> sP0(X1,X2,X0) )
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f11,plain,(
    ! [X1,X2,X0] :
      ( sP0(X1,X2,X0)
    <=> ( ! [X3,X4] :
            ( r2_hidden(k4_tarski(X3,X4),X0)
          <=> ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
              & r2_hidden(X4,k3_relat_1(X0))
              & r2_hidden(X3,k3_relat_1(X0)) ) )
        & v2_funct_1(X2)
        & k3_relat_1(X1) = k2_relat_1(X2)
        & k1_relat_1(X2) = k3_relat_1(X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X0,X2,X1)
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f8,f12,f11])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X2,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,plain,(
    ! [X0,X2,X1] :
      ( ( ( r3_wellord1(X0,X1,X2)
          | ~ sP0(X1,X2,X0) )
        & ( sP0(X1,X2,X0)
          | ~ r3_wellord1(X0,X1,X2) ) )
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_wellord1(X0,X2,X1)
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | ~ r3_wellord1(X0,X2,X1) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f14])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,X0)
      | ~ r3_wellord1(X0,X2,X1)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f3,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( r3_wellord1(X0,X1,X2)
               => ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X0)
                   => ( ( k1_funct_1(X2,X3) != k1_funct_1(X2,X4)
                        & r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) )
                      | X3 = X4 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v1_relat_1(X2) )
               => ( r3_wellord1(X0,X1,X2)
                 => ! [X3,X4] :
                      ( r2_hidden(k4_tarski(X3,X4),X0)
                     => ( ( k1_funct_1(X2,X3) != k1_funct_1(X2,X4)
                          & r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) )
                        | X3 = X4 ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3,X4] :
                  ( ( k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
                    | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) )
                  & X3 != X4
                  & r2_hidden(k4_tarski(X3,X4),X0) )
              & r3_wellord1(X0,X1,X2)
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3,X4] :
                  ( ( k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
                    | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) )
                  & X3 != X4
                  & r2_hidden(k4_tarski(X3,X4),X0) )
              & r3_wellord1(X0,X1,X2)
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ? [X3,X4] :
          ( ( k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
            | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) )
          & X3 != X4
          & r2_hidden(k4_tarski(X3,X4),X0) )
     => ( ( k1_funct_1(X2,sK7) = k1_funct_1(X2,sK8)
          | ~ r2_hidden(k4_tarski(k1_funct_1(X2,sK7),k1_funct_1(X2,sK8)),X1) )
        & sK7 != sK8
        & r2_hidden(k4_tarski(sK7,sK8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3,X4] :
              ( ( k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
                | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) )
              & X3 != X4
              & r2_hidden(k4_tarski(X3,X4),X0) )
          & r3_wellord1(X0,X1,X2)
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( ? [X4,X3] :
            ( ( k1_funct_1(sK6,X3) = k1_funct_1(sK6,X4)
              | ~ r2_hidden(k4_tarski(k1_funct_1(sK6,X3),k1_funct_1(sK6,X4)),X1) )
            & X3 != X4
            & r2_hidden(k4_tarski(X3,X4),X0) )
        & r3_wellord1(X0,X1,sK6)
        & v1_funct_1(sK6)
        & v1_relat_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3,X4] :
                  ( ( k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
                    | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) )
                  & X3 != X4
                  & r2_hidden(k4_tarski(X3,X4),X0) )
              & r3_wellord1(X0,X1,X2)
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
     => ( ? [X2] :
            ( ? [X4,X3] :
                ( ( k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
                  | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),sK5) )
                & X3 != X4
                & r2_hidden(k4_tarski(X3,X4),X0) )
            & r3_wellord1(X0,sK5,X2)
            & v1_funct_1(X2)
            & v1_relat_1(X2) )
        & v1_relat_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3,X4] :
                    ( ( k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
                      | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) )
                    & X3 != X4
                    & r2_hidden(k4_tarski(X3,X4),X0) )
                & r3_wellord1(X0,X1,X2)
                & v1_funct_1(X2)
                & v1_relat_1(X2) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X4,X3] :
                  ( ( k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
                    | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) )
                  & X3 != X4
                  & r2_hidden(k4_tarski(X3,X4),sK4) )
              & r3_wellord1(sK4,X1,X2)
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ( k1_funct_1(sK6,sK7) = k1_funct_1(sK6,sK8)
      | ~ r2_hidden(k4_tarski(k1_funct_1(sK6,sK7),k1_funct_1(sK6,sK8)),sK5) )
    & sK7 != sK8
    & r2_hidden(k4_tarski(sK7,sK8),sK4)
    & r3_wellord1(sK4,sK5,sK6)
    & v1_funct_1(sK6)
    & v1_relat_1(sK6)
    & v1_relat_1(sK5)
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f10,f24,f23,f22,f21])).

fof(f46,plain,(
    r3_wellord1(sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f25])).

fof(f42,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f25])).

fof(f43,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f25])).

fof(f44,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f25])).

fof(f45,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f25])).

fof(f16,plain,(
    ! [X1,X2,X0] :
      ( ( sP0(X1,X2,X0)
        | ? [X3,X4] :
            ( ( ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
              | ~ r2_hidden(X4,k3_relat_1(X0))
              | ~ r2_hidden(X3,k3_relat_1(X0))
              | ~ r2_hidden(k4_tarski(X3,X4),X0) )
            & ( ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                & r2_hidden(X4,k3_relat_1(X0))
                & r2_hidden(X3,k3_relat_1(X0)) )
              | r2_hidden(k4_tarski(X3,X4),X0) ) )
        | ~ v2_funct_1(X2)
        | k3_relat_1(X1) != k2_relat_1(X2)
        | k1_relat_1(X2) != k3_relat_1(X0) )
      & ( ( ! [X3,X4] :
              ( ( r2_hidden(k4_tarski(X3,X4),X0)
                | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                | ~ r2_hidden(X4,k3_relat_1(X0))
                | ~ r2_hidden(X3,k3_relat_1(X0)) )
              & ( ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                  & r2_hidden(X4,k3_relat_1(X0))
                  & r2_hidden(X3,k3_relat_1(X0)) )
                | ~ r2_hidden(k4_tarski(X3,X4),X0) ) )
          & v2_funct_1(X2)
          & k3_relat_1(X1) = k2_relat_1(X2)
          & k1_relat_1(X2) = k3_relat_1(X0) )
        | ~ sP0(X1,X2,X0) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f17,plain,(
    ! [X1,X2,X0] :
      ( ( sP0(X1,X2,X0)
        | ? [X3,X4] :
            ( ( ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
              | ~ r2_hidden(X4,k3_relat_1(X0))
              | ~ r2_hidden(X3,k3_relat_1(X0))
              | ~ r2_hidden(k4_tarski(X3,X4),X0) )
            & ( ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                & r2_hidden(X4,k3_relat_1(X0))
                & r2_hidden(X3,k3_relat_1(X0)) )
              | r2_hidden(k4_tarski(X3,X4),X0) ) )
        | ~ v2_funct_1(X2)
        | k3_relat_1(X1) != k2_relat_1(X2)
        | k1_relat_1(X2) != k3_relat_1(X0) )
      & ( ( ! [X3,X4] :
              ( ( r2_hidden(k4_tarski(X3,X4),X0)
                | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                | ~ r2_hidden(X4,k3_relat_1(X0))
                | ~ r2_hidden(X3,k3_relat_1(X0)) )
              & ( ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                  & r2_hidden(X4,k3_relat_1(X0))
                  & r2_hidden(X3,k3_relat_1(X0)) )
                | ~ r2_hidden(k4_tarski(X3,X4),X0) ) )
          & v2_funct_1(X2)
          & k3_relat_1(X1) = k2_relat_1(X2)
          & k1_relat_1(X2) = k3_relat_1(X0) )
        | ~ sP0(X1,X2,X0) ) ) ),
    inference(flattening,[],[f16])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3,X4] :
            ( ( ~ r2_hidden(k4_tarski(k1_funct_1(X1,X3),k1_funct_1(X1,X4)),X0)
              | ~ r2_hidden(X4,k3_relat_1(X2))
              | ~ r2_hidden(X3,k3_relat_1(X2))
              | ~ r2_hidden(k4_tarski(X3,X4),X2) )
            & ( ( r2_hidden(k4_tarski(k1_funct_1(X1,X3),k1_funct_1(X1,X4)),X0)
                & r2_hidden(X4,k3_relat_1(X2))
                & r2_hidden(X3,k3_relat_1(X2)) )
              | r2_hidden(k4_tarski(X3,X4),X2) ) )
        | ~ v2_funct_1(X1)
        | k3_relat_1(X0) != k2_relat_1(X1)
        | k1_relat_1(X1) != k3_relat_1(X2) )
      & ( ( ! [X5,X6] :
              ( ( r2_hidden(k4_tarski(X5,X6),X2)
                | ~ r2_hidden(k4_tarski(k1_funct_1(X1,X5),k1_funct_1(X1,X6)),X0)
                | ~ r2_hidden(X6,k3_relat_1(X2))
                | ~ r2_hidden(X5,k3_relat_1(X2)) )
              & ( ( r2_hidden(k4_tarski(k1_funct_1(X1,X5),k1_funct_1(X1,X6)),X0)
                  & r2_hidden(X6,k3_relat_1(X2))
                  & r2_hidden(X5,k3_relat_1(X2)) )
                | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
          & v2_funct_1(X1)
          & k3_relat_1(X0) = k2_relat_1(X1)
          & k1_relat_1(X1) = k3_relat_1(X2) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f17])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(k1_funct_1(X1,X3),k1_funct_1(X1,X4)),X0)
            | ~ r2_hidden(X4,k3_relat_1(X2))
            | ~ r2_hidden(X3,k3_relat_1(X2))
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(k1_funct_1(X1,X3),k1_funct_1(X1,X4)),X0)
              & r2_hidden(X4,k3_relat_1(X2))
              & r2_hidden(X3,k3_relat_1(X2)) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(k1_funct_1(X1,sK2(X0,X1,X2)),k1_funct_1(X1,sK3(X0,X1,X2))),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),k3_relat_1(X2))
          | ~ r2_hidden(sK2(X0,X1,X2),k3_relat_1(X2))
          | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(k1_funct_1(X1,sK2(X0,X1,X2)),k1_funct_1(X1,sK3(X0,X1,X2))),X0)
            & r2_hidden(sK3(X0,X1,X2),k3_relat_1(X2))
            & r2_hidden(sK2(X0,X1,X2),k3_relat_1(X2)) )
          | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ~ r2_hidden(k4_tarski(k1_funct_1(X1,sK2(X0,X1,X2)),k1_funct_1(X1,sK3(X0,X1,X2))),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),k3_relat_1(X2))
            | ~ r2_hidden(sK2(X0,X1,X2),k3_relat_1(X2))
            | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) )
          & ( ( r2_hidden(k4_tarski(k1_funct_1(X1,sK2(X0,X1,X2)),k1_funct_1(X1,sK3(X0,X1,X2))),X0)
              & r2_hidden(sK3(X0,X1,X2),k3_relat_1(X2))
              & r2_hidden(sK2(X0,X1,X2),k3_relat_1(X2)) )
            | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) ) )
        | ~ v2_funct_1(X1)
        | k3_relat_1(X0) != k2_relat_1(X1)
        | k1_relat_1(X1) != k3_relat_1(X2) )
      & ( ( ! [X5,X6] :
              ( ( r2_hidden(k4_tarski(X5,X6),X2)
                | ~ r2_hidden(k4_tarski(k1_funct_1(X1,X5),k1_funct_1(X1,X6)),X0)
                | ~ r2_hidden(X6,k3_relat_1(X2))
                | ~ r2_hidden(X5,k3_relat_1(X2)) )
              & ( ( r2_hidden(k4_tarski(k1_funct_1(X1,X5),k1_funct_1(X1,X6)),X0)
                  & r2_hidden(X6,k3_relat_1(X2))
                  & r2_hidden(X5,k3_relat_1(X2)) )
                | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
          & v2_funct_1(X1)
          & k3_relat_1(X0) = k2_relat_1(X1)
          & k1_relat_1(X1) = k3_relat_1(X2) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f18,f19])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X1) = k3_relat_1(X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f47,plain,(
    r2_hidden(k4_tarski(sK7,sK8),sK4) ),
    inference(cnf_transformation,[],[f25])).

fof(f33,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(X5,k3_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X1)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k1_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
          & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f6,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f5])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f34,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(X6,k3_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f35,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(k1_funct_1(X1,X5),k1_funct_1(X1,X6)),X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f49,plain,
    ( k1_funct_1(sK6,sK7) = k1_funct_1(sK6,sK8)
    | ~ r2_hidden(k4_tarski(k1_funct_1(sK6,sK7),k1_funct_1(sK6,sK8)),sK5) ),
    inference(cnf_transformation,[],[f25])).

fof(f48,plain,(
    sK7 != sK8 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_15,plain,
    ( sP1(X0,X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_3,plain,
    ( ~ sP1(X0,X1,X2)
    | sP0(X2,X1,X0)
    | ~ r3_wellord1(X0,X2,X1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_19,negated_conjecture,
    ( r3_wellord1(sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_253,plain,
    ( ~ sP1(X0,X1,X2)
    | sP0(X2,X1,X0)
    | sK4 != X0
    | sK5 != X2
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_19])).

cnf(c_254,plain,
    ( ~ sP1(sK4,sK6,sK5)
    | sP0(sK5,sK6,sK4) ),
    inference(unflattening,[status(thm)],[c_253])).

cnf(c_266,plain,
    ( sP0(sK5,sK6,sK4)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X1)
    | sK4 != X0
    | sK5 != X2
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_254])).

cnf(c_267,plain,
    ( sP0(sK5,sK6,sK4)
    | ~ v1_relat_1(sK4)
    | ~ v1_relat_1(sK5)
    | ~ v1_relat_1(sK6)
    | ~ v1_funct_1(sK6) ),
    inference(unflattening,[status(thm)],[c_266])).

cnf(c_23,negated_conjecture,
    ( v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_22,negated_conjecture,
    ( v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_21,negated_conjecture,
    ( v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_269,plain,
    ( sP0(sK5,sK6,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_267,c_23,c_22,c_21,c_20])).

cnf(c_2420,plain,
    ( sP0(sK5,sK6,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_269])).

cnf(c_14,plain,
    ( ~ sP0(X0,X1,X2)
    | k3_relat_1(X2) = k1_relat_1(X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_2423,plain,
    ( k3_relat_1(X0) = k1_relat_1(X1)
    | sP0(X2,X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2774,plain,
    ( k3_relat_1(sK4) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_2420,c_2423])).

cnf(c_18,negated_conjecture,
    ( r2_hidden(k4_tarski(sK7,sK8),sK4) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2421,plain,
    ( r2_hidden(k4_tarski(sK7,sK8),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_11,plain,
    ( ~ sP0(X0,X1,X2)
    | r2_hidden(X3,k3_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X4),X2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_2426,plain,
    ( sP0(X0,X1,X2) != iProver_top
    | r2_hidden(X3,k3_relat_1(X2)) = iProver_top
    | r2_hidden(k4_tarski(X3,X4),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2767,plain,
    ( sP0(X0,X1,sK4) != iProver_top
    | r2_hidden(sK7,k3_relat_1(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2421,c_2426])).

cnf(c_24,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_25,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_26,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_27,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_29,plain,
    ( r2_hidden(k4_tarski(sK7,sK8),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_268,plain,
    ( sP0(sK5,sK6,sK4) = iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_relat_1(sK6) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_267])).

cnf(c_2592,plain,
    ( ~ sP0(sK5,sK6,sK4)
    | r2_hidden(X0,k3_relat_1(sK4))
    | ~ r2_hidden(k4_tarski(X0,X1),sK4) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2657,plain,
    ( ~ sP0(sK5,sK6,sK4)
    | ~ r2_hidden(k4_tarski(sK7,sK8),sK4)
    | r2_hidden(sK7,k3_relat_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_2592])).

cnf(c_2658,plain,
    ( sP0(sK5,sK6,sK4) != iProver_top
    | r2_hidden(k4_tarski(sK7,sK8),sK4) != iProver_top
    | r2_hidden(sK7,k3_relat_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2657])).

cnf(c_2914,plain,
    ( r2_hidden(sK7,k3_relat_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2767,c_24,c_25,c_26,c_27,c_29,c_268,c_2658])).

cnf(c_3642,plain,
    ( r2_hidden(sK7,k1_relat_1(sK6)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2774,c_2914])).

cnf(c_12,plain,
    ( ~ sP0(X0,X1,X2)
    | v2_funct_1(X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_959,plain,
    ( v2_funct_1(X0)
    | sK4 != X1
    | sK5 != X2
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_269])).

cnf(c_960,plain,
    ( v2_funct_1(sK6) ),
    inference(unflattening,[status(thm)],[c_959])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_279,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v2_funct_1(X1)
    | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_20])).

cnf(c_280,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK6))
    | ~ v1_relat_1(sK6)
    | ~ v2_funct_1(sK6)
    | k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_279])).

cnf(c_284,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK6))
    | ~ v2_funct_1(sK6)
    | k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_280,c_21])).

cnf(c_1139,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK6))
    | k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,X0)) = X0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_960,c_284])).

cnf(c_2418,plain,
    ( k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,X0)) = X0
    | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1139])).

cnf(c_3952,plain,
    ( k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,sK7)) = sK7 ),
    inference(superposition,[status(thm)],[c_3642,c_2418])).

cnf(c_10,plain,
    ( ~ sP0(X0,X1,X2)
    | r2_hidden(X3,k3_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X4,X3),X2) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_2427,plain,
    ( sP0(X0,X1,X2) != iProver_top
    | r2_hidden(X3,k3_relat_1(X2)) = iProver_top
    | r2_hidden(k4_tarski(X4,X3),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2822,plain,
    ( sP0(X0,X1,sK4) != iProver_top
    | r2_hidden(sK8,k3_relat_1(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2421,c_2427])).

cnf(c_2589,plain,
    ( ~ sP0(sK5,sK6,sK4)
    | r2_hidden(X0,k3_relat_1(sK4))
    | ~ r2_hidden(k4_tarski(X1,X0),sK4) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2654,plain,
    ( ~ sP0(sK5,sK6,sK4)
    | ~ r2_hidden(k4_tarski(sK7,sK8),sK4)
    | r2_hidden(sK8,k3_relat_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_2589])).

cnf(c_2655,plain,
    ( sP0(sK5,sK6,sK4) != iProver_top
    | r2_hidden(k4_tarski(sK7,sK8),sK4) != iProver_top
    | r2_hidden(sK8,k3_relat_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2654])).

cnf(c_2954,plain,
    ( r2_hidden(sK8,k3_relat_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2822,c_24,c_25,c_26,c_27,c_29,c_268,c_2655])).

cnf(c_3641,plain,
    ( r2_hidden(sK8,k1_relat_1(sK6)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2774,c_2954])).

cnf(c_3881,plain,
    ( k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,sK8)) = sK8 ),
    inference(superposition,[status(thm)],[c_3641,c_2418])).

cnf(c_9,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X4),X2)
    | r2_hidden(k4_tarski(k1_funct_1(X1,X3),k1_funct_1(X1,X4)),X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_2428,plain,
    ( sP0(X0,X1,X2) != iProver_top
    | r2_hidden(k4_tarski(X3,X4),X2) != iProver_top
    | r2_hidden(k4_tarski(k1_funct_1(X1,X3),k1_funct_1(X1,X4)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2909,plain,
    ( sP0(X0,X1,sK4) != iProver_top
    | r2_hidden(k4_tarski(k1_funct_1(X1,sK7),k1_funct_1(X1,sK8)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2421,c_2428])).

cnf(c_16,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(k1_funct_1(sK6,sK7),k1_funct_1(sK6,sK8)),sK5)
    | k1_funct_1(sK6,sK7) = k1_funct_1(sK6,sK8) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2422,plain,
    ( k1_funct_1(sK6,sK7) = k1_funct_1(sK6,sK8)
    | r2_hidden(k4_tarski(k1_funct_1(sK6,sK7),k1_funct_1(sK6,sK8)),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2965,plain,
    ( k1_funct_1(sK6,sK8) = k1_funct_1(sK6,sK7)
    | sP0(sK5,sK6,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2909,c_2422])).

cnf(c_3043,plain,
    ( k1_funct_1(sK6,sK8) = k1_funct_1(sK6,sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2965,c_24,c_25,c_26,c_27,c_268])).

cnf(c_3883,plain,
    ( k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,sK7)) = sK8 ),
    inference(light_normalisation,[status(thm)],[c_3881,c_3043])).

cnf(c_4221,plain,
    ( sK8 = sK7 ),
    inference(demodulation,[status(thm)],[c_3952,c_3883])).

cnf(c_17,negated_conjecture,
    ( sK7 != sK8 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_4324,plain,
    ( sK7 != sK7 ),
    inference(demodulation,[status(thm)],[c_4221,c_17])).

cnf(c_4325,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_4324])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:58:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.72/0.97  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.72/0.97  
% 2.72/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.72/0.97  
% 2.72/0.97  ------  iProver source info
% 2.72/0.97  
% 2.72/0.97  git: date: 2020-06-30 10:37:57 +0100
% 2.72/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.72/0.97  git: non_committed_changes: false
% 2.72/0.97  git: last_make_outside_of_git: false
% 2.72/0.97  
% 2.72/0.97  ------ 
% 2.72/0.97  
% 2.72/0.97  ------ Input Options
% 2.72/0.97  
% 2.72/0.97  --out_options                           all
% 2.72/0.97  --tptp_safe_out                         true
% 2.72/0.97  --problem_path                          ""
% 2.72/0.97  --include_path                          ""
% 2.72/0.97  --clausifier                            res/vclausify_rel
% 2.72/0.97  --clausifier_options                    --mode clausify
% 2.72/0.97  --stdin                                 false
% 2.72/0.97  --stats_out                             all
% 2.72/0.97  
% 2.72/0.97  ------ General Options
% 2.72/0.97  
% 2.72/0.97  --fof                                   false
% 2.72/0.97  --time_out_real                         305.
% 2.72/0.97  --time_out_virtual                      -1.
% 2.72/0.97  --symbol_type_check                     false
% 2.72/0.97  --clausify_out                          false
% 2.72/0.97  --sig_cnt_out                           false
% 2.72/0.97  --trig_cnt_out                          false
% 2.72/0.97  --trig_cnt_out_tolerance                1.
% 2.72/0.97  --trig_cnt_out_sk_spl                   false
% 2.72/0.97  --abstr_cl_out                          false
% 2.72/0.97  
% 2.72/0.97  ------ Global Options
% 2.72/0.97  
% 2.72/0.97  --schedule                              default
% 2.72/0.97  --add_important_lit                     false
% 2.72/0.97  --prop_solver_per_cl                    1000
% 2.72/0.97  --min_unsat_core                        false
% 2.72/0.97  --soft_assumptions                      false
% 2.72/0.97  --soft_lemma_size                       3
% 2.72/0.97  --prop_impl_unit_size                   0
% 2.72/0.97  --prop_impl_unit                        []
% 2.72/0.97  --share_sel_clauses                     true
% 2.72/0.97  --reset_solvers                         false
% 2.72/0.97  --bc_imp_inh                            [conj_cone]
% 2.72/0.97  --conj_cone_tolerance                   3.
% 2.72/0.97  --extra_neg_conj                        none
% 2.72/0.97  --large_theory_mode                     true
% 2.72/0.97  --prolific_symb_bound                   200
% 2.72/0.97  --lt_threshold                          2000
% 2.72/0.97  --clause_weak_htbl                      true
% 2.72/0.97  --gc_record_bc_elim                     false
% 2.72/0.97  
% 2.72/0.97  ------ Preprocessing Options
% 2.72/0.97  
% 2.72/0.97  --preprocessing_flag                    true
% 2.72/0.97  --time_out_prep_mult                    0.1
% 2.72/0.97  --splitting_mode                        input
% 2.72/0.97  --splitting_grd                         true
% 2.72/0.97  --splitting_cvd                         false
% 2.72/0.97  --splitting_cvd_svl                     false
% 2.72/0.97  --splitting_nvd                         32
% 2.72/0.97  --sub_typing                            true
% 2.72/0.97  --prep_gs_sim                           true
% 2.72/0.97  --prep_unflatten                        true
% 2.72/0.97  --prep_res_sim                          true
% 2.72/0.97  --prep_upred                            true
% 2.72/0.97  --prep_sem_filter                       exhaustive
% 2.72/0.97  --prep_sem_filter_out                   false
% 2.72/0.97  --pred_elim                             true
% 2.72/0.97  --res_sim_input                         true
% 2.72/0.97  --eq_ax_congr_red                       true
% 2.72/0.97  --pure_diseq_elim                       true
% 2.72/0.97  --brand_transform                       false
% 2.72/0.97  --non_eq_to_eq                          false
% 2.72/0.97  --prep_def_merge                        true
% 2.72/0.97  --prep_def_merge_prop_impl              false
% 2.72/0.97  --prep_def_merge_mbd                    true
% 2.72/0.97  --prep_def_merge_tr_red                 false
% 2.72/0.97  --prep_def_merge_tr_cl                  false
% 2.72/0.97  --smt_preprocessing                     true
% 2.72/0.97  --smt_ac_axioms                         fast
% 2.72/0.97  --preprocessed_out                      false
% 2.72/0.97  --preprocessed_stats                    false
% 2.72/0.97  
% 2.72/0.97  ------ Abstraction refinement Options
% 2.72/0.97  
% 2.72/0.97  --abstr_ref                             []
% 2.72/0.97  --abstr_ref_prep                        false
% 2.72/0.97  --abstr_ref_until_sat                   false
% 2.72/0.97  --abstr_ref_sig_restrict                funpre
% 2.72/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.72/0.97  --abstr_ref_under                       []
% 2.72/0.97  
% 2.72/0.97  ------ SAT Options
% 2.72/0.97  
% 2.72/0.97  --sat_mode                              false
% 2.72/0.97  --sat_fm_restart_options                ""
% 2.72/0.97  --sat_gr_def                            false
% 2.72/0.97  --sat_epr_types                         true
% 2.72/0.97  --sat_non_cyclic_types                  false
% 2.72/0.97  --sat_finite_models                     false
% 2.72/0.97  --sat_fm_lemmas                         false
% 2.72/0.97  --sat_fm_prep                           false
% 2.72/0.97  --sat_fm_uc_incr                        true
% 2.72/0.97  --sat_out_model                         small
% 2.72/0.97  --sat_out_clauses                       false
% 2.72/0.97  
% 2.72/0.97  ------ QBF Options
% 2.72/0.97  
% 2.72/0.97  --qbf_mode                              false
% 2.72/0.97  --qbf_elim_univ                         false
% 2.72/0.97  --qbf_dom_inst                          none
% 2.72/0.97  --qbf_dom_pre_inst                      false
% 2.72/0.97  --qbf_sk_in                             false
% 2.72/0.97  --qbf_pred_elim                         true
% 2.72/0.97  --qbf_split                             512
% 2.72/0.97  
% 2.72/0.97  ------ BMC1 Options
% 2.72/0.97  
% 2.72/0.97  --bmc1_incremental                      false
% 2.72/0.97  --bmc1_axioms                           reachable_all
% 2.72/0.97  --bmc1_min_bound                        0
% 2.72/0.97  --bmc1_max_bound                        -1
% 2.72/0.97  --bmc1_max_bound_default                -1
% 2.72/0.97  --bmc1_symbol_reachability              true
% 2.72/0.97  --bmc1_property_lemmas                  false
% 2.72/0.97  --bmc1_k_induction                      false
% 2.72/0.97  --bmc1_non_equiv_states                 false
% 2.72/0.97  --bmc1_deadlock                         false
% 2.72/0.97  --bmc1_ucm                              false
% 2.72/0.97  --bmc1_add_unsat_core                   none
% 2.72/0.97  --bmc1_unsat_core_children              false
% 2.72/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.72/0.97  --bmc1_out_stat                         full
% 2.72/0.97  --bmc1_ground_init                      false
% 2.72/0.97  --bmc1_pre_inst_next_state              false
% 2.72/0.97  --bmc1_pre_inst_state                   false
% 2.72/0.97  --bmc1_pre_inst_reach_state             false
% 2.72/0.97  --bmc1_out_unsat_core                   false
% 2.72/0.97  --bmc1_aig_witness_out                  false
% 2.72/0.97  --bmc1_verbose                          false
% 2.72/0.97  --bmc1_dump_clauses_tptp                false
% 2.72/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.72/0.97  --bmc1_dump_file                        -
% 2.72/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.72/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.72/0.97  --bmc1_ucm_extend_mode                  1
% 2.72/0.97  --bmc1_ucm_init_mode                    2
% 2.72/0.97  --bmc1_ucm_cone_mode                    none
% 2.72/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.72/0.97  --bmc1_ucm_relax_model                  4
% 2.72/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.72/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.72/0.97  --bmc1_ucm_layered_model                none
% 2.72/0.97  --bmc1_ucm_max_lemma_size               10
% 2.72/0.97  
% 2.72/0.97  ------ AIG Options
% 2.72/0.97  
% 2.72/0.97  --aig_mode                              false
% 2.72/0.97  
% 2.72/0.97  ------ Instantiation Options
% 2.72/0.97  
% 2.72/0.97  --instantiation_flag                    true
% 2.72/0.97  --inst_sos_flag                         false
% 2.72/0.97  --inst_sos_phase                        true
% 2.72/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.72/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.72/0.97  --inst_lit_sel_side                     num_symb
% 2.72/0.97  --inst_solver_per_active                1400
% 2.72/0.97  --inst_solver_calls_frac                1.
% 2.72/0.97  --inst_passive_queue_type               priority_queues
% 2.72/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.72/0.97  --inst_passive_queues_freq              [25;2]
% 2.72/0.97  --inst_dismatching                      true
% 2.72/0.97  --inst_eager_unprocessed_to_passive     true
% 2.72/0.97  --inst_prop_sim_given                   true
% 2.72/0.97  --inst_prop_sim_new                     false
% 2.72/0.97  --inst_subs_new                         false
% 2.72/0.97  --inst_eq_res_simp                      false
% 2.72/0.97  --inst_subs_given                       false
% 2.72/0.97  --inst_orphan_elimination               true
% 2.72/0.97  --inst_learning_loop_flag               true
% 2.72/0.97  --inst_learning_start                   3000
% 2.72/0.97  --inst_learning_factor                  2
% 2.72/0.97  --inst_start_prop_sim_after_learn       3
% 2.72/0.97  --inst_sel_renew                        solver
% 2.72/0.97  --inst_lit_activity_flag                true
% 2.72/0.97  --inst_restr_to_given                   false
% 2.72/0.97  --inst_activity_threshold               500
% 2.72/0.97  --inst_out_proof                        true
% 2.72/0.97  
% 2.72/0.97  ------ Resolution Options
% 2.72/0.97  
% 2.72/0.97  --resolution_flag                       true
% 2.72/0.97  --res_lit_sel                           adaptive
% 2.72/0.97  --res_lit_sel_side                      none
% 2.72/0.97  --res_ordering                          kbo
% 2.72/0.97  --res_to_prop_solver                    active
% 2.72/0.97  --res_prop_simpl_new                    false
% 2.72/0.97  --res_prop_simpl_given                  true
% 2.72/0.97  --res_passive_queue_type                priority_queues
% 2.72/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.72/0.97  --res_passive_queues_freq               [15;5]
% 2.72/0.97  --res_forward_subs                      full
% 2.72/0.97  --res_backward_subs                     full
% 2.72/0.97  --res_forward_subs_resolution           true
% 2.72/0.97  --res_backward_subs_resolution          true
% 2.72/0.97  --res_orphan_elimination                true
% 2.72/0.97  --res_time_limit                        2.
% 2.72/0.97  --res_out_proof                         true
% 2.72/0.97  
% 2.72/0.97  ------ Superposition Options
% 2.72/0.97  
% 2.72/0.97  --superposition_flag                    true
% 2.72/0.97  --sup_passive_queue_type                priority_queues
% 2.72/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.72/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.72/0.97  --demod_completeness_check              fast
% 2.72/0.97  --demod_use_ground                      true
% 2.72/0.97  --sup_to_prop_solver                    passive
% 2.72/0.97  --sup_prop_simpl_new                    true
% 2.72/0.97  --sup_prop_simpl_given                  true
% 2.72/0.97  --sup_fun_splitting                     false
% 2.72/0.97  --sup_smt_interval                      50000
% 2.72/0.97  
% 2.72/0.97  ------ Superposition Simplification Setup
% 2.72/0.97  
% 2.72/0.97  --sup_indices_passive                   []
% 2.72/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.72/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.72/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.72/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.72/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.72/0.97  --sup_full_bw                           [BwDemod]
% 2.72/0.97  --sup_immed_triv                        [TrivRules]
% 2.72/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.72/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.72/0.97  --sup_immed_bw_main                     []
% 2.72/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.72/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.72/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.72/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.72/0.97  
% 2.72/0.97  ------ Combination Options
% 2.72/0.97  
% 2.72/0.97  --comb_res_mult                         3
% 2.72/0.97  --comb_sup_mult                         2
% 2.72/0.97  --comb_inst_mult                        10
% 2.72/0.97  
% 2.72/0.97  ------ Debug Options
% 2.72/0.97  
% 2.72/0.97  --dbg_backtrace                         false
% 2.72/0.97  --dbg_dump_prop_clauses                 false
% 2.72/0.97  --dbg_dump_prop_clauses_file            -
% 2.72/0.97  --dbg_out_stat                          false
% 2.72/0.97  ------ Parsing...
% 2.72/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.72/0.97  
% 2.72/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.72/0.97  
% 2.72/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.72/0.97  
% 2.72/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.72/0.97  ------ Proving...
% 2.72/0.97  ------ Problem Properties 
% 2.72/0.97  
% 2.72/0.97  
% 2.72/0.97  clauses                                 17
% 2.72/0.97  conjectures                             3
% 2.72/0.97  EPR                                     3
% 2.72/0.97  Horn                                    14
% 2.72/0.97  unary                                   3
% 2.72/0.97  binary                                  6
% 2.72/0.97  lits                                    55
% 2.72/0.97  lits eq                                 14
% 2.72/0.97  fd_pure                                 0
% 2.72/0.97  fd_pseudo                               0
% 2.72/0.97  fd_cond                                 0
% 2.72/0.97  fd_pseudo_cond                          0
% 2.72/0.97  AC symbols                              0
% 2.72/0.97  
% 2.72/0.97  ------ Schedule dynamic 5 is on 
% 2.72/0.97  
% 2.72/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.72/0.97  
% 2.72/0.97  
% 2.72/0.97  ------ 
% 2.72/0.97  Current options:
% 2.72/0.97  ------ 
% 2.72/0.97  
% 2.72/0.97  ------ Input Options
% 2.72/0.97  
% 2.72/0.97  --out_options                           all
% 2.72/0.97  --tptp_safe_out                         true
% 2.72/0.97  --problem_path                          ""
% 2.72/0.97  --include_path                          ""
% 2.72/0.97  --clausifier                            res/vclausify_rel
% 2.72/0.97  --clausifier_options                    --mode clausify
% 2.72/0.97  --stdin                                 false
% 2.72/0.97  --stats_out                             all
% 2.72/0.97  
% 2.72/0.97  ------ General Options
% 2.72/0.97  
% 2.72/0.97  --fof                                   false
% 2.72/0.97  --time_out_real                         305.
% 2.72/0.97  --time_out_virtual                      -1.
% 2.72/0.97  --symbol_type_check                     false
% 2.72/0.97  --clausify_out                          false
% 2.72/0.97  --sig_cnt_out                           false
% 2.72/0.97  --trig_cnt_out                          false
% 2.72/0.97  --trig_cnt_out_tolerance                1.
% 2.72/0.97  --trig_cnt_out_sk_spl                   false
% 2.72/0.97  --abstr_cl_out                          false
% 2.72/0.97  
% 2.72/0.97  ------ Global Options
% 2.72/0.97  
% 2.72/0.97  --schedule                              default
% 2.72/0.97  --add_important_lit                     false
% 2.72/0.97  --prop_solver_per_cl                    1000
% 2.72/0.97  --min_unsat_core                        false
% 2.72/0.97  --soft_assumptions                      false
% 2.72/0.97  --soft_lemma_size                       3
% 2.72/0.97  --prop_impl_unit_size                   0
% 2.72/0.97  --prop_impl_unit                        []
% 2.72/0.97  --share_sel_clauses                     true
% 2.72/0.97  --reset_solvers                         false
% 2.72/0.97  --bc_imp_inh                            [conj_cone]
% 2.72/0.97  --conj_cone_tolerance                   3.
% 2.72/0.97  --extra_neg_conj                        none
% 2.72/0.97  --large_theory_mode                     true
% 2.72/0.97  --prolific_symb_bound                   200
% 2.72/0.97  --lt_threshold                          2000
% 2.72/0.97  --clause_weak_htbl                      true
% 2.72/0.97  --gc_record_bc_elim                     false
% 2.72/0.97  
% 2.72/0.97  ------ Preprocessing Options
% 2.72/0.97  
% 2.72/0.97  --preprocessing_flag                    true
% 2.72/0.97  --time_out_prep_mult                    0.1
% 2.72/0.97  --splitting_mode                        input
% 2.72/0.97  --splitting_grd                         true
% 2.72/0.97  --splitting_cvd                         false
% 2.72/0.97  --splitting_cvd_svl                     false
% 2.72/0.97  --splitting_nvd                         32
% 2.72/0.97  --sub_typing                            true
% 2.72/0.97  --prep_gs_sim                           true
% 2.72/0.97  --prep_unflatten                        true
% 2.72/0.97  --prep_res_sim                          true
% 2.72/0.97  --prep_upred                            true
% 2.72/0.97  --prep_sem_filter                       exhaustive
% 2.72/0.97  --prep_sem_filter_out                   false
% 2.72/0.97  --pred_elim                             true
% 2.72/0.97  --res_sim_input                         true
% 2.72/0.97  --eq_ax_congr_red                       true
% 2.72/0.97  --pure_diseq_elim                       true
% 2.72/0.97  --brand_transform                       false
% 2.72/0.97  --non_eq_to_eq                          false
% 2.72/0.97  --prep_def_merge                        true
% 2.72/0.97  --prep_def_merge_prop_impl              false
% 2.72/0.97  --prep_def_merge_mbd                    true
% 2.72/0.97  --prep_def_merge_tr_red                 false
% 2.72/0.97  --prep_def_merge_tr_cl                  false
% 2.72/0.97  --smt_preprocessing                     true
% 2.72/0.97  --smt_ac_axioms                         fast
% 2.72/0.97  --preprocessed_out                      false
% 2.72/0.97  --preprocessed_stats                    false
% 2.72/0.97  
% 2.72/0.97  ------ Abstraction refinement Options
% 2.72/0.97  
% 2.72/0.97  --abstr_ref                             []
% 2.72/0.97  --abstr_ref_prep                        false
% 2.72/0.97  --abstr_ref_until_sat                   false
% 2.72/0.97  --abstr_ref_sig_restrict                funpre
% 2.72/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.72/0.97  --abstr_ref_under                       []
% 2.72/0.97  
% 2.72/0.97  ------ SAT Options
% 2.72/0.97  
% 2.72/0.97  --sat_mode                              false
% 2.72/0.97  --sat_fm_restart_options                ""
% 2.72/0.97  --sat_gr_def                            false
% 2.72/0.97  --sat_epr_types                         true
% 2.72/0.97  --sat_non_cyclic_types                  false
% 2.72/0.97  --sat_finite_models                     false
% 2.72/0.97  --sat_fm_lemmas                         false
% 2.72/0.97  --sat_fm_prep                           false
% 2.72/0.97  --sat_fm_uc_incr                        true
% 2.72/0.97  --sat_out_model                         small
% 2.72/0.97  --sat_out_clauses                       false
% 2.72/0.97  
% 2.72/0.97  ------ QBF Options
% 2.72/0.97  
% 2.72/0.97  --qbf_mode                              false
% 2.72/0.97  --qbf_elim_univ                         false
% 2.72/0.97  --qbf_dom_inst                          none
% 2.72/0.97  --qbf_dom_pre_inst                      false
% 2.72/0.97  --qbf_sk_in                             false
% 2.72/0.97  --qbf_pred_elim                         true
% 2.72/0.97  --qbf_split                             512
% 2.72/0.97  
% 2.72/0.97  ------ BMC1 Options
% 2.72/0.97  
% 2.72/0.97  --bmc1_incremental                      false
% 2.72/0.97  --bmc1_axioms                           reachable_all
% 2.72/0.97  --bmc1_min_bound                        0
% 2.72/0.97  --bmc1_max_bound                        -1
% 2.72/0.97  --bmc1_max_bound_default                -1
% 2.72/0.97  --bmc1_symbol_reachability              true
% 2.72/0.97  --bmc1_property_lemmas                  false
% 2.72/0.97  --bmc1_k_induction                      false
% 2.72/0.97  --bmc1_non_equiv_states                 false
% 2.72/0.97  --bmc1_deadlock                         false
% 2.72/0.97  --bmc1_ucm                              false
% 2.72/0.97  --bmc1_add_unsat_core                   none
% 2.72/0.97  --bmc1_unsat_core_children              false
% 2.72/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.72/0.97  --bmc1_out_stat                         full
% 2.72/0.97  --bmc1_ground_init                      false
% 2.72/0.97  --bmc1_pre_inst_next_state              false
% 2.72/0.97  --bmc1_pre_inst_state                   false
% 2.72/0.97  --bmc1_pre_inst_reach_state             false
% 2.72/0.97  --bmc1_out_unsat_core                   false
% 2.72/0.97  --bmc1_aig_witness_out                  false
% 2.72/0.97  --bmc1_verbose                          false
% 2.72/0.97  --bmc1_dump_clauses_tptp                false
% 2.72/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.72/0.97  --bmc1_dump_file                        -
% 2.72/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.72/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.72/0.97  --bmc1_ucm_extend_mode                  1
% 2.72/0.97  --bmc1_ucm_init_mode                    2
% 2.72/0.97  --bmc1_ucm_cone_mode                    none
% 2.72/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.72/0.97  --bmc1_ucm_relax_model                  4
% 2.72/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.72/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.72/0.97  --bmc1_ucm_layered_model                none
% 2.72/0.97  --bmc1_ucm_max_lemma_size               10
% 2.72/0.97  
% 2.72/0.97  ------ AIG Options
% 2.72/0.97  
% 2.72/0.97  --aig_mode                              false
% 2.72/0.97  
% 2.72/0.97  ------ Instantiation Options
% 2.72/0.97  
% 2.72/0.97  --instantiation_flag                    true
% 2.72/0.97  --inst_sos_flag                         false
% 2.72/0.97  --inst_sos_phase                        true
% 2.72/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.72/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.72/0.97  --inst_lit_sel_side                     none
% 2.72/0.97  --inst_solver_per_active                1400
% 2.72/0.97  --inst_solver_calls_frac                1.
% 2.72/0.97  --inst_passive_queue_type               priority_queues
% 2.72/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.72/0.97  --inst_passive_queues_freq              [25;2]
% 2.72/0.97  --inst_dismatching                      true
% 2.72/0.97  --inst_eager_unprocessed_to_passive     true
% 2.72/0.97  --inst_prop_sim_given                   true
% 2.72/0.97  --inst_prop_sim_new                     false
% 2.72/0.97  --inst_subs_new                         false
% 2.72/0.97  --inst_eq_res_simp                      false
% 2.72/0.97  --inst_subs_given                       false
% 2.72/0.97  --inst_orphan_elimination               true
% 2.72/0.97  --inst_learning_loop_flag               true
% 2.72/0.97  --inst_learning_start                   3000
% 2.72/0.97  --inst_learning_factor                  2
% 2.72/0.97  --inst_start_prop_sim_after_learn       3
% 2.72/0.97  --inst_sel_renew                        solver
% 2.72/0.97  --inst_lit_activity_flag                true
% 2.72/0.97  --inst_restr_to_given                   false
% 2.72/0.97  --inst_activity_threshold               500
% 2.72/0.97  --inst_out_proof                        true
% 2.72/0.97  
% 2.72/0.97  ------ Resolution Options
% 2.72/0.97  
% 2.72/0.97  --resolution_flag                       false
% 2.72/0.97  --res_lit_sel                           adaptive
% 2.72/0.97  --res_lit_sel_side                      none
% 2.72/0.97  --res_ordering                          kbo
% 2.72/0.97  --res_to_prop_solver                    active
% 2.72/0.97  --res_prop_simpl_new                    false
% 2.72/0.97  --res_prop_simpl_given                  true
% 2.72/0.97  --res_passive_queue_type                priority_queues
% 2.72/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.72/0.97  --res_passive_queues_freq               [15;5]
% 2.72/0.97  --res_forward_subs                      full
% 2.72/0.97  --res_backward_subs                     full
% 2.72/0.97  --res_forward_subs_resolution           true
% 2.72/0.97  --res_backward_subs_resolution          true
% 2.72/0.97  --res_orphan_elimination                true
% 2.72/0.97  --res_time_limit                        2.
% 2.72/0.97  --res_out_proof                         true
% 2.72/0.97  
% 2.72/0.97  ------ Superposition Options
% 2.72/0.97  
% 2.72/0.97  --superposition_flag                    true
% 2.72/0.97  --sup_passive_queue_type                priority_queues
% 2.72/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.72/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.72/0.97  --demod_completeness_check              fast
% 2.72/0.97  --demod_use_ground                      true
% 2.72/0.97  --sup_to_prop_solver                    passive
% 2.72/0.97  --sup_prop_simpl_new                    true
% 2.72/0.97  --sup_prop_simpl_given                  true
% 2.72/0.97  --sup_fun_splitting                     false
% 2.72/0.97  --sup_smt_interval                      50000
% 2.72/0.97  
% 2.72/0.97  ------ Superposition Simplification Setup
% 2.72/0.97  
% 2.72/0.97  --sup_indices_passive                   []
% 2.72/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.72/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.72/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.72/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.72/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.72/0.97  --sup_full_bw                           [BwDemod]
% 2.72/0.97  --sup_immed_triv                        [TrivRules]
% 2.72/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.72/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.72/0.97  --sup_immed_bw_main                     []
% 2.72/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.72/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.72/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.72/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.72/0.97  
% 2.72/0.97  ------ Combination Options
% 2.72/0.97  
% 2.72/0.97  --comb_res_mult                         3
% 2.72/0.97  --comb_sup_mult                         2
% 2.72/0.97  --comb_inst_mult                        10
% 2.72/0.97  
% 2.72/0.97  ------ Debug Options
% 2.72/0.97  
% 2.72/0.97  --dbg_backtrace                         false
% 2.72/0.97  --dbg_dump_prop_clauses                 false
% 2.72/0.97  --dbg_dump_prop_clauses_file            -
% 2.72/0.97  --dbg_out_stat                          false
% 2.72/0.97  
% 2.72/0.97  
% 2.72/0.97  
% 2.72/0.97  
% 2.72/0.97  ------ Proving...
% 2.72/0.97  
% 2.72/0.97  
% 2.72/0.97  % SZS status Theorem for theBenchmark.p
% 2.72/0.97  
% 2.72/0.97   Resolution empty clause
% 2.72/0.97  
% 2.72/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 2.72/0.97  
% 2.72/0.97  fof(f2,axiom,(
% 2.72/0.97    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r3_wellord1(X0,X1,X2) <=> (! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X0) <=> (r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) & r2_hidden(X4,k3_relat_1(X0)) & r2_hidden(X3,k3_relat_1(X0)))) & v2_funct_1(X2) & k3_relat_1(X1) = k2_relat_1(X2) & k1_relat_1(X2) = k3_relat_1(X0))))))),
% 2.72/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.72/0.97  
% 2.72/0.97  fof(f7,plain,(
% 2.72/0.97    ! [X0] : (! [X1] : (! [X2] : ((r3_wellord1(X0,X1,X2) <=> (! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X0) <=> (r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) & r2_hidden(X4,k3_relat_1(X0)) & r2_hidden(X3,k3_relat_1(X0)))) & v2_funct_1(X2) & k3_relat_1(X1) = k2_relat_1(X2) & k1_relat_1(X2) = k3_relat_1(X0))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.72/0.97    inference(ennf_transformation,[],[f2])).
% 2.72/0.97  
% 2.72/0.97  fof(f8,plain,(
% 2.72/0.97    ! [X0] : (! [X1] : (! [X2] : ((r3_wellord1(X0,X1,X2) <=> (! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X0) <=> (r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) & r2_hidden(X4,k3_relat_1(X0)) & r2_hidden(X3,k3_relat_1(X0)))) & v2_funct_1(X2) & k3_relat_1(X1) = k2_relat_1(X2) & k1_relat_1(X2) = k3_relat_1(X0))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.72/0.97    inference(flattening,[],[f7])).
% 2.72/0.97  
% 2.72/0.97  fof(f12,plain,(
% 2.72/0.97    ! [X0,X2,X1] : ((r3_wellord1(X0,X1,X2) <=> sP0(X1,X2,X0)) | ~sP1(X0,X2,X1))),
% 2.72/0.97    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.72/0.97  
% 2.72/0.97  fof(f11,plain,(
% 2.72/0.97    ! [X1,X2,X0] : (sP0(X1,X2,X0) <=> (! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X0) <=> (r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) & r2_hidden(X4,k3_relat_1(X0)) & r2_hidden(X3,k3_relat_1(X0)))) & v2_funct_1(X2) & k3_relat_1(X1) = k2_relat_1(X2) & k1_relat_1(X2) = k3_relat_1(X0)))),
% 2.72/0.97    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.72/0.97  
% 2.72/0.97  fof(f13,plain,(
% 2.72/0.97    ! [X0] : (! [X1] : (! [X2] : (sP1(X0,X2,X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.72/0.97    inference(definition_folding,[],[f8,f12,f11])).
% 2.72/0.97  
% 2.72/0.97  fof(f41,plain,(
% 2.72/0.97    ( ! [X2,X0,X1] : (sP1(X0,X2,X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.72/0.97    inference(cnf_transformation,[],[f13])).
% 2.72/0.97  
% 2.72/0.97  fof(f14,plain,(
% 2.72/0.97    ! [X0,X2,X1] : (((r3_wellord1(X0,X1,X2) | ~sP0(X1,X2,X0)) & (sP0(X1,X2,X0) | ~r3_wellord1(X0,X1,X2))) | ~sP1(X0,X2,X1))),
% 2.72/0.97    inference(nnf_transformation,[],[f12])).
% 2.72/0.97  
% 2.72/0.97  fof(f15,plain,(
% 2.72/0.97    ! [X0,X1,X2] : (((r3_wellord1(X0,X2,X1) | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | ~r3_wellord1(X0,X2,X1))) | ~sP1(X0,X1,X2))),
% 2.72/0.97    inference(rectify,[],[f14])).
% 2.72/0.97  
% 2.72/0.97  fof(f28,plain,(
% 2.72/0.97    ( ! [X2,X0,X1] : (sP0(X2,X1,X0) | ~r3_wellord1(X0,X2,X1) | ~sP1(X0,X1,X2)) )),
% 2.72/0.97    inference(cnf_transformation,[],[f15])).
% 2.72/0.97  
% 2.72/0.97  fof(f3,conjecture,(
% 2.72/0.97    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r3_wellord1(X0,X1,X2) => ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X0) => ((k1_funct_1(X2,X3) != k1_funct_1(X2,X4) & r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)) | X3 = X4))))))),
% 2.72/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.72/0.97  
% 2.72/0.97  fof(f4,negated_conjecture,(
% 2.72/0.97    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r3_wellord1(X0,X1,X2) => ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X0) => ((k1_funct_1(X2,X3) != k1_funct_1(X2,X4) & r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)) | X3 = X4))))))),
% 2.72/0.97    inference(negated_conjecture,[],[f3])).
% 2.72/0.97  
% 2.72/0.97  fof(f9,plain,(
% 2.72/0.97    ? [X0] : (? [X1] : (? [X2] : ((? [X3,X4] : (((k1_funct_1(X2,X3) = k1_funct_1(X2,X4) | ~r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)) & X3 != X4) & r2_hidden(k4_tarski(X3,X4),X0)) & r3_wellord1(X0,X1,X2)) & (v1_funct_1(X2) & v1_relat_1(X2))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 2.72/0.97    inference(ennf_transformation,[],[f4])).
% 2.72/0.97  
% 2.72/0.97  fof(f10,plain,(
% 2.72/0.97    ? [X0] : (? [X1] : (? [X2] : (? [X3,X4] : ((k1_funct_1(X2,X3) = k1_funct_1(X2,X4) | ~r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)) & X3 != X4 & r2_hidden(k4_tarski(X3,X4),X0)) & r3_wellord1(X0,X1,X2) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 2.72/0.97    inference(flattening,[],[f9])).
% 2.72/0.97  
% 2.72/0.97  fof(f24,plain,(
% 2.72/0.97    ( ! [X2,X0,X1] : (? [X3,X4] : ((k1_funct_1(X2,X3) = k1_funct_1(X2,X4) | ~r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)) & X3 != X4 & r2_hidden(k4_tarski(X3,X4),X0)) => ((k1_funct_1(X2,sK7) = k1_funct_1(X2,sK8) | ~r2_hidden(k4_tarski(k1_funct_1(X2,sK7),k1_funct_1(X2,sK8)),X1)) & sK7 != sK8 & r2_hidden(k4_tarski(sK7,sK8),X0))) )),
% 2.72/0.97    introduced(choice_axiom,[])).
% 2.72/0.97  
% 2.72/0.97  fof(f23,plain,(
% 2.72/0.97    ( ! [X0,X1] : (? [X2] : (? [X3,X4] : ((k1_funct_1(X2,X3) = k1_funct_1(X2,X4) | ~r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)) & X3 != X4 & r2_hidden(k4_tarski(X3,X4),X0)) & r3_wellord1(X0,X1,X2) & v1_funct_1(X2) & v1_relat_1(X2)) => (? [X4,X3] : ((k1_funct_1(sK6,X3) = k1_funct_1(sK6,X4) | ~r2_hidden(k4_tarski(k1_funct_1(sK6,X3),k1_funct_1(sK6,X4)),X1)) & X3 != X4 & r2_hidden(k4_tarski(X3,X4),X0)) & r3_wellord1(X0,X1,sK6) & v1_funct_1(sK6) & v1_relat_1(sK6))) )),
% 2.72/0.97    introduced(choice_axiom,[])).
% 2.72/0.97  
% 2.72/0.97  fof(f22,plain,(
% 2.72/0.97    ( ! [X0] : (? [X1] : (? [X2] : (? [X3,X4] : ((k1_funct_1(X2,X3) = k1_funct_1(X2,X4) | ~r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)) & X3 != X4 & r2_hidden(k4_tarski(X3,X4),X0)) & r3_wellord1(X0,X1,X2) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (? [X4,X3] : ((k1_funct_1(X2,X3) = k1_funct_1(X2,X4) | ~r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),sK5)) & X3 != X4 & r2_hidden(k4_tarski(X3,X4),X0)) & r3_wellord1(X0,sK5,X2) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_relat_1(sK5))) )),
% 2.72/0.97    introduced(choice_axiom,[])).
% 2.72/0.97  
% 2.72/0.97  fof(f21,plain,(
% 2.72/0.97    ? [X0] : (? [X1] : (? [X2] : (? [X3,X4] : ((k1_funct_1(X2,X3) = k1_funct_1(X2,X4) | ~r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)) & X3 != X4 & r2_hidden(k4_tarski(X3,X4),X0)) & r3_wellord1(X0,X1,X2) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (? [X2] : (? [X4,X3] : ((k1_funct_1(X2,X3) = k1_funct_1(X2,X4) | ~r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)) & X3 != X4 & r2_hidden(k4_tarski(X3,X4),sK4)) & r3_wellord1(sK4,X1,X2) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(sK4))),
% 2.72/0.97    introduced(choice_axiom,[])).
% 2.72/0.97  
% 2.72/0.97  fof(f25,plain,(
% 2.72/0.97    ((((k1_funct_1(sK6,sK7) = k1_funct_1(sK6,sK8) | ~r2_hidden(k4_tarski(k1_funct_1(sK6,sK7),k1_funct_1(sK6,sK8)),sK5)) & sK7 != sK8 & r2_hidden(k4_tarski(sK7,sK8),sK4)) & r3_wellord1(sK4,sK5,sK6) & v1_funct_1(sK6) & v1_relat_1(sK6)) & v1_relat_1(sK5)) & v1_relat_1(sK4)),
% 2.72/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f10,f24,f23,f22,f21])).
% 2.72/0.97  
% 2.72/0.97  fof(f46,plain,(
% 2.72/0.97    r3_wellord1(sK4,sK5,sK6)),
% 2.72/0.97    inference(cnf_transformation,[],[f25])).
% 2.72/0.97  
% 2.72/0.97  fof(f42,plain,(
% 2.72/0.97    v1_relat_1(sK4)),
% 2.72/0.97    inference(cnf_transformation,[],[f25])).
% 2.72/0.97  
% 2.72/0.97  fof(f43,plain,(
% 2.72/0.97    v1_relat_1(sK5)),
% 2.72/0.97    inference(cnf_transformation,[],[f25])).
% 2.72/0.97  
% 2.72/0.97  fof(f44,plain,(
% 2.72/0.97    v1_relat_1(sK6)),
% 2.72/0.97    inference(cnf_transformation,[],[f25])).
% 2.72/0.97  
% 2.72/0.97  fof(f45,plain,(
% 2.72/0.97    v1_funct_1(sK6)),
% 2.72/0.97    inference(cnf_transformation,[],[f25])).
% 2.72/0.97  
% 2.72/0.97  fof(f16,plain,(
% 2.72/0.97    ! [X1,X2,X0] : ((sP0(X1,X2,X0) | (? [X3,X4] : (((~r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0))) | ~r2_hidden(k4_tarski(X3,X4),X0)) & ((r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) & r2_hidden(X4,k3_relat_1(X0)) & r2_hidden(X3,k3_relat_1(X0))) | r2_hidden(k4_tarski(X3,X4),X0))) | ~v2_funct_1(X2) | k3_relat_1(X1) != k2_relat_1(X2) | k1_relat_1(X2) != k3_relat_1(X0))) & ((! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X0) | (~r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0)))) & ((r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) & r2_hidden(X4,k3_relat_1(X0)) & r2_hidden(X3,k3_relat_1(X0))) | ~r2_hidden(k4_tarski(X3,X4),X0))) & v2_funct_1(X2) & k3_relat_1(X1) = k2_relat_1(X2) & k1_relat_1(X2) = k3_relat_1(X0)) | ~sP0(X1,X2,X0)))),
% 2.72/0.97    inference(nnf_transformation,[],[f11])).
% 2.72/0.97  
% 2.72/0.97  fof(f17,plain,(
% 2.72/0.97    ! [X1,X2,X0] : ((sP0(X1,X2,X0) | ? [X3,X4] : ((~r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0)) | ~r2_hidden(k4_tarski(X3,X4),X0)) & ((r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) & r2_hidden(X4,k3_relat_1(X0)) & r2_hidden(X3,k3_relat_1(X0))) | r2_hidden(k4_tarski(X3,X4),X0))) | ~v2_funct_1(X2) | k3_relat_1(X1) != k2_relat_1(X2) | k1_relat_1(X2) != k3_relat_1(X0)) & ((! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0))) & ((r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) & r2_hidden(X4,k3_relat_1(X0)) & r2_hidden(X3,k3_relat_1(X0))) | ~r2_hidden(k4_tarski(X3,X4),X0))) & v2_funct_1(X2) & k3_relat_1(X1) = k2_relat_1(X2) & k1_relat_1(X2) = k3_relat_1(X0)) | ~sP0(X1,X2,X0)))),
% 2.72/0.97    inference(flattening,[],[f16])).
% 2.72/0.97  
% 2.72/0.97  fof(f18,plain,(
% 2.72/0.97    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3,X4] : ((~r2_hidden(k4_tarski(k1_funct_1(X1,X3),k1_funct_1(X1,X4)),X0) | ~r2_hidden(X4,k3_relat_1(X2)) | ~r2_hidden(X3,k3_relat_1(X2)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(k1_funct_1(X1,X3),k1_funct_1(X1,X4)),X0) & r2_hidden(X4,k3_relat_1(X2)) & r2_hidden(X3,k3_relat_1(X2))) | r2_hidden(k4_tarski(X3,X4),X2))) | ~v2_funct_1(X1) | k3_relat_1(X0) != k2_relat_1(X1) | k1_relat_1(X1) != k3_relat_1(X2)) & ((! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(k1_funct_1(X1,X5),k1_funct_1(X1,X6)),X0) | ~r2_hidden(X6,k3_relat_1(X2)) | ~r2_hidden(X5,k3_relat_1(X2))) & ((r2_hidden(k4_tarski(k1_funct_1(X1,X5),k1_funct_1(X1,X6)),X0) & r2_hidden(X6,k3_relat_1(X2)) & r2_hidden(X5,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X5,X6),X2))) & v2_funct_1(X1) & k3_relat_1(X0) = k2_relat_1(X1) & k1_relat_1(X1) = k3_relat_1(X2)) | ~sP0(X0,X1,X2)))),
% 2.72/0.97    inference(rectify,[],[f17])).
% 2.72/0.97  
% 2.72/0.97  fof(f19,plain,(
% 2.72/0.97    ! [X2,X1,X0] : (? [X3,X4] : ((~r2_hidden(k4_tarski(k1_funct_1(X1,X3),k1_funct_1(X1,X4)),X0) | ~r2_hidden(X4,k3_relat_1(X2)) | ~r2_hidden(X3,k3_relat_1(X2)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(k1_funct_1(X1,X3),k1_funct_1(X1,X4)),X0) & r2_hidden(X4,k3_relat_1(X2)) & r2_hidden(X3,k3_relat_1(X2))) | r2_hidden(k4_tarski(X3,X4),X2))) => ((~r2_hidden(k4_tarski(k1_funct_1(X1,sK2(X0,X1,X2)),k1_funct_1(X1,sK3(X0,X1,X2))),X0) | ~r2_hidden(sK3(X0,X1,X2),k3_relat_1(X2)) | ~r2_hidden(sK2(X0,X1,X2),k3_relat_1(X2)) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(k1_funct_1(X1,sK2(X0,X1,X2)),k1_funct_1(X1,sK3(X0,X1,X2))),X0) & r2_hidden(sK3(X0,X1,X2),k3_relat_1(X2)) & r2_hidden(sK2(X0,X1,X2),k3_relat_1(X2))) | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2))))),
% 2.72/0.97    introduced(choice_axiom,[])).
% 2.72/0.97  
% 2.72/0.97  fof(f20,plain,(
% 2.72/0.97    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((~r2_hidden(k4_tarski(k1_funct_1(X1,sK2(X0,X1,X2)),k1_funct_1(X1,sK3(X0,X1,X2))),X0) | ~r2_hidden(sK3(X0,X1,X2),k3_relat_1(X2)) | ~r2_hidden(sK2(X0,X1,X2),k3_relat_1(X2)) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(k1_funct_1(X1,sK2(X0,X1,X2)),k1_funct_1(X1,sK3(X0,X1,X2))),X0) & r2_hidden(sK3(X0,X1,X2),k3_relat_1(X2)) & r2_hidden(sK2(X0,X1,X2),k3_relat_1(X2))) | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2))) | ~v2_funct_1(X1) | k3_relat_1(X0) != k2_relat_1(X1) | k1_relat_1(X1) != k3_relat_1(X2)) & ((! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(k1_funct_1(X1,X5),k1_funct_1(X1,X6)),X0) | ~r2_hidden(X6,k3_relat_1(X2)) | ~r2_hidden(X5,k3_relat_1(X2))) & ((r2_hidden(k4_tarski(k1_funct_1(X1,X5),k1_funct_1(X1,X6)),X0) & r2_hidden(X6,k3_relat_1(X2)) & r2_hidden(X5,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X5,X6),X2))) & v2_funct_1(X1) & k3_relat_1(X0) = k2_relat_1(X1) & k1_relat_1(X1) = k3_relat_1(X2)) | ~sP0(X0,X1,X2)))),
% 2.72/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f18,f19])).
% 2.72/0.97  
% 2.72/0.97  fof(f30,plain,(
% 2.72/0.97    ( ! [X2,X0,X1] : (k1_relat_1(X1) = k3_relat_1(X2) | ~sP0(X0,X1,X2)) )),
% 2.72/0.97    inference(cnf_transformation,[],[f20])).
% 2.72/0.97  
% 2.72/0.97  fof(f47,plain,(
% 2.72/0.97    r2_hidden(k4_tarski(sK7,sK8),sK4)),
% 2.72/0.97    inference(cnf_transformation,[],[f25])).
% 2.72/0.97  
% 2.72/0.97  fof(f33,plain,(
% 2.72/0.97    ( ! [X6,X2,X0,X5,X1] : (r2_hidden(X5,k3_relat_1(X2)) | ~r2_hidden(k4_tarski(X5,X6),X2) | ~sP0(X0,X1,X2)) )),
% 2.72/0.97    inference(cnf_transformation,[],[f20])).
% 2.72/0.97  
% 2.72/0.97  fof(f32,plain,(
% 2.72/0.97    ( ! [X2,X0,X1] : (v2_funct_1(X1) | ~sP0(X0,X1,X2)) )),
% 2.72/0.97    inference(cnf_transformation,[],[f20])).
% 2.72/0.97  
% 2.72/0.97  fof(f1,axiom,(
% 2.72/0.97    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0)))),
% 2.72/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.72/0.97  
% 2.72/0.97  fof(f5,plain,(
% 2.72/0.97    ! [X0,X1] : (((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) | (~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.72/0.97    inference(ennf_transformation,[],[f1])).
% 2.72/0.97  
% 2.72/0.97  fof(f6,plain,(
% 2.72/0.97    ! [X0,X1] : ((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.72/0.97    inference(flattening,[],[f5])).
% 2.72/0.97  
% 2.72/0.97  fof(f26,plain,(
% 2.72/0.97    ( ! [X0,X1] : (k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 | ~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.72/0.97    inference(cnf_transformation,[],[f6])).
% 2.72/0.97  
% 2.72/0.97  fof(f34,plain,(
% 2.72/0.97    ( ! [X6,X2,X0,X5,X1] : (r2_hidden(X6,k3_relat_1(X2)) | ~r2_hidden(k4_tarski(X5,X6),X2) | ~sP0(X0,X1,X2)) )),
% 2.72/0.97    inference(cnf_transformation,[],[f20])).
% 2.72/0.97  
% 2.72/0.97  fof(f35,plain,(
% 2.72/0.97    ( ! [X6,X2,X0,X5,X1] : (r2_hidden(k4_tarski(k1_funct_1(X1,X5),k1_funct_1(X1,X6)),X0) | ~r2_hidden(k4_tarski(X5,X6),X2) | ~sP0(X0,X1,X2)) )),
% 2.72/0.97    inference(cnf_transformation,[],[f20])).
% 2.72/0.97  
% 2.72/0.97  fof(f49,plain,(
% 2.72/0.97    k1_funct_1(sK6,sK7) = k1_funct_1(sK6,sK8) | ~r2_hidden(k4_tarski(k1_funct_1(sK6,sK7),k1_funct_1(sK6,sK8)),sK5)),
% 2.72/0.97    inference(cnf_transformation,[],[f25])).
% 2.72/0.97  
% 2.72/0.97  fof(f48,plain,(
% 2.72/0.97    sK7 != sK8),
% 2.72/0.97    inference(cnf_transformation,[],[f25])).
% 2.72/0.97  
% 2.72/0.97  cnf(c_15,plain,
% 2.72/0.97      ( sP1(X0,X1,X2)
% 2.72/0.97      | ~ v1_relat_1(X2)
% 2.72/0.97      | ~ v1_relat_1(X0)
% 2.72/0.97      | ~ v1_relat_1(X1)
% 2.72/0.97      | ~ v1_funct_1(X1) ),
% 2.72/0.97      inference(cnf_transformation,[],[f41]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_3,plain,
% 2.72/0.97      ( ~ sP1(X0,X1,X2) | sP0(X2,X1,X0) | ~ r3_wellord1(X0,X2,X1) ),
% 2.72/0.97      inference(cnf_transformation,[],[f28]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_19,negated_conjecture,
% 2.72/0.97      ( r3_wellord1(sK4,sK5,sK6) ),
% 2.72/0.97      inference(cnf_transformation,[],[f46]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_253,plain,
% 2.72/0.97      ( ~ sP1(X0,X1,X2) | sP0(X2,X1,X0) | sK4 != X0 | sK5 != X2 | sK6 != X1 ),
% 2.72/0.97      inference(resolution_lifted,[status(thm)],[c_3,c_19]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_254,plain,
% 2.72/0.97      ( ~ sP1(sK4,sK6,sK5) | sP0(sK5,sK6,sK4) ),
% 2.72/0.97      inference(unflattening,[status(thm)],[c_253]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_266,plain,
% 2.72/0.97      ( sP0(sK5,sK6,sK4)
% 2.72/0.97      | ~ v1_relat_1(X0)
% 2.72/0.97      | ~ v1_relat_1(X1)
% 2.72/0.97      | ~ v1_relat_1(X2)
% 2.72/0.97      | ~ v1_funct_1(X1)
% 2.72/0.97      | sK4 != X0
% 2.72/0.97      | sK5 != X2
% 2.72/0.97      | sK6 != X1 ),
% 2.72/0.97      inference(resolution_lifted,[status(thm)],[c_15,c_254]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_267,plain,
% 2.72/0.97      ( sP0(sK5,sK6,sK4)
% 2.72/0.97      | ~ v1_relat_1(sK4)
% 2.72/0.97      | ~ v1_relat_1(sK5)
% 2.72/0.97      | ~ v1_relat_1(sK6)
% 2.72/0.97      | ~ v1_funct_1(sK6) ),
% 2.72/0.97      inference(unflattening,[status(thm)],[c_266]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_23,negated_conjecture,
% 2.72/0.97      ( v1_relat_1(sK4) ),
% 2.72/0.97      inference(cnf_transformation,[],[f42]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_22,negated_conjecture,
% 2.72/0.97      ( v1_relat_1(sK5) ),
% 2.72/0.97      inference(cnf_transformation,[],[f43]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_21,negated_conjecture,
% 2.72/0.97      ( v1_relat_1(sK6) ),
% 2.72/0.97      inference(cnf_transformation,[],[f44]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_20,negated_conjecture,
% 2.72/0.97      ( v1_funct_1(sK6) ),
% 2.72/0.97      inference(cnf_transformation,[],[f45]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_269,plain,
% 2.72/0.97      ( sP0(sK5,sK6,sK4) ),
% 2.72/0.97      inference(global_propositional_subsumption,
% 2.72/0.97                [status(thm)],
% 2.72/0.97                [c_267,c_23,c_22,c_21,c_20]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_2420,plain,
% 2.72/0.97      ( sP0(sK5,sK6,sK4) = iProver_top ),
% 2.72/0.97      inference(predicate_to_equality,[status(thm)],[c_269]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_14,plain,
% 2.72/0.97      ( ~ sP0(X0,X1,X2) | k3_relat_1(X2) = k1_relat_1(X1) ),
% 2.72/0.97      inference(cnf_transformation,[],[f30]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_2423,plain,
% 2.72/0.97      ( k3_relat_1(X0) = k1_relat_1(X1) | sP0(X2,X1,X0) != iProver_top ),
% 2.72/0.97      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_2774,plain,
% 2.72/0.97      ( k3_relat_1(sK4) = k1_relat_1(sK6) ),
% 2.72/0.97      inference(superposition,[status(thm)],[c_2420,c_2423]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_18,negated_conjecture,
% 2.72/0.97      ( r2_hidden(k4_tarski(sK7,sK8),sK4) ),
% 2.72/0.97      inference(cnf_transformation,[],[f47]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_2421,plain,
% 2.72/0.97      ( r2_hidden(k4_tarski(sK7,sK8),sK4) = iProver_top ),
% 2.72/0.97      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_11,plain,
% 2.72/0.97      ( ~ sP0(X0,X1,X2)
% 2.72/0.97      | r2_hidden(X3,k3_relat_1(X2))
% 2.72/0.97      | ~ r2_hidden(k4_tarski(X3,X4),X2) ),
% 2.72/0.97      inference(cnf_transformation,[],[f33]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_2426,plain,
% 2.72/0.97      ( sP0(X0,X1,X2) != iProver_top
% 2.72/0.97      | r2_hidden(X3,k3_relat_1(X2)) = iProver_top
% 2.72/0.97      | r2_hidden(k4_tarski(X3,X4),X2) != iProver_top ),
% 2.72/0.97      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_2767,plain,
% 2.72/0.97      ( sP0(X0,X1,sK4) != iProver_top
% 2.72/0.97      | r2_hidden(sK7,k3_relat_1(sK4)) = iProver_top ),
% 2.72/0.97      inference(superposition,[status(thm)],[c_2421,c_2426]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_24,plain,
% 2.72/0.97      ( v1_relat_1(sK4) = iProver_top ),
% 2.72/0.97      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_25,plain,
% 2.72/0.97      ( v1_relat_1(sK5) = iProver_top ),
% 2.72/0.97      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_26,plain,
% 2.72/0.97      ( v1_relat_1(sK6) = iProver_top ),
% 2.72/0.97      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_27,plain,
% 2.72/0.97      ( v1_funct_1(sK6) = iProver_top ),
% 2.72/0.97      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_29,plain,
% 2.72/0.97      ( r2_hidden(k4_tarski(sK7,sK8),sK4) = iProver_top ),
% 2.72/0.97      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_268,plain,
% 2.72/0.97      ( sP0(sK5,sK6,sK4) = iProver_top
% 2.72/0.97      | v1_relat_1(sK4) != iProver_top
% 2.72/0.97      | v1_relat_1(sK5) != iProver_top
% 2.72/0.97      | v1_relat_1(sK6) != iProver_top
% 2.72/0.97      | v1_funct_1(sK6) != iProver_top ),
% 2.72/0.97      inference(predicate_to_equality,[status(thm)],[c_267]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_2592,plain,
% 2.72/0.97      ( ~ sP0(sK5,sK6,sK4)
% 2.72/0.97      | r2_hidden(X0,k3_relat_1(sK4))
% 2.72/0.97      | ~ r2_hidden(k4_tarski(X0,X1),sK4) ),
% 2.72/0.97      inference(instantiation,[status(thm)],[c_11]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_2657,plain,
% 2.72/0.97      ( ~ sP0(sK5,sK6,sK4)
% 2.72/0.97      | ~ r2_hidden(k4_tarski(sK7,sK8),sK4)
% 2.72/0.97      | r2_hidden(sK7,k3_relat_1(sK4)) ),
% 2.72/0.97      inference(instantiation,[status(thm)],[c_2592]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_2658,plain,
% 2.72/0.97      ( sP0(sK5,sK6,sK4) != iProver_top
% 2.72/0.97      | r2_hidden(k4_tarski(sK7,sK8),sK4) != iProver_top
% 2.72/0.97      | r2_hidden(sK7,k3_relat_1(sK4)) = iProver_top ),
% 2.72/0.97      inference(predicate_to_equality,[status(thm)],[c_2657]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_2914,plain,
% 2.72/0.97      ( r2_hidden(sK7,k3_relat_1(sK4)) = iProver_top ),
% 2.72/0.97      inference(global_propositional_subsumption,
% 2.72/0.97                [status(thm)],
% 2.72/0.97                [c_2767,c_24,c_25,c_26,c_27,c_29,c_268,c_2658]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_3642,plain,
% 2.72/0.97      ( r2_hidden(sK7,k1_relat_1(sK6)) = iProver_top ),
% 2.72/0.97      inference(demodulation,[status(thm)],[c_2774,c_2914]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_12,plain,
% 2.72/0.97      ( ~ sP0(X0,X1,X2) | v2_funct_1(X1) ),
% 2.72/0.97      inference(cnf_transformation,[],[f32]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_959,plain,
% 2.72/0.97      ( v2_funct_1(X0) | sK4 != X1 | sK5 != X2 | sK6 != X0 ),
% 2.72/0.97      inference(resolution_lifted,[status(thm)],[c_12,c_269]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_960,plain,
% 2.72/0.97      ( v2_funct_1(sK6) ),
% 2.72/0.97      inference(unflattening,[status(thm)],[c_959]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_1,plain,
% 2.72/0.97      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.72/0.97      | ~ v1_relat_1(X1)
% 2.72/0.97      | ~ v1_funct_1(X1)
% 2.72/0.97      | ~ v2_funct_1(X1)
% 2.72/0.97      | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ),
% 2.72/0.97      inference(cnf_transformation,[],[f26]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_279,plain,
% 2.72/0.97      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.72/0.97      | ~ v1_relat_1(X1)
% 2.72/0.97      | ~ v2_funct_1(X1)
% 2.72/0.97      | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0
% 2.72/0.97      | sK6 != X1 ),
% 2.72/0.97      inference(resolution_lifted,[status(thm)],[c_1,c_20]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_280,plain,
% 2.72/0.97      ( ~ r2_hidden(X0,k1_relat_1(sK6))
% 2.72/0.97      | ~ v1_relat_1(sK6)
% 2.72/0.97      | ~ v2_funct_1(sK6)
% 2.72/0.97      | k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,X0)) = X0 ),
% 2.72/0.97      inference(unflattening,[status(thm)],[c_279]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_284,plain,
% 2.72/0.97      ( ~ r2_hidden(X0,k1_relat_1(sK6))
% 2.72/0.97      | ~ v2_funct_1(sK6)
% 2.72/0.97      | k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,X0)) = X0 ),
% 2.72/0.97      inference(global_propositional_subsumption,[status(thm)],[c_280,c_21]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_1139,plain,
% 2.72/0.97      ( ~ r2_hidden(X0,k1_relat_1(sK6))
% 2.72/0.97      | k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,X0)) = X0 ),
% 2.72/0.97      inference(backward_subsumption_resolution,[status(thm)],[c_960,c_284]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_2418,plain,
% 2.72/0.97      ( k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,X0)) = X0
% 2.72/0.97      | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
% 2.72/0.97      inference(predicate_to_equality,[status(thm)],[c_1139]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_3952,plain,
% 2.72/0.97      ( k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,sK7)) = sK7 ),
% 2.72/0.97      inference(superposition,[status(thm)],[c_3642,c_2418]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_10,plain,
% 2.72/0.97      ( ~ sP0(X0,X1,X2)
% 2.72/0.97      | r2_hidden(X3,k3_relat_1(X2))
% 2.72/0.97      | ~ r2_hidden(k4_tarski(X4,X3),X2) ),
% 2.72/0.97      inference(cnf_transformation,[],[f34]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_2427,plain,
% 2.72/0.97      ( sP0(X0,X1,X2) != iProver_top
% 2.72/0.97      | r2_hidden(X3,k3_relat_1(X2)) = iProver_top
% 2.72/0.97      | r2_hidden(k4_tarski(X4,X3),X2) != iProver_top ),
% 2.72/0.97      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_2822,plain,
% 2.72/0.97      ( sP0(X0,X1,sK4) != iProver_top
% 2.72/0.97      | r2_hidden(sK8,k3_relat_1(sK4)) = iProver_top ),
% 2.72/0.97      inference(superposition,[status(thm)],[c_2421,c_2427]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_2589,plain,
% 2.72/0.97      ( ~ sP0(sK5,sK6,sK4)
% 2.72/0.97      | r2_hidden(X0,k3_relat_1(sK4))
% 2.72/0.97      | ~ r2_hidden(k4_tarski(X1,X0),sK4) ),
% 2.72/0.97      inference(instantiation,[status(thm)],[c_10]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_2654,plain,
% 2.72/0.97      ( ~ sP0(sK5,sK6,sK4)
% 2.72/0.97      | ~ r2_hidden(k4_tarski(sK7,sK8),sK4)
% 2.72/0.97      | r2_hidden(sK8,k3_relat_1(sK4)) ),
% 2.72/0.97      inference(instantiation,[status(thm)],[c_2589]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_2655,plain,
% 2.72/0.97      ( sP0(sK5,sK6,sK4) != iProver_top
% 2.72/0.97      | r2_hidden(k4_tarski(sK7,sK8),sK4) != iProver_top
% 2.72/0.97      | r2_hidden(sK8,k3_relat_1(sK4)) = iProver_top ),
% 2.72/0.97      inference(predicate_to_equality,[status(thm)],[c_2654]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_2954,plain,
% 2.72/0.97      ( r2_hidden(sK8,k3_relat_1(sK4)) = iProver_top ),
% 2.72/0.97      inference(global_propositional_subsumption,
% 2.72/0.97                [status(thm)],
% 2.72/0.97                [c_2822,c_24,c_25,c_26,c_27,c_29,c_268,c_2655]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_3641,plain,
% 2.72/0.97      ( r2_hidden(sK8,k1_relat_1(sK6)) = iProver_top ),
% 2.72/0.97      inference(demodulation,[status(thm)],[c_2774,c_2954]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_3881,plain,
% 2.72/0.97      ( k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,sK8)) = sK8 ),
% 2.72/0.97      inference(superposition,[status(thm)],[c_3641,c_2418]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_9,plain,
% 2.72/0.97      ( ~ sP0(X0,X1,X2)
% 2.72/0.97      | ~ r2_hidden(k4_tarski(X3,X4),X2)
% 2.72/0.97      | r2_hidden(k4_tarski(k1_funct_1(X1,X3),k1_funct_1(X1,X4)),X0) ),
% 2.72/0.97      inference(cnf_transformation,[],[f35]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_2428,plain,
% 2.72/0.97      ( sP0(X0,X1,X2) != iProver_top
% 2.72/0.97      | r2_hidden(k4_tarski(X3,X4),X2) != iProver_top
% 2.72/0.97      | r2_hidden(k4_tarski(k1_funct_1(X1,X3),k1_funct_1(X1,X4)),X0) = iProver_top ),
% 2.72/0.97      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_2909,plain,
% 2.72/0.97      ( sP0(X0,X1,sK4) != iProver_top
% 2.72/0.97      | r2_hidden(k4_tarski(k1_funct_1(X1,sK7),k1_funct_1(X1,sK8)),X0) = iProver_top ),
% 2.72/0.97      inference(superposition,[status(thm)],[c_2421,c_2428]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_16,negated_conjecture,
% 2.72/0.97      ( ~ r2_hidden(k4_tarski(k1_funct_1(sK6,sK7),k1_funct_1(sK6,sK8)),sK5)
% 2.72/0.97      | k1_funct_1(sK6,sK7) = k1_funct_1(sK6,sK8) ),
% 2.72/0.97      inference(cnf_transformation,[],[f49]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_2422,plain,
% 2.72/0.97      ( k1_funct_1(sK6,sK7) = k1_funct_1(sK6,sK8)
% 2.72/0.97      | r2_hidden(k4_tarski(k1_funct_1(sK6,sK7),k1_funct_1(sK6,sK8)),sK5) != iProver_top ),
% 2.72/0.97      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_2965,plain,
% 2.72/0.97      ( k1_funct_1(sK6,sK8) = k1_funct_1(sK6,sK7)
% 2.72/0.97      | sP0(sK5,sK6,sK4) != iProver_top ),
% 2.72/0.97      inference(superposition,[status(thm)],[c_2909,c_2422]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_3043,plain,
% 2.72/0.97      ( k1_funct_1(sK6,sK8) = k1_funct_1(sK6,sK7) ),
% 2.72/0.97      inference(global_propositional_subsumption,
% 2.72/0.97                [status(thm)],
% 2.72/0.97                [c_2965,c_24,c_25,c_26,c_27,c_268]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_3883,plain,
% 2.72/0.97      ( k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,sK7)) = sK8 ),
% 2.72/0.97      inference(light_normalisation,[status(thm)],[c_3881,c_3043]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_4221,plain,
% 2.72/0.97      ( sK8 = sK7 ),
% 2.72/0.97      inference(demodulation,[status(thm)],[c_3952,c_3883]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_17,negated_conjecture,
% 2.72/0.97      ( sK7 != sK8 ),
% 2.72/0.97      inference(cnf_transformation,[],[f48]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_4324,plain,
% 2.72/0.97      ( sK7 != sK7 ),
% 2.72/0.97      inference(demodulation,[status(thm)],[c_4221,c_17]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_4325,plain,
% 2.72/0.97      ( $false ),
% 2.72/0.97      inference(equality_resolution_simp,[status(thm)],[c_4324]) ).
% 2.72/0.97  
% 2.72/0.97  
% 2.72/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 2.72/0.97  
% 2.72/0.97  ------                               Statistics
% 2.72/0.97  
% 2.72/0.97  ------ General
% 2.72/0.97  
% 2.72/0.97  abstr_ref_over_cycles:                  0
% 2.72/0.97  abstr_ref_under_cycles:                 0
% 2.72/0.97  gc_basic_clause_elim:                   0
% 2.72/0.97  forced_gc_time:                         0
% 2.72/0.97  parsing_time:                           0.01
% 2.72/0.97  unif_index_cands_time:                  0.
% 2.72/0.97  unif_index_add_time:                    0.
% 2.72/0.97  orderings_time:                         0.
% 2.72/0.97  out_proof_time:                         0.017
% 2.72/0.97  total_time:                             0.191
% 2.72/0.97  num_of_symbols:                         52
% 2.72/0.97  num_of_terms:                           2312
% 2.72/0.97  
% 2.72/0.97  ------ Preprocessing
% 2.72/0.97  
% 2.72/0.97  num_of_splits:                          0
% 2.72/0.97  num_of_split_atoms:                     0
% 2.72/0.97  num_of_reused_defs:                     0
% 2.72/0.97  num_eq_ax_congr_red:                    36
% 2.72/0.97  num_of_sem_filtered_clauses:            1
% 2.72/0.97  num_of_subtypes:                        0
% 2.72/0.97  monotx_restored_types:                  0
% 2.72/0.97  sat_num_of_epr_types:                   0
% 2.72/0.97  sat_num_of_non_cyclic_types:            0
% 2.72/0.97  sat_guarded_non_collapsed_types:        0
% 2.72/0.97  num_pure_diseq_elim:                    0
% 2.72/0.97  simp_replaced_by:                       0
% 2.72/0.97  res_preprocessed:                       94
% 2.72/0.97  prep_upred:                             0
% 2.72/0.97  prep_unflattend:                        52
% 2.72/0.97  smt_new_axioms:                         0
% 2.72/0.97  pred_elim_cands:                        3
% 2.72/0.97  pred_elim:                              4
% 2.72/0.97  pred_elim_cl:                           7
% 2.72/0.97  pred_elim_cycles:                       9
% 2.72/0.97  merged_defs:                            0
% 2.72/0.97  merged_defs_ncl:                        0
% 2.72/0.97  bin_hyper_res:                          0
% 2.72/0.97  prep_cycles:                            4
% 2.72/0.97  pred_elim_time:                         0.048
% 2.72/0.97  splitting_time:                         0.
% 2.72/0.97  sem_filter_time:                        0.
% 2.72/0.97  monotx_time:                            0.001
% 2.72/0.97  subtype_inf_time:                       0.
% 2.72/0.97  
% 2.72/0.97  ------ Problem properties
% 2.72/0.97  
% 2.72/0.97  clauses:                                17
% 2.72/0.97  conjectures:                            3
% 2.72/0.97  epr:                                    3
% 2.72/0.97  horn:                                   14
% 2.72/0.97  ground:                                 4
% 2.72/0.97  unary:                                  3
% 2.72/0.97  binary:                                 6
% 2.72/0.97  lits:                                   55
% 2.72/0.97  lits_eq:                                14
% 2.72/0.97  fd_pure:                                0
% 2.72/0.97  fd_pseudo:                              0
% 2.72/0.97  fd_cond:                                0
% 2.72/0.97  fd_pseudo_cond:                         0
% 2.72/0.97  ac_symbols:                             0
% 2.72/0.97  
% 2.72/0.97  ------ Propositional Solver
% 2.72/0.97  
% 2.72/0.97  prop_solver_calls:                      29
% 2.72/0.97  prop_fast_solver_calls:                 1102
% 2.72/0.97  smt_solver_calls:                       0
% 2.72/0.97  smt_fast_solver_calls:                  0
% 2.72/0.97  prop_num_of_clauses:                    858
% 2.72/0.97  prop_preprocess_simplified:             3645
% 2.72/0.97  prop_fo_subsumed:                       9
% 2.72/0.97  prop_solver_time:                       0.
% 2.72/0.97  smt_solver_time:                        0.
% 2.72/0.97  smt_fast_solver_time:                   0.
% 2.72/0.97  prop_fast_solver_time:                  0.
% 2.72/0.97  prop_unsat_core_time:                   0.
% 2.72/0.97  
% 2.72/0.97  ------ QBF
% 2.72/0.97  
% 2.72/0.97  qbf_q_res:                              0
% 2.72/0.97  qbf_num_tautologies:                    0
% 2.72/0.97  qbf_prep_cycles:                        0
% 2.72/0.97  
% 2.72/0.97  ------ BMC1
% 2.72/0.97  
% 2.72/0.97  bmc1_current_bound:                     -1
% 2.72/0.97  bmc1_last_solved_bound:                 -1
% 2.72/0.97  bmc1_unsat_core_size:                   -1
% 2.72/0.97  bmc1_unsat_core_parents_size:           -1
% 2.72/0.97  bmc1_merge_next_fun:                    0
% 2.72/0.97  bmc1_unsat_core_clauses_time:           0.
% 2.72/0.97  
% 2.72/0.97  ------ Instantiation
% 2.72/0.97  
% 2.72/0.97  inst_num_of_clauses:                    274
% 2.72/0.97  inst_num_in_passive:                    6
% 2.72/0.97  inst_num_in_active:                     214
% 2.72/0.97  inst_num_in_unprocessed:                54
% 2.72/0.97  inst_num_of_loops:                      230
% 2.72/0.97  inst_num_of_learning_restarts:          0
% 2.72/0.97  inst_num_moves_active_passive:          10
% 2.72/0.97  inst_lit_activity:                      0
% 2.72/0.97  inst_lit_activity_moves:                0
% 2.72/0.97  inst_num_tautologies:                   0
% 2.72/0.97  inst_num_prop_implied:                  0
% 2.72/0.97  inst_num_existing_simplified:           0
% 2.72/0.97  inst_num_eq_res_simplified:             0
% 2.72/0.97  inst_num_child_elim:                    0
% 2.72/0.97  inst_num_of_dismatching_blockings:      33
% 2.72/0.97  inst_num_of_non_proper_insts:           339
% 2.72/0.97  inst_num_of_duplicates:                 0
% 2.72/0.97  inst_inst_num_from_inst_to_res:         0
% 2.72/0.97  inst_dismatching_checking_time:         0.
% 2.72/0.97  
% 2.72/0.97  ------ Resolution
% 2.72/0.97  
% 2.72/0.97  res_num_of_clauses:                     0
% 2.72/0.97  res_num_in_passive:                     0
% 2.72/0.97  res_num_in_active:                      0
% 2.72/0.97  res_num_of_loops:                       98
% 2.72/0.97  res_forward_subset_subsumed:            49
% 2.72/0.97  res_backward_subset_subsumed:           4
% 2.72/0.97  res_forward_subsumed:                   0
% 2.72/0.97  res_backward_subsumed:                  0
% 2.72/0.97  res_forward_subsumption_resolution:     0
% 2.72/0.97  res_backward_subsumption_resolution:    2
% 2.72/0.97  res_clause_to_clause_subsumption:       164
% 2.72/0.97  res_orphan_elimination:                 0
% 2.72/0.97  res_tautology_del:                      115
% 2.72/0.97  res_num_eq_res_simplified:              0
% 2.72/0.97  res_num_sel_changes:                    0
% 2.72/0.97  res_moves_from_active_to_pass:          0
% 2.72/0.97  
% 2.72/0.97  ------ Superposition
% 2.72/0.97  
% 2.72/0.97  sup_time_total:                         0.
% 2.72/0.97  sup_time_generating:                    0.
% 2.72/0.97  sup_time_sim_full:                      0.
% 2.72/0.97  sup_time_sim_immed:                     0.
% 2.72/0.97  
% 2.72/0.97  sup_num_of_clauses:                     53
% 2.72/0.97  sup_num_in_active:                      24
% 2.72/0.97  sup_num_in_passive:                     29
% 2.72/0.97  sup_num_of_loops:                       44
% 2.72/0.97  sup_fw_superposition:                   23
% 2.72/0.97  sup_bw_superposition:                   35
% 2.72/0.97  sup_immediate_simplified:               9
% 2.72/0.97  sup_given_eliminated:                   0
% 2.72/0.97  comparisons_done:                       0
% 2.72/0.97  comparisons_avoided:                    0
% 2.72/0.97  
% 2.72/0.97  ------ Simplifications
% 2.72/0.97  
% 2.72/0.97  
% 2.72/0.97  sim_fw_subset_subsumed:                 1
% 2.72/0.97  sim_bw_subset_subsumed:                 0
% 2.72/0.97  sim_fw_subsumed:                        3
% 2.72/0.97  sim_bw_subsumed:                        0
% 2.72/0.97  sim_fw_subsumption_res:                 0
% 2.72/0.97  sim_bw_subsumption_res:                 0
% 2.72/0.97  sim_tautology_del:                      0
% 2.72/0.97  sim_eq_tautology_del:                   1
% 2.72/0.97  sim_eq_res_simp:                        0
% 2.72/0.97  sim_fw_demodulated:                     0
% 2.72/0.97  sim_bw_demodulated:                     20
% 2.72/0.97  sim_light_normalised:                   6
% 2.72/0.97  sim_joinable_taut:                      0
% 2.72/0.97  sim_joinable_simp:                      0
% 2.72/0.97  sim_ac_normalised:                      0
% 2.72/0.97  sim_smt_subsumption:                    0
% 2.72/0.97  
%------------------------------------------------------------------------------
