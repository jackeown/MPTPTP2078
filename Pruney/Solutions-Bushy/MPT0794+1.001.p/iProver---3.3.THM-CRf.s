%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0794+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:07 EST 2020

% Result     : Theorem 1.77s
% Output     : CNFRefutation 1.77s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 351 expanded)
%              Number of clauses        :   48 (  75 expanded)
%              Number of leaves         :   13 ( 128 expanded)
%              Depth                    :   16
%              Number of atoms          :  526 (3168 expanded)
%              Number of equality atoms :  126 ( 725 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f37,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(k1_funct_1(X1,X5),k1_funct_1(X1,X6)),X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f35,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(X5,k3_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f36,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(X6,k3_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X1)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
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

fof(f5,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f6,plain,(
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
    inference(flattening,[],[f5])).

fof(f12,plain,(
    ! [X0,X2,X1] :
      ( ( r3_wellord1(X0,X1,X2)
      <=> sP0(X1,X2,X0) )
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X0,X2,X1)
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f6,f12,f11])).

fof(f43,plain,(
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

fof(f30,plain,(
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

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ? [X3,X4] :
          ( ( k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
            | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) )
          & X3 != X4
          & r2_hidden(k4_tarski(X3,X4),X0) )
     => ( ( k1_funct_1(X2,sK9) = k1_funct_1(X2,sK10)
          | ~ r2_hidden(k4_tarski(k1_funct_1(X2,sK9),k1_funct_1(X2,sK10)),X1) )
        & sK9 != sK10
        & r2_hidden(k4_tarski(sK9,sK10),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
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
            ( ( k1_funct_1(sK8,X3) = k1_funct_1(sK8,X4)
              | ~ r2_hidden(k4_tarski(k1_funct_1(sK8,X3),k1_funct_1(sK8,X4)),X1) )
            & X3 != X4
            & r2_hidden(k4_tarski(X3,X4),X0) )
        & r3_wellord1(X0,X1,sK8)
        & v1_funct_1(sK8)
        & v1_relat_1(sK8) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
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
                  | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),sK7) )
                & X3 != X4
                & r2_hidden(k4_tarski(X3,X4),X0) )
            & r3_wellord1(X0,sK7,X2)
            & v1_funct_1(X2)
            & v1_relat_1(X2) )
        & v1_relat_1(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
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
                  & r2_hidden(k4_tarski(X3,X4),sK6) )
              & r3_wellord1(sK6,X1,X2)
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ( k1_funct_1(sK8,sK9) = k1_funct_1(sK8,sK10)
      | ~ r2_hidden(k4_tarski(k1_funct_1(sK8,sK9),k1_funct_1(sK8,sK10)),sK7) )
    & sK9 != sK10
    & r2_hidden(k4_tarski(sK9,sK10),sK6)
    & r3_wellord1(sK6,sK7,sK8)
    & v1_funct_1(sK8)
    & v1_relat_1(sK8)
    & v1_relat_1(sK7)
    & v1_relat_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9,sK10])],[f10,f28,f27,f26,f25])).

fof(f53,plain,(
    r3_wellord1(sK6,sK7,sK8) ),
    inference(cnf_transformation,[],[f29])).

fof(f49,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f29])).

fof(f50,plain,(
    v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f29])).

fof(f51,plain,(
    v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f29])).

fof(f52,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f29])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f8,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f21,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X1,X2] :
              ( X1 = X2
              | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
              | ~ r2_hidden(X2,k1_relat_1(X0))
              | ~ r2_hidden(X1,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f22,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f21])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
          & r2_hidden(X2,k1_relat_1(X0))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( sK4(X0) != sK5(X0)
        & k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0))
        & r2_hidden(sK5(X0),k1_relat_1(X0))
        & r2_hidden(sK4(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ( sK4(X0) != sK5(X0)
            & k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0))
            & r2_hidden(sK5(X0),k1_relat_1(X0))
            & r2_hidden(sK4(X0),k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f22,f23])).

fof(f44,plain,(
    ! [X4,X0,X3] :
      ( X3 = X4
      | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X1) = k3_relat_1(X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f56,plain,
    ( k1_funct_1(sK8,sK9) = k1_funct_1(sK8,sK10)
    | ~ r2_hidden(k4_tarski(k1_funct_1(sK8,sK9),k1_funct_1(sK8,sK10)),sK7) ),
    inference(cnf_transformation,[],[f29])).

fof(f55,plain,(
    sK9 != sK10 ),
    inference(cnf_transformation,[],[f29])).

fof(f54,plain,(
    r2_hidden(k4_tarski(sK9,sK10),sK6) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_3032,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3735,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK9,k3_relat_1(sK6))
    | X1 != k3_relat_1(sK6)
    | X0 != sK9 ),
    inference(instantiation,[status(thm)],[c_3032])).

cnf(c_3869,plain,
    ( r2_hidden(sK9,X0)
    | ~ r2_hidden(sK9,k3_relat_1(sK6))
    | X0 != k3_relat_1(sK6)
    | sK9 != sK9 ),
    inference(instantiation,[status(thm)],[c_3735])).

cnf(c_3984,plain,
    ( r2_hidden(sK9,k1_relat_1(sK8))
    | ~ r2_hidden(sK9,k3_relat_1(sK6))
    | k1_relat_1(sK8) != k3_relat_1(sK6)
    | sK9 != sK9 ),
    inference(instantiation,[status(thm)],[c_3869])).

cnf(c_3725,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK10,k3_relat_1(sK6))
    | X1 != k3_relat_1(sK6)
    | X0 != sK10 ),
    inference(instantiation,[status(thm)],[c_3032])).

cnf(c_3859,plain,
    ( r2_hidden(sK10,X0)
    | ~ r2_hidden(sK10,k3_relat_1(sK6))
    | X0 != k3_relat_1(sK6)
    | sK10 != sK10 ),
    inference(instantiation,[status(thm)],[c_3725])).

cnf(c_3978,plain,
    ( r2_hidden(sK10,k1_relat_1(sK8))
    | ~ r2_hidden(sK10,k3_relat_1(sK6))
    | k1_relat_1(sK8) != k3_relat_1(sK6)
    | sK10 != sK10 ),
    inference(instantiation,[status(thm)],[c_3859])).

cnf(c_3027,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3870,plain,
    ( sK9 = sK9 ),
    inference(instantiation,[status(thm)],[c_3027])).

cnf(c_7,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X4),X2)
    | r2_hidden(k4_tarski(k1_funct_1(X1,X3),k1_funct_1(X1,X4)),X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_3502,plain,
    ( ~ sP0(sK7,sK8,sK6)
    | ~ r2_hidden(k4_tarski(X0,X1),sK6)
    | r2_hidden(k4_tarski(k1_funct_1(sK8,X0),k1_funct_1(sK8,X1)),sK7) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_3645,plain,
    ( ~ sP0(sK7,sK8,sK6)
    | r2_hidden(k4_tarski(k1_funct_1(sK8,sK9),k1_funct_1(sK8,sK10)),sK7)
    | ~ r2_hidden(k4_tarski(sK9,sK10),sK6) ),
    inference(instantiation,[status(thm)],[c_3502])).

cnf(c_9,plain,
    ( ~ sP0(X0,X1,X2)
    | r2_hidden(X3,k3_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X4),X2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_3494,plain,
    ( ~ sP0(sK7,sK8,sK6)
    | r2_hidden(X0,k3_relat_1(sK6))
    | ~ r2_hidden(k4_tarski(X0,X1),sK6) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_3630,plain,
    ( ~ sP0(sK7,sK8,sK6)
    | ~ r2_hidden(k4_tarski(sK9,sK10),sK6)
    | r2_hidden(sK9,k3_relat_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_3494])).

cnf(c_8,plain,
    ( ~ sP0(X0,X1,X2)
    | r2_hidden(X3,k3_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X4,X3),X2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_3491,plain,
    ( ~ sP0(sK7,sK8,sK6)
    | r2_hidden(X0,k3_relat_1(sK6))
    | ~ r2_hidden(k4_tarski(X1,X0),sK6) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_3627,plain,
    ( ~ sP0(sK7,sK8,sK6)
    | ~ r2_hidden(k4_tarski(sK9,sK10),sK6)
    | r2_hidden(sK10,k3_relat_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_3491])).

cnf(c_3616,plain,
    ( sK10 = sK10 ),
    inference(instantiation,[status(thm)],[c_3027])).

cnf(c_10,plain,
    ( ~ sP0(X0,X1,X2)
    | v2_funct_1(X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_13,plain,
    ( sP1(X0,X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1,plain,
    ( ~ sP1(X0,X1,X2)
    | sP0(X2,X1,X0)
    | ~ r3_wellord1(X0,X2,X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_22,negated_conjecture,
    ( r3_wellord1(sK6,sK7,sK8) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_285,plain,
    ( ~ sP1(X0,X1,X2)
    | sP0(X2,X1,X0)
    | sK6 != X0
    | sK7 != X2
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_22])).

cnf(c_286,plain,
    ( ~ sP1(sK6,sK8,sK7)
    | sP0(sK7,sK8,sK6) ),
    inference(unflattening,[status(thm)],[c_285])).

cnf(c_298,plain,
    ( sP0(sK7,sK8,sK6)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X0)
    | sK6 != X2
    | sK7 != X1
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_286])).

cnf(c_299,plain,
    ( sP0(sK7,sK8,sK6)
    | ~ v1_relat_1(sK6)
    | ~ v1_relat_1(sK7)
    | ~ v1_relat_1(sK8)
    | ~ v1_funct_1(sK8) ),
    inference(unflattening,[status(thm)],[c_298])).

cnf(c_26,negated_conjecture,
    ( v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_25,negated_conjecture,
    ( v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_24,negated_conjecture,
    ( v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_23,negated_conjecture,
    ( v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_301,plain,
    ( sP0(sK7,sK8,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_299,c_26,c_25,c_24,c_23])).

cnf(c_1644,plain,
    ( v2_funct_1(X0)
    | sK6 != X1
    | sK7 != X2
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_301])).

cnf(c_1645,plain,
    ( v2_funct_1(sK8) ),
    inference(unflattening,[status(thm)],[c_1644])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | X0 = X2
    | k1_funct_1(X1,X0) != k1_funct_1(X1,X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_311,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v2_funct_1(X1)
    | X2 = X0
    | k1_funct_1(X1,X2) != k1_funct_1(X1,X0)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_23])).

cnf(c_312,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK8))
    | ~ r2_hidden(X1,k1_relat_1(sK8))
    | ~ v1_relat_1(sK8)
    | ~ v2_funct_1(sK8)
    | X0 = X1
    | k1_funct_1(sK8,X0) != k1_funct_1(sK8,X1) ),
    inference(unflattening,[status(thm)],[c_311])).

cnf(c_316,plain,
    ( ~ r2_hidden(X1,k1_relat_1(sK8))
    | ~ r2_hidden(X0,k1_relat_1(sK8))
    | ~ v2_funct_1(sK8)
    | X0 = X1
    | k1_funct_1(sK8,X0) != k1_funct_1(sK8,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_312,c_24])).

cnf(c_317,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK8))
    | ~ r2_hidden(X1,k1_relat_1(sK8))
    | ~ v2_funct_1(sK8)
    | X0 = X1
    | k1_funct_1(sK8,X0) != k1_funct_1(sK8,X1) ),
    inference(renaming,[status(thm)],[c_316])).

cnf(c_1824,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK8))
    | ~ r2_hidden(X1,k1_relat_1(sK8))
    | X0 = X1
    | k1_funct_1(sK8,X0) != k1_funct_1(sK8,X1) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1645,c_317])).

cnf(c_3477,plain,
    ( ~ r2_hidden(sK10,k1_relat_1(sK8))
    | ~ r2_hidden(sK9,k1_relat_1(sK8))
    | k1_funct_1(sK8,sK9) != k1_funct_1(sK8,sK10)
    | sK9 = sK10 ),
    inference(instantiation,[status(thm)],[c_1824])).

cnf(c_12,plain,
    ( ~ sP0(X0,X1,X2)
    | k1_relat_1(X1) = k3_relat_1(X2) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1634,plain,
    ( k1_relat_1(X0) = k3_relat_1(X1)
    | sK6 != X1
    | sK7 != X2
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_301])).

cnf(c_1635,plain,
    ( k1_relat_1(sK8) = k3_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_1634])).

cnf(c_19,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(k1_funct_1(sK8,sK9),k1_funct_1(sK8,sK10)),sK7)
    | k1_funct_1(sK8,sK9) = k1_funct_1(sK8,sK10) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_20,negated_conjecture,
    ( sK9 != sK10 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_21,negated_conjecture,
    ( r2_hidden(k4_tarski(sK9,sK10),sK6) ),
    inference(cnf_transformation,[],[f54])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3984,c_3978,c_3870,c_3645,c_3630,c_3627,c_3616,c_3477,c_1635,c_299,c_19,c_20,c_21,c_23,c_24,c_25,c_26])).


%------------------------------------------------------------------------------
