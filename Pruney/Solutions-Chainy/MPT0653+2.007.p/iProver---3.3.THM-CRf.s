%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:50:41 EST 2020

% Result     : Theorem 3.85s
% Output     : CNFRefutation 3.85s
% Verified   : 
% Statistics : Number of formulae       :  221 (8393 expanded)
%              Number of clauses        :  173 (2104 expanded)
%              Number of leaves         :   14 (2016 expanded)
%              Depth                    :   37
%              Number of atoms          :  930 (91855 expanded)
%              Number of equality atoms :  476 (42981 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   28 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,plain,(
    ! [X2,X3,X0,X1] :
      ( sP0(X2,X3,X0,X1)
    <=> ( ( k1_funct_1(X0,X3) = X2
          & r2_hidden(X3,k1_relat_1(X0)) )
        | k1_funct_1(X1,X2) != X3
        | ~ r2_hidden(X2,k2_relat_1(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f13,plain,(
    ! [X2,X3,X0,X1] :
      ( ( sP0(X2,X3,X0,X1)
        | ( ( k1_funct_1(X0,X3) != X2
            | ~ r2_hidden(X3,k1_relat_1(X0)) )
          & k1_funct_1(X1,X2) = X3
          & r2_hidden(X2,k2_relat_1(X0)) ) )
      & ( ( k1_funct_1(X0,X3) = X2
          & r2_hidden(X3,k1_relat_1(X0)) )
        | k1_funct_1(X1,X2) != X3
        | ~ r2_hidden(X2,k2_relat_1(X0))
        | ~ sP0(X2,X3,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f14,plain,(
    ! [X2,X3,X0,X1] :
      ( ( sP0(X2,X3,X0,X1)
        | ( ( k1_funct_1(X0,X3) != X2
            | ~ r2_hidden(X3,k1_relat_1(X0)) )
          & k1_funct_1(X1,X2) = X3
          & r2_hidden(X2,k2_relat_1(X0)) ) )
      & ( ( k1_funct_1(X0,X3) = X2
          & r2_hidden(X3,k1_relat_1(X0)) )
        | k1_funct_1(X1,X2) != X3
        | ~ r2_hidden(X2,k2_relat_1(X0))
        | ~ sP0(X2,X3,X0,X1) ) ) ),
    inference(flattening,[],[f13])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( ( k1_funct_1(X2,X1) != X0
            | ~ r2_hidden(X1,k1_relat_1(X2)) )
          & k1_funct_1(X3,X0) = X1
          & r2_hidden(X0,k2_relat_1(X2)) ) )
      & ( ( k1_funct_1(X2,X1) = X0
          & r2_hidden(X1,k1_relat_1(X2)) )
        | k1_funct_1(X3,X0) != X1
        | ~ r2_hidden(X0,k2_relat_1(X2))
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f14])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | r2_hidden(X0,k2_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( k2_funct_1(X0) = X1
            <=> ( ! [X2,X3] :
                    ( ( ( k1_funct_1(X0,X3) = X2
                        & r2_hidden(X3,k1_relat_1(X0)) )
                     => ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) ) )
                    & ( ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) )
                     => ( k1_funct_1(X0,X3) = X2
                        & r2_hidden(X3,k1_relat_1(X0)) ) ) )
                & k1_relat_1(X1) = k2_relat_1(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_funct_1(X0) = X1
          <=> ( ! [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) = X3
                      & r2_hidden(X2,k2_relat_1(X0)) )
                    | k1_funct_1(X0,X3) != X2
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  & ( ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                    | k1_funct_1(X1,X2) != X3
                    | ~ r2_hidden(X2,k2_relat_1(X0)) ) )
              & k1_relat_1(X1) = k2_relat_1(X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_funct_1(X0) = X1
          <=> ( ! [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) = X3
                      & r2_hidden(X2,k2_relat_1(X0)) )
                    | k1_funct_1(X0,X3) != X2
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  & ( ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                    | k1_funct_1(X1,X2) != X3
                    | ~ r2_hidden(X2,k2_relat_1(X0)) ) )
              & k1_relat_1(X1) = k2_relat_1(X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_funct_1(X0) = X1
          <=> ( ! [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) = X3
                      & r2_hidden(X2,k2_relat_1(X0)) )
                    | k1_funct_1(X0,X3) != X2
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  & sP0(X2,X3,X0,X1) )
              & k1_relat_1(X1) = k2_relat_1(X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f8,f11])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k2_funct_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) != X3
                      | ~ r2_hidden(X2,k2_relat_1(X0)) )
                    & k1_funct_1(X0,X3) = X2
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ sP0(X2,X3,X0,X1) )
              | k1_relat_1(X1) != k2_relat_1(X0) )
            & ( ( ! [X2,X3] :
                    ( ( ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) )
                      | k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                    & sP0(X2,X3,X0,X1) )
                & k1_relat_1(X1) = k2_relat_1(X0) )
              | k2_funct_1(X0) != X1 ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k2_funct_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) != X3
                      | ~ r2_hidden(X2,k2_relat_1(X0)) )
                    & k1_funct_1(X0,X3) = X2
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ sP0(X2,X3,X0,X1) )
              | k1_relat_1(X1) != k2_relat_1(X0) )
            & ( ( ! [X2,X3] :
                    ( ( ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) )
                      | k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                    & sP0(X2,X3,X0,X1) )
                & k1_relat_1(X1) = k2_relat_1(X0) )
              | k2_funct_1(X0) != X1 ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k2_funct_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) != X3
                      | ~ r2_hidden(X2,k2_relat_1(X0)) )
                    & k1_funct_1(X0,X3) = X2
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ sP0(X2,X3,X0,X1) )
              | k1_relat_1(X1) != k2_relat_1(X0) )
            & ( ( ! [X4,X5] :
                    ( ( ( k1_funct_1(X1,X4) = X5
                        & r2_hidden(X4,k2_relat_1(X0)) )
                      | k1_funct_1(X0,X5) != X4
                      | ~ r2_hidden(X5,k1_relat_1(X0)) )
                    & sP0(X4,X5,X0,X1) )
                & k1_relat_1(X1) = k2_relat_1(X0) )
              | k2_funct_1(X0) != X1 ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f17])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ( k1_funct_1(X1,X2) != X3
              | ~ r2_hidden(X2,k2_relat_1(X0)) )
            & k1_funct_1(X0,X3) = X2
            & r2_hidden(X3,k1_relat_1(X0)) )
          | ~ sP0(X2,X3,X0,X1) )
     => ( ( ( k1_funct_1(X1,sK1(X0,X1)) != sK2(X0,X1)
            | ~ r2_hidden(sK1(X0,X1),k2_relat_1(X0)) )
          & k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1)
          & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) )
        | ~ sP0(sK1(X0,X1),sK2(X0,X1),X0,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k2_funct_1(X0) = X1
              | ( ( k1_funct_1(X1,sK1(X0,X1)) != sK2(X0,X1)
                  | ~ r2_hidden(sK1(X0,X1),k2_relat_1(X0)) )
                & k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1)
                & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) )
              | ~ sP0(sK1(X0,X1),sK2(X0,X1),X0,X1)
              | k1_relat_1(X1) != k2_relat_1(X0) )
            & ( ( ! [X4,X5] :
                    ( ( ( k1_funct_1(X1,X4) = X5
                        & r2_hidden(X4,k2_relat_1(X0)) )
                      | k1_funct_1(X0,X5) != X4
                      | ~ r2_hidden(X5,k1_relat_1(X0)) )
                    & sP0(X4,X5,X0,X1) )
                & k1_relat_1(X1) = k2_relat_1(X0) )
              | k2_funct_1(X0) != X1 ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f18,f19])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | r2_hidden(sK2(X0,X1),k1_relat_1(X0))
      | ~ sP0(sK1(X0,X1),sK2(X0,X1),X0,X1)
      | k1_relat_1(X1) != k2_relat_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2,X3] :
                  ( ( r2_hidden(X3,k1_relat_1(X1))
                    & r2_hidden(X2,k1_relat_1(X0)) )
                 => ( k1_funct_1(X0,X2) = X3
                  <=> k1_funct_1(X1,X3) = X2 ) )
              & k1_relat_1(X1) = k2_relat_1(X0)
              & k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( ! [X2,X3] :
                    ( ( r2_hidden(X3,k1_relat_1(X1))
                      & r2_hidden(X2,k1_relat_1(X0)) )
                   => ( k1_funct_1(X0,X2) = X3
                    <=> k1_funct_1(X1,X3) = X2 ) )
                & k1_relat_1(X1) = k2_relat_1(X0)
                & k1_relat_1(X0) = k2_relat_1(X1)
                & v2_funct_1(X0) )
             => k2_funct_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & ! [X2,X3] :
              ( ( k1_funct_1(X0,X2) = X3
              <=> k1_funct_1(X1,X3) = X2 )
              | ~ r2_hidden(X3,k1_relat_1(X1))
              | ~ r2_hidden(X2,k1_relat_1(X0)) )
          & k1_relat_1(X1) = k2_relat_1(X0)
          & k1_relat_1(X0) = k2_relat_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & ! [X2,X3] :
              ( ( k1_funct_1(X0,X2) = X3
              <=> k1_funct_1(X1,X3) = X2 )
              | ~ r2_hidden(X3,k1_relat_1(X1))
              | ~ r2_hidden(X2,k1_relat_1(X0)) )
          & k1_relat_1(X1) = k2_relat_1(X0)
          & k1_relat_1(X0) = k2_relat_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & ! [X2,X3] :
              ( ( ( k1_funct_1(X0,X2) = X3
                  | k1_funct_1(X1,X3) != X2 )
                & ( k1_funct_1(X1,X3) = X2
                  | k1_funct_1(X0,X2) != X3 ) )
              | ~ r2_hidden(X3,k1_relat_1(X1))
              | ~ r2_hidden(X2,k1_relat_1(X0)) )
          & k1_relat_1(X1) = k2_relat_1(X0)
          & k1_relat_1(X0) = k2_relat_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & ! [X2,X3] :
              ( ( ( k1_funct_1(X0,X2) = X3
                  | k1_funct_1(X1,X3) != X2 )
                & ( k1_funct_1(X1,X3) = X2
                  | k1_funct_1(X0,X2) != X3 ) )
              | ~ r2_hidden(X3,k1_relat_1(X1))
              | ~ r2_hidden(X2,k1_relat_1(X0)) )
          & k1_relat_1(X1) = k2_relat_1(X0)
          & k1_relat_1(X0) = k2_relat_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( k2_funct_1(X0) != sK4
        & ! [X3,X2] :
            ( ( ( k1_funct_1(X0,X2) = X3
                | k1_funct_1(sK4,X3) != X2 )
              & ( k1_funct_1(sK4,X3) = X2
                | k1_funct_1(X0,X2) != X3 ) )
            | ~ r2_hidden(X3,k1_relat_1(sK4))
            | ~ r2_hidden(X2,k1_relat_1(X0)) )
        & k1_relat_1(sK4) = k2_relat_1(X0)
        & k1_relat_1(X0) = k2_relat_1(sK4)
        & v2_funct_1(X0)
        & v1_funct_1(sK4)
        & v1_relat_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_funct_1(X0) != X1
            & ! [X2,X3] :
                ( ( ( k1_funct_1(X0,X2) = X3
                    | k1_funct_1(X1,X3) != X2 )
                  & ( k1_funct_1(X1,X3) = X2
                    | k1_funct_1(X0,X2) != X3 ) )
                | ~ r2_hidden(X3,k1_relat_1(X1))
                | ~ r2_hidden(X2,k1_relat_1(X0)) )
            & k1_relat_1(X1) = k2_relat_1(X0)
            & k1_relat_1(X0) = k2_relat_1(X1)
            & v2_funct_1(X0)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k2_funct_1(sK3) != X1
          & ! [X3,X2] :
              ( ( ( k1_funct_1(sK3,X2) = X3
                  | k1_funct_1(X1,X3) != X2 )
                & ( k1_funct_1(X1,X3) = X2
                  | k1_funct_1(sK3,X2) != X3 ) )
              | ~ r2_hidden(X3,k1_relat_1(X1))
              | ~ r2_hidden(X2,k1_relat_1(sK3)) )
          & k1_relat_1(X1) = k2_relat_1(sK3)
          & k1_relat_1(sK3) = k2_relat_1(X1)
          & v2_funct_1(sK3)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( k2_funct_1(sK3) != sK4
    & ! [X2,X3] :
        ( ( ( k1_funct_1(sK3,X2) = X3
            | k1_funct_1(sK4,X3) != X2 )
          & ( k1_funct_1(sK4,X3) = X2
            | k1_funct_1(sK3,X2) != X3 ) )
        | ~ r2_hidden(X3,k1_relat_1(sK4))
        | ~ r2_hidden(X2,k1_relat_1(sK3)) )
    & k1_relat_1(sK4) = k2_relat_1(sK3)
    & k1_relat_1(sK3) = k2_relat_1(sK4)
    & v2_funct_1(sK3)
    & v1_funct_1(sK4)
    & v1_relat_1(sK4)
    & v1_funct_1(sK3)
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f21,f23,f22])).

fof(f42,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f38,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f39,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f41,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f24])).

fof(f40,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f24])).

fof(f44,plain,(
    k1_relat_1(sK4) = k2_relat_1(sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f47,plain,(
    k2_funct_1(sK3) != sK4 ),
    inference(cnf_transformation,[],[f24])).

fof(f45,plain,(
    ! [X2,X3] :
      ( k1_funct_1(sK4,X3) = X2
      | k1_funct_1(sK3,X2) != X3
      | ~ r2_hidden(X3,k1_relat_1(sK4))
      | ~ r2_hidden(X2,k1_relat_1(sK3)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f58,plain,(
    ! [X2] :
      ( k1_funct_1(sK4,k1_funct_1(sK3,X2)) = X2
      | ~ r2_hidden(k1_funct_1(sK3,X2),k1_relat_1(sK4))
      | ~ r2_hidden(X2,k1_relat_1(sK3)) ) ),
    inference(equality_resolution,[],[f45])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f6,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f5])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f43,plain,(
    k1_relat_1(sK3) = k2_relat_1(sK4) ),
    inference(cnf_transformation,[],[f24])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(X2,X1) = X0
      | k1_funct_1(X3,X0) != X1
      | ~ r2_hidden(X0,k2_relat_1(X2))
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f49,plain,(
    ! [X2,X0,X3] :
      ( k1_funct_1(X2,k1_funct_1(X3,X0)) = X0
      | ~ r2_hidden(X0,k2_relat_1(X2))
      | ~ sP0(X0,k1_funct_1(X3,X0),X2,X3) ) ),
    inference(equality_resolution,[],[f27])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | k1_funct_1(X3,X0) = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1)
      | ~ sP0(sK1(X0,X1),sK2(X0,X1),X0,X1)
      | k1_relat_1(X1) != k2_relat_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f46,plain,(
    ! [X2,X3] :
      ( k1_funct_1(sK3,X2) = X3
      | k1_funct_1(sK4,X3) != X2
      | ~ r2_hidden(X3,k1_relat_1(sK4))
      | ~ r2_hidden(X2,k1_relat_1(sK3)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f57,plain,(
    ! [X3] :
      ( k1_funct_1(sK3,k1_funct_1(sK4,X3)) = X3
      | ~ r2_hidden(X3,k1_relat_1(sK4))
      | ~ r2_hidden(k1_funct_1(sK4,X3),k1_relat_1(sK3)) ) ),
    inference(equality_resolution,[],[f46])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | k1_funct_1(X2,X1) != X0
      | ~ r2_hidden(X1,k1_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f48,plain,(
    ! [X2,X3,X1] :
      ( sP0(k1_funct_1(X2,X1),X1,X2,X3)
      | ~ r2_hidden(X1,k1_relat_1(X2)) ) ),
    inference(equality_resolution,[],[f30])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,k1_relat_1(X2))
      | k1_funct_1(X3,X0) != X1
      | ~ r2_hidden(X0,k2_relat_1(X2))
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f50,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(k1_funct_1(X3,X0),k1_relat_1(X2))
      | ~ r2_hidden(X0,k2_relat_1(X2))
      | ~ sP0(X0,k1_funct_1(X3,X0),X2,X3) ) ),
    inference(equality_resolution,[],[f26])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k1_funct_1(X1,sK1(X0,X1)) != sK2(X0,X1)
      | ~ r2_hidden(sK1(X0,X1),k2_relat_1(X0))
      | ~ sP0(sK1(X0,X1),sK2(X0,X1),X0,X1)
      | k1_relat_1(X1) != k2_relat_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_3,plain,
    ( sP0(X0,X1,X2,X3)
    | r2_hidden(X0,k2_relat_1(X2)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_1398,plain,
    ( sP0(X0_41,X1_41,X0_42,X1_42)
    | r2_hidden(X0_41,k2_relat_1(X0_42)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1751,plain,
    ( sP0(X0_41,X1_41,X0_42,X1_42) = iProver_top
    | r2_hidden(X0_41,k2_relat_1(X0_42)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1398])).

cnf(c_8,plain,
    ( ~ sP0(sK1(X0,X1),sK2(X0,X1),X0,X1)
    | r2_hidden(sK2(X0,X1),k1_relat_1(X0))
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | k2_funct_1(X0) = X1
    | k1_relat_1(X1) != k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_18,negated_conjecture,
    ( v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_269,plain,
    ( ~ sP0(sK1(X0,X1),sK2(X0,X1),X0,X1)
    | r2_hidden(sK2(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | k2_funct_1(X0) = X1
    | k1_relat_1(X1) != k2_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_18])).

cnf(c_270,plain,
    ( ~ sP0(sK1(sK3,X0),sK2(sK3,X0),sK3,X0)
    | r2_hidden(sK2(sK3,X0),k1_relat_1(sK3))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK3)
    | k2_funct_1(sK3) = X0
    | k1_relat_1(X0) != k2_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_269])).

cnf(c_22,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_274,plain,
    ( ~ v1_funct_1(X0)
    | ~ sP0(sK1(sK3,X0),sK2(sK3,X0),sK3,X0)
    | r2_hidden(sK2(sK3,X0),k1_relat_1(sK3))
    | ~ v1_relat_1(X0)
    | k2_funct_1(sK3) = X0
    | k1_relat_1(X0) != k2_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_270,c_22,c_21])).

cnf(c_275,plain,
    ( ~ sP0(sK1(sK3,X0),sK2(sK3,X0),sK3,X0)
    | r2_hidden(sK2(sK3,X0),k1_relat_1(sK3))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_funct_1(sK3) = X0
    | k1_relat_1(X0) != k2_relat_1(sK3) ),
    inference(renaming,[status(thm)],[c_274])).

cnf(c_19,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_443,plain,
    ( ~ sP0(sK1(sK3,X0),sK2(sK3,X0),sK3,X0)
    | r2_hidden(sK2(sK3,X0),k1_relat_1(sK3))
    | ~ v1_relat_1(X0)
    | k2_funct_1(sK3) = X0
    | k1_relat_1(X0) != k2_relat_1(sK3)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_275,c_19])).

cnf(c_444,plain,
    ( ~ sP0(sK1(sK3,sK4),sK2(sK3,sK4),sK3,sK4)
    | r2_hidden(sK2(sK3,sK4),k1_relat_1(sK3))
    | ~ v1_relat_1(sK4)
    | k2_funct_1(sK3) = sK4
    | k1_relat_1(sK4) != k2_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_443])).

cnf(c_20,negated_conjecture,
    ( v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_16,negated_conjecture,
    ( k1_relat_1(sK4) = k2_relat_1(sK3) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_13,negated_conjecture,
    ( k2_funct_1(sK3) != sK4 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_446,plain,
    ( r2_hidden(sK2(sK3,sK4),k1_relat_1(sK3))
    | ~ sP0(sK1(sK3,sK4),sK2(sK3,sK4),sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_444,c_20,c_16,c_13])).

cnf(c_447,plain,
    ( ~ sP0(sK1(sK3,sK4),sK2(sK3,sK4),sK3,sK4)
    | r2_hidden(sK2(sK3,sK4),k1_relat_1(sK3)) ),
    inference(renaming,[status(thm)],[c_446])).

cnf(c_1388,plain,
    ( ~ sP0(sK1(sK3,sK4),sK2(sK3,sK4),sK3,sK4)
    | r2_hidden(sK2(sK3,sK4),k1_relat_1(sK3)) ),
    inference(subtyping,[status(esa)],[c_447])).

cnf(c_1758,plain,
    ( sP0(sK1(sK3,sK4),sK2(sK3,sK4),sK3,sK4) != iProver_top
    | r2_hidden(sK2(sK3,sK4),k1_relat_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1388])).

cnf(c_2432,plain,
    ( r2_hidden(sK2(sK3,sK4),k1_relat_1(sK3)) = iProver_top
    | r2_hidden(sK1(sK3,sK4),k2_relat_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1751,c_1758])).

cnf(c_1392,negated_conjecture,
    ( k1_relat_1(sK4) = k2_relat_1(sK3) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_15,negated_conjecture,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | ~ r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4))
    | k1_funct_1(sK4,k1_funct_1(sK3,X0)) = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1393,negated_conjecture,
    ( ~ r2_hidden(X0_41,k1_relat_1(sK3))
    | ~ r2_hidden(k1_funct_1(sK3,X0_41),k1_relat_1(sK4))
    | k1_funct_1(sK4,k1_funct_1(sK3,X0_41)) = X0_41 ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1755,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,X0_41)) = X0_41
    | r2_hidden(X0_41,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0_41),k1_relat_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1393])).

cnf(c_1971,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,X0_41)) = X0_41
    | r2_hidden(X0_41,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0_41),k2_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1392,c_1755])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_538,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_21])).

cnf(c_539,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_538])).

cnf(c_543,plain,
    ( r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3))
    | ~ r2_hidden(X0,k1_relat_1(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_539,c_22])).

cnf(c_544,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3)) ),
    inference(renaming,[status(thm)],[c_543])).

cnf(c_1383,plain,
    ( ~ r2_hidden(X0_41,k1_relat_1(sK3))
    | r2_hidden(k1_funct_1(sK3,X0_41),k2_relat_1(sK3)) ),
    inference(subtyping,[status(esa)],[c_544])).

cnf(c_1458,plain,
    ( r2_hidden(X0_41,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0_41),k2_relat_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1383])).

cnf(c_2107,plain,
    ( r2_hidden(X0_41,k1_relat_1(sK3)) != iProver_top
    | k1_funct_1(sK4,k1_funct_1(sK3,X0_41)) = X0_41 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1971,c_1458])).

cnf(c_2108,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,X0_41)) = X0_41
    | r2_hidden(X0_41,k1_relat_1(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2107])).

cnf(c_2438,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK2(sK3,sK4))) = sK2(sK3,sK4)
    | r2_hidden(sK1(sK3,sK4),k2_relat_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2432,c_2108])).

cnf(c_520,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_19])).

cnf(c_521,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_520])).

cnf(c_525,plain,
    ( r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4))
    | ~ r2_hidden(X0,k1_relat_1(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_521,c_20])).

cnf(c_526,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) ),
    inference(renaming,[status(thm)],[c_525])).

cnf(c_1384,plain,
    ( ~ r2_hidden(X0_41,k1_relat_1(sK4))
    | r2_hidden(k1_funct_1(sK4,X0_41),k2_relat_1(sK4)) ),
    inference(subtyping,[status(esa)],[c_526])).

cnf(c_1762,plain,
    ( r2_hidden(X0_41,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0_41),k2_relat_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1384])).

cnf(c_17,negated_conjecture,
    ( k1_relat_1(sK3) = k2_relat_1(sK4) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1391,negated_conjecture,
    ( k1_relat_1(sK3) = k2_relat_1(sK4) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_2113,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,X0_41)) = X0_41
    | r2_hidden(X0_41,k2_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1391,c_2108])).

cnf(c_3317,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,k1_funct_1(sK4,X0_41))) = k1_funct_1(sK4,X0_41)
    | r2_hidden(X0_41,k1_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1762,c_2113])).

cnf(c_3322,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,k1_funct_1(sK4,X0_41))) = k1_funct_1(sK4,X0_41)
    | r2_hidden(X0_41,k2_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1392,c_3317])).

cnf(c_3456,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK2(sK3,sK4))) = sK2(sK3,sK4)
    | k1_funct_1(sK4,k1_funct_1(sK3,k1_funct_1(sK4,sK1(sK3,sK4)))) = k1_funct_1(sK4,sK1(sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_2438,c_3322])).

cnf(c_4,plain,
    ( ~ sP0(X0,k1_funct_1(X1,X0),X2,X1)
    | ~ r2_hidden(X0,k2_relat_1(X2))
    | k1_funct_1(X2,k1_funct_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1397,plain,
    ( ~ sP0(X0_41,k1_funct_1(X0_42,X0_41),X1_42,X0_42)
    | ~ r2_hidden(X0_41,k2_relat_1(X1_42))
    | k1_funct_1(X1_42,k1_funct_1(X0_42,X0_41)) = X0_41 ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1752,plain,
    ( k1_funct_1(X0_42,k1_funct_1(X1_42,X0_41)) = X0_41
    | sP0(X0_41,k1_funct_1(X1_42,X0_41),X0_42,X1_42) != iProver_top
    | r2_hidden(X0_41,k2_relat_1(X0_42)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1397])).

cnf(c_4051,plain,
    ( k1_funct_1(X0_42,k1_funct_1(sK4,k1_funct_1(sK3,k1_funct_1(sK4,sK1(sK3,sK4))))) = k1_funct_1(sK3,k1_funct_1(sK4,sK1(sK3,sK4)))
    | k1_funct_1(sK4,k1_funct_1(sK3,sK2(sK3,sK4))) = sK2(sK3,sK4)
    | sP0(k1_funct_1(sK3,k1_funct_1(sK4,sK1(sK3,sK4))),k1_funct_1(sK4,sK1(sK3,sK4)),X0_42,sK4) != iProver_top
    | r2_hidden(k1_funct_1(sK3,k1_funct_1(sK4,sK1(sK3,sK4))),k2_relat_1(X0_42)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3456,c_1752])).

cnf(c_1402,plain,
    ( X0_41 = X0_41 ),
    theory(equality)).

cnf(c_2012,plain,
    ( sK1(sK3,sK4) = sK1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1402])).

cnf(c_1410,plain,
    ( ~ r2_hidden(X0_41,X0_43)
    | r2_hidden(X1_41,X1_43)
    | X1_43 != X0_43
    | X1_41 != X0_41 ),
    theory(equality)).

cnf(c_1899,plain,
    ( r2_hidden(X0_41,X0_43)
    | ~ r2_hidden(sK1(sK3,sK4),k2_relat_1(sK3))
    | X0_43 != k2_relat_1(sK3)
    | X0_41 != sK1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1410])).

cnf(c_2011,plain,
    ( r2_hidden(sK1(sK3,sK4),X0_43)
    | ~ r2_hidden(sK1(sK3,sK4),k2_relat_1(sK3))
    | X0_43 != k2_relat_1(sK3)
    | sK1(sK3,sK4) != sK1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1899])).

cnf(c_2309,plain,
    ( r2_hidden(sK1(sK3,sK4),k1_relat_1(sK4))
    | ~ r2_hidden(sK1(sK3,sK4),k2_relat_1(sK3))
    | k1_relat_1(sK4) != k2_relat_1(sK3)
    | sK1(sK3,sK4) != sK1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_2011])).

cnf(c_2310,plain,
    ( k1_relat_1(sK4) != k2_relat_1(sK3)
    | sK1(sK3,sK4) != sK1(sK3,sK4)
    | r2_hidden(sK1(sK3,sK4),k1_relat_1(sK4)) = iProver_top
    | r2_hidden(sK1(sK3,sK4),k2_relat_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2309])).

cnf(c_2,plain,
    ( sP0(X0,X1,X2,X3)
    | k1_funct_1(X3,X0) = X1 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_1399,plain,
    ( sP0(X0_41,X1_41,X0_42,X1_42)
    | k1_funct_1(X1_42,X0_41) = X1_41 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1750,plain,
    ( k1_funct_1(X0_42,X0_41) = X1_41
    | sP0(X0_41,X1_41,X1_42,X0_42) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1399])).

cnf(c_7,plain,
    ( ~ sP0(sK1(X0,X1),sK2(X0,X1),X0,X1)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1)
    | k2_funct_1(X0) = X1
    | k1_relat_1(X1) != k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_297,plain,
    ( ~ sP0(sK1(X0,X1),sK2(X0,X1),X0,X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1)
    | k2_funct_1(X0) = X1
    | k1_relat_1(X1) != k2_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_18])).

cnf(c_298,plain,
    ( ~ sP0(sK1(sK3,X0),sK2(sK3,X0),sK3,X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK3)
    | k1_funct_1(sK3,sK2(sK3,X0)) = sK1(sK3,X0)
    | k2_funct_1(sK3) = X0
    | k1_relat_1(X0) != k2_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_297])).

cnf(c_302,plain,
    ( ~ v1_funct_1(X0)
    | ~ sP0(sK1(sK3,X0),sK2(sK3,X0),sK3,X0)
    | ~ v1_relat_1(X0)
    | k1_funct_1(sK3,sK2(sK3,X0)) = sK1(sK3,X0)
    | k2_funct_1(sK3) = X0
    | k1_relat_1(X0) != k2_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_298,c_22,c_21])).

cnf(c_303,plain,
    ( ~ sP0(sK1(sK3,X0),sK2(sK3,X0),sK3,X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_funct_1(sK3,sK2(sK3,X0)) = sK1(sK3,X0)
    | k2_funct_1(sK3) = X0
    | k1_relat_1(X0) != k2_relat_1(sK3) ),
    inference(renaming,[status(thm)],[c_302])).

cnf(c_429,plain,
    ( ~ sP0(sK1(sK3,X0),sK2(sK3,X0),sK3,X0)
    | ~ v1_relat_1(X0)
    | k1_funct_1(sK3,sK2(sK3,X0)) = sK1(sK3,X0)
    | k2_funct_1(sK3) = X0
    | k1_relat_1(X0) != k2_relat_1(sK3)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_303,c_19])).

cnf(c_430,plain,
    ( ~ sP0(sK1(sK3,sK4),sK2(sK3,sK4),sK3,sK4)
    | ~ v1_relat_1(sK4)
    | k1_funct_1(sK3,sK2(sK3,sK4)) = sK1(sK3,sK4)
    | k2_funct_1(sK3) = sK4
    | k1_relat_1(sK4) != k2_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_429])).

cnf(c_432,plain,
    ( ~ sP0(sK1(sK3,sK4),sK2(sK3,sK4),sK3,sK4)
    | k1_funct_1(sK3,sK2(sK3,sK4)) = sK1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_430,c_20,c_16,c_13])).

cnf(c_1389,plain,
    ( ~ sP0(sK1(sK3,sK4),sK2(sK3,sK4),sK3,sK4)
    | k1_funct_1(sK3,sK2(sK3,sK4)) = sK1(sK3,sK4) ),
    inference(subtyping,[status(esa)],[c_432])).

cnf(c_1757,plain,
    ( k1_funct_1(sK3,sK2(sK3,sK4)) = sK1(sK3,sK4)
    | sP0(sK1(sK3,sK4),sK2(sK3,sK4),sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1389])).

cnf(c_2326,plain,
    ( k1_funct_1(sK4,sK1(sK3,sK4)) = sK2(sK3,sK4)
    | k1_funct_1(sK3,sK2(sK3,sK4)) = sK1(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_1750,c_1757])).

cnf(c_2325,plain,
    ( k1_funct_1(sK3,sK2(sK3,sK4)) = sK1(sK3,sK4)
    | r2_hidden(sK1(sK3,sK4),k2_relat_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1751,c_1757])).

cnf(c_14,negated_conjecture,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | ~ r2_hidden(k1_funct_1(sK4,X0),k1_relat_1(sK3))
    | k1_funct_1(sK3,k1_funct_1(sK4,X0)) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1394,negated_conjecture,
    ( ~ r2_hidden(X0_41,k1_relat_1(sK4))
    | ~ r2_hidden(k1_funct_1(sK4,X0_41),k1_relat_1(sK3))
    | k1_funct_1(sK3,k1_funct_1(sK4,X0_41)) = X0_41 ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1754,plain,
    ( k1_funct_1(sK3,k1_funct_1(sK4,X0_41)) = X0_41
    | r2_hidden(X0_41,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0_41),k1_relat_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1394])).

cnf(c_1911,plain,
    ( k1_funct_1(sK3,k1_funct_1(sK4,X0_41)) = X0_41
    | r2_hidden(X0_41,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0_41),k2_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1391,c_1754])).

cnf(c_1455,plain,
    ( r2_hidden(X0_41,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0_41),k2_relat_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1384])).

cnf(c_1976,plain,
    ( r2_hidden(X0_41,k1_relat_1(sK4)) != iProver_top
    | k1_funct_1(sK3,k1_funct_1(sK4,X0_41)) = X0_41 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1911,c_1455])).

cnf(c_1977,plain,
    ( k1_funct_1(sK3,k1_funct_1(sK4,X0_41)) = X0_41
    | r2_hidden(X0_41,k1_relat_1(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_1976])).

cnf(c_1982,plain,
    ( k1_funct_1(sK3,k1_funct_1(sK4,X0_41)) = X0_41
    | r2_hidden(X0_41,k2_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1392,c_1977])).

cnf(c_2329,plain,
    ( k1_funct_1(sK3,sK2(sK3,sK4)) = sK1(sK3,sK4)
    | k1_funct_1(sK3,k1_funct_1(sK4,sK1(sK3,sK4))) = sK1(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_2325,c_1982])).

cnf(c_2727,plain,
    ( k1_funct_1(sK3,sK2(sK3,sK4)) = sK1(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_2326,c_2329])).

cnf(c_1763,plain,
    ( r2_hidden(X0_41,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0_41),k2_relat_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1383])).

cnf(c_3583,plain,
    ( r2_hidden(sK2(sK3,sK4),k1_relat_1(sK3)) != iProver_top
    | r2_hidden(sK1(sK3,sK4),k2_relat_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2727,c_1763])).

cnf(c_847,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK2(sK3,sK4),k1_relat_1(sK3))
    | sK2(sK3,sK4) != X2
    | sK1(sK3,sK4) != X0
    | sK4 != X3
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_447])).

cnf(c_848,plain,
    ( r2_hidden(sK2(sK3,sK4),k1_relat_1(sK3))
    | r2_hidden(sK1(sK3,sK4),k2_relat_1(sK3)) ),
    inference(unflattening,[status(thm)],[c_847])).

cnf(c_849,plain,
    ( r2_hidden(sK2(sK3,sK4),k1_relat_1(sK3)) = iProver_top
    | r2_hidden(sK1(sK3,sK4),k2_relat_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_848])).

cnf(c_4188,plain,
    ( r2_hidden(sK1(sK3,sK4),k2_relat_1(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3583,c_849])).

cnf(c_2433,plain,
    ( k1_funct_1(sK4,sK1(sK3,sK4)) = sK2(sK3,sK4)
    | r2_hidden(sK2(sK3,sK4),k1_relat_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1750,c_1758])).

cnf(c_2517,plain,
    ( k1_funct_1(sK4,sK1(sK3,sK4)) = sK2(sK3,sK4)
    | k1_funct_1(sK4,k1_funct_1(sK3,sK2(sK3,sK4))) = sK2(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_2433,c_2108])).

cnf(c_3818,plain,
    ( k1_funct_1(sK4,sK1(sK3,sK4)) = sK2(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_2727,c_2517])).

cnf(c_6763,plain,
    ( r2_hidden(sK2(sK3,sK4),k2_relat_1(sK4)) = iProver_top
    | r2_hidden(sK1(sK3,sK4),k1_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3818,c_1762])).

cnf(c_1,plain,
    ( sP0(k1_funct_1(X0,X1),X1,X0,X2)
    | ~ r2_hidden(X1,k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1400,plain,
    ( sP0(k1_funct_1(X0_42,X0_41),X0_41,X0_42,X1_42)
    | ~ r2_hidden(X0_41,k1_relat_1(X0_42)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1749,plain,
    ( sP0(k1_funct_1(X0_42,X0_41),X0_41,X0_42,X1_42) = iProver_top
    | r2_hidden(X0_41,k1_relat_1(X0_42)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1400])).

cnf(c_6766,plain,
    ( sP0(sK2(sK3,sK4),sK1(sK3,sK4),sK4,X0_42) = iProver_top
    | r2_hidden(sK1(sK3,sK4),k1_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3818,c_1749])).

cnf(c_7166,plain,
    ( sP0(sK2(sK3,sK4),sK1(sK3,sK4),sK4,X0_42) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6766,c_849,c_1392,c_2012,c_2310,c_3583])).

cnf(c_2959,plain,
    ( k1_funct_1(X0_42,k1_funct_1(sK3,sK2(sK3,sK4))) = sK2(sK3,sK4)
    | sP0(sK2(sK3,sK4),sK1(sK3,sK4),X0_42,sK3) != iProver_top
    | r2_hidden(sK2(sK3,sK4),k2_relat_1(X0_42)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2727,c_1752])).

cnf(c_7172,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK2(sK3,sK4))) = sK2(sK3,sK4)
    | r2_hidden(sK2(sK3,sK4),k2_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7166,c_2959])).

cnf(c_7967,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK2(sK3,sK4))) = sK2(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4051,c_849,c_1392,c_2012,c_2310,c_3583,c_6763,c_7172])).

cnf(c_4193,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,k1_funct_1(sK4,sK1(sK3,sK4)))) = k1_funct_1(sK4,sK1(sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_4188,c_3322])).

cnf(c_4377,plain,
    ( sP0(k1_funct_1(sK4,sK1(sK3,sK4)),k1_funct_1(sK3,k1_funct_1(sK4,sK1(sK3,sK4))),sK4,X0_42) = iProver_top
    | r2_hidden(k1_funct_1(sK3,k1_funct_1(sK4,sK1(sK3,sK4))),k1_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4193,c_1749])).

cnf(c_1409,plain,
    ( k2_relat_1(X0_42) = k2_relat_1(X1_42)
    | X0_42 != X1_42 ),
    theory(equality)).

cnf(c_1417,plain,
    ( k2_relat_1(sK3) = k2_relat_1(sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1409])).

cnf(c_1403,plain,
    ( X0_42 = X0_42 ),
    theory(equality)).

cnf(c_1426,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1403])).

cnf(c_2101,plain,
    ( ~ r2_hidden(sK1(sK3,sK4),k2_relat_1(sK3))
    | r2_hidden(k1_funct_1(sK3,sK2(sK3,sK4)),X0_43)
    | X0_43 != k2_relat_1(sK3)
    | k1_funct_1(sK3,sK2(sK3,sK4)) != sK1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1899])).

cnf(c_2279,plain,
    ( ~ r2_hidden(sK1(sK3,sK4),k2_relat_1(sK3))
    | r2_hidden(k1_funct_1(sK3,sK2(sK3,sK4)),k2_relat_1(sK3))
    | k2_relat_1(sK3) != k2_relat_1(sK3)
    | k1_funct_1(sK3,sK2(sK3,sK4)) != sK1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_2101])).

cnf(c_2280,plain,
    ( k2_relat_1(sK3) != k2_relat_1(sK3)
    | k1_funct_1(sK3,sK2(sK3,sK4)) != sK1(sK3,sK4)
    | r2_hidden(sK1(sK3,sK4),k2_relat_1(sK3)) != iProver_top
    | r2_hidden(k1_funct_1(sK3,sK2(sK3,sK4)),k2_relat_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2279])).

cnf(c_1408,plain,
    ( X0_42 != X1_42
    | X0_41 != X1_41
    | k1_funct_1(X0_42,X0_41) = k1_funct_1(X1_42,X1_41) ),
    theory(equality)).

cnf(c_2782,plain,
    ( X0_42 != sK3
    | X0_41 != sK2(sK3,sK4)
    | k1_funct_1(X0_42,X0_41) = k1_funct_1(sK3,sK2(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_1408])).

cnf(c_3501,plain,
    ( X0_42 != sK3
    | k1_funct_1(X0_42,k1_funct_1(sK4,sK1(sK3,sK4))) = k1_funct_1(sK3,sK2(sK3,sK4))
    | k1_funct_1(sK4,sK1(sK3,sK4)) != sK2(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_2782])).

cnf(c_3502,plain,
    ( sK3 != sK3
    | k1_funct_1(sK4,sK1(sK3,sK4)) != sK2(sK3,sK4)
    | k1_funct_1(sK3,k1_funct_1(sK4,sK1(sK3,sK4))) = k1_funct_1(sK3,sK2(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_3501])).

cnf(c_2228,plain,
    ( r2_hidden(X0_41,X0_43)
    | ~ r2_hidden(k1_funct_1(sK3,sK2(sK3,sK4)),k2_relat_1(sK3))
    | X0_43 != k2_relat_1(sK3)
    | X0_41 != k1_funct_1(sK3,sK2(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_1410])).

cnf(c_2781,plain,
    ( r2_hidden(k1_funct_1(X0_42,X0_41),X0_43)
    | ~ r2_hidden(k1_funct_1(sK3,sK2(sK3,sK4)),k2_relat_1(sK3))
    | X0_43 != k2_relat_1(sK3)
    | k1_funct_1(X0_42,X0_41) != k1_funct_1(sK3,sK2(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_2228])).

cnf(c_3546,plain,
    ( r2_hidden(k1_funct_1(X0_42,X0_41),k1_relat_1(sK4))
    | ~ r2_hidden(k1_funct_1(sK3,sK2(sK3,sK4)),k2_relat_1(sK3))
    | k1_relat_1(sK4) != k2_relat_1(sK3)
    | k1_funct_1(X0_42,X0_41) != k1_funct_1(sK3,sK2(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_2781])).

cnf(c_4544,plain,
    ( r2_hidden(k1_funct_1(X0_42,k1_funct_1(sK4,sK1(sK3,sK4))),k1_relat_1(sK4))
    | ~ r2_hidden(k1_funct_1(sK3,sK2(sK3,sK4)),k2_relat_1(sK3))
    | k1_relat_1(sK4) != k2_relat_1(sK3)
    | k1_funct_1(X0_42,k1_funct_1(sK4,sK1(sK3,sK4))) != k1_funct_1(sK3,sK2(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_3546])).

cnf(c_4545,plain,
    ( k1_relat_1(sK4) != k2_relat_1(sK3)
    | k1_funct_1(X0_42,k1_funct_1(sK4,sK1(sK3,sK4))) != k1_funct_1(sK3,sK2(sK3,sK4))
    | r2_hidden(k1_funct_1(X0_42,k1_funct_1(sK4,sK1(sK3,sK4))),k1_relat_1(sK4)) = iProver_top
    | r2_hidden(k1_funct_1(sK3,sK2(sK3,sK4)),k2_relat_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4544])).

cnf(c_4547,plain,
    ( k1_relat_1(sK4) != k2_relat_1(sK3)
    | k1_funct_1(sK3,k1_funct_1(sK4,sK1(sK3,sK4))) != k1_funct_1(sK3,sK2(sK3,sK4))
    | r2_hidden(k1_funct_1(sK3,sK2(sK3,sK4)),k2_relat_1(sK3)) != iProver_top
    | r2_hidden(k1_funct_1(sK3,k1_funct_1(sK4,sK1(sK3,sK4))),k1_relat_1(sK4)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4545])).

cnf(c_4968,plain,
    ( sP0(k1_funct_1(sK4,sK1(sK3,sK4)),k1_funct_1(sK3,k1_funct_1(sK4,sK1(sK3,sK4))),sK4,X0_42) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4377,c_849,c_1417,c_1426,c_1392,c_2280,c_2727,c_3502,c_3583,c_3818,c_4547])).

cnf(c_5,plain,
    ( ~ sP0(X0,k1_funct_1(X1,X0),X2,X1)
    | ~ r2_hidden(X0,k2_relat_1(X2))
    | r2_hidden(k1_funct_1(X1,X0),k1_relat_1(X2)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1396,plain,
    ( ~ sP0(X0_41,k1_funct_1(X0_42,X0_41),X1_42,X0_42)
    | ~ r2_hidden(X0_41,k2_relat_1(X1_42))
    | r2_hidden(k1_funct_1(X0_42,X0_41),k1_relat_1(X1_42)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1753,plain,
    ( sP0(X0_41,k1_funct_1(X0_42,X0_41),X1_42,X0_42) != iProver_top
    | r2_hidden(X0_41,k2_relat_1(X1_42)) != iProver_top
    | r2_hidden(k1_funct_1(X0_42,X0_41),k1_relat_1(X1_42)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1396])).

cnf(c_4975,plain,
    ( r2_hidden(k1_funct_1(sK4,sK1(sK3,sK4)),k2_relat_1(sK4)) != iProver_top
    | r2_hidden(k1_funct_1(sK3,k1_funct_1(sK4,sK1(sK3,sK4))),k1_relat_1(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4968,c_1753])).

cnf(c_4982,plain,
    ( r2_hidden(k1_funct_1(sK3,k1_funct_1(sK4,sK1(sK3,sK4))),k1_relat_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4975,c_849,c_1417,c_1426,c_1392,c_2280,c_2727,c_3502,c_3583,c_3818,c_4547])).

cnf(c_4987,plain,
    ( r2_hidden(k1_funct_1(sK3,k1_funct_1(sK4,sK1(sK3,sK4))),k2_relat_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1392,c_4982])).

cnf(c_6752,plain,
    ( r2_hidden(k1_funct_1(sK3,sK2(sK3,sK4)),k2_relat_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3818,c_4987])).

cnf(c_6967,plain,
    ( k1_funct_1(sK3,k1_funct_1(sK4,k1_funct_1(sK3,sK2(sK3,sK4)))) = k1_funct_1(sK3,sK2(sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_6752,c_1982])).

cnf(c_6972,plain,
    ( sP0(k1_funct_1(sK3,sK2(sK3,sK4)),k1_funct_1(sK4,k1_funct_1(sK3,sK2(sK3,sK4))),sK3,X0_42) = iProver_top
    | r2_hidden(k1_funct_1(sK4,k1_funct_1(sK3,sK2(sK3,sK4))),k1_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6967,c_1749])).

cnf(c_2271,plain,
    ( ~ r2_hidden(sK1(sK3,sK4),k2_relat_1(sK3))
    | r2_hidden(k1_funct_1(sK3,sK2(sK3,sK4)),k1_relat_1(sK4))
    | k1_relat_1(sK4) != k2_relat_1(sK3)
    | k1_funct_1(sK3,sK2(sK3,sK4)) != sK1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_2101])).

cnf(c_2272,plain,
    ( k1_relat_1(sK4) != k2_relat_1(sK3)
    | k1_funct_1(sK3,sK2(sK3,sK4)) != sK1(sK3,sK4)
    | r2_hidden(sK1(sK3,sK4),k2_relat_1(sK3)) != iProver_top
    | r2_hidden(k1_funct_1(sK3,sK2(sK3,sK4)),k1_relat_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2271])).

cnf(c_2588,plain,
    ( r2_hidden(k1_funct_1(sK4,k1_funct_1(sK3,sK2(sK3,sK4))),k2_relat_1(sK4))
    | ~ r2_hidden(k1_funct_1(sK3,sK2(sK3,sK4)),k1_relat_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_1384])).

cnf(c_2589,plain,
    ( r2_hidden(k1_funct_1(sK4,k1_funct_1(sK3,sK2(sK3,sK4))),k2_relat_1(sK4)) = iProver_top
    | r2_hidden(k1_funct_1(sK3,sK2(sK3,sK4)),k1_relat_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2588])).

cnf(c_4646,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK2(sK3,sK4))) = k1_funct_1(sK4,k1_funct_1(sK3,sK2(sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_1402])).

cnf(c_3161,plain,
    ( r2_hidden(X0_41,X0_43)
    | ~ r2_hidden(k1_funct_1(sK4,k1_funct_1(sK3,sK2(sK3,sK4))),k2_relat_1(sK4))
    | X0_43 != k2_relat_1(sK4)
    | X0_41 != k1_funct_1(sK4,k1_funct_1(sK3,sK2(sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_1410])).

cnf(c_4645,plain,
    ( r2_hidden(k1_funct_1(sK4,k1_funct_1(sK3,sK2(sK3,sK4))),X0_43)
    | ~ r2_hidden(k1_funct_1(sK4,k1_funct_1(sK3,sK2(sK3,sK4))),k2_relat_1(sK4))
    | X0_43 != k2_relat_1(sK4)
    | k1_funct_1(sK4,k1_funct_1(sK3,sK2(sK3,sK4))) != k1_funct_1(sK4,k1_funct_1(sK3,sK2(sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_3161])).

cnf(c_7111,plain,
    ( r2_hidden(k1_funct_1(sK4,k1_funct_1(sK3,sK2(sK3,sK4))),k1_relat_1(sK3))
    | ~ r2_hidden(k1_funct_1(sK4,k1_funct_1(sK3,sK2(sK3,sK4))),k2_relat_1(sK4))
    | k1_relat_1(sK3) != k2_relat_1(sK4)
    | k1_funct_1(sK4,k1_funct_1(sK3,sK2(sK3,sK4))) != k1_funct_1(sK4,k1_funct_1(sK3,sK2(sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_4645])).

cnf(c_7112,plain,
    ( k1_relat_1(sK3) != k2_relat_1(sK4)
    | k1_funct_1(sK4,k1_funct_1(sK3,sK2(sK3,sK4))) != k1_funct_1(sK4,k1_funct_1(sK3,sK2(sK3,sK4)))
    | r2_hidden(k1_funct_1(sK4,k1_funct_1(sK3,sK2(sK3,sK4))),k1_relat_1(sK3)) = iProver_top
    | r2_hidden(k1_funct_1(sK4,k1_funct_1(sK3,sK2(sK3,sK4))),k2_relat_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7111])).

cnf(c_7530,plain,
    ( sP0(k1_funct_1(sK3,sK2(sK3,sK4)),k1_funct_1(sK4,k1_funct_1(sK3,sK2(sK3,sK4))),sK3,X0_42) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6972,c_849,c_1392,c_1391,c_2272,c_2589,c_2727,c_3583,c_4646,c_7112])).

cnf(c_7539,plain,
    ( r2_hidden(k1_funct_1(sK4,k1_funct_1(sK3,sK2(sK3,sK4))),k1_relat_1(sK3)) = iProver_top
    | r2_hidden(k1_funct_1(sK3,sK2(sK3,sK4)),k2_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7530,c_1753])).

cnf(c_7682,plain,
    ( r2_hidden(k1_funct_1(sK4,k1_funct_1(sK3,sK2(sK3,sK4))),k1_relat_1(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7539,c_849,c_1392,c_1391,c_2272,c_2589,c_2727,c_3583,c_4646,c_7112])).

cnf(c_7975,plain,
    ( r2_hidden(sK2(sK3,sK4),k1_relat_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7967,c_7682])).

cnf(c_2091,plain,
    ( sP0(k1_funct_1(sK3,sK2(sK3,sK4)),sK2(sK3,sK4),sK3,X0_42)
    | ~ r2_hidden(sK2(sK3,sK4),k1_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_1400])).

cnf(c_4854,plain,
    ( sP0(k1_funct_1(sK3,sK2(sK3,sK4)),sK2(sK3,sK4),sK3,sK4)
    | ~ r2_hidden(sK2(sK3,sK4),k1_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_2091])).

cnf(c_4857,plain,
    ( sP0(k1_funct_1(sK3,sK2(sK3,sK4)),sK2(sK3,sK4),sK3,sK4) = iProver_top
    | r2_hidden(sK2(sK3,sK4),k1_relat_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4854])).

cnf(c_1412,plain,
    ( ~ sP0(X0_41,X1_41,X0_42,X1_42)
    | sP0(X2_41,X3_41,X2_42,X3_42)
    | X2_42 != X0_42
    | X3_42 != X1_42
    | X2_41 != X0_41
    | X3_41 != X1_41 ),
    theory(equality)).

cnf(c_1879,plain,
    ( ~ sP0(X0_41,X1_41,X0_42,X1_42)
    | sP0(sK1(sK3,sK4),sK2(sK3,sK4),sK3,sK4)
    | sK4 != X1_42
    | sK3 != X0_42
    | sK2(sK3,sK4) != X1_41
    | sK1(sK3,sK4) != X0_41 ),
    inference(instantiation,[status(thm)],[c_1412])).

cnf(c_1947,plain,
    ( ~ sP0(X0_41,X1_41,X0_42,sK4)
    | sP0(sK1(sK3,sK4),sK2(sK3,sK4),sK3,sK4)
    | sK4 != sK4
    | sK3 != X0_42
    | sK2(sK3,sK4) != X1_41
    | sK1(sK3,sK4) != X0_41 ),
    inference(instantiation,[status(thm)],[c_1879])).

cnf(c_3181,plain,
    ( sP0(sK1(sK3,sK4),sK2(sK3,sK4),sK3,sK4)
    | ~ sP0(k1_funct_1(sK3,sK2(sK3,sK4)),X0_41,X0_42,sK4)
    | sK4 != sK4
    | sK3 != X0_42
    | sK2(sK3,sK4) != X0_41
    | sK1(sK3,sK4) != k1_funct_1(sK3,sK2(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_1947])).

cnf(c_4678,plain,
    ( sP0(sK1(sK3,sK4),sK2(sK3,sK4),sK3,sK4)
    | ~ sP0(k1_funct_1(sK3,sK2(sK3,sK4)),sK2(sK3,sK4),X0_42,sK4)
    | sK4 != sK4
    | sK3 != X0_42
    | sK2(sK3,sK4) != sK2(sK3,sK4)
    | sK1(sK3,sK4) != k1_funct_1(sK3,sK2(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_3181])).

cnf(c_4679,plain,
    ( sK4 != sK4
    | sK3 != X0_42
    | sK2(sK3,sK4) != sK2(sK3,sK4)
    | sK1(sK3,sK4) != k1_funct_1(sK3,sK2(sK3,sK4))
    | sP0(sK1(sK3,sK4),sK2(sK3,sK4),sK3,sK4) = iProver_top
    | sP0(k1_funct_1(sK3,sK2(sK3,sK4)),sK2(sK3,sK4),X0_42,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4678])).

cnf(c_4681,plain,
    ( sK4 != sK4
    | sK3 != sK3
    | sK2(sK3,sK4) != sK2(sK3,sK4)
    | sK1(sK3,sK4) != k1_funct_1(sK3,sK2(sK3,sK4))
    | sP0(sK1(sK3,sK4),sK2(sK3,sK4),sK3,sK4) = iProver_top
    | sP0(k1_funct_1(sK3,sK2(sK3,sK4)),sK2(sK3,sK4),sK3,sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4679])).

cnf(c_1405,plain,
    ( X0_41 != X1_41
    | X2_41 != X1_41
    | X2_41 = X0_41 ),
    theory(equality)).

cnf(c_2076,plain,
    ( X0_41 != X1_41
    | sK1(sK3,sK4) != X1_41
    | sK1(sK3,sK4) = X0_41 ),
    inference(instantiation,[status(thm)],[c_1405])).

cnf(c_2387,plain,
    ( X0_41 != sK1(sK3,sK4)
    | sK1(sK3,sK4) = X0_41
    | sK1(sK3,sK4) != sK1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_2076])).

cnf(c_2914,plain,
    ( sK1(sK3,sK4) != sK1(sK3,sK4)
    | sK1(sK3,sK4) = k1_funct_1(sK3,sK2(sK3,sK4))
    | k1_funct_1(sK3,sK2(sK3,sK4)) != sK1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_2387])).

cnf(c_2417,plain,
    ( sK2(sK3,sK4) = sK2(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1402])).

cnf(c_1948,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_1403])).

cnf(c_6,plain,
    ( ~ sP0(sK1(X0,X1),sK2(X0,X1),X0,X1)
    | ~ r2_hidden(sK1(X0,X1),k2_relat_1(X0))
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | k1_funct_1(X1,sK1(X0,X1)) != sK2(X0,X1)
    | k2_funct_1(X0) = X1
    | k1_relat_1(X1) != k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_325,plain,
    ( ~ sP0(sK1(X0,X1),sK2(X0,X1),X0,X1)
    | ~ r2_hidden(sK1(X0,X1),k2_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | k1_funct_1(X1,sK1(X0,X1)) != sK2(X0,X1)
    | k2_funct_1(X0) = X1
    | k1_relat_1(X1) != k2_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_18])).

cnf(c_326,plain,
    ( ~ sP0(sK1(sK3,X0),sK2(sK3,X0),sK3,X0)
    | ~ r2_hidden(sK1(sK3,X0),k2_relat_1(sK3))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK3)
    | k1_funct_1(X0,sK1(sK3,X0)) != sK2(sK3,X0)
    | k2_funct_1(sK3) = X0
    | k1_relat_1(X0) != k2_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_325])).

cnf(c_330,plain,
    ( ~ v1_funct_1(X0)
    | ~ sP0(sK1(sK3,X0),sK2(sK3,X0),sK3,X0)
    | ~ r2_hidden(sK1(sK3,X0),k2_relat_1(sK3))
    | ~ v1_relat_1(X0)
    | k1_funct_1(X0,sK1(sK3,X0)) != sK2(sK3,X0)
    | k2_funct_1(sK3) = X0
    | k1_relat_1(X0) != k2_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_326,c_22,c_21])).

cnf(c_331,plain,
    ( ~ sP0(sK1(sK3,X0),sK2(sK3,X0),sK3,X0)
    | ~ r2_hidden(sK1(sK3,X0),k2_relat_1(sK3))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_funct_1(X0,sK1(sK3,X0)) != sK2(sK3,X0)
    | k2_funct_1(sK3) = X0
    | k1_relat_1(X0) != k2_relat_1(sK3) ),
    inference(renaming,[status(thm)],[c_330])).

cnf(c_412,plain,
    ( ~ sP0(sK1(sK3,X0),sK2(sK3,X0),sK3,X0)
    | ~ r2_hidden(sK1(sK3,X0),k2_relat_1(sK3))
    | ~ v1_relat_1(X0)
    | k1_funct_1(X0,sK1(sK3,X0)) != sK2(sK3,X0)
    | k2_funct_1(sK3) = X0
    | k1_relat_1(X0) != k2_relat_1(sK3)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_331,c_19])).

cnf(c_413,plain,
    ( ~ sP0(sK1(sK3,sK4),sK2(sK3,sK4),sK3,sK4)
    | ~ r2_hidden(sK1(sK3,sK4),k2_relat_1(sK3))
    | ~ v1_relat_1(sK4)
    | k1_funct_1(sK4,sK1(sK3,sK4)) != sK2(sK3,sK4)
    | k2_funct_1(sK3) = sK4
    | k1_relat_1(sK4) != k2_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_412])).

cnf(c_415,plain,
    ( ~ r2_hidden(sK1(sK3,sK4),k2_relat_1(sK3))
    | ~ sP0(sK1(sK3,sK4),sK2(sK3,sK4),sK3,sK4)
    | k1_funct_1(sK4,sK1(sK3,sK4)) != sK2(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_413,c_20,c_16,c_13])).

cnf(c_416,plain,
    ( ~ sP0(sK1(sK3,sK4),sK2(sK3,sK4),sK3,sK4)
    | ~ r2_hidden(sK1(sK3,sK4),k2_relat_1(sK3))
    | k1_funct_1(sK4,sK1(sK3,sK4)) != sK2(sK3,sK4) ),
    inference(renaming,[status(thm)],[c_415])).

cnf(c_1390,plain,
    ( ~ sP0(sK1(sK3,sK4),sK2(sK3,sK4),sK3,sK4)
    | ~ r2_hidden(sK1(sK3,sK4),k2_relat_1(sK3))
    | k1_funct_1(sK4,sK1(sK3,sK4)) != sK2(sK3,sK4) ),
    inference(subtyping,[status(esa)],[c_416])).

cnf(c_1449,plain,
    ( k1_funct_1(sK4,sK1(sK3,sK4)) != sK2(sK3,sK4)
    | sP0(sK1(sK3,sK4),sK2(sK3,sK4),sK3,sK4) != iProver_top
    | r2_hidden(sK1(sK3,sK4),k2_relat_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1390])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7975,c_4857,c_4681,c_4188,c_3818,c_2914,c_2727,c_2417,c_2012,c_1948,c_1449,c_1426])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:23:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.85/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.85/1.00  
% 3.85/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.85/1.00  
% 3.85/1.00  ------  iProver source info
% 3.85/1.00  
% 3.85/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.85/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.85/1.00  git: non_committed_changes: false
% 3.85/1.00  git: last_make_outside_of_git: false
% 3.85/1.00  
% 3.85/1.00  ------ 
% 3.85/1.00  ------ Parsing...
% 3.85/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.85/1.00  
% 3.85/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.85/1.00  
% 3.85/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.85/1.00  
% 3.85/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.85/1.00  ------ Proving...
% 3.85/1.00  ------ Problem Properties 
% 3.85/1.00  
% 3.85/1.00  
% 3.85/1.00  clauses                                 21
% 3.85/1.00  conjectures                             5
% 3.85/1.00  EPR                                     0
% 3.85/1.00  Horn                                    17
% 3.85/1.00  unary                                   3
% 3.85/1.00  binary                                  9
% 3.85/1.00  lits                                    52
% 3.85/1.00  lits eq                                 22
% 3.85/1.00  fd_pure                                 0
% 3.85/1.00  fd_pseudo                               0
% 3.85/1.00  fd_cond                                 0
% 3.85/1.00  fd_pseudo_cond                          1
% 3.85/1.00  AC symbols                              0
% 3.85/1.00  
% 3.85/1.00  ------ Input Options Time Limit: Unbounded
% 3.85/1.00  
% 3.85/1.00  
% 3.85/1.00  ------ 
% 3.85/1.00  Current options:
% 3.85/1.00  ------ 
% 3.85/1.00  
% 3.85/1.00  
% 3.85/1.00  
% 3.85/1.00  
% 3.85/1.00  ------ Proving...
% 3.85/1.00  
% 3.85/1.00  
% 3.85/1.00  % SZS status Theorem for theBenchmark.p
% 3.85/1.00  
% 3.85/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.85/1.00  
% 3.85/1.00  fof(f11,plain,(
% 3.85/1.00    ! [X2,X3,X0,X1] : (sP0(X2,X3,X0,X1) <=> ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))))),
% 3.85/1.00    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.85/1.00  
% 3.85/1.00  fof(f13,plain,(
% 3.85/1.00    ! [X2,X3,X0,X1] : ((sP0(X2,X3,X0,X1) | ((k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0)))) & (((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))) | ~sP0(X2,X3,X0,X1)))),
% 3.85/1.00    inference(nnf_transformation,[],[f11])).
% 3.85/1.00  
% 3.85/1.00  fof(f14,plain,(
% 3.85/1.00    ! [X2,X3,X0,X1] : ((sP0(X2,X3,X0,X1) | ((k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0)))) & ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0)) | ~sP0(X2,X3,X0,X1)))),
% 3.85/1.00    inference(flattening,[],[f13])).
% 3.85/1.00  
% 3.85/1.00  fof(f15,plain,(
% 3.85/1.00    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ((k1_funct_1(X2,X1) != X0 | ~r2_hidden(X1,k1_relat_1(X2))) & k1_funct_1(X3,X0) = X1 & r2_hidden(X0,k2_relat_1(X2)))) & ((k1_funct_1(X2,X1) = X0 & r2_hidden(X1,k1_relat_1(X2))) | k1_funct_1(X3,X0) != X1 | ~r2_hidden(X0,k2_relat_1(X2)) | ~sP0(X0,X1,X2,X3)))),
% 3.85/1.00    inference(rectify,[],[f14])).
% 3.85/1.00  
% 3.85/1.00  fof(f28,plain,(
% 3.85/1.00    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2,X3) | r2_hidden(X0,k2_relat_1(X2))) )),
% 3.85/1.00    inference(cnf_transformation,[],[f15])).
% 3.85/1.00  
% 3.85/1.00  fof(f2,axiom,(
% 3.85/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) => (k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0)))) & ((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) => (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) & k1_relat_1(X1) = k2_relat_1(X0))))))),
% 3.85/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/1.00  
% 3.85/1.00  fof(f7,plain,(
% 3.85/1.00    ! [X0] : ((! [X1] : ((k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | (k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))))) & k1_relat_1(X1) = k2_relat_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.85/1.00    inference(ennf_transformation,[],[f2])).
% 3.85/1.00  
% 3.85/1.00  fof(f8,plain,(
% 3.85/1.00    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0)))) & k1_relat_1(X1) = k2_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.85/1.00    inference(flattening,[],[f7])).
% 3.85/1.00  
% 3.85/1.00  fof(f12,plain,(
% 3.85/1.00    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & sP0(X2,X3,X0,X1)) & k1_relat_1(X1) = k2_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.85/1.00    inference(definition_folding,[],[f8,f11])).
% 3.85/1.00  
% 3.85/1.00  fof(f16,plain,(
% 3.85/1.00    ! [X0] : (! [X1] : (((k2_funct_1(X0) = X1 | (? [X2,X3] : (((k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))) & k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X2,X3,X0,X1)) | k1_relat_1(X1) != k2_relat_1(X0))) & ((! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & sP0(X2,X3,X0,X1)) & k1_relat_1(X1) = k2_relat_1(X0)) | k2_funct_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.85/1.00    inference(nnf_transformation,[],[f12])).
% 3.85/1.00  
% 3.85/1.00  fof(f17,plain,(
% 3.85/1.00    ! [X0] : (! [X1] : (((k2_funct_1(X0) = X1 | ? [X2,X3] : (((k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))) & k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X2,X3,X0,X1)) | k1_relat_1(X1) != k2_relat_1(X0)) & ((! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & sP0(X2,X3,X0,X1)) & k1_relat_1(X1) = k2_relat_1(X0)) | k2_funct_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.85/1.00    inference(flattening,[],[f16])).
% 3.85/1.00  
% 3.85/1.00  fof(f18,plain,(
% 3.85/1.00    ! [X0] : (! [X1] : (((k2_funct_1(X0) = X1 | ? [X2,X3] : (((k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))) & k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X2,X3,X0,X1)) | k1_relat_1(X1) != k2_relat_1(X0)) & ((! [X4,X5] : (((k1_funct_1(X1,X4) = X5 & r2_hidden(X4,k2_relat_1(X0))) | k1_funct_1(X0,X5) != X4 | ~r2_hidden(X5,k1_relat_1(X0))) & sP0(X4,X5,X0,X1)) & k1_relat_1(X1) = k2_relat_1(X0)) | k2_funct_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.85/1.00    inference(rectify,[],[f17])).
% 3.85/1.00  
% 3.85/1.00  fof(f19,plain,(
% 3.85/1.00    ! [X1,X0] : (? [X2,X3] : (((k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))) & k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X2,X3,X0,X1)) => (((k1_funct_1(X1,sK1(X0,X1)) != sK2(X0,X1) | ~r2_hidden(sK1(X0,X1),k2_relat_1(X0))) & k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))) | ~sP0(sK1(X0,X1),sK2(X0,X1),X0,X1)))),
% 3.85/1.00    introduced(choice_axiom,[])).
% 3.85/1.00  
% 3.85/1.00  fof(f20,plain,(
% 3.85/1.00    ! [X0] : (! [X1] : (((k2_funct_1(X0) = X1 | (((k1_funct_1(X1,sK1(X0,X1)) != sK2(X0,X1) | ~r2_hidden(sK1(X0,X1),k2_relat_1(X0))) & k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))) | ~sP0(sK1(X0,X1),sK2(X0,X1),X0,X1)) | k1_relat_1(X1) != k2_relat_1(X0)) & ((! [X4,X5] : (((k1_funct_1(X1,X4) = X5 & r2_hidden(X4,k2_relat_1(X0))) | k1_funct_1(X0,X5) != X4 | ~r2_hidden(X5,k1_relat_1(X0))) & sP0(X4,X5,X0,X1)) & k1_relat_1(X1) = k2_relat_1(X0)) | k2_funct_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.85/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f18,f19])).
% 3.85/1.00  
% 3.85/1.00  fof(f35,plain,(
% 3.85/1.00    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | r2_hidden(sK2(X0,X1),k1_relat_1(X0)) | ~sP0(sK1(X0,X1),sK2(X0,X1),X0,X1) | k1_relat_1(X1) != k2_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.85/1.00    inference(cnf_transformation,[],[f20])).
% 3.85/1.00  
% 3.85/1.00  fof(f3,conjecture,(
% 3.85/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2,X3] : ((r2_hidden(X3,k1_relat_1(X1)) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,X2) = X3 <=> k1_funct_1(X1,X3) = X2)) & k1_relat_1(X1) = k2_relat_1(X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 3.85/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/1.00  
% 3.85/1.00  fof(f4,negated_conjecture,(
% 3.85/1.00    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2,X3] : ((r2_hidden(X3,k1_relat_1(X1)) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,X2) = X3 <=> k1_funct_1(X1,X3) = X2)) & k1_relat_1(X1) = k2_relat_1(X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 3.85/1.00    inference(negated_conjecture,[],[f3])).
% 3.85/1.00  
% 3.85/1.00  fof(f9,plain,(
% 3.85/1.00    ? [X0] : (? [X1] : ((k2_funct_1(X0) != X1 & (! [X2,X3] : ((k1_funct_1(X0,X2) = X3 <=> k1_funct_1(X1,X3) = X2) | (~r2_hidden(X3,k1_relat_1(X1)) | ~r2_hidden(X2,k1_relat_1(X0)))) & k1_relat_1(X1) = k2_relat_1(X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 3.85/1.00    inference(ennf_transformation,[],[f4])).
% 3.85/1.00  
% 3.85/1.00  fof(f10,plain,(
% 3.85/1.00    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & ! [X2,X3] : ((k1_funct_1(X0,X2) = X3 <=> k1_funct_1(X1,X3) = X2) | ~r2_hidden(X3,k1_relat_1(X1)) | ~r2_hidden(X2,k1_relat_1(X0))) & k1_relat_1(X1) = k2_relat_1(X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 3.85/1.00    inference(flattening,[],[f9])).
% 3.85/1.00  
% 3.85/1.00  fof(f21,plain,(
% 3.85/1.00    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & ! [X2,X3] : (((k1_funct_1(X0,X2) = X3 | k1_funct_1(X1,X3) != X2) & (k1_funct_1(X1,X3) = X2 | k1_funct_1(X0,X2) != X3)) | ~r2_hidden(X3,k1_relat_1(X1)) | ~r2_hidden(X2,k1_relat_1(X0))) & k1_relat_1(X1) = k2_relat_1(X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 3.85/1.00    inference(nnf_transformation,[],[f10])).
% 3.85/1.00  
% 3.85/1.00  fof(f23,plain,(
% 3.85/1.00    ( ! [X0] : (? [X1] : (k2_funct_1(X0) != X1 & ! [X2,X3] : (((k1_funct_1(X0,X2) = X3 | k1_funct_1(X1,X3) != X2) & (k1_funct_1(X1,X3) = X2 | k1_funct_1(X0,X2) != X3)) | ~r2_hidden(X3,k1_relat_1(X1)) | ~r2_hidden(X2,k1_relat_1(X0))) & k1_relat_1(X1) = k2_relat_1(X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) => (k2_funct_1(X0) != sK4 & ! [X3,X2] : (((k1_funct_1(X0,X2) = X3 | k1_funct_1(sK4,X3) != X2) & (k1_funct_1(sK4,X3) = X2 | k1_funct_1(X0,X2) != X3)) | ~r2_hidden(X3,k1_relat_1(sK4)) | ~r2_hidden(X2,k1_relat_1(X0))) & k1_relat_1(sK4) = k2_relat_1(X0) & k1_relat_1(X0) = k2_relat_1(sK4) & v2_funct_1(X0) & v1_funct_1(sK4) & v1_relat_1(sK4))) )),
% 3.85/1.00    introduced(choice_axiom,[])).
% 3.85/1.00  
% 3.85/1.00  fof(f22,plain,(
% 3.85/1.00    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & ! [X2,X3] : (((k1_funct_1(X0,X2) = X3 | k1_funct_1(X1,X3) != X2) & (k1_funct_1(X1,X3) = X2 | k1_funct_1(X0,X2) != X3)) | ~r2_hidden(X3,k1_relat_1(X1)) | ~r2_hidden(X2,k1_relat_1(X0))) & k1_relat_1(X1) = k2_relat_1(X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k2_funct_1(sK3) != X1 & ! [X3,X2] : (((k1_funct_1(sK3,X2) = X3 | k1_funct_1(X1,X3) != X2) & (k1_funct_1(X1,X3) = X2 | k1_funct_1(sK3,X2) != X3)) | ~r2_hidden(X3,k1_relat_1(X1)) | ~r2_hidden(X2,k1_relat_1(sK3))) & k1_relat_1(X1) = k2_relat_1(sK3) & k1_relat_1(sK3) = k2_relat_1(X1) & v2_funct_1(sK3) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK3) & v1_relat_1(sK3))),
% 3.85/1.00    introduced(choice_axiom,[])).
% 3.85/1.00  
% 3.85/1.00  fof(f24,plain,(
% 3.85/1.00    (k2_funct_1(sK3) != sK4 & ! [X2,X3] : (((k1_funct_1(sK3,X2) = X3 | k1_funct_1(sK4,X3) != X2) & (k1_funct_1(sK4,X3) = X2 | k1_funct_1(sK3,X2) != X3)) | ~r2_hidden(X3,k1_relat_1(sK4)) | ~r2_hidden(X2,k1_relat_1(sK3))) & k1_relat_1(sK4) = k2_relat_1(sK3) & k1_relat_1(sK3) = k2_relat_1(sK4) & v2_funct_1(sK3) & v1_funct_1(sK4) & v1_relat_1(sK4)) & v1_funct_1(sK3) & v1_relat_1(sK3)),
% 3.85/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f21,f23,f22])).
% 3.85/1.00  
% 3.85/1.00  fof(f42,plain,(
% 3.85/1.00    v2_funct_1(sK3)),
% 3.85/1.00    inference(cnf_transformation,[],[f24])).
% 3.85/1.00  
% 3.85/1.00  fof(f38,plain,(
% 3.85/1.00    v1_relat_1(sK3)),
% 3.85/1.00    inference(cnf_transformation,[],[f24])).
% 3.85/1.00  
% 3.85/1.00  fof(f39,plain,(
% 3.85/1.00    v1_funct_1(sK3)),
% 3.85/1.00    inference(cnf_transformation,[],[f24])).
% 3.85/1.00  
% 3.85/1.00  fof(f41,plain,(
% 3.85/1.00    v1_funct_1(sK4)),
% 3.85/1.00    inference(cnf_transformation,[],[f24])).
% 3.85/1.00  
% 3.85/1.00  fof(f40,plain,(
% 3.85/1.00    v1_relat_1(sK4)),
% 3.85/1.00    inference(cnf_transformation,[],[f24])).
% 3.85/1.00  
% 3.85/1.00  fof(f44,plain,(
% 3.85/1.00    k1_relat_1(sK4) = k2_relat_1(sK3)),
% 3.85/1.00    inference(cnf_transformation,[],[f24])).
% 3.85/1.00  
% 3.85/1.00  fof(f47,plain,(
% 3.85/1.00    k2_funct_1(sK3) != sK4),
% 3.85/1.00    inference(cnf_transformation,[],[f24])).
% 3.85/1.00  
% 3.85/1.00  fof(f45,plain,(
% 3.85/1.00    ( ! [X2,X3] : (k1_funct_1(sK4,X3) = X2 | k1_funct_1(sK3,X2) != X3 | ~r2_hidden(X3,k1_relat_1(sK4)) | ~r2_hidden(X2,k1_relat_1(sK3))) )),
% 3.85/1.00    inference(cnf_transformation,[],[f24])).
% 3.85/1.00  
% 3.85/1.00  fof(f58,plain,(
% 3.85/1.00    ( ! [X2] : (k1_funct_1(sK4,k1_funct_1(sK3,X2)) = X2 | ~r2_hidden(k1_funct_1(sK3,X2),k1_relat_1(sK4)) | ~r2_hidden(X2,k1_relat_1(sK3))) )),
% 3.85/1.00    inference(equality_resolution,[],[f45])).
% 3.85/1.00  
% 3.85/1.00  fof(f1,axiom,(
% 3.85/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 3.85/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/1.00  
% 3.85/1.00  fof(f5,plain,(
% 3.85/1.00    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.85/1.00    inference(ennf_transformation,[],[f1])).
% 3.85/1.00  
% 3.85/1.00  fof(f6,plain,(
% 3.85/1.00    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.85/1.00    inference(flattening,[],[f5])).
% 3.85/1.00  
% 3.85/1.00  fof(f25,plain,(
% 3.85/1.00    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.85/1.00    inference(cnf_transformation,[],[f6])).
% 3.85/1.00  
% 3.85/1.00  fof(f43,plain,(
% 3.85/1.00    k1_relat_1(sK3) = k2_relat_1(sK4)),
% 3.85/1.00    inference(cnf_transformation,[],[f24])).
% 3.85/1.00  
% 3.85/1.00  fof(f27,plain,(
% 3.85/1.00    ( ! [X2,X0,X3,X1] : (k1_funct_1(X2,X1) = X0 | k1_funct_1(X3,X0) != X1 | ~r2_hidden(X0,k2_relat_1(X2)) | ~sP0(X0,X1,X2,X3)) )),
% 3.85/1.00    inference(cnf_transformation,[],[f15])).
% 3.85/1.00  
% 3.85/1.00  fof(f49,plain,(
% 3.85/1.00    ( ! [X2,X0,X3] : (k1_funct_1(X2,k1_funct_1(X3,X0)) = X0 | ~r2_hidden(X0,k2_relat_1(X2)) | ~sP0(X0,k1_funct_1(X3,X0),X2,X3)) )),
% 3.85/1.00    inference(equality_resolution,[],[f27])).
% 3.85/1.00  
% 3.85/1.00  fof(f29,plain,(
% 3.85/1.00    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2,X3) | k1_funct_1(X3,X0) = X1) )),
% 3.85/1.00    inference(cnf_transformation,[],[f15])).
% 3.85/1.00  
% 3.85/1.00  fof(f36,plain,(
% 3.85/1.00    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1) | ~sP0(sK1(X0,X1),sK2(X0,X1),X0,X1) | k1_relat_1(X1) != k2_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.85/1.00    inference(cnf_transformation,[],[f20])).
% 3.85/1.00  
% 3.85/1.00  fof(f46,plain,(
% 3.85/1.00    ( ! [X2,X3] : (k1_funct_1(sK3,X2) = X3 | k1_funct_1(sK4,X3) != X2 | ~r2_hidden(X3,k1_relat_1(sK4)) | ~r2_hidden(X2,k1_relat_1(sK3))) )),
% 3.85/1.00    inference(cnf_transformation,[],[f24])).
% 3.85/1.00  
% 3.85/1.00  fof(f57,plain,(
% 3.85/1.00    ( ! [X3] : (k1_funct_1(sK3,k1_funct_1(sK4,X3)) = X3 | ~r2_hidden(X3,k1_relat_1(sK4)) | ~r2_hidden(k1_funct_1(sK4,X3),k1_relat_1(sK3))) )),
% 3.85/1.00    inference(equality_resolution,[],[f46])).
% 3.85/1.00  
% 3.85/1.00  fof(f30,plain,(
% 3.85/1.00    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2,X3) | k1_funct_1(X2,X1) != X0 | ~r2_hidden(X1,k1_relat_1(X2))) )),
% 3.85/1.00    inference(cnf_transformation,[],[f15])).
% 3.85/1.00  
% 3.85/1.00  fof(f48,plain,(
% 3.85/1.00    ( ! [X2,X3,X1] : (sP0(k1_funct_1(X2,X1),X1,X2,X3) | ~r2_hidden(X1,k1_relat_1(X2))) )),
% 3.85/1.00    inference(equality_resolution,[],[f30])).
% 3.85/1.00  
% 3.85/1.00  fof(f26,plain,(
% 3.85/1.00    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,k1_relat_1(X2)) | k1_funct_1(X3,X0) != X1 | ~r2_hidden(X0,k2_relat_1(X2)) | ~sP0(X0,X1,X2,X3)) )),
% 3.85/1.00    inference(cnf_transformation,[],[f15])).
% 3.85/1.00  
% 3.85/1.00  fof(f50,plain,(
% 3.85/1.00    ( ! [X2,X0,X3] : (r2_hidden(k1_funct_1(X3,X0),k1_relat_1(X2)) | ~r2_hidden(X0,k2_relat_1(X2)) | ~sP0(X0,k1_funct_1(X3,X0),X2,X3)) )),
% 3.85/1.00    inference(equality_resolution,[],[f26])).
% 3.85/1.00  
% 3.85/1.00  fof(f37,plain,(
% 3.85/1.00    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k1_funct_1(X1,sK1(X0,X1)) != sK2(X0,X1) | ~r2_hidden(sK1(X0,X1),k2_relat_1(X0)) | ~sP0(sK1(X0,X1),sK2(X0,X1),X0,X1) | k1_relat_1(X1) != k2_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.85/1.00    inference(cnf_transformation,[],[f20])).
% 3.85/1.00  
% 3.85/1.00  cnf(c_3,plain,
% 3.85/1.00      ( sP0(X0,X1,X2,X3) | r2_hidden(X0,k2_relat_1(X2)) ),
% 3.85/1.00      inference(cnf_transformation,[],[f28]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1398,plain,
% 3.85/1.00      ( sP0(X0_41,X1_41,X0_42,X1_42)
% 3.85/1.00      | r2_hidden(X0_41,k2_relat_1(X0_42)) ),
% 3.85/1.00      inference(subtyping,[status(esa)],[c_3]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1751,plain,
% 3.85/1.00      ( sP0(X0_41,X1_41,X0_42,X1_42) = iProver_top
% 3.85/1.00      | r2_hidden(X0_41,k2_relat_1(X0_42)) = iProver_top ),
% 3.85/1.00      inference(predicate_to_equality,[status(thm)],[c_1398]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_8,plain,
% 3.85/1.00      ( ~ sP0(sK1(X0,X1),sK2(X0,X1),X0,X1)
% 3.85/1.00      | r2_hidden(sK2(X0,X1),k1_relat_1(X0))
% 3.85/1.00      | ~ v2_funct_1(X0)
% 3.85/1.00      | ~ v1_relat_1(X1)
% 3.85/1.00      | ~ v1_relat_1(X0)
% 3.85/1.00      | ~ v1_funct_1(X1)
% 3.85/1.00      | ~ v1_funct_1(X0)
% 3.85/1.00      | k2_funct_1(X0) = X1
% 3.85/1.00      | k1_relat_1(X1) != k2_relat_1(X0) ),
% 3.85/1.00      inference(cnf_transformation,[],[f35]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_18,negated_conjecture,
% 3.85/1.00      ( v2_funct_1(sK3) ),
% 3.85/1.00      inference(cnf_transformation,[],[f42]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_269,plain,
% 3.85/1.00      ( ~ sP0(sK1(X0,X1),sK2(X0,X1),X0,X1)
% 3.85/1.00      | r2_hidden(sK2(X0,X1),k1_relat_1(X0))
% 3.85/1.00      | ~ v1_relat_1(X0)
% 3.85/1.00      | ~ v1_relat_1(X1)
% 3.85/1.00      | ~ v1_funct_1(X0)
% 3.85/1.00      | ~ v1_funct_1(X1)
% 3.85/1.00      | k2_funct_1(X0) = X1
% 3.85/1.00      | k1_relat_1(X1) != k2_relat_1(X0)
% 3.85/1.00      | sK3 != X0 ),
% 3.85/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_18]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_270,plain,
% 3.85/1.00      ( ~ sP0(sK1(sK3,X0),sK2(sK3,X0),sK3,X0)
% 3.85/1.00      | r2_hidden(sK2(sK3,X0),k1_relat_1(sK3))
% 3.85/1.00      | ~ v1_relat_1(X0)
% 3.85/1.00      | ~ v1_relat_1(sK3)
% 3.85/1.00      | ~ v1_funct_1(X0)
% 3.85/1.00      | ~ v1_funct_1(sK3)
% 3.85/1.00      | k2_funct_1(sK3) = X0
% 3.85/1.00      | k1_relat_1(X0) != k2_relat_1(sK3) ),
% 3.85/1.00      inference(unflattening,[status(thm)],[c_269]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_22,negated_conjecture,
% 3.85/1.00      ( v1_relat_1(sK3) ),
% 3.85/1.00      inference(cnf_transformation,[],[f38]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_21,negated_conjecture,
% 3.85/1.00      ( v1_funct_1(sK3) ),
% 3.85/1.00      inference(cnf_transformation,[],[f39]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_274,plain,
% 3.85/1.00      ( ~ v1_funct_1(X0)
% 3.85/1.00      | ~ sP0(sK1(sK3,X0),sK2(sK3,X0),sK3,X0)
% 3.85/1.00      | r2_hidden(sK2(sK3,X0),k1_relat_1(sK3))
% 3.85/1.00      | ~ v1_relat_1(X0)
% 3.85/1.00      | k2_funct_1(sK3) = X0
% 3.85/1.00      | k1_relat_1(X0) != k2_relat_1(sK3) ),
% 3.85/1.00      inference(global_propositional_subsumption,
% 3.85/1.00                [status(thm)],
% 3.85/1.00                [c_270,c_22,c_21]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_275,plain,
% 3.85/1.00      ( ~ sP0(sK1(sK3,X0),sK2(sK3,X0),sK3,X0)
% 3.85/1.00      | r2_hidden(sK2(sK3,X0),k1_relat_1(sK3))
% 3.85/1.00      | ~ v1_relat_1(X0)
% 3.85/1.00      | ~ v1_funct_1(X0)
% 3.85/1.00      | k2_funct_1(sK3) = X0
% 3.85/1.00      | k1_relat_1(X0) != k2_relat_1(sK3) ),
% 3.85/1.00      inference(renaming,[status(thm)],[c_274]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_19,negated_conjecture,
% 3.85/1.00      ( v1_funct_1(sK4) ),
% 3.85/1.00      inference(cnf_transformation,[],[f41]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_443,plain,
% 3.85/1.00      ( ~ sP0(sK1(sK3,X0),sK2(sK3,X0),sK3,X0)
% 3.85/1.00      | r2_hidden(sK2(sK3,X0),k1_relat_1(sK3))
% 3.85/1.00      | ~ v1_relat_1(X0)
% 3.85/1.00      | k2_funct_1(sK3) = X0
% 3.85/1.00      | k1_relat_1(X0) != k2_relat_1(sK3)
% 3.85/1.00      | sK4 != X0 ),
% 3.85/1.00      inference(resolution_lifted,[status(thm)],[c_275,c_19]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_444,plain,
% 3.85/1.00      ( ~ sP0(sK1(sK3,sK4),sK2(sK3,sK4),sK3,sK4)
% 3.85/1.00      | r2_hidden(sK2(sK3,sK4),k1_relat_1(sK3))
% 3.85/1.00      | ~ v1_relat_1(sK4)
% 3.85/1.00      | k2_funct_1(sK3) = sK4
% 3.85/1.00      | k1_relat_1(sK4) != k2_relat_1(sK3) ),
% 3.85/1.00      inference(unflattening,[status(thm)],[c_443]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_20,negated_conjecture,
% 3.85/1.00      ( v1_relat_1(sK4) ),
% 3.85/1.00      inference(cnf_transformation,[],[f40]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_16,negated_conjecture,
% 3.85/1.00      ( k1_relat_1(sK4) = k2_relat_1(sK3) ),
% 3.85/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_13,negated_conjecture,
% 3.85/1.00      ( k2_funct_1(sK3) != sK4 ),
% 3.85/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_446,plain,
% 3.85/1.00      ( r2_hidden(sK2(sK3,sK4),k1_relat_1(sK3))
% 3.85/1.00      | ~ sP0(sK1(sK3,sK4),sK2(sK3,sK4),sK3,sK4) ),
% 3.85/1.00      inference(global_propositional_subsumption,
% 3.85/1.00                [status(thm)],
% 3.85/1.00                [c_444,c_20,c_16,c_13]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_447,plain,
% 3.85/1.00      ( ~ sP0(sK1(sK3,sK4),sK2(sK3,sK4),sK3,sK4)
% 3.85/1.00      | r2_hidden(sK2(sK3,sK4),k1_relat_1(sK3)) ),
% 3.85/1.00      inference(renaming,[status(thm)],[c_446]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1388,plain,
% 3.85/1.00      ( ~ sP0(sK1(sK3,sK4),sK2(sK3,sK4),sK3,sK4)
% 3.85/1.00      | r2_hidden(sK2(sK3,sK4),k1_relat_1(sK3)) ),
% 3.85/1.00      inference(subtyping,[status(esa)],[c_447]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1758,plain,
% 3.85/1.00      ( sP0(sK1(sK3,sK4),sK2(sK3,sK4),sK3,sK4) != iProver_top
% 3.85/1.00      | r2_hidden(sK2(sK3,sK4),k1_relat_1(sK3)) = iProver_top ),
% 3.85/1.00      inference(predicate_to_equality,[status(thm)],[c_1388]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2432,plain,
% 3.85/1.00      ( r2_hidden(sK2(sK3,sK4),k1_relat_1(sK3)) = iProver_top
% 3.85/1.00      | r2_hidden(sK1(sK3,sK4),k2_relat_1(sK3)) = iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_1751,c_1758]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1392,negated_conjecture,
% 3.85/1.00      ( k1_relat_1(sK4) = k2_relat_1(sK3) ),
% 3.85/1.00      inference(subtyping,[status(esa)],[c_16]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_15,negated_conjecture,
% 3.85/1.00      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 3.85/1.00      | ~ r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4))
% 3.85/1.00      | k1_funct_1(sK4,k1_funct_1(sK3,X0)) = X0 ),
% 3.85/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1393,negated_conjecture,
% 3.85/1.00      ( ~ r2_hidden(X0_41,k1_relat_1(sK3))
% 3.85/1.00      | ~ r2_hidden(k1_funct_1(sK3,X0_41),k1_relat_1(sK4))
% 3.85/1.00      | k1_funct_1(sK4,k1_funct_1(sK3,X0_41)) = X0_41 ),
% 3.85/1.00      inference(subtyping,[status(esa)],[c_15]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1755,plain,
% 3.85/1.00      ( k1_funct_1(sK4,k1_funct_1(sK3,X0_41)) = X0_41
% 3.85/1.00      | r2_hidden(X0_41,k1_relat_1(sK3)) != iProver_top
% 3.85/1.00      | r2_hidden(k1_funct_1(sK3,X0_41),k1_relat_1(sK4)) != iProver_top ),
% 3.85/1.00      inference(predicate_to_equality,[status(thm)],[c_1393]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1971,plain,
% 3.85/1.00      ( k1_funct_1(sK4,k1_funct_1(sK3,X0_41)) = X0_41
% 3.85/1.00      | r2_hidden(X0_41,k1_relat_1(sK3)) != iProver_top
% 3.85/1.00      | r2_hidden(k1_funct_1(sK3,X0_41),k2_relat_1(sK3)) != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_1392,c_1755]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_0,plain,
% 3.85/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.85/1.00      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 3.85/1.00      | ~ v1_relat_1(X1)
% 3.85/1.00      | ~ v1_funct_1(X1) ),
% 3.85/1.00      inference(cnf_transformation,[],[f25]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_538,plain,
% 3.85/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.85/1.00      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 3.85/1.00      | ~ v1_relat_1(X1)
% 3.85/1.00      | sK3 != X1 ),
% 3.85/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_21]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_539,plain,
% 3.85/1.00      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 3.85/1.00      | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3))
% 3.85/1.00      | ~ v1_relat_1(sK3) ),
% 3.85/1.00      inference(unflattening,[status(thm)],[c_538]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_543,plain,
% 3.85/1.00      ( r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3))
% 3.85/1.00      | ~ r2_hidden(X0,k1_relat_1(sK3)) ),
% 3.85/1.00      inference(global_propositional_subsumption,
% 3.85/1.00                [status(thm)],
% 3.85/1.00                [c_539,c_22]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_544,plain,
% 3.85/1.00      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 3.85/1.00      | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3)) ),
% 3.85/1.00      inference(renaming,[status(thm)],[c_543]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1383,plain,
% 3.85/1.00      ( ~ r2_hidden(X0_41,k1_relat_1(sK3))
% 3.85/1.00      | r2_hidden(k1_funct_1(sK3,X0_41),k2_relat_1(sK3)) ),
% 3.85/1.00      inference(subtyping,[status(esa)],[c_544]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1458,plain,
% 3.85/1.00      ( r2_hidden(X0_41,k1_relat_1(sK3)) != iProver_top
% 3.85/1.00      | r2_hidden(k1_funct_1(sK3,X0_41),k2_relat_1(sK3)) = iProver_top ),
% 3.85/1.00      inference(predicate_to_equality,[status(thm)],[c_1383]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2107,plain,
% 3.85/1.00      ( r2_hidden(X0_41,k1_relat_1(sK3)) != iProver_top
% 3.85/1.00      | k1_funct_1(sK4,k1_funct_1(sK3,X0_41)) = X0_41 ),
% 3.85/1.00      inference(global_propositional_subsumption,
% 3.85/1.00                [status(thm)],
% 3.85/1.00                [c_1971,c_1458]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2108,plain,
% 3.85/1.00      ( k1_funct_1(sK4,k1_funct_1(sK3,X0_41)) = X0_41
% 3.85/1.00      | r2_hidden(X0_41,k1_relat_1(sK3)) != iProver_top ),
% 3.85/1.00      inference(renaming,[status(thm)],[c_2107]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2438,plain,
% 3.85/1.00      ( k1_funct_1(sK4,k1_funct_1(sK3,sK2(sK3,sK4))) = sK2(sK3,sK4)
% 3.85/1.00      | r2_hidden(sK1(sK3,sK4),k2_relat_1(sK3)) = iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_2432,c_2108]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_520,plain,
% 3.85/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.85/1.00      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 3.85/1.00      | ~ v1_relat_1(X1)
% 3.85/1.00      | sK4 != X1 ),
% 3.85/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_19]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_521,plain,
% 3.85/1.00      ( ~ r2_hidden(X0,k1_relat_1(sK4))
% 3.85/1.00      | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4))
% 3.85/1.00      | ~ v1_relat_1(sK4) ),
% 3.85/1.00      inference(unflattening,[status(thm)],[c_520]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_525,plain,
% 3.85/1.00      ( r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4))
% 3.85/1.00      | ~ r2_hidden(X0,k1_relat_1(sK4)) ),
% 3.85/1.00      inference(global_propositional_subsumption,
% 3.85/1.00                [status(thm)],
% 3.85/1.00                [c_521,c_20]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_526,plain,
% 3.85/1.00      ( ~ r2_hidden(X0,k1_relat_1(sK4))
% 3.85/1.00      | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) ),
% 3.85/1.00      inference(renaming,[status(thm)],[c_525]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1384,plain,
% 3.85/1.00      ( ~ r2_hidden(X0_41,k1_relat_1(sK4))
% 3.85/1.00      | r2_hidden(k1_funct_1(sK4,X0_41),k2_relat_1(sK4)) ),
% 3.85/1.00      inference(subtyping,[status(esa)],[c_526]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1762,plain,
% 3.85/1.00      ( r2_hidden(X0_41,k1_relat_1(sK4)) != iProver_top
% 3.85/1.00      | r2_hidden(k1_funct_1(sK4,X0_41),k2_relat_1(sK4)) = iProver_top ),
% 3.85/1.00      inference(predicate_to_equality,[status(thm)],[c_1384]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_17,negated_conjecture,
% 3.85/1.00      ( k1_relat_1(sK3) = k2_relat_1(sK4) ),
% 3.85/1.00      inference(cnf_transformation,[],[f43]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1391,negated_conjecture,
% 3.85/1.00      ( k1_relat_1(sK3) = k2_relat_1(sK4) ),
% 3.85/1.00      inference(subtyping,[status(esa)],[c_17]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2113,plain,
% 3.85/1.00      ( k1_funct_1(sK4,k1_funct_1(sK3,X0_41)) = X0_41
% 3.85/1.00      | r2_hidden(X0_41,k2_relat_1(sK4)) != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_1391,c_2108]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_3317,plain,
% 3.85/1.00      ( k1_funct_1(sK4,k1_funct_1(sK3,k1_funct_1(sK4,X0_41))) = k1_funct_1(sK4,X0_41)
% 3.85/1.00      | r2_hidden(X0_41,k1_relat_1(sK4)) != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_1762,c_2113]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_3322,plain,
% 3.85/1.00      ( k1_funct_1(sK4,k1_funct_1(sK3,k1_funct_1(sK4,X0_41))) = k1_funct_1(sK4,X0_41)
% 3.85/1.00      | r2_hidden(X0_41,k2_relat_1(sK3)) != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_1392,c_3317]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_3456,plain,
% 3.85/1.00      ( k1_funct_1(sK4,k1_funct_1(sK3,sK2(sK3,sK4))) = sK2(sK3,sK4)
% 3.85/1.00      | k1_funct_1(sK4,k1_funct_1(sK3,k1_funct_1(sK4,sK1(sK3,sK4)))) = k1_funct_1(sK4,sK1(sK3,sK4)) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_2438,c_3322]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_4,plain,
% 3.85/1.00      ( ~ sP0(X0,k1_funct_1(X1,X0),X2,X1)
% 3.85/1.00      | ~ r2_hidden(X0,k2_relat_1(X2))
% 3.85/1.00      | k1_funct_1(X2,k1_funct_1(X1,X0)) = X0 ),
% 3.85/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1397,plain,
% 3.85/1.00      ( ~ sP0(X0_41,k1_funct_1(X0_42,X0_41),X1_42,X0_42)
% 3.85/1.00      | ~ r2_hidden(X0_41,k2_relat_1(X1_42))
% 3.85/1.00      | k1_funct_1(X1_42,k1_funct_1(X0_42,X0_41)) = X0_41 ),
% 3.85/1.00      inference(subtyping,[status(esa)],[c_4]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1752,plain,
% 3.85/1.00      ( k1_funct_1(X0_42,k1_funct_1(X1_42,X0_41)) = X0_41
% 3.85/1.00      | sP0(X0_41,k1_funct_1(X1_42,X0_41),X0_42,X1_42) != iProver_top
% 3.85/1.00      | r2_hidden(X0_41,k2_relat_1(X0_42)) != iProver_top ),
% 3.85/1.00      inference(predicate_to_equality,[status(thm)],[c_1397]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_4051,plain,
% 3.85/1.00      ( k1_funct_1(X0_42,k1_funct_1(sK4,k1_funct_1(sK3,k1_funct_1(sK4,sK1(sK3,sK4))))) = k1_funct_1(sK3,k1_funct_1(sK4,sK1(sK3,sK4)))
% 3.85/1.00      | k1_funct_1(sK4,k1_funct_1(sK3,sK2(sK3,sK4))) = sK2(sK3,sK4)
% 3.85/1.00      | sP0(k1_funct_1(sK3,k1_funct_1(sK4,sK1(sK3,sK4))),k1_funct_1(sK4,sK1(sK3,sK4)),X0_42,sK4) != iProver_top
% 3.85/1.00      | r2_hidden(k1_funct_1(sK3,k1_funct_1(sK4,sK1(sK3,sK4))),k2_relat_1(X0_42)) != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_3456,c_1752]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1402,plain,( X0_41 = X0_41 ),theory(equality) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2012,plain,
% 3.85/1.00      ( sK1(sK3,sK4) = sK1(sK3,sK4) ),
% 3.85/1.00      inference(instantiation,[status(thm)],[c_1402]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1410,plain,
% 3.85/1.00      ( ~ r2_hidden(X0_41,X0_43)
% 3.85/1.00      | r2_hidden(X1_41,X1_43)
% 3.85/1.00      | X1_43 != X0_43
% 3.85/1.00      | X1_41 != X0_41 ),
% 3.85/1.00      theory(equality) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1899,plain,
% 3.85/1.00      ( r2_hidden(X0_41,X0_43)
% 3.85/1.00      | ~ r2_hidden(sK1(sK3,sK4),k2_relat_1(sK3))
% 3.85/1.00      | X0_43 != k2_relat_1(sK3)
% 3.85/1.00      | X0_41 != sK1(sK3,sK4) ),
% 3.85/1.00      inference(instantiation,[status(thm)],[c_1410]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2011,plain,
% 3.85/1.00      ( r2_hidden(sK1(sK3,sK4),X0_43)
% 3.85/1.00      | ~ r2_hidden(sK1(sK3,sK4),k2_relat_1(sK3))
% 3.85/1.00      | X0_43 != k2_relat_1(sK3)
% 3.85/1.00      | sK1(sK3,sK4) != sK1(sK3,sK4) ),
% 3.85/1.00      inference(instantiation,[status(thm)],[c_1899]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2309,plain,
% 3.85/1.00      ( r2_hidden(sK1(sK3,sK4),k1_relat_1(sK4))
% 3.85/1.00      | ~ r2_hidden(sK1(sK3,sK4),k2_relat_1(sK3))
% 3.85/1.00      | k1_relat_1(sK4) != k2_relat_1(sK3)
% 3.85/1.00      | sK1(sK3,sK4) != sK1(sK3,sK4) ),
% 3.85/1.00      inference(instantiation,[status(thm)],[c_2011]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2310,plain,
% 3.85/1.00      ( k1_relat_1(sK4) != k2_relat_1(sK3)
% 3.85/1.00      | sK1(sK3,sK4) != sK1(sK3,sK4)
% 3.85/1.00      | r2_hidden(sK1(sK3,sK4),k1_relat_1(sK4)) = iProver_top
% 3.85/1.00      | r2_hidden(sK1(sK3,sK4),k2_relat_1(sK3)) != iProver_top ),
% 3.85/1.00      inference(predicate_to_equality,[status(thm)],[c_2309]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2,plain,
% 3.85/1.00      ( sP0(X0,X1,X2,X3) | k1_funct_1(X3,X0) = X1 ),
% 3.85/1.00      inference(cnf_transformation,[],[f29]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1399,plain,
% 3.85/1.00      ( sP0(X0_41,X1_41,X0_42,X1_42) | k1_funct_1(X1_42,X0_41) = X1_41 ),
% 3.85/1.00      inference(subtyping,[status(esa)],[c_2]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1750,plain,
% 3.85/1.00      ( k1_funct_1(X0_42,X0_41) = X1_41
% 3.85/1.00      | sP0(X0_41,X1_41,X1_42,X0_42) = iProver_top ),
% 3.85/1.00      inference(predicate_to_equality,[status(thm)],[c_1399]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_7,plain,
% 3.85/1.00      ( ~ sP0(sK1(X0,X1),sK2(X0,X1),X0,X1)
% 3.85/1.00      | ~ v2_funct_1(X0)
% 3.85/1.00      | ~ v1_relat_1(X1)
% 3.85/1.00      | ~ v1_relat_1(X0)
% 3.85/1.00      | ~ v1_funct_1(X1)
% 3.85/1.00      | ~ v1_funct_1(X0)
% 3.85/1.00      | k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1)
% 3.85/1.00      | k2_funct_1(X0) = X1
% 3.85/1.00      | k1_relat_1(X1) != k2_relat_1(X0) ),
% 3.85/1.00      inference(cnf_transformation,[],[f36]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_297,plain,
% 3.85/1.00      ( ~ sP0(sK1(X0,X1),sK2(X0,X1),X0,X1)
% 3.85/1.00      | ~ v1_relat_1(X0)
% 3.85/1.00      | ~ v1_relat_1(X1)
% 3.85/1.00      | ~ v1_funct_1(X0)
% 3.85/1.00      | ~ v1_funct_1(X1)
% 3.85/1.00      | k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1)
% 3.85/1.00      | k2_funct_1(X0) = X1
% 3.85/1.00      | k1_relat_1(X1) != k2_relat_1(X0)
% 3.85/1.00      | sK3 != X0 ),
% 3.85/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_18]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_298,plain,
% 3.85/1.00      ( ~ sP0(sK1(sK3,X0),sK2(sK3,X0),sK3,X0)
% 3.85/1.00      | ~ v1_relat_1(X0)
% 3.85/1.00      | ~ v1_relat_1(sK3)
% 3.85/1.00      | ~ v1_funct_1(X0)
% 3.85/1.00      | ~ v1_funct_1(sK3)
% 3.85/1.00      | k1_funct_1(sK3,sK2(sK3,X0)) = sK1(sK3,X0)
% 3.85/1.00      | k2_funct_1(sK3) = X0
% 3.85/1.00      | k1_relat_1(X0) != k2_relat_1(sK3) ),
% 3.85/1.00      inference(unflattening,[status(thm)],[c_297]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_302,plain,
% 3.85/1.00      ( ~ v1_funct_1(X0)
% 3.85/1.00      | ~ sP0(sK1(sK3,X0),sK2(sK3,X0),sK3,X0)
% 3.85/1.00      | ~ v1_relat_1(X0)
% 3.85/1.00      | k1_funct_1(sK3,sK2(sK3,X0)) = sK1(sK3,X0)
% 3.85/1.00      | k2_funct_1(sK3) = X0
% 3.85/1.00      | k1_relat_1(X0) != k2_relat_1(sK3) ),
% 3.85/1.00      inference(global_propositional_subsumption,
% 3.85/1.00                [status(thm)],
% 3.85/1.00                [c_298,c_22,c_21]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_303,plain,
% 3.85/1.00      ( ~ sP0(sK1(sK3,X0),sK2(sK3,X0),sK3,X0)
% 3.85/1.00      | ~ v1_relat_1(X0)
% 3.85/1.00      | ~ v1_funct_1(X0)
% 3.85/1.00      | k1_funct_1(sK3,sK2(sK3,X0)) = sK1(sK3,X0)
% 3.85/1.00      | k2_funct_1(sK3) = X0
% 3.85/1.00      | k1_relat_1(X0) != k2_relat_1(sK3) ),
% 3.85/1.00      inference(renaming,[status(thm)],[c_302]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_429,plain,
% 3.85/1.00      ( ~ sP0(sK1(sK3,X0),sK2(sK3,X0),sK3,X0)
% 3.85/1.00      | ~ v1_relat_1(X0)
% 3.85/1.00      | k1_funct_1(sK3,sK2(sK3,X0)) = sK1(sK3,X0)
% 3.85/1.00      | k2_funct_1(sK3) = X0
% 3.85/1.00      | k1_relat_1(X0) != k2_relat_1(sK3)
% 3.85/1.00      | sK4 != X0 ),
% 3.85/1.00      inference(resolution_lifted,[status(thm)],[c_303,c_19]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_430,plain,
% 3.85/1.00      ( ~ sP0(sK1(sK3,sK4),sK2(sK3,sK4),sK3,sK4)
% 3.85/1.00      | ~ v1_relat_1(sK4)
% 3.85/1.00      | k1_funct_1(sK3,sK2(sK3,sK4)) = sK1(sK3,sK4)
% 3.85/1.00      | k2_funct_1(sK3) = sK4
% 3.85/1.00      | k1_relat_1(sK4) != k2_relat_1(sK3) ),
% 3.85/1.00      inference(unflattening,[status(thm)],[c_429]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_432,plain,
% 3.85/1.00      ( ~ sP0(sK1(sK3,sK4),sK2(sK3,sK4),sK3,sK4)
% 3.85/1.00      | k1_funct_1(sK3,sK2(sK3,sK4)) = sK1(sK3,sK4) ),
% 3.85/1.00      inference(global_propositional_subsumption,
% 3.85/1.00                [status(thm)],
% 3.85/1.00                [c_430,c_20,c_16,c_13]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1389,plain,
% 3.85/1.00      ( ~ sP0(sK1(sK3,sK4),sK2(sK3,sK4),sK3,sK4)
% 3.85/1.00      | k1_funct_1(sK3,sK2(sK3,sK4)) = sK1(sK3,sK4) ),
% 3.85/1.00      inference(subtyping,[status(esa)],[c_432]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1757,plain,
% 3.85/1.00      ( k1_funct_1(sK3,sK2(sK3,sK4)) = sK1(sK3,sK4)
% 3.85/1.00      | sP0(sK1(sK3,sK4),sK2(sK3,sK4),sK3,sK4) != iProver_top ),
% 3.85/1.00      inference(predicate_to_equality,[status(thm)],[c_1389]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2326,plain,
% 3.85/1.00      ( k1_funct_1(sK4,sK1(sK3,sK4)) = sK2(sK3,sK4)
% 3.85/1.00      | k1_funct_1(sK3,sK2(sK3,sK4)) = sK1(sK3,sK4) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_1750,c_1757]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2325,plain,
% 3.85/1.00      ( k1_funct_1(sK3,sK2(sK3,sK4)) = sK1(sK3,sK4)
% 3.85/1.00      | r2_hidden(sK1(sK3,sK4),k2_relat_1(sK3)) = iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_1751,c_1757]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_14,negated_conjecture,
% 3.85/1.00      ( ~ r2_hidden(X0,k1_relat_1(sK4))
% 3.85/1.00      | ~ r2_hidden(k1_funct_1(sK4,X0),k1_relat_1(sK3))
% 3.85/1.00      | k1_funct_1(sK3,k1_funct_1(sK4,X0)) = X0 ),
% 3.85/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1394,negated_conjecture,
% 3.85/1.00      ( ~ r2_hidden(X0_41,k1_relat_1(sK4))
% 3.85/1.00      | ~ r2_hidden(k1_funct_1(sK4,X0_41),k1_relat_1(sK3))
% 3.85/1.00      | k1_funct_1(sK3,k1_funct_1(sK4,X0_41)) = X0_41 ),
% 3.85/1.00      inference(subtyping,[status(esa)],[c_14]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1754,plain,
% 3.85/1.00      ( k1_funct_1(sK3,k1_funct_1(sK4,X0_41)) = X0_41
% 3.85/1.00      | r2_hidden(X0_41,k1_relat_1(sK4)) != iProver_top
% 3.85/1.00      | r2_hidden(k1_funct_1(sK4,X0_41),k1_relat_1(sK3)) != iProver_top ),
% 3.85/1.00      inference(predicate_to_equality,[status(thm)],[c_1394]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1911,plain,
% 3.85/1.00      ( k1_funct_1(sK3,k1_funct_1(sK4,X0_41)) = X0_41
% 3.85/1.00      | r2_hidden(X0_41,k1_relat_1(sK4)) != iProver_top
% 3.85/1.00      | r2_hidden(k1_funct_1(sK4,X0_41),k2_relat_1(sK4)) != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_1391,c_1754]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1455,plain,
% 3.85/1.00      ( r2_hidden(X0_41,k1_relat_1(sK4)) != iProver_top
% 3.85/1.00      | r2_hidden(k1_funct_1(sK4,X0_41),k2_relat_1(sK4)) = iProver_top ),
% 3.85/1.00      inference(predicate_to_equality,[status(thm)],[c_1384]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1976,plain,
% 3.85/1.00      ( r2_hidden(X0_41,k1_relat_1(sK4)) != iProver_top
% 3.85/1.00      | k1_funct_1(sK3,k1_funct_1(sK4,X0_41)) = X0_41 ),
% 3.85/1.00      inference(global_propositional_subsumption,
% 3.85/1.00                [status(thm)],
% 3.85/1.00                [c_1911,c_1455]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1977,plain,
% 3.85/1.00      ( k1_funct_1(sK3,k1_funct_1(sK4,X0_41)) = X0_41
% 3.85/1.00      | r2_hidden(X0_41,k1_relat_1(sK4)) != iProver_top ),
% 3.85/1.00      inference(renaming,[status(thm)],[c_1976]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1982,plain,
% 3.85/1.00      ( k1_funct_1(sK3,k1_funct_1(sK4,X0_41)) = X0_41
% 3.85/1.00      | r2_hidden(X0_41,k2_relat_1(sK3)) != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_1392,c_1977]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2329,plain,
% 3.85/1.00      ( k1_funct_1(sK3,sK2(sK3,sK4)) = sK1(sK3,sK4)
% 3.85/1.00      | k1_funct_1(sK3,k1_funct_1(sK4,sK1(sK3,sK4))) = sK1(sK3,sK4) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_2325,c_1982]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2727,plain,
% 3.85/1.00      ( k1_funct_1(sK3,sK2(sK3,sK4)) = sK1(sK3,sK4) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_2326,c_2329]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1763,plain,
% 3.85/1.00      ( r2_hidden(X0_41,k1_relat_1(sK3)) != iProver_top
% 3.85/1.00      | r2_hidden(k1_funct_1(sK3,X0_41),k2_relat_1(sK3)) = iProver_top ),
% 3.85/1.00      inference(predicate_to_equality,[status(thm)],[c_1383]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_3583,plain,
% 3.85/1.00      ( r2_hidden(sK2(sK3,sK4),k1_relat_1(sK3)) != iProver_top
% 3.85/1.00      | r2_hidden(sK1(sK3,sK4),k2_relat_1(sK3)) = iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_2727,c_1763]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_847,plain,
% 3.85/1.00      ( r2_hidden(X0,k2_relat_1(X1))
% 3.85/1.00      | r2_hidden(sK2(sK3,sK4),k1_relat_1(sK3))
% 3.85/1.00      | sK2(sK3,sK4) != X2
% 3.85/1.00      | sK1(sK3,sK4) != X0
% 3.85/1.00      | sK4 != X3
% 3.85/1.00      | sK3 != X1 ),
% 3.85/1.00      inference(resolution_lifted,[status(thm)],[c_3,c_447]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_848,plain,
% 3.85/1.00      ( r2_hidden(sK2(sK3,sK4),k1_relat_1(sK3))
% 3.85/1.00      | r2_hidden(sK1(sK3,sK4),k2_relat_1(sK3)) ),
% 3.85/1.00      inference(unflattening,[status(thm)],[c_847]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_849,plain,
% 3.85/1.00      ( r2_hidden(sK2(sK3,sK4),k1_relat_1(sK3)) = iProver_top
% 3.85/1.00      | r2_hidden(sK1(sK3,sK4),k2_relat_1(sK3)) = iProver_top ),
% 3.85/1.00      inference(predicate_to_equality,[status(thm)],[c_848]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_4188,plain,
% 3.85/1.00      ( r2_hidden(sK1(sK3,sK4),k2_relat_1(sK3)) = iProver_top ),
% 3.85/1.00      inference(global_propositional_subsumption,
% 3.85/1.00                [status(thm)],
% 3.85/1.00                [c_3583,c_849]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2433,plain,
% 3.85/1.00      ( k1_funct_1(sK4,sK1(sK3,sK4)) = sK2(sK3,sK4)
% 3.85/1.00      | r2_hidden(sK2(sK3,sK4),k1_relat_1(sK3)) = iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_1750,c_1758]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2517,plain,
% 3.85/1.00      ( k1_funct_1(sK4,sK1(sK3,sK4)) = sK2(sK3,sK4)
% 3.85/1.00      | k1_funct_1(sK4,k1_funct_1(sK3,sK2(sK3,sK4))) = sK2(sK3,sK4) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_2433,c_2108]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_3818,plain,
% 3.85/1.00      ( k1_funct_1(sK4,sK1(sK3,sK4)) = sK2(sK3,sK4) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_2727,c_2517]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_6763,plain,
% 3.85/1.00      ( r2_hidden(sK2(sK3,sK4),k2_relat_1(sK4)) = iProver_top
% 3.85/1.00      | r2_hidden(sK1(sK3,sK4),k1_relat_1(sK4)) != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_3818,c_1762]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1,plain,
% 3.85/1.00      ( sP0(k1_funct_1(X0,X1),X1,X0,X2)
% 3.85/1.00      | ~ r2_hidden(X1,k1_relat_1(X0)) ),
% 3.85/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1400,plain,
% 3.85/1.00      ( sP0(k1_funct_1(X0_42,X0_41),X0_41,X0_42,X1_42)
% 3.85/1.00      | ~ r2_hidden(X0_41,k1_relat_1(X0_42)) ),
% 3.85/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1749,plain,
% 3.85/1.00      ( sP0(k1_funct_1(X0_42,X0_41),X0_41,X0_42,X1_42) = iProver_top
% 3.85/1.00      | r2_hidden(X0_41,k1_relat_1(X0_42)) != iProver_top ),
% 3.85/1.00      inference(predicate_to_equality,[status(thm)],[c_1400]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_6766,plain,
% 3.85/1.00      ( sP0(sK2(sK3,sK4),sK1(sK3,sK4),sK4,X0_42) = iProver_top
% 3.85/1.00      | r2_hidden(sK1(sK3,sK4),k1_relat_1(sK4)) != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_3818,c_1749]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_7166,plain,
% 3.85/1.00      ( sP0(sK2(sK3,sK4),sK1(sK3,sK4),sK4,X0_42) = iProver_top ),
% 3.85/1.00      inference(global_propositional_subsumption,
% 3.85/1.00                [status(thm)],
% 3.85/1.00                [c_6766,c_849,c_1392,c_2012,c_2310,c_3583]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2959,plain,
% 3.85/1.00      ( k1_funct_1(X0_42,k1_funct_1(sK3,sK2(sK3,sK4))) = sK2(sK3,sK4)
% 3.85/1.00      | sP0(sK2(sK3,sK4),sK1(sK3,sK4),X0_42,sK3) != iProver_top
% 3.85/1.00      | r2_hidden(sK2(sK3,sK4),k2_relat_1(X0_42)) != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_2727,c_1752]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_7172,plain,
% 3.85/1.00      ( k1_funct_1(sK4,k1_funct_1(sK3,sK2(sK3,sK4))) = sK2(sK3,sK4)
% 3.85/1.00      | r2_hidden(sK2(sK3,sK4),k2_relat_1(sK4)) != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_7166,c_2959]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_7967,plain,
% 3.85/1.00      ( k1_funct_1(sK4,k1_funct_1(sK3,sK2(sK3,sK4))) = sK2(sK3,sK4) ),
% 3.85/1.00      inference(global_propositional_subsumption,
% 3.85/1.00                [status(thm)],
% 3.85/1.00                [c_4051,c_849,c_1392,c_2012,c_2310,c_3583,c_6763,c_7172]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_4193,plain,
% 3.85/1.00      ( k1_funct_1(sK4,k1_funct_1(sK3,k1_funct_1(sK4,sK1(sK3,sK4)))) = k1_funct_1(sK4,sK1(sK3,sK4)) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_4188,c_3322]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_4377,plain,
% 3.85/1.00      ( sP0(k1_funct_1(sK4,sK1(sK3,sK4)),k1_funct_1(sK3,k1_funct_1(sK4,sK1(sK3,sK4))),sK4,X0_42) = iProver_top
% 3.85/1.00      | r2_hidden(k1_funct_1(sK3,k1_funct_1(sK4,sK1(sK3,sK4))),k1_relat_1(sK4)) != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_4193,c_1749]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1409,plain,
% 3.85/1.00      ( k2_relat_1(X0_42) = k2_relat_1(X1_42) | X0_42 != X1_42 ),
% 3.85/1.00      theory(equality) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1417,plain,
% 3.85/1.00      ( k2_relat_1(sK3) = k2_relat_1(sK3) | sK3 != sK3 ),
% 3.85/1.00      inference(instantiation,[status(thm)],[c_1409]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1403,plain,( X0_42 = X0_42 ),theory(equality) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1426,plain,
% 3.85/1.00      ( sK3 = sK3 ),
% 3.85/1.00      inference(instantiation,[status(thm)],[c_1403]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2101,plain,
% 3.85/1.00      ( ~ r2_hidden(sK1(sK3,sK4),k2_relat_1(sK3))
% 3.85/1.00      | r2_hidden(k1_funct_1(sK3,sK2(sK3,sK4)),X0_43)
% 3.85/1.00      | X0_43 != k2_relat_1(sK3)
% 3.85/1.00      | k1_funct_1(sK3,sK2(sK3,sK4)) != sK1(sK3,sK4) ),
% 3.85/1.00      inference(instantiation,[status(thm)],[c_1899]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2279,plain,
% 3.85/1.00      ( ~ r2_hidden(sK1(sK3,sK4),k2_relat_1(sK3))
% 3.85/1.00      | r2_hidden(k1_funct_1(sK3,sK2(sK3,sK4)),k2_relat_1(sK3))
% 3.85/1.00      | k2_relat_1(sK3) != k2_relat_1(sK3)
% 3.85/1.00      | k1_funct_1(sK3,sK2(sK3,sK4)) != sK1(sK3,sK4) ),
% 3.85/1.00      inference(instantiation,[status(thm)],[c_2101]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2280,plain,
% 3.85/1.00      ( k2_relat_1(sK3) != k2_relat_1(sK3)
% 3.85/1.00      | k1_funct_1(sK3,sK2(sK3,sK4)) != sK1(sK3,sK4)
% 3.85/1.00      | r2_hidden(sK1(sK3,sK4),k2_relat_1(sK3)) != iProver_top
% 3.85/1.00      | r2_hidden(k1_funct_1(sK3,sK2(sK3,sK4)),k2_relat_1(sK3)) = iProver_top ),
% 3.85/1.00      inference(predicate_to_equality,[status(thm)],[c_2279]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1408,plain,
% 3.85/1.00      ( X0_42 != X1_42
% 3.85/1.00      | X0_41 != X1_41
% 3.85/1.00      | k1_funct_1(X0_42,X0_41) = k1_funct_1(X1_42,X1_41) ),
% 3.85/1.00      theory(equality) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2782,plain,
% 3.85/1.00      ( X0_42 != sK3
% 3.85/1.00      | X0_41 != sK2(sK3,sK4)
% 3.85/1.00      | k1_funct_1(X0_42,X0_41) = k1_funct_1(sK3,sK2(sK3,sK4)) ),
% 3.85/1.00      inference(instantiation,[status(thm)],[c_1408]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_3501,plain,
% 3.85/1.00      ( X0_42 != sK3
% 3.85/1.00      | k1_funct_1(X0_42,k1_funct_1(sK4,sK1(sK3,sK4))) = k1_funct_1(sK3,sK2(sK3,sK4))
% 3.85/1.00      | k1_funct_1(sK4,sK1(sK3,sK4)) != sK2(sK3,sK4) ),
% 3.85/1.00      inference(instantiation,[status(thm)],[c_2782]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_3502,plain,
% 3.85/1.00      ( sK3 != sK3
% 3.85/1.00      | k1_funct_1(sK4,sK1(sK3,sK4)) != sK2(sK3,sK4)
% 3.85/1.00      | k1_funct_1(sK3,k1_funct_1(sK4,sK1(sK3,sK4))) = k1_funct_1(sK3,sK2(sK3,sK4)) ),
% 3.85/1.00      inference(instantiation,[status(thm)],[c_3501]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2228,plain,
% 3.85/1.00      ( r2_hidden(X0_41,X0_43)
% 3.85/1.00      | ~ r2_hidden(k1_funct_1(sK3,sK2(sK3,sK4)),k2_relat_1(sK3))
% 3.85/1.00      | X0_43 != k2_relat_1(sK3)
% 3.85/1.00      | X0_41 != k1_funct_1(sK3,sK2(sK3,sK4)) ),
% 3.85/1.00      inference(instantiation,[status(thm)],[c_1410]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2781,plain,
% 3.85/1.00      ( r2_hidden(k1_funct_1(X0_42,X0_41),X0_43)
% 3.85/1.00      | ~ r2_hidden(k1_funct_1(sK3,sK2(sK3,sK4)),k2_relat_1(sK3))
% 3.85/1.00      | X0_43 != k2_relat_1(sK3)
% 3.85/1.00      | k1_funct_1(X0_42,X0_41) != k1_funct_1(sK3,sK2(sK3,sK4)) ),
% 3.85/1.00      inference(instantiation,[status(thm)],[c_2228]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_3546,plain,
% 3.85/1.00      ( r2_hidden(k1_funct_1(X0_42,X0_41),k1_relat_1(sK4))
% 3.85/1.00      | ~ r2_hidden(k1_funct_1(sK3,sK2(sK3,sK4)),k2_relat_1(sK3))
% 3.85/1.00      | k1_relat_1(sK4) != k2_relat_1(sK3)
% 3.85/1.00      | k1_funct_1(X0_42,X0_41) != k1_funct_1(sK3,sK2(sK3,sK4)) ),
% 3.85/1.00      inference(instantiation,[status(thm)],[c_2781]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_4544,plain,
% 3.85/1.00      ( r2_hidden(k1_funct_1(X0_42,k1_funct_1(sK4,sK1(sK3,sK4))),k1_relat_1(sK4))
% 3.85/1.00      | ~ r2_hidden(k1_funct_1(sK3,sK2(sK3,sK4)),k2_relat_1(sK3))
% 3.85/1.00      | k1_relat_1(sK4) != k2_relat_1(sK3)
% 3.85/1.00      | k1_funct_1(X0_42,k1_funct_1(sK4,sK1(sK3,sK4))) != k1_funct_1(sK3,sK2(sK3,sK4)) ),
% 3.85/1.00      inference(instantiation,[status(thm)],[c_3546]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_4545,plain,
% 3.85/1.00      ( k1_relat_1(sK4) != k2_relat_1(sK3)
% 3.85/1.00      | k1_funct_1(X0_42,k1_funct_1(sK4,sK1(sK3,sK4))) != k1_funct_1(sK3,sK2(sK3,sK4))
% 3.85/1.00      | r2_hidden(k1_funct_1(X0_42,k1_funct_1(sK4,sK1(sK3,sK4))),k1_relat_1(sK4)) = iProver_top
% 3.85/1.00      | r2_hidden(k1_funct_1(sK3,sK2(sK3,sK4)),k2_relat_1(sK3)) != iProver_top ),
% 3.85/1.00      inference(predicate_to_equality,[status(thm)],[c_4544]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_4547,plain,
% 3.85/1.00      ( k1_relat_1(sK4) != k2_relat_1(sK3)
% 3.85/1.00      | k1_funct_1(sK3,k1_funct_1(sK4,sK1(sK3,sK4))) != k1_funct_1(sK3,sK2(sK3,sK4))
% 3.85/1.00      | r2_hidden(k1_funct_1(sK3,sK2(sK3,sK4)),k2_relat_1(sK3)) != iProver_top
% 3.85/1.00      | r2_hidden(k1_funct_1(sK3,k1_funct_1(sK4,sK1(sK3,sK4))),k1_relat_1(sK4)) = iProver_top ),
% 3.85/1.00      inference(instantiation,[status(thm)],[c_4545]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_4968,plain,
% 3.85/1.00      ( sP0(k1_funct_1(sK4,sK1(sK3,sK4)),k1_funct_1(sK3,k1_funct_1(sK4,sK1(sK3,sK4))),sK4,X0_42) = iProver_top ),
% 3.85/1.00      inference(global_propositional_subsumption,
% 3.85/1.00                [status(thm)],
% 3.85/1.00                [c_4377,c_849,c_1417,c_1426,c_1392,c_2280,c_2727,c_3502,
% 3.85/1.00                 c_3583,c_3818,c_4547]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_5,plain,
% 3.85/1.00      ( ~ sP0(X0,k1_funct_1(X1,X0),X2,X1)
% 3.85/1.00      | ~ r2_hidden(X0,k2_relat_1(X2))
% 3.85/1.00      | r2_hidden(k1_funct_1(X1,X0),k1_relat_1(X2)) ),
% 3.85/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1396,plain,
% 3.85/1.00      ( ~ sP0(X0_41,k1_funct_1(X0_42,X0_41),X1_42,X0_42)
% 3.85/1.00      | ~ r2_hidden(X0_41,k2_relat_1(X1_42))
% 3.85/1.00      | r2_hidden(k1_funct_1(X0_42,X0_41),k1_relat_1(X1_42)) ),
% 3.85/1.00      inference(subtyping,[status(esa)],[c_5]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1753,plain,
% 3.85/1.00      ( sP0(X0_41,k1_funct_1(X0_42,X0_41),X1_42,X0_42) != iProver_top
% 3.85/1.00      | r2_hidden(X0_41,k2_relat_1(X1_42)) != iProver_top
% 3.85/1.00      | r2_hidden(k1_funct_1(X0_42,X0_41),k1_relat_1(X1_42)) = iProver_top ),
% 3.85/1.00      inference(predicate_to_equality,[status(thm)],[c_1396]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_4975,plain,
% 3.85/1.00      ( r2_hidden(k1_funct_1(sK4,sK1(sK3,sK4)),k2_relat_1(sK4)) != iProver_top
% 3.85/1.00      | r2_hidden(k1_funct_1(sK3,k1_funct_1(sK4,sK1(sK3,sK4))),k1_relat_1(sK4)) = iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_4968,c_1753]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_4982,plain,
% 3.85/1.00      ( r2_hidden(k1_funct_1(sK3,k1_funct_1(sK4,sK1(sK3,sK4))),k1_relat_1(sK4)) = iProver_top ),
% 3.85/1.00      inference(global_propositional_subsumption,
% 3.85/1.00                [status(thm)],
% 3.85/1.00                [c_4975,c_849,c_1417,c_1426,c_1392,c_2280,c_2727,c_3502,
% 3.85/1.00                 c_3583,c_3818,c_4547]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_4987,plain,
% 3.85/1.00      ( r2_hidden(k1_funct_1(sK3,k1_funct_1(sK4,sK1(sK3,sK4))),k2_relat_1(sK3)) = iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_1392,c_4982]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_6752,plain,
% 3.85/1.00      ( r2_hidden(k1_funct_1(sK3,sK2(sK3,sK4)),k2_relat_1(sK3)) = iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_3818,c_4987]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_6967,plain,
% 3.85/1.00      ( k1_funct_1(sK3,k1_funct_1(sK4,k1_funct_1(sK3,sK2(sK3,sK4)))) = k1_funct_1(sK3,sK2(sK3,sK4)) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_6752,c_1982]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_6972,plain,
% 3.85/1.00      ( sP0(k1_funct_1(sK3,sK2(sK3,sK4)),k1_funct_1(sK4,k1_funct_1(sK3,sK2(sK3,sK4))),sK3,X0_42) = iProver_top
% 3.85/1.00      | r2_hidden(k1_funct_1(sK4,k1_funct_1(sK3,sK2(sK3,sK4))),k1_relat_1(sK3)) != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_6967,c_1749]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2271,plain,
% 3.85/1.00      ( ~ r2_hidden(sK1(sK3,sK4),k2_relat_1(sK3))
% 3.85/1.00      | r2_hidden(k1_funct_1(sK3,sK2(sK3,sK4)),k1_relat_1(sK4))
% 3.85/1.00      | k1_relat_1(sK4) != k2_relat_1(sK3)
% 3.85/1.00      | k1_funct_1(sK3,sK2(sK3,sK4)) != sK1(sK3,sK4) ),
% 3.85/1.00      inference(instantiation,[status(thm)],[c_2101]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2272,plain,
% 3.85/1.00      ( k1_relat_1(sK4) != k2_relat_1(sK3)
% 3.85/1.00      | k1_funct_1(sK3,sK2(sK3,sK4)) != sK1(sK3,sK4)
% 3.85/1.00      | r2_hidden(sK1(sK3,sK4),k2_relat_1(sK3)) != iProver_top
% 3.85/1.00      | r2_hidden(k1_funct_1(sK3,sK2(sK3,sK4)),k1_relat_1(sK4)) = iProver_top ),
% 3.85/1.00      inference(predicate_to_equality,[status(thm)],[c_2271]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2588,plain,
% 3.85/1.00      ( r2_hidden(k1_funct_1(sK4,k1_funct_1(sK3,sK2(sK3,sK4))),k2_relat_1(sK4))
% 3.85/1.00      | ~ r2_hidden(k1_funct_1(sK3,sK2(sK3,sK4)),k1_relat_1(sK4)) ),
% 3.85/1.00      inference(instantiation,[status(thm)],[c_1384]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2589,plain,
% 3.85/1.00      ( r2_hidden(k1_funct_1(sK4,k1_funct_1(sK3,sK2(sK3,sK4))),k2_relat_1(sK4)) = iProver_top
% 3.85/1.00      | r2_hidden(k1_funct_1(sK3,sK2(sK3,sK4)),k1_relat_1(sK4)) != iProver_top ),
% 3.85/1.00      inference(predicate_to_equality,[status(thm)],[c_2588]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_4646,plain,
% 3.85/1.00      ( k1_funct_1(sK4,k1_funct_1(sK3,sK2(sK3,sK4))) = k1_funct_1(sK4,k1_funct_1(sK3,sK2(sK3,sK4))) ),
% 3.85/1.00      inference(instantiation,[status(thm)],[c_1402]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_3161,plain,
% 3.85/1.00      ( r2_hidden(X0_41,X0_43)
% 3.85/1.00      | ~ r2_hidden(k1_funct_1(sK4,k1_funct_1(sK3,sK2(sK3,sK4))),k2_relat_1(sK4))
% 3.85/1.00      | X0_43 != k2_relat_1(sK4)
% 3.85/1.00      | X0_41 != k1_funct_1(sK4,k1_funct_1(sK3,sK2(sK3,sK4))) ),
% 3.85/1.00      inference(instantiation,[status(thm)],[c_1410]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_4645,plain,
% 3.85/1.00      ( r2_hidden(k1_funct_1(sK4,k1_funct_1(sK3,sK2(sK3,sK4))),X0_43)
% 3.85/1.00      | ~ r2_hidden(k1_funct_1(sK4,k1_funct_1(sK3,sK2(sK3,sK4))),k2_relat_1(sK4))
% 3.85/1.01      | X0_43 != k2_relat_1(sK4)
% 3.85/1.01      | k1_funct_1(sK4,k1_funct_1(sK3,sK2(sK3,sK4))) != k1_funct_1(sK4,k1_funct_1(sK3,sK2(sK3,sK4))) ),
% 3.85/1.01      inference(instantiation,[status(thm)],[c_3161]) ).
% 3.85/1.01  
% 3.85/1.01  cnf(c_7111,plain,
% 3.85/1.01      ( r2_hidden(k1_funct_1(sK4,k1_funct_1(sK3,sK2(sK3,sK4))),k1_relat_1(sK3))
% 3.85/1.01      | ~ r2_hidden(k1_funct_1(sK4,k1_funct_1(sK3,sK2(sK3,sK4))),k2_relat_1(sK4))
% 3.85/1.01      | k1_relat_1(sK3) != k2_relat_1(sK4)
% 3.85/1.01      | k1_funct_1(sK4,k1_funct_1(sK3,sK2(sK3,sK4))) != k1_funct_1(sK4,k1_funct_1(sK3,sK2(sK3,sK4))) ),
% 3.85/1.01      inference(instantiation,[status(thm)],[c_4645]) ).
% 3.85/1.01  
% 3.85/1.01  cnf(c_7112,plain,
% 3.85/1.01      ( k1_relat_1(sK3) != k2_relat_1(sK4)
% 3.85/1.01      | k1_funct_1(sK4,k1_funct_1(sK3,sK2(sK3,sK4))) != k1_funct_1(sK4,k1_funct_1(sK3,sK2(sK3,sK4)))
% 3.85/1.01      | r2_hidden(k1_funct_1(sK4,k1_funct_1(sK3,sK2(sK3,sK4))),k1_relat_1(sK3)) = iProver_top
% 3.85/1.01      | r2_hidden(k1_funct_1(sK4,k1_funct_1(sK3,sK2(sK3,sK4))),k2_relat_1(sK4)) != iProver_top ),
% 3.85/1.01      inference(predicate_to_equality,[status(thm)],[c_7111]) ).
% 3.85/1.01  
% 3.85/1.01  cnf(c_7530,plain,
% 3.85/1.01      ( sP0(k1_funct_1(sK3,sK2(sK3,sK4)),k1_funct_1(sK4,k1_funct_1(sK3,sK2(sK3,sK4))),sK3,X0_42) = iProver_top ),
% 3.85/1.01      inference(global_propositional_subsumption,
% 3.85/1.01                [status(thm)],
% 3.85/1.01                [c_6972,c_849,c_1392,c_1391,c_2272,c_2589,c_2727,c_3583,
% 3.85/1.01                 c_4646,c_7112]) ).
% 3.85/1.01  
% 3.85/1.01  cnf(c_7539,plain,
% 3.85/1.01      ( r2_hidden(k1_funct_1(sK4,k1_funct_1(sK3,sK2(sK3,sK4))),k1_relat_1(sK3)) = iProver_top
% 3.85/1.01      | r2_hidden(k1_funct_1(sK3,sK2(sK3,sK4)),k2_relat_1(sK3)) != iProver_top ),
% 3.85/1.01      inference(superposition,[status(thm)],[c_7530,c_1753]) ).
% 3.85/1.01  
% 3.85/1.01  cnf(c_7682,plain,
% 3.85/1.01      ( r2_hidden(k1_funct_1(sK4,k1_funct_1(sK3,sK2(sK3,sK4))),k1_relat_1(sK3)) = iProver_top ),
% 3.85/1.01      inference(global_propositional_subsumption,
% 3.85/1.01                [status(thm)],
% 3.85/1.01                [c_7539,c_849,c_1392,c_1391,c_2272,c_2589,c_2727,c_3583,
% 3.85/1.01                 c_4646,c_7112]) ).
% 3.85/1.01  
% 3.85/1.01  cnf(c_7975,plain,
% 3.85/1.01      ( r2_hidden(sK2(sK3,sK4),k1_relat_1(sK3)) = iProver_top ),
% 3.85/1.01      inference(superposition,[status(thm)],[c_7967,c_7682]) ).
% 3.85/1.01  
% 3.85/1.01  cnf(c_2091,plain,
% 3.85/1.01      ( sP0(k1_funct_1(sK3,sK2(sK3,sK4)),sK2(sK3,sK4),sK3,X0_42)
% 3.85/1.01      | ~ r2_hidden(sK2(sK3,sK4),k1_relat_1(sK3)) ),
% 3.85/1.01      inference(instantiation,[status(thm)],[c_1400]) ).
% 3.85/1.01  
% 3.85/1.01  cnf(c_4854,plain,
% 3.85/1.01      ( sP0(k1_funct_1(sK3,sK2(sK3,sK4)),sK2(sK3,sK4),sK3,sK4)
% 3.85/1.01      | ~ r2_hidden(sK2(sK3,sK4),k1_relat_1(sK3)) ),
% 3.85/1.01      inference(instantiation,[status(thm)],[c_2091]) ).
% 3.85/1.01  
% 3.85/1.01  cnf(c_4857,plain,
% 3.85/1.01      ( sP0(k1_funct_1(sK3,sK2(sK3,sK4)),sK2(sK3,sK4),sK3,sK4) = iProver_top
% 3.85/1.01      | r2_hidden(sK2(sK3,sK4),k1_relat_1(sK3)) != iProver_top ),
% 3.85/1.01      inference(predicate_to_equality,[status(thm)],[c_4854]) ).
% 3.85/1.01  
% 3.85/1.01  cnf(c_1412,plain,
% 3.85/1.01      ( ~ sP0(X0_41,X1_41,X0_42,X1_42)
% 3.85/1.01      | sP0(X2_41,X3_41,X2_42,X3_42)
% 3.85/1.01      | X2_42 != X0_42
% 3.85/1.01      | X3_42 != X1_42
% 3.85/1.01      | X2_41 != X0_41
% 3.85/1.01      | X3_41 != X1_41 ),
% 3.85/1.01      theory(equality) ).
% 3.85/1.01  
% 3.85/1.01  cnf(c_1879,plain,
% 3.85/1.01      ( ~ sP0(X0_41,X1_41,X0_42,X1_42)
% 3.85/1.01      | sP0(sK1(sK3,sK4),sK2(sK3,sK4),sK3,sK4)
% 3.85/1.01      | sK4 != X1_42
% 3.85/1.01      | sK3 != X0_42
% 3.85/1.01      | sK2(sK3,sK4) != X1_41
% 3.85/1.01      | sK1(sK3,sK4) != X0_41 ),
% 3.85/1.01      inference(instantiation,[status(thm)],[c_1412]) ).
% 3.85/1.01  
% 3.85/1.01  cnf(c_1947,plain,
% 3.85/1.01      ( ~ sP0(X0_41,X1_41,X0_42,sK4)
% 3.85/1.01      | sP0(sK1(sK3,sK4),sK2(sK3,sK4),sK3,sK4)
% 3.85/1.01      | sK4 != sK4
% 3.85/1.01      | sK3 != X0_42
% 3.85/1.01      | sK2(sK3,sK4) != X1_41
% 3.85/1.01      | sK1(sK3,sK4) != X0_41 ),
% 3.85/1.01      inference(instantiation,[status(thm)],[c_1879]) ).
% 3.85/1.01  
% 3.85/1.01  cnf(c_3181,plain,
% 3.85/1.01      ( sP0(sK1(sK3,sK4),sK2(sK3,sK4),sK3,sK4)
% 3.85/1.01      | ~ sP0(k1_funct_1(sK3,sK2(sK3,sK4)),X0_41,X0_42,sK4)
% 3.85/1.01      | sK4 != sK4
% 3.85/1.01      | sK3 != X0_42
% 3.85/1.01      | sK2(sK3,sK4) != X0_41
% 3.85/1.01      | sK1(sK3,sK4) != k1_funct_1(sK3,sK2(sK3,sK4)) ),
% 3.85/1.01      inference(instantiation,[status(thm)],[c_1947]) ).
% 3.85/1.01  
% 3.85/1.01  cnf(c_4678,plain,
% 3.85/1.01      ( sP0(sK1(sK3,sK4),sK2(sK3,sK4),sK3,sK4)
% 3.85/1.01      | ~ sP0(k1_funct_1(sK3,sK2(sK3,sK4)),sK2(sK3,sK4),X0_42,sK4)
% 3.85/1.01      | sK4 != sK4
% 3.85/1.01      | sK3 != X0_42
% 3.85/1.01      | sK2(sK3,sK4) != sK2(sK3,sK4)
% 3.85/1.01      | sK1(sK3,sK4) != k1_funct_1(sK3,sK2(sK3,sK4)) ),
% 3.85/1.01      inference(instantiation,[status(thm)],[c_3181]) ).
% 3.85/1.01  
% 3.85/1.01  cnf(c_4679,plain,
% 3.85/1.01      ( sK4 != sK4
% 3.85/1.01      | sK3 != X0_42
% 3.85/1.01      | sK2(sK3,sK4) != sK2(sK3,sK4)
% 3.85/1.01      | sK1(sK3,sK4) != k1_funct_1(sK3,sK2(sK3,sK4))
% 3.85/1.01      | sP0(sK1(sK3,sK4),sK2(sK3,sK4),sK3,sK4) = iProver_top
% 3.85/1.01      | sP0(k1_funct_1(sK3,sK2(sK3,sK4)),sK2(sK3,sK4),X0_42,sK4) != iProver_top ),
% 3.85/1.01      inference(predicate_to_equality,[status(thm)],[c_4678]) ).
% 3.85/1.01  
% 3.85/1.01  cnf(c_4681,plain,
% 3.85/1.01      ( sK4 != sK4
% 3.85/1.01      | sK3 != sK3
% 3.85/1.01      | sK2(sK3,sK4) != sK2(sK3,sK4)
% 3.85/1.01      | sK1(sK3,sK4) != k1_funct_1(sK3,sK2(sK3,sK4))
% 3.85/1.01      | sP0(sK1(sK3,sK4),sK2(sK3,sK4),sK3,sK4) = iProver_top
% 3.85/1.01      | sP0(k1_funct_1(sK3,sK2(sK3,sK4)),sK2(sK3,sK4),sK3,sK4) != iProver_top ),
% 3.85/1.01      inference(instantiation,[status(thm)],[c_4679]) ).
% 3.85/1.01  
% 3.85/1.01  cnf(c_1405,plain,
% 3.85/1.01      ( X0_41 != X1_41 | X2_41 != X1_41 | X2_41 = X0_41 ),
% 3.85/1.01      theory(equality) ).
% 3.85/1.01  
% 3.85/1.01  cnf(c_2076,plain,
% 3.85/1.01      ( X0_41 != X1_41 | sK1(sK3,sK4) != X1_41 | sK1(sK3,sK4) = X0_41 ),
% 3.85/1.01      inference(instantiation,[status(thm)],[c_1405]) ).
% 3.85/1.01  
% 3.85/1.01  cnf(c_2387,plain,
% 3.85/1.01      ( X0_41 != sK1(sK3,sK4)
% 3.85/1.01      | sK1(sK3,sK4) = X0_41
% 3.85/1.01      | sK1(sK3,sK4) != sK1(sK3,sK4) ),
% 3.85/1.01      inference(instantiation,[status(thm)],[c_2076]) ).
% 3.85/1.01  
% 3.85/1.01  cnf(c_2914,plain,
% 3.85/1.01      ( sK1(sK3,sK4) != sK1(sK3,sK4)
% 3.85/1.01      | sK1(sK3,sK4) = k1_funct_1(sK3,sK2(sK3,sK4))
% 3.85/1.01      | k1_funct_1(sK3,sK2(sK3,sK4)) != sK1(sK3,sK4) ),
% 3.85/1.01      inference(instantiation,[status(thm)],[c_2387]) ).
% 3.85/1.01  
% 3.85/1.01  cnf(c_2417,plain,
% 3.85/1.01      ( sK2(sK3,sK4) = sK2(sK3,sK4) ),
% 3.85/1.01      inference(instantiation,[status(thm)],[c_1402]) ).
% 3.85/1.01  
% 3.85/1.01  cnf(c_1948,plain,
% 3.85/1.01      ( sK4 = sK4 ),
% 3.85/1.01      inference(instantiation,[status(thm)],[c_1403]) ).
% 3.85/1.01  
% 3.85/1.01  cnf(c_6,plain,
% 3.85/1.01      ( ~ sP0(sK1(X0,X1),sK2(X0,X1),X0,X1)
% 3.85/1.01      | ~ r2_hidden(sK1(X0,X1),k2_relat_1(X0))
% 3.85/1.01      | ~ v2_funct_1(X0)
% 3.85/1.01      | ~ v1_relat_1(X1)
% 3.85/1.01      | ~ v1_relat_1(X0)
% 3.85/1.01      | ~ v1_funct_1(X1)
% 3.85/1.01      | ~ v1_funct_1(X0)
% 3.85/1.01      | k1_funct_1(X1,sK1(X0,X1)) != sK2(X0,X1)
% 3.85/1.01      | k2_funct_1(X0) = X1
% 3.85/1.01      | k1_relat_1(X1) != k2_relat_1(X0) ),
% 3.85/1.01      inference(cnf_transformation,[],[f37]) ).
% 3.85/1.01  
% 3.85/1.01  cnf(c_325,plain,
% 3.85/1.01      ( ~ sP0(sK1(X0,X1),sK2(X0,X1),X0,X1)
% 3.85/1.01      | ~ r2_hidden(sK1(X0,X1),k2_relat_1(X0))
% 3.85/1.01      | ~ v1_relat_1(X0)
% 3.85/1.01      | ~ v1_relat_1(X1)
% 3.85/1.01      | ~ v1_funct_1(X0)
% 3.85/1.01      | ~ v1_funct_1(X1)
% 3.85/1.01      | k1_funct_1(X1,sK1(X0,X1)) != sK2(X0,X1)
% 3.85/1.01      | k2_funct_1(X0) = X1
% 3.85/1.01      | k1_relat_1(X1) != k2_relat_1(X0)
% 3.85/1.01      | sK3 != X0 ),
% 3.85/1.01      inference(resolution_lifted,[status(thm)],[c_6,c_18]) ).
% 3.85/1.01  
% 3.85/1.01  cnf(c_326,plain,
% 3.85/1.01      ( ~ sP0(sK1(sK3,X0),sK2(sK3,X0),sK3,X0)
% 3.85/1.01      | ~ r2_hidden(sK1(sK3,X0),k2_relat_1(sK3))
% 3.85/1.01      | ~ v1_relat_1(X0)
% 3.85/1.01      | ~ v1_relat_1(sK3)
% 3.85/1.01      | ~ v1_funct_1(X0)
% 3.85/1.01      | ~ v1_funct_1(sK3)
% 3.85/1.01      | k1_funct_1(X0,sK1(sK3,X0)) != sK2(sK3,X0)
% 3.85/1.01      | k2_funct_1(sK3) = X0
% 3.85/1.01      | k1_relat_1(X0) != k2_relat_1(sK3) ),
% 3.85/1.01      inference(unflattening,[status(thm)],[c_325]) ).
% 3.85/1.01  
% 3.85/1.01  cnf(c_330,plain,
% 3.85/1.01      ( ~ v1_funct_1(X0)
% 3.85/1.01      | ~ sP0(sK1(sK3,X0),sK2(sK3,X0),sK3,X0)
% 3.85/1.01      | ~ r2_hidden(sK1(sK3,X0),k2_relat_1(sK3))
% 3.85/1.01      | ~ v1_relat_1(X0)
% 3.85/1.01      | k1_funct_1(X0,sK1(sK3,X0)) != sK2(sK3,X0)
% 3.85/1.01      | k2_funct_1(sK3) = X0
% 3.85/1.01      | k1_relat_1(X0) != k2_relat_1(sK3) ),
% 3.85/1.01      inference(global_propositional_subsumption,
% 3.85/1.01                [status(thm)],
% 3.85/1.01                [c_326,c_22,c_21]) ).
% 3.85/1.01  
% 3.85/1.01  cnf(c_331,plain,
% 3.85/1.01      ( ~ sP0(sK1(sK3,X0),sK2(sK3,X0),sK3,X0)
% 3.85/1.01      | ~ r2_hidden(sK1(sK3,X0),k2_relat_1(sK3))
% 3.85/1.01      | ~ v1_relat_1(X0)
% 3.85/1.01      | ~ v1_funct_1(X0)
% 3.85/1.01      | k1_funct_1(X0,sK1(sK3,X0)) != sK2(sK3,X0)
% 3.85/1.01      | k2_funct_1(sK3) = X0
% 3.85/1.01      | k1_relat_1(X0) != k2_relat_1(sK3) ),
% 3.85/1.01      inference(renaming,[status(thm)],[c_330]) ).
% 3.85/1.01  
% 3.85/1.01  cnf(c_412,plain,
% 3.85/1.01      ( ~ sP0(sK1(sK3,X0),sK2(sK3,X0),sK3,X0)
% 3.85/1.01      | ~ r2_hidden(sK1(sK3,X0),k2_relat_1(sK3))
% 3.85/1.01      | ~ v1_relat_1(X0)
% 3.85/1.01      | k1_funct_1(X0,sK1(sK3,X0)) != sK2(sK3,X0)
% 3.85/1.01      | k2_funct_1(sK3) = X0
% 3.85/1.01      | k1_relat_1(X0) != k2_relat_1(sK3)
% 3.85/1.01      | sK4 != X0 ),
% 3.85/1.01      inference(resolution_lifted,[status(thm)],[c_331,c_19]) ).
% 3.85/1.01  
% 3.85/1.01  cnf(c_413,plain,
% 3.85/1.01      ( ~ sP0(sK1(sK3,sK4),sK2(sK3,sK4),sK3,sK4)
% 3.85/1.01      | ~ r2_hidden(sK1(sK3,sK4),k2_relat_1(sK3))
% 3.85/1.01      | ~ v1_relat_1(sK4)
% 3.85/1.01      | k1_funct_1(sK4,sK1(sK3,sK4)) != sK2(sK3,sK4)
% 3.85/1.01      | k2_funct_1(sK3) = sK4
% 3.85/1.01      | k1_relat_1(sK4) != k2_relat_1(sK3) ),
% 3.85/1.01      inference(unflattening,[status(thm)],[c_412]) ).
% 3.85/1.01  
% 3.85/1.01  cnf(c_415,plain,
% 3.85/1.01      ( ~ r2_hidden(sK1(sK3,sK4),k2_relat_1(sK3))
% 3.85/1.01      | ~ sP0(sK1(sK3,sK4),sK2(sK3,sK4),sK3,sK4)
% 3.85/1.01      | k1_funct_1(sK4,sK1(sK3,sK4)) != sK2(sK3,sK4) ),
% 3.85/1.01      inference(global_propositional_subsumption,
% 3.85/1.01                [status(thm)],
% 3.85/1.01                [c_413,c_20,c_16,c_13]) ).
% 3.85/1.01  
% 3.85/1.01  cnf(c_416,plain,
% 3.85/1.01      ( ~ sP0(sK1(sK3,sK4),sK2(sK3,sK4),sK3,sK4)
% 3.85/1.01      | ~ r2_hidden(sK1(sK3,sK4),k2_relat_1(sK3))
% 3.85/1.01      | k1_funct_1(sK4,sK1(sK3,sK4)) != sK2(sK3,sK4) ),
% 3.85/1.01      inference(renaming,[status(thm)],[c_415]) ).
% 3.85/1.01  
% 3.85/1.01  cnf(c_1390,plain,
% 3.85/1.01      ( ~ sP0(sK1(sK3,sK4),sK2(sK3,sK4),sK3,sK4)
% 3.85/1.01      | ~ r2_hidden(sK1(sK3,sK4),k2_relat_1(sK3))
% 3.85/1.01      | k1_funct_1(sK4,sK1(sK3,sK4)) != sK2(sK3,sK4) ),
% 3.85/1.01      inference(subtyping,[status(esa)],[c_416]) ).
% 3.85/1.01  
% 3.85/1.01  cnf(c_1449,plain,
% 3.85/1.01      ( k1_funct_1(sK4,sK1(sK3,sK4)) != sK2(sK3,sK4)
% 3.85/1.01      | sP0(sK1(sK3,sK4),sK2(sK3,sK4),sK3,sK4) != iProver_top
% 3.85/1.01      | r2_hidden(sK1(sK3,sK4),k2_relat_1(sK3)) != iProver_top ),
% 3.85/1.01      inference(predicate_to_equality,[status(thm)],[c_1390]) ).
% 3.85/1.01  
% 3.85/1.01  cnf(contradiction,plain,
% 3.85/1.01      ( $false ),
% 3.85/1.01      inference(minisat,
% 3.85/1.01                [status(thm)],
% 3.85/1.01                [c_7975,c_4857,c_4681,c_4188,c_3818,c_2914,c_2727,c_2417,
% 3.85/1.01                 c_2012,c_1948,c_1449,c_1426]) ).
% 3.85/1.01  
% 3.85/1.01  
% 3.85/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.85/1.01  
% 3.85/1.01  ------                               Statistics
% 3.85/1.01  
% 3.85/1.01  ------ Selected
% 3.85/1.01  
% 3.85/1.01  total_time:                             0.293
% 3.85/1.01  
%------------------------------------------------------------------------------
