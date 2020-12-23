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
% DateTime   : Thu Dec  3 11:50:41 EST 2020

% Result     : Theorem 3.96s
% Output     : CNFRefutation 3.96s
% Verified   : 
% Statistics : Number of formulae       :  164 (1464 expanded)
%              Number of clauses        :  103 ( 385 expanded)
%              Number of leaves         :   16 ( 348 expanded)
%              Depth                    :   30
%              Number of atoms          :  805 (14466 expanded)
%              Number of equality atoms :  346 (6577 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   28 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,conjecture,(
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

fof(f7,negated_conjecture,(
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
    inference(negated_conjecture,[],[f6])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f34,plain,(
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
     => ( k2_funct_1(X0) != sK5
        & ! [X3,X2] :
            ( ( ( k1_funct_1(X0,X2) = X3
                | k1_funct_1(sK5,X3) != X2 )
              & ( k1_funct_1(sK5,X3) = X2
                | k1_funct_1(X0,X2) != X3 ) )
            | ~ r2_hidden(X3,k1_relat_1(sK5))
            | ~ r2_hidden(X2,k1_relat_1(X0)) )
        & k1_relat_1(sK5) = k2_relat_1(X0)
        & k1_relat_1(X0) = k2_relat_1(sK5)
        & v2_funct_1(X0)
        & v1_funct_1(sK5)
        & v1_relat_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
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
          ( k2_funct_1(sK4) != X1
          & ! [X3,X2] :
              ( ( ( k1_funct_1(sK4,X2) = X3
                  | k1_funct_1(X1,X3) != X2 )
                & ( k1_funct_1(X1,X3) = X2
                  | k1_funct_1(sK4,X2) != X3 ) )
              | ~ r2_hidden(X3,k1_relat_1(X1))
              | ~ r2_hidden(X2,k1_relat_1(sK4)) )
          & k1_relat_1(X1) = k2_relat_1(sK4)
          & k1_relat_1(sK4) = k2_relat_1(X1)
          & v2_funct_1(sK4)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK4)
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( k2_funct_1(sK4) != sK5
    & ! [X2,X3] :
        ( ( ( k1_funct_1(sK4,X2) = X3
            | k1_funct_1(sK5,X3) != X2 )
          & ( k1_funct_1(sK5,X3) = X2
            | k1_funct_1(sK4,X2) != X3 ) )
        | ~ r2_hidden(X3,k1_relat_1(sK5))
        | ~ r2_hidden(X2,k1_relat_1(sK4)) )
    & k1_relat_1(sK5) = k2_relat_1(sK4)
    & k1_relat_1(sK4) = k2_relat_1(sK5)
    & v2_funct_1(sK4)
    & v1_funct_1(sK5)
    & v1_relat_1(sK5)
    & v1_funct_1(sK4)
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f32,f34,f33])).

fof(f62,plain,(
    k1_relat_1(sK5) = k2_relat_1(sK4) ),
    inference(cnf_transformation,[],[f35])).

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

fof(f10,plain,(
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

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f20,plain,(
    ! [X2,X3,X0,X1] :
      ( sP0(X2,X3,X0,X1)
    <=> ( ( k1_funct_1(X0,X3) = X2
          & r2_hidden(X3,k1_relat_1(X0)) )
        | k1_funct_1(X1,X2) != X3
        | ~ r2_hidden(X2,k2_relat_1(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f21,plain,(
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
    inference(definition_folding,[],[f11,f20])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f28,plain,(
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

fof(f29,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f27,f28])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = k2_relat_1(X0)
      | k2_funct_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f74,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f43])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f13,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f50,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f60,plain,(
    v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f56,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f57,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X1)) != k1_funct_1(X1,sK3(X0,X1))
        & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ( k1_funct_1(X0,sK3(X0,X1)) != k1_funct_1(X1,sK3(X0,X1))
            & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f30])).

fof(f54,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK3(X0,X1),k1_relat_1(X0))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f9,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f36,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f37,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f58,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f35])).

fof(f59,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f35])).

fof(f65,plain,(
    k2_funct_1(sK4) != sK5 ),
    inference(cnf_transformation,[],[f35])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k2_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
          & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
        & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 )
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
        & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 )
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | k1_funct_1(X2,X1) != X0
      | ~ r2_hidden(X1,k1_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f66,plain,(
    ! [X2,X3,X1] :
      ( sP0(k1_funct_1(X2,X1),X1,X2,X3)
      | ~ r2_hidden(X1,k1_relat_1(X2)) ) ),
    inference(equality_resolution,[],[f42])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,k1_relat_1(X2))
      | k1_funct_1(X3,X0) != X1
      | ~ r2_hidden(X0,k2_relat_1(X2))
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f68,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(k1_funct_1(X3,X0),k1_relat_1(X2))
      | ~ r2_hidden(X0,k2_relat_1(X2))
      | ~ sP0(X0,k1_funct_1(X3,X0),X2,X3) ) ),
    inference(equality_resolution,[],[f38])).

fof(f44,plain,(
    ! [X4,X0,X5,X1] :
      ( sP0(X4,X5,X0,X1)
      | k2_funct_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f73,plain,(
    ! [X4,X0,X5] :
      ( sP0(X4,X5,X0,k2_funct_1(X0))
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f45,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X4,k2_relat_1(X0))
      | k1_funct_1(X0,X5) != X4
      | ~ r2_hidden(X5,k1_relat_1(X0))
      | k2_funct_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f71,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k1_funct_1(X0,X5),k2_relat_1(X0))
      | ~ r2_hidden(X5,k1_relat_1(X0))
      | k2_funct_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f72,plain,(
    ! [X0,X5] :
      ( r2_hidden(k1_funct_1(X0,X5),k2_relat_1(X0))
      | ~ r2_hidden(X5,k1_relat_1(X0))
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f71])).

fof(f63,plain,(
    ! [X2,X3] :
      ( k1_funct_1(sK5,X3) = X2
      | k1_funct_1(sK4,X2) != X3
      | ~ r2_hidden(X3,k1_relat_1(sK5))
      | ~ r2_hidden(X2,k1_relat_1(sK4)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f76,plain,(
    ! [X2] :
      ( k1_funct_1(sK5,k1_funct_1(sK4,X2)) = X2
      | ~ r2_hidden(k1_funct_1(sK4,X2),k1_relat_1(sK5))
      | ~ r2_hidden(X2,k1_relat_1(sK4)) ) ),
    inference(equality_resolution,[],[f63])).

fof(f55,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_funct_1(X0,sK3(X0,X1)) != k1_funct_1(X1,sK3(X0,X1))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_23,negated_conjecture,
    ( k1_relat_1(sK5) = k2_relat_1(sK4) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1170,negated_conjecture,
    ( k1_relat_1(sK5) = k2_relat_1(sK4) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_13,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(X0))
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_15,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_167,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13,c_15])).

cnf(c_168,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(renaming,[status(thm)],[c_167])).

cnf(c_25,negated_conjecture,
    ( v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_304,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_168,c_25])).

cnf(c_305,plain,
    ( ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK4)
    | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_304])).

cnf(c_29,negated_conjecture,
    ( v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_54,plain,
    ( ~ v2_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK4)
    | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_307,plain,
    ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_305,c_29,c_28,c_25,c_54])).

cnf(c_1164,plain,
    ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
    inference(subtyping,[status(esa)],[c_307])).

cnf(c_19,plain,
    ( r2_hidden(sK3(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | X1 = X0
    | k1_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1174,plain,
    ( r2_hidden(sK3(X0_44,X1_44),k1_relat_1(X0_44))
    | ~ v1_relat_1(X0_44)
    | ~ v1_relat_1(X1_44)
    | ~ v1_funct_1(X0_44)
    | ~ v1_funct_1(X1_44)
    | k1_relat_1(X1_44) != k1_relat_1(X0_44)
    | X1_44 = X0_44 ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1669,plain,
    ( k1_relat_1(X0_44) != k1_relat_1(X1_44)
    | X0_44 = X1_44
    | r2_hidden(sK3(X1_44,X0_44),k1_relat_1(X1_44)) = iProver_top
    | v1_relat_1(X0_44) != iProver_top
    | v1_relat_1(X1_44) != iProver_top
    | v1_funct_1(X0_44) != iProver_top
    | v1_funct_1(X1_44) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1174])).

cnf(c_2216,plain,
    ( k1_relat_1(X0_44) != k2_relat_1(sK4)
    | k2_funct_1(sK4) = X0_44
    | r2_hidden(sK3(X0_44,k2_funct_1(sK4)),k1_relat_1(X0_44)) = iProver_top
    | v1_relat_1(X0_44) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top
    | v1_funct_1(X0_44) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1164,c_1669])).

cnf(c_30,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_31,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_93,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_95,plain,
    ( v1_relat_1(k2_funct_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_93])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_96,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_98,plain,
    ( v1_relat_1(sK4) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_96])).

cnf(c_3549,plain,
    ( v1_funct_1(X0_44) != iProver_top
    | k1_relat_1(X0_44) != k2_relat_1(sK4)
    | k2_funct_1(sK4) = X0_44
    | r2_hidden(sK3(X0_44,k2_funct_1(sK4)),k1_relat_1(X0_44)) = iProver_top
    | v1_relat_1(X0_44) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2216,c_30,c_31,c_95,c_98])).

cnf(c_3550,plain,
    ( k1_relat_1(X0_44) != k2_relat_1(sK4)
    | k2_funct_1(sK4) = X0_44
    | r2_hidden(sK3(X0_44,k2_funct_1(sK4)),k1_relat_1(X0_44)) = iProver_top
    | v1_relat_1(X0_44) != iProver_top
    | v1_funct_1(X0_44) != iProver_top ),
    inference(renaming,[status(thm)],[c_3549])).

cnf(c_3556,plain,
    ( k1_relat_1(X0_44) != k1_relat_1(sK5)
    | k2_funct_1(sK4) = X0_44
    | r2_hidden(sK3(X0_44,k2_funct_1(sK4)),k1_relat_1(X0_44)) = iProver_top
    | v1_relat_1(X0_44) != iProver_top
    | v1_funct_1(X0_44) != iProver_top ),
    inference(superposition,[status(thm)],[c_1170,c_3550])).

cnf(c_3626,plain,
    ( k2_funct_1(sK4) = sK5
    | r2_hidden(sK3(sK5,k2_funct_1(sK4)),k1_relat_1(sK5)) = iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3556])).

cnf(c_27,negated_conjecture,
    ( v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_32,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_33,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_20,negated_conjecture,
    ( k2_funct_1(sK4) != sK5 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1173,negated_conjecture,
    ( k2_funct_1(sK4) != sK5 ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1805,plain,
    ( r2_hidden(sK3(sK5,k2_funct_1(sK4)),k1_relat_1(sK5))
    | ~ v1_relat_1(k2_funct_1(sK4))
    | ~ v1_relat_1(sK5)
    | ~ v1_funct_1(k2_funct_1(sK4))
    | ~ v1_funct_1(sK5)
    | k1_relat_1(k2_funct_1(sK4)) != k1_relat_1(sK5)
    | k2_funct_1(sK4) = sK5 ),
    inference(instantiation,[status(thm)],[c_1174])).

cnf(c_1806,plain,
    ( k1_relat_1(k2_funct_1(sK4)) != k1_relat_1(sK5)
    | k2_funct_1(sK4) = sK5
    | r2_hidden(sK3(sK5,k2_funct_1(sK4)),k1_relat_1(sK5)) = iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1805])).

cnf(c_1189,plain,
    ( X0_45 != X1_45
    | X2_45 != X1_45
    | X2_45 = X0_45 ),
    theory(equality)).

cnf(c_1821,plain,
    ( k1_relat_1(k2_funct_1(sK4)) != X0_45
    | k1_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK5)
    | k1_relat_1(sK5) != X0_45 ),
    inference(instantiation,[status(thm)],[c_1189])).

cnf(c_1852,plain,
    ( k1_relat_1(k2_funct_1(sK4)) != k2_relat_1(sK4)
    | k1_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK5)
    | k1_relat_1(sK5) != k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1821])).

cnf(c_3727,plain,
    ( r2_hidden(sK3(sK5,k2_funct_1(sK4)),k1_relat_1(sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3626,c_30,c_31,c_32,c_33,c_95,c_98,c_1173,c_1170,c_1164,c_1806,c_1852])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_407,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_25])).

cnf(c_408,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK4)
    | k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_407])).

cnf(c_412,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK4))
    | k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_408,c_29,c_28])).

cnf(c_1159,plain,
    ( ~ r2_hidden(X0_43,k2_relat_1(sK4))
    | k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),X0_43)) = X0_43 ),
    inference(subtyping,[status(esa)],[c_412])).

cnf(c_1679,plain,
    ( k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),X0_43)) = X0_43
    | r2_hidden(X0_43,k2_relat_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1159])).

cnf(c_3311,plain,
    ( k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),X0_43)) = X0_43
    | r2_hidden(X0_43,k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1170,c_1679])).

cnf(c_3732,plain,
    ( k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),sK3(sK5,k2_funct_1(sK4)))) = sK3(sK5,k2_funct_1(sK4)) ),
    inference(superposition,[status(thm)],[c_3727,c_3311])).

cnf(c_2,plain,
    ( sP0(k1_funct_1(X0,X1),X1,X0,X2)
    | ~ r2_hidden(X1,k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1180,plain,
    ( sP0(k1_funct_1(X0_44,X0_43),X0_43,X0_44,X1_44)
    | ~ r2_hidden(X0_43,k1_relat_1(X0_44)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1663,plain,
    ( sP0(k1_funct_1(X0_44,X0_43),X0_43,X0_44,X1_44) = iProver_top
    | r2_hidden(X0_43,k1_relat_1(X0_44)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1180])).

cnf(c_3923,plain,
    ( sP0(sK3(sK5,k2_funct_1(sK4)),k1_funct_1(k2_funct_1(sK4),sK3(sK5,k2_funct_1(sK4))),sK4,X0_44) = iProver_top
    | r2_hidden(k1_funct_1(k2_funct_1(sK4),sK3(sK5,k2_funct_1(sK4))),k1_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3732,c_1663])).

cnf(c_1197,plain,
    ( k2_relat_1(X0_44) = k2_relat_1(X1_44)
    | X0_44 != X1_44 ),
    theory(equality)).

cnf(c_1208,plain,
    ( k2_relat_1(sK4) = k2_relat_1(sK4)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1197])).

cnf(c_1185,plain,
    ( X0_44 = X0_44 ),
    theory(equality)).

cnf(c_1214,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_1185])).

cnf(c_1783,plain,
    ( k2_relat_1(sK4) != X0_45
    | k2_relat_1(sK4) = k1_relat_1(X0_44)
    | k1_relat_1(X0_44) != X0_45 ),
    inference(instantiation,[status(thm)],[c_1189])).

cnf(c_1836,plain,
    ( k2_relat_1(sK4) != k2_relat_1(sK4)
    | k2_relat_1(sK4) = k1_relat_1(X0_44)
    | k1_relat_1(X0_44) != k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1783])).

cnf(c_1873,plain,
    ( k2_relat_1(sK4) != k2_relat_1(sK4)
    | k2_relat_1(sK4) = k1_relat_1(sK5)
    | k1_relat_1(sK5) != k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1836])).

cnf(c_1184,plain,
    ( X0_43 = X0_43 ),
    theory(equality)).

cnf(c_1986,plain,
    ( sK3(sK5,k2_funct_1(sK4)) = sK3(sK5,k2_funct_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_1184])).

cnf(c_1196,plain,
    ( ~ r2_hidden(X0_43,X0_45)
    | r2_hidden(X1_43,X1_45)
    | X1_45 != X0_45
    | X1_43 != X0_43 ),
    theory(equality)).

cnf(c_1816,plain,
    ( r2_hidden(X0_43,X0_45)
    | ~ r2_hidden(sK3(sK5,k2_funct_1(sK4)),k1_relat_1(sK5))
    | X0_45 != k1_relat_1(sK5)
    | X0_43 != sK3(sK5,k2_funct_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_1196])).

cnf(c_1985,plain,
    ( r2_hidden(sK3(sK5,k2_funct_1(sK4)),X0_45)
    | ~ r2_hidden(sK3(sK5,k2_funct_1(sK4)),k1_relat_1(sK5))
    | X0_45 != k1_relat_1(sK5)
    | sK3(sK5,k2_funct_1(sK4)) != sK3(sK5,k2_funct_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_1816])).

cnf(c_2103,plain,
    ( r2_hidden(sK3(sK5,k2_funct_1(sK4)),k2_relat_1(sK4))
    | ~ r2_hidden(sK3(sK5,k2_funct_1(sK4)),k1_relat_1(sK5))
    | k2_relat_1(sK4) != k1_relat_1(sK5)
    | sK3(sK5,k2_funct_1(sK4)) != sK3(sK5,k2_funct_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_1985])).

cnf(c_2104,plain,
    ( k2_relat_1(sK4) != k1_relat_1(sK5)
    | sK3(sK5,k2_funct_1(sK4)) != sK3(sK5,k2_funct_1(sK4))
    | r2_hidden(sK3(sK5,k2_funct_1(sK4)),k2_relat_1(sK4)) = iProver_top
    | r2_hidden(sK3(sK5,k2_funct_1(sK4)),k1_relat_1(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2103])).

cnf(c_6,plain,
    ( ~ sP0(X0,k1_funct_1(X1,X0),X2,X1)
    | ~ r2_hidden(X0,k2_relat_1(X2))
    | r2_hidden(k1_funct_1(X1,X0),k1_relat_1(X2)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1176,plain,
    ( ~ sP0(X0_43,k1_funct_1(X0_44,X0_43),X1_44,X0_44)
    | ~ r2_hidden(X0_43,k2_relat_1(X1_44))
    | r2_hidden(k1_funct_1(X0_44,X0_43),k1_relat_1(X1_44)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_2301,plain,
    ( ~ sP0(sK3(sK5,k2_funct_1(sK4)),k1_funct_1(X0_44,sK3(sK5,k2_funct_1(sK4))),sK4,X0_44)
    | ~ r2_hidden(sK3(sK5,k2_funct_1(sK4)),k2_relat_1(sK4))
    | r2_hidden(k1_funct_1(X0_44,sK3(sK5,k2_funct_1(sK4))),k1_relat_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_1176])).

cnf(c_3250,plain,
    ( ~ sP0(sK3(sK5,k2_funct_1(sK4)),k1_funct_1(k2_funct_1(sK4),sK3(sK5,k2_funct_1(sK4))),sK4,k2_funct_1(sK4))
    | ~ r2_hidden(sK3(sK5,k2_funct_1(sK4)),k2_relat_1(sK4))
    | r2_hidden(k1_funct_1(k2_funct_1(sK4),sK3(sK5,k2_funct_1(sK4))),k1_relat_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_2301])).

cnf(c_3252,plain,
    ( sP0(sK3(sK5,k2_funct_1(sK4)),k1_funct_1(k2_funct_1(sK4),sK3(sK5,k2_funct_1(sK4))),sK4,k2_funct_1(sK4)) != iProver_top
    | r2_hidden(sK3(sK5,k2_funct_1(sK4)),k2_relat_1(sK4)) != iProver_top
    | r2_hidden(k1_funct_1(k2_funct_1(sK4),sK3(sK5,k2_funct_1(sK4))),k1_relat_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3250])).

cnf(c_12,plain,
    ( sP0(X0,X1,X2,k2_funct_1(X2))
    | ~ v2_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(k2_funct_1(X2))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(k2_funct_1(X2)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_479,plain,
    ( sP0(X0,X1,X2,k2_funct_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(k2_funct_1(X2))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(k2_funct_1(X2))
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_25])).

cnf(c_480,plain,
    ( sP0(X0,X1,sK4,k2_funct_1(sK4))
    | ~ v1_relat_1(k2_funct_1(sK4))
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(k2_funct_1(sK4))
    | ~ v1_funct_1(sK4) ),
    inference(unflattening,[status(thm)],[c_479])).

cnf(c_94,plain,
    ( v1_relat_1(k2_funct_1(sK4))
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_97,plain,
    ( ~ v1_relat_1(sK4)
    | v1_funct_1(k2_funct_1(sK4))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_484,plain,
    ( sP0(X0,X1,sK4,k2_funct_1(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_480,c_29,c_28,c_94,c_97])).

cnf(c_1155,plain,
    ( sP0(X0_43,X1_43,sK4,k2_funct_1(sK4)) ),
    inference(subtyping,[status(esa)],[c_484])).

cnf(c_3251,plain,
    ( sP0(sK3(sK5,k2_funct_1(sK4)),k1_funct_1(k2_funct_1(sK4),sK3(sK5,k2_funct_1(sK4))),sK4,k2_funct_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_1155])).

cnf(c_3254,plain,
    ( sP0(sK3(sK5,k2_funct_1(sK4)),k1_funct_1(k2_funct_1(sK4),sK3(sK5,k2_funct_1(sK4))),sK4,k2_funct_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3251])).

cnf(c_4261,plain,
    ( sP0(sK3(sK5,k2_funct_1(sK4)),k1_funct_1(k2_funct_1(sK4),sK3(sK5,k2_funct_1(sK4))),sK4,X0_44) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3923,c_30,c_31,c_32,c_33,c_95,c_98,c_1208,c_1214,c_1173,c_1170,c_1164,c_1806,c_1852,c_1873,c_1986,c_2104,c_3252,c_3254])).

cnf(c_1667,plain,
    ( sP0(X0_43,k1_funct_1(X0_44,X0_43),X1_44,X0_44) != iProver_top
    | r2_hidden(X0_43,k2_relat_1(X1_44)) != iProver_top
    | r2_hidden(k1_funct_1(X0_44,X0_43),k1_relat_1(X1_44)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1176])).

cnf(c_4267,plain,
    ( r2_hidden(sK3(sK5,k2_funct_1(sK4)),k2_relat_1(sK4)) != iProver_top
    | r2_hidden(k1_funct_1(k2_funct_1(sK4),sK3(sK5,k2_funct_1(sK4))),k1_relat_1(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4261,c_1667])).

cnf(c_4271,plain,
    ( r2_hidden(k1_funct_1(k2_funct_1(sK4),sK3(sK5,k2_funct_1(sK4))),k1_relat_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4267,c_30,c_31,c_32,c_33,c_95,c_98,c_1208,c_1214,c_1173,c_1170,c_1164,c_1806,c_1852,c_1873,c_1986,c_2104,c_3252,c_3254])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(X1)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_443,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(X1))
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_25])).

cnf(c_444,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4))
    | ~ v1_relat_1(k2_funct_1(sK4))
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(k2_funct_1(sK4))
    | ~ v1_funct_1(sK4) ),
    inference(unflattening,[status(thm)],[c_443])).

cnf(c_448,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_444,c_29,c_28,c_94,c_97])).

cnf(c_1157,plain,
    ( ~ r2_hidden(X0_43,k1_relat_1(sK4))
    | r2_hidden(k1_funct_1(sK4,X0_43),k2_relat_1(sK4)) ),
    inference(subtyping,[status(esa)],[c_448])).

cnf(c_1681,plain,
    ( r2_hidden(X0_43,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0_43),k2_relat_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1157])).

cnf(c_3830,plain,
    ( r2_hidden(X0_43,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0_43),k1_relat_1(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1170,c_1681])).

cnf(c_22,negated_conjecture,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | ~ r2_hidden(k1_funct_1(sK4,X0),k1_relat_1(sK5))
    | k1_funct_1(sK5,k1_funct_1(sK4,X0)) = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1171,negated_conjecture,
    ( ~ r2_hidden(X0_43,k1_relat_1(sK4))
    | ~ r2_hidden(k1_funct_1(sK4,X0_43),k1_relat_1(sK5))
    | k1_funct_1(sK5,k1_funct_1(sK4,X0_43)) = X0_43 ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1671,plain,
    ( k1_funct_1(sK5,k1_funct_1(sK4,X0_43)) = X0_43
    | r2_hidden(X0_43,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0_43),k1_relat_1(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1171])).

cnf(c_3843,plain,
    ( k1_funct_1(sK5,k1_funct_1(sK4,X0_43)) = X0_43
    | r2_hidden(X0_43,k1_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3830,c_1671])).

cnf(c_4276,plain,
    ( k1_funct_1(sK5,k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),sK3(sK5,k2_funct_1(sK4))))) = k1_funct_1(k2_funct_1(sK4),sK3(sK5,k2_funct_1(sK4))) ),
    inference(superposition,[status(thm)],[c_4271,c_3843])).

cnf(c_6178,plain,
    ( k1_funct_1(k2_funct_1(sK4),sK3(sK5,k2_funct_1(sK4))) = k1_funct_1(sK5,sK3(sK5,k2_funct_1(sK4))) ),
    inference(superposition,[status(thm)],[c_3732,c_4276])).

cnf(c_18,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | X1 = X0
    | k1_funct_1(X1,sK3(X0,X1)) != k1_funct_1(X0,sK3(X0,X1))
    | k1_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1175,plain,
    ( ~ v1_relat_1(X0_44)
    | ~ v1_relat_1(X1_44)
    | ~ v1_funct_1(X0_44)
    | ~ v1_funct_1(X1_44)
    | k1_relat_1(X1_44) != k1_relat_1(X0_44)
    | X1_44 = X0_44
    | k1_funct_1(X1_44,sK3(X0_44,X1_44)) != k1_funct_1(X0_44,sK3(X0_44,X1_44)) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1808,plain,
    ( ~ v1_relat_1(k2_funct_1(sK4))
    | ~ v1_relat_1(sK5)
    | ~ v1_funct_1(k2_funct_1(sK4))
    | ~ v1_funct_1(sK5)
    | k1_relat_1(k2_funct_1(sK4)) != k1_relat_1(sK5)
    | k2_funct_1(sK4) = sK5
    | k1_funct_1(k2_funct_1(sK4),sK3(sK5,k2_funct_1(sK4))) != k1_funct_1(sK5,sK3(sK5,k2_funct_1(sK4))) ),
    inference(instantiation,[status(thm)],[c_1175])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6178,c_1852,c_1808,c_1164,c_1170,c_1173,c_97,c_94,c_26,c_27,c_28,c_29])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:10:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.96/1.09  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.96/1.09  
% 3.96/1.09  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.96/1.09  
% 3.96/1.09  ------  iProver source info
% 3.96/1.09  
% 3.96/1.09  git: date: 2020-06-30 10:37:57 +0100
% 3.96/1.09  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.96/1.09  git: non_committed_changes: false
% 3.96/1.09  git: last_make_outside_of_git: false
% 3.96/1.09  
% 3.96/1.09  ------ 
% 3.96/1.09  ------ Parsing...
% 3.96/1.09  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.96/1.09  
% 3.96/1.09  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.96/1.09  
% 3.96/1.09  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.96/1.09  
% 3.96/1.09  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.96/1.09  ------ Proving...
% 3.96/1.09  ------ Problem Properties 
% 3.96/1.09  
% 3.96/1.09  
% 3.96/1.09  clauses                                 28
% 3.96/1.09  conjectures                             9
% 3.96/1.09  EPR                                     4
% 3.96/1.09  Horn                                    23
% 3.96/1.09  unary                                   10
% 3.96/1.09  binary                                  7
% 3.96/1.09  lits                                    75
% 3.96/1.09  lits eq                                 25
% 3.96/1.09  fd_pure                                 0
% 3.96/1.09  fd_pseudo                               0
% 3.96/1.09  fd_cond                                 3
% 3.96/1.09  fd_pseudo_cond                          3
% 3.96/1.09  AC symbols                              0
% 3.96/1.09  
% 3.96/1.09  ------ Input Options Time Limit: Unbounded
% 3.96/1.09  
% 3.96/1.09  
% 3.96/1.09  ------ 
% 3.96/1.09  Current options:
% 3.96/1.09  ------ 
% 3.96/1.09  
% 3.96/1.09  
% 3.96/1.09  
% 3.96/1.09  
% 3.96/1.09  ------ Proving...
% 3.96/1.09  
% 3.96/1.09  
% 3.96/1.09  % SZS status Theorem for theBenchmark.p
% 3.96/1.09  
% 3.96/1.09  % SZS output start CNFRefutation for theBenchmark.p
% 3.96/1.09  
% 3.96/1.09  fof(f6,conjecture,(
% 3.96/1.09    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2,X3] : ((r2_hidden(X3,k1_relat_1(X1)) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,X2) = X3 <=> k1_funct_1(X1,X3) = X2)) & k1_relat_1(X1) = k2_relat_1(X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 3.96/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.96/1.09  
% 3.96/1.09  fof(f7,negated_conjecture,(
% 3.96/1.09    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2,X3] : ((r2_hidden(X3,k1_relat_1(X1)) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,X2) = X3 <=> k1_funct_1(X1,X3) = X2)) & k1_relat_1(X1) = k2_relat_1(X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 3.96/1.09    inference(negated_conjecture,[],[f6])).
% 3.96/1.09  
% 3.96/1.09  fof(f18,plain,(
% 3.96/1.09    ? [X0] : (? [X1] : ((k2_funct_1(X0) != X1 & (! [X2,X3] : ((k1_funct_1(X0,X2) = X3 <=> k1_funct_1(X1,X3) = X2) | (~r2_hidden(X3,k1_relat_1(X1)) | ~r2_hidden(X2,k1_relat_1(X0)))) & k1_relat_1(X1) = k2_relat_1(X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 3.96/1.09    inference(ennf_transformation,[],[f7])).
% 3.96/1.09  
% 3.96/1.09  fof(f19,plain,(
% 3.96/1.09    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & ! [X2,X3] : ((k1_funct_1(X0,X2) = X3 <=> k1_funct_1(X1,X3) = X2) | ~r2_hidden(X3,k1_relat_1(X1)) | ~r2_hidden(X2,k1_relat_1(X0))) & k1_relat_1(X1) = k2_relat_1(X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 3.96/1.09    inference(flattening,[],[f18])).
% 3.96/1.09  
% 3.96/1.09  fof(f32,plain,(
% 3.96/1.09    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & ! [X2,X3] : (((k1_funct_1(X0,X2) = X3 | k1_funct_1(X1,X3) != X2) & (k1_funct_1(X1,X3) = X2 | k1_funct_1(X0,X2) != X3)) | ~r2_hidden(X3,k1_relat_1(X1)) | ~r2_hidden(X2,k1_relat_1(X0))) & k1_relat_1(X1) = k2_relat_1(X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 3.96/1.09    inference(nnf_transformation,[],[f19])).
% 3.96/1.09  
% 3.96/1.09  fof(f34,plain,(
% 3.96/1.09    ( ! [X0] : (? [X1] : (k2_funct_1(X0) != X1 & ! [X2,X3] : (((k1_funct_1(X0,X2) = X3 | k1_funct_1(X1,X3) != X2) & (k1_funct_1(X1,X3) = X2 | k1_funct_1(X0,X2) != X3)) | ~r2_hidden(X3,k1_relat_1(X1)) | ~r2_hidden(X2,k1_relat_1(X0))) & k1_relat_1(X1) = k2_relat_1(X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) => (k2_funct_1(X0) != sK5 & ! [X3,X2] : (((k1_funct_1(X0,X2) = X3 | k1_funct_1(sK5,X3) != X2) & (k1_funct_1(sK5,X3) = X2 | k1_funct_1(X0,X2) != X3)) | ~r2_hidden(X3,k1_relat_1(sK5)) | ~r2_hidden(X2,k1_relat_1(X0))) & k1_relat_1(sK5) = k2_relat_1(X0) & k1_relat_1(X0) = k2_relat_1(sK5) & v2_funct_1(X0) & v1_funct_1(sK5) & v1_relat_1(sK5))) )),
% 3.96/1.09    introduced(choice_axiom,[])).
% 3.96/1.09  
% 3.96/1.09  fof(f33,plain,(
% 3.96/1.09    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & ! [X2,X3] : (((k1_funct_1(X0,X2) = X3 | k1_funct_1(X1,X3) != X2) & (k1_funct_1(X1,X3) = X2 | k1_funct_1(X0,X2) != X3)) | ~r2_hidden(X3,k1_relat_1(X1)) | ~r2_hidden(X2,k1_relat_1(X0))) & k1_relat_1(X1) = k2_relat_1(X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k2_funct_1(sK4) != X1 & ! [X3,X2] : (((k1_funct_1(sK4,X2) = X3 | k1_funct_1(X1,X3) != X2) & (k1_funct_1(X1,X3) = X2 | k1_funct_1(sK4,X2) != X3)) | ~r2_hidden(X3,k1_relat_1(X1)) | ~r2_hidden(X2,k1_relat_1(sK4))) & k1_relat_1(X1) = k2_relat_1(sK4) & k1_relat_1(sK4) = k2_relat_1(X1) & v2_funct_1(sK4) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK4) & v1_relat_1(sK4))),
% 3.96/1.09    introduced(choice_axiom,[])).
% 3.96/1.09  
% 3.96/1.09  fof(f35,plain,(
% 3.96/1.09    (k2_funct_1(sK4) != sK5 & ! [X2,X3] : (((k1_funct_1(sK4,X2) = X3 | k1_funct_1(sK5,X3) != X2) & (k1_funct_1(sK5,X3) = X2 | k1_funct_1(sK4,X2) != X3)) | ~r2_hidden(X3,k1_relat_1(sK5)) | ~r2_hidden(X2,k1_relat_1(sK4))) & k1_relat_1(sK5) = k2_relat_1(sK4) & k1_relat_1(sK4) = k2_relat_1(sK5) & v2_funct_1(sK4) & v1_funct_1(sK5) & v1_relat_1(sK5)) & v1_funct_1(sK4) & v1_relat_1(sK4)),
% 3.96/1.09    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f32,f34,f33])).
% 3.96/1.09  
% 3.96/1.09  fof(f62,plain,(
% 3.96/1.09    k1_relat_1(sK5) = k2_relat_1(sK4)),
% 3.96/1.09    inference(cnf_transformation,[],[f35])).
% 3.96/1.09  
% 3.96/1.09  fof(f2,axiom,(
% 3.96/1.09    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) => (k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0)))) & ((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) => (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) & k1_relat_1(X1) = k2_relat_1(X0))))))),
% 3.96/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.96/1.09  
% 3.96/1.09  fof(f10,plain,(
% 3.96/1.09    ! [X0] : ((! [X1] : ((k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | (k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))))) & k1_relat_1(X1) = k2_relat_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.96/1.09    inference(ennf_transformation,[],[f2])).
% 3.96/1.09  
% 3.96/1.09  fof(f11,plain,(
% 3.96/1.09    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0)))) & k1_relat_1(X1) = k2_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.96/1.09    inference(flattening,[],[f10])).
% 3.96/1.09  
% 3.96/1.09  fof(f20,plain,(
% 3.96/1.09    ! [X2,X3,X0,X1] : (sP0(X2,X3,X0,X1) <=> ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))))),
% 3.96/1.09    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.96/1.09  
% 3.96/1.09  fof(f21,plain,(
% 3.96/1.09    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & sP0(X2,X3,X0,X1)) & k1_relat_1(X1) = k2_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.96/1.09    inference(definition_folding,[],[f11,f20])).
% 3.96/1.09  
% 3.96/1.09  fof(f25,plain,(
% 3.96/1.09    ! [X0] : (! [X1] : (((k2_funct_1(X0) = X1 | (? [X2,X3] : (((k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))) & k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X2,X3,X0,X1)) | k1_relat_1(X1) != k2_relat_1(X0))) & ((! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & sP0(X2,X3,X0,X1)) & k1_relat_1(X1) = k2_relat_1(X0)) | k2_funct_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.96/1.09    inference(nnf_transformation,[],[f21])).
% 3.96/1.09  
% 3.96/1.09  fof(f26,plain,(
% 3.96/1.09    ! [X0] : (! [X1] : (((k2_funct_1(X0) = X1 | ? [X2,X3] : (((k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))) & k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X2,X3,X0,X1)) | k1_relat_1(X1) != k2_relat_1(X0)) & ((! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & sP0(X2,X3,X0,X1)) & k1_relat_1(X1) = k2_relat_1(X0)) | k2_funct_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.96/1.09    inference(flattening,[],[f25])).
% 3.96/1.09  
% 3.96/1.09  fof(f27,plain,(
% 3.96/1.09    ! [X0] : (! [X1] : (((k2_funct_1(X0) = X1 | ? [X2,X3] : (((k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))) & k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X2,X3,X0,X1)) | k1_relat_1(X1) != k2_relat_1(X0)) & ((! [X4,X5] : (((k1_funct_1(X1,X4) = X5 & r2_hidden(X4,k2_relat_1(X0))) | k1_funct_1(X0,X5) != X4 | ~r2_hidden(X5,k1_relat_1(X0))) & sP0(X4,X5,X0,X1)) & k1_relat_1(X1) = k2_relat_1(X0)) | k2_funct_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.96/1.09    inference(rectify,[],[f26])).
% 3.96/1.09  
% 3.96/1.09  fof(f28,plain,(
% 3.96/1.09    ! [X1,X0] : (? [X2,X3] : (((k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))) & k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X2,X3,X0,X1)) => (((k1_funct_1(X1,sK1(X0,X1)) != sK2(X0,X1) | ~r2_hidden(sK1(X0,X1),k2_relat_1(X0))) & k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))) | ~sP0(sK1(X0,X1),sK2(X0,X1),X0,X1)))),
% 3.96/1.09    introduced(choice_axiom,[])).
% 3.96/1.09  
% 3.96/1.09  fof(f29,plain,(
% 3.96/1.09    ! [X0] : (! [X1] : (((k2_funct_1(X0) = X1 | (((k1_funct_1(X1,sK1(X0,X1)) != sK2(X0,X1) | ~r2_hidden(sK1(X0,X1),k2_relat_1(X0))) & k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))) | ~sP0(sK1(X0,X1),sK2(X0,X1),X0,X1)) | k1_relat_1(X1) != k2_relat_1(X0)) & ((! [X4,X5] : (((k1_funct_1(X1,X4) = X5 & r2_hidden(X4,k2_relat_1(X0))) | k1_funct_1(X0,X5) != X4 | ~r2_hidden(X5,k1_relat_1(X0))) & sP0(X4,X5,X0,X1)) & k1_relat_1(X1) = k2_relat_1(X0)) | k2_funct_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.96/1.09    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f27,f28])).
% 3.96/1.09  
% 3.96/1.09  fof(f43,plain,(
% 3.96/1.09    ( ! [X0,X1] : (k1_relat_1(X1) = k2_relat_1(X0) | k2_funct_1(X0) != X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.96/1.09    inference(cnf_transformation,[],[f29])).
% 3.96/1.09  
% 3.96/1.09  fof(f74,plain,(
% 3.96/1.09    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v1_funct_1(k2_funct_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.96/1.09    inference(equality_resolution,[],[f43])).
% 3.96/1.09  
% 3.96/1.09  fof(f3,axiom,(
% 3.96/1.09    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 3.96/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.96/1.09  
% 3.96/1.09  fof(f12,plain,(
% 3.96/1.09    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.96/1.09    inference(ennf_transformation,[],[f3])).
% 3.96/1.09  
% 3.96/1.09  fof(f13,plain,(
% 3.96/1.09    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.96/1.09    inference(flattening,[],[f12])).
% 3.96/1.09  
% 3.96/1.09  fof(f50,plain,(
% 3.96/1.09    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.96/1.09    inference(cnf_transformation,[],[f13])).
% 3.96/1.09  
% 3.96/1.09  fof(f60,plain,(
% 3.96/1.09    v2_funct_1(sK4)),
% 3.96/1.09    inference(cnf_transformation,[],[f35])).
% 3.96/1.09  
% 3.96/1.09  fof(f56,plain,(
% 3.96/1.09    v1_relat_1(sK4)),
% 3.96/1.09    inference(cnf_transformation,[],[f35])).
% 3.96/1.09  
% 3.96/1.09  fof(f57,plain,(
% 3.96/1.09    v1_funct_1(sK4)),
% 3.96/1.09    inference(cnf_transformation,[],[f35])).
% 3.96/1.09  
% 3.96/1.09  fof(f5,axiom,(
% 3.96/1.09    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 3.96/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.96/1.09  
% 3.96/1.09  fof(f16,plain,(
% 3.96/1.09    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.96/1.09    inference(ennf_transformation,[],[f5])).
% 3.96/1.09  
% 3.96/1.09  fof(f17,plain,(
% 3.96/1.09    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.96/1.09    inference(flattening,[],[f16])).
% 3.96/1.09  
% 3.96/1.09  fof(f30,plain,(
% 3.96/1.09    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X1)) != k1_funct_1(X1,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),k1_relat_1(X0))))),
% 3.96/1.09    introduced(choice_axiom,[])).
% 3.96/1.09  
% 3.96/1.09  fof(f31,plain,(
% 3.96/1.09    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK3(X0,X1)) != k1_funct_1(X1,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.96/1.09    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f30])).
% 3.96/1.09  
% 3.96/1.09  fof(f54,plain,(
% 3.96/1.09    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK3(X0,X1),k1_relat_1(X0)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.96/1.09    inference(cnf_transformation,[],[f31])).
% 3.96/1.09  
% 3.96/1.09  fof(f1,axiom,(
% 3.96/1.09    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.96/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.96/1.09  
% 3.96/1.09  fof(f8,plain,(
% 3.96/1.09    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.96/1.09    inference(ennf_transformation,[],[f1])).
% 3.96/1.09  
% 3.96/1.09  fof(f9,plain,(
% 3.96/1.09    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.96/1.09    inference(flattening,[],[f8])).
% 3.96/1.09  
% 3.96/1.09  fof(f36,plain,(
% 3.96/1.09    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.96/1.09    inference(cnf_transformation,[],[f9])).
% 3.96/1.09  
% 3.96/1.09  fof(f37,plain,(
% 3.96/1.09    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.96/1.09    inference(cnf_transformation,[],[f9])).
% 3.96/1.09  
% 3.96/1.09  fof(f58,plain,(
% 3.96/1.09    v1_relat_1(sK5)),
% 3.96/1.09    inference(cnf_transformation,[],[f35])).
% 3.96/1.09  
% 3.96/1.09  fof(f59,plain,(
% 3.96/1.09    v1_funct_1(sK5)),
% 3.96/1.09    inference(cnf_transformation,[],[f35])).
% 3.96/1.09  
% 3.96/1.09  fof(f65,plain,(
% 3.96/1.09    k2_funct_1(sK4) != sK5),
% 3.96/1.09    inference(cnf_transformation,[],[f35])).
% 3.96/1.09  
% 3.96/1.09  fof(f4,axiom,(
% 3.96/1.09    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0 & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0)))),
% 3.96/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.96/1.09  
% 3.96/1.09  fof(f14,plain,(
% 3.96/1.09    ! [X0,X1] : (((k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0 & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0) | (~r2_hidden(X0,k2_relat_1(X1)) | ~v2_funct_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.96/1.09    inference(ennf_transformation,[],[f4])).
% 3.96/1.09  
% 3.96/1.09  fof(f15,plain,(
% 3.96/1.09    ! [X0,X1] : ((k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0 & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.96/1.09    inference(flattening,[],[f14])).
% 3.96/1.09  
% 3.96/1.09  fof(f52,plain,(
% 3.96/1.09    ( ! [X0,X1] : (k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 | ~r2_hidden(X0,k2_relat_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.96/1.09    inference(cnf_transformation,[],[f15])).
% 3.96/1.09  
% 3.96/1.09  fof(f22,plain,(
% 3.96/1.09    ! [X2,X3,X0,X1] : ((sP0(X2,X3,X0,X1) | ((k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0)))) & (((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))) | ~sP0(X2,X3,X0,X1)))),
% 3.96/1.09    inference(nnf_transformation,[],[f20])).
% 3.96/1.09  
% 3.96/1.09  fof(f23,plain,(
% 3.96/1.09    ! [X2,X3,X0,X1] : ((sP0(X2,X3,X0,X1) | ((k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0)))) & ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0)) | ~sP0(X2,X3,X0,X1)))),
% 3.96/1.09    inference(flattening,[],[f22])).
% 3.96/1.09  
% 3.96/1.09  fof(f24,plain,(
% 3.96/1.09    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ((k1_funct_1(X2,X1) != X0 | ~r2_hidden(X1,k1_relat_1(X2))) & k1_funct_1(X3,X0) = X1 & r2_hidden(X0,k2_relat_1(X2)))) & ((k1_funct_1(X2,X1) = X0 & r2_hidden(X1,k1_relat_1(X2))) | k1_funct_1(X3,X0) != X1 | ~r2_hidden(X0,k2_relat_1(X2)) | ~sP0(X0,X1,X2,X3)))),
% 3.96/1.09    inference(rectify,[],[f23])).
% 3.96/1.09  
% 3.96/1.09  fof(f42,plain,(
% 3.96/1.09    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2,X3) | k1_funct_1(X2,X1) != X0 | ~r2_hidden(X1,k1_relat_1(X2))) )),
% 3.96/1.09    inference(cnf_transformation,[],[f24])).
% 3.96/1.09  
% 3.96/1.09  fof(f66,plain,(
% 3.96/1.09    ( ! [X2,X3,X1] : (sP0(k1_funct_1(X2,X1),X1,X2,X3) | ~r2_hidden(X1,k1_relat_1(X2))) )),
% 3.96/1.09    inference(equality_resolution,[],[f42])).
% 3.96/1.09  
% 3.96/1.09  fof(f38,plain,(
% 3.96/1.09    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,k1_relat_1(X2)) | k1_funct_1(X3,X0) != X1 | ~r2_hidden(X0,k2_relat_1(X2)) | ~sP0(X0,X1,X2,X3)) )),
% 3.96/1.09    inference(cnf_transformation,[],[f24])).
% 3.96/1.09  
% 3.96/1.09  fof(f68,plain,(
% 3.96/1.09    ( ! [X2,X0,X3] : (r2_hidden(k1_funct_1(X3,X0),k1_relat_1(X2)) | ~r2_hidden(X0,k2_relat_1(X2)) | ~sP0(X0,k1_funct_1(X3,X0),X2,X3)) )),
% 3.96/1.09    inference(equality_resolution,[],[f38])).
% 3.96/1.09  
% 3.96/1.09  fof(f44,plain,(
% 3.96/1.09    ( ! [X4,X0,X5,X1] : (sP0(X4,X5,X0,X1) | k2_funct_1(X0) != X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.96/1.09    inference(cnf_transformation,[],[f29])).
% 3.96/1.09  
% 3.96/1.09  fof(f73,plain,(
% 3.96/1.09    ( ! [X4,X0,X5] : (sP0(X4,X5,X0,k2_funct_1(X0)) | ~v1_funct_1(k2_funct_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.96/1.09    inference(equality_resolution,[],[f44])).
% 3.96/1.09  
% 3.96/1.09  fof(f45,plain,(
% 3.96/1.09    ( ! [X4,X0,X5,X1] : (r2_hidden(X4,k2_relat_1(X0)) | k1_funct_1(X0,X5) != X4 | ~r2_hidden(X5,k1_relat_1(X0)) | k2_funct_1(X0) != X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.96/1.09    inference(cnf_transformation,[],[f29])).
% 3.96/1.09  
% 3.96/1.09  fof(f71,plain,(
% 3.96/1.09    ( ! [X0,X5,X1] : (r2_hidden(k1_funct_1(X0,X5),k2_relat_1(X0)) | ~r2_hidden(X5,k1_relat_1(X0)) | k2_funct_1(X0) != X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.96/1.09    inference(equality_resolution,[],[f45])).
% 3.96/1.09  
% 3.96/1.09  fof(f72,plain,(
% 3.96/1.09    ( ! [X0,X5] : (r2_hidden(k1_funct_1(X0,X5),k2_relat_1(X0)) | ~r2_hidden(X5,k1_relat_1(X0)) | ~v1_funct_1(k2_funct_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.96/1.09    inference(equality_resolution,[],[f71])).
% 3.96/1.09  
% 3.96/1.09  fof(f63,plain,(
% 3.96/1.09    ( ! [X2,X3] : (k1_funct_1(sK5,X3) = X2 | k1_funct_1(sK4,X2) != X3 | ~r2_hidden(X3,k1_relat_1(sK5)) | ~r2_hidden(X2,k1_relat_1(sK4))) )),
% 3.96/1.09    inference(cnf_transformation,[],[f35])).
% 3.96/1.09  
% 3.96/1.09  fof(f76,plain,(
% 3.96/1.09    ( ! [X2] : (k1_funct_1(sK5,k1_funct_1(sK4,X2)) = X2 | ~r2_hidden(k1_funct_1(sK4,X2),k1_relat_1(sK5)) | ~r2_hidden(X2,k1_relat_1(sK4))) )),
% 3.96/1.09    inference(equality_resolution,[],[f63])).
% 3.96/1.09  
% 3.96/1.09  fof(f55,plain,(
% 3.96/1.09    ( ! [X0,X1] : (X0 = X1 | k1_funct_1(X0,sK3(X0,X1)) != k1_funct_1(X1,sK3(X0,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.96/1.09    inference(cnf_transformation,[],[f31])).
% 3.96/1.09  
% 3.96/1.09  cnf(c_23,negated_conjecture,
% 3.96/1.09      ( k1_relat_1(sK5) = k2_relat_1(sK4) ),
% 3.96/1.09      inference(cnf_transformation,[],[f62]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_1170,negated_conjecture,
% 3.96/1.09      ( k1_relat_1(sK5) = k2_relat_1(sK4) ),
% 3.96/1.09      inference(subtyping,[status(esa)],[c_23]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_13,plain,
% 3.96/1.09      ( ~ v2_funct_1(X0)
% 3.96/1.09      | ~ v1_relat_1(X0)
% 3.96/1.09      | ~ v1_relat_1(k2_funct_1(X0))
% 3.96/1.09      | ~ v1_funct_1(X0)
% 3.96/1.09      | ~ v1_funct_1(k2_funct_1(X0))
% 3.96/1.09      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 3.96/1.09      inference(cnf_transformation,[],[f74]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_15,plain,
% 3.96/1.09      ( ~ v2_funct_1(X0)
% 3.96/1.09      | ~ v1_relat_1(X0)
% 3.96/1.09      | ~ v1_funct_1(X0)
% 3.96/1.09      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 3.96/1.09      inference(cnf_transformation,[],[f50]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_167,plain,
% 3.96/1.09      ( ~ v1_funct_1(X0)
% 3.96/1.09      | ~ v2_funct_1(X0)
% 3.96/1.09      | ~ v1_relat_1(X0)
% 3.96/1.09      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 3.96/1.09      inference(global_propositional_subsumption,
% 3.96/1.09                [status(thm)],
% 3.96/1.09                [c_13,c_15]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_168,plain,
% 3.96/1.09      ( ~ v2_funct_1(X0)
% 3.96/1.09      | ~ v1_relat_1(X0)
% 3.96/1.09      | ~ v1_funct_1(X0)
% 3.96/1.09      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 3.96/1.09      inference(renaming,[status(thm)],[c_167]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_25,negated_conjecture,
% 3.96/1.09      ( v2_funct_1(sK4) ),
% 3.96/1.09      inference(cnf_transformation,[],[f60]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_304,plain,
% 3.96/1.09      ( ~ v1_relat_1(X0)
% 3.96/1.09      | ~ v1_funct_1(X0)
% 3.96/1.09      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 3.96/1.09      | sK4 != X0 ),
% 3.96/1.09      inference(resolution_lifted,[status(thm)],[c_168,c_25]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_305,plain,
% 3.96/1.09      ( ~ v1_relat_1(sK4)
% 3.96/1.09      | ~ v1_funct_1(sK4)
% 3.96/1.09      | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
% 3.96/1.09      inference(unflattening,[status(thm)],[c_304]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_29,negated_conjecture,
% 3.96/1.09      ( v1_relat_1(sK4) ),
% 3.96/1.09      inference(cnf_transformation,[],[f56]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_28,negated_conjecture,
% 3.96/1.09      ( v1_funct_1(sK4) ),
% 3.96/1.09      inference(cnf_transformation,[],[f57]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_54,plain,
% 3.96/1.09      ( ~ v2_funct_1(sK4)
% 3.96/1.09      | ~ v1_relat_1(sK4)
% 3.96/1.09      | ~ v1_funct_1(sK4)
% 3.96/1.09      | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
% 3.96/1.09      inference(instantiation,[status(thm)],[c_15]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_307,plain,
% 3.96/1.09      ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
% 3.96/1.09      inference(global_propositional_subsumption,
% 3.96/1.09                [status(thm)],
% 3.96/1.09                [c_305,c_29,c_28,c_25,c_54]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_1164,plain,
% 3.96/1.09      ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
% 3.96/1.09      inference(subtyping,[status(esa)],[c_307]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_19,plain,
% 3.96/1.09      ( r2_hidden(sK3(X0,X1),k1_relat_1(X0))
% 3.96/1.09      | ~ v1_relat_1(X0)
% 3.96/1.09      | ~ v1_relat_1(X1)
% 3.96/1.09      | ~ v1_funct_1(X0)
% 3.96/1.09      | ~ v1_funct_1(X1)
% 3.96/1.09      | X1 = X0
% 3.96/1.09      | k1_relat_1(X1) != k1_relat_1(X0) ),
% 3.96/1.09      inference(cnf_transformation,[],[f54]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_1174,plain,
% 3.96/1.09      ( r2_hidden(sK3(X0_44,X1_44),k1_relat_1(X0_44))
% 3.96/1.09      | ~ v1_relat_1(X0_44)
% 3.96/1.09      | ~ v1_relat_1(X1_44)
% 3.96/1.09      | ~ v1_funct_1(X0_44)
% 3.96/1.09      | ~ v1_funct_1(X1_44)
% 3.96/1.09      | k1_relat_1(X1_44) != k1_relat_1(X0_44)
% 3.96/1.09      | X1_44 = X0_44 ),
% 3.96/1.09      inference(subtyping,[status(esa)],[c_19]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_1669,plain,
% 3.96/1.09      ( k1_relat_1(X0_44) != k1_relat_1(X1_44)
% 3.96/1.09      | X0_44 = X1_44
% 3.96/1.09      | r2_hidden(sK3(X1_44,X0_44),k1_relat_1(X1_44)) = iProver_top
% 3.96/1.09      | v1_relat_1(X0_44) != iProver_top
% 3.96/1.09      | v1_relat_1(X1_44) != iProver_top
% 3.96/1.09      | v1_funct_1(X0_44) != iProver_top
% 3.96/1.09      | v1_funct_1(X1_44) != iProver_top ),
% 3.96/1.09      inference(predicate_to_equality,[status(thm)],[c_1174]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_2216,plain,
% 3.96/1.09      ( k1_relat_1(X0_44) != k2_relat_1(sK4)
% 3.96/1.09      | k2_funct_1(sK4) = X0_44
% 3.96/1.09      | r2_hidden(sK3(X0_44,k2_funct_1(sK4)),k1_relat_1(X0_44)) = iProver_top
% 3.96/1.09      | v1_relat_1(X0_44) != iProver_top
% 3.96/1.09      | v1_relat_1(k2_funct_1(sK4)) != iProver_top
% 3.96/1.09      | v1_funct_1(X0_44) != iProver_top
% 3.96/1.09      | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
% 3.96/1.09      inference(superposition,[status(thm)],[c_1164,c_1669]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_30,plain,
% 3.96/1.09      ( v1_relat_1(sK4) = iProver_top ),
% 3.96/1.09      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_31,plain,
% 3.96/1.09      ( v1_funct_1(sK4) = iProver_top ),
% 3.96/1.09      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_1,plain,
% 3.96/1.09      ( ~ v1_relat_1(X0)
% 3.96/1.09      | v1_relat_1(k2_funct_1(X0))
% 3.96/1.09      | ~ v1_funct_1(X0) ),
% 3.96/1.09      inference(cnf_transformation,[],[f36]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_93,plain,
% 3.96/1.09      ( v1_relat_1(X0) != iProver_top
% 3.96/1.09      | v1_relat_1(k2_funct_1(X0)) = iProver_top
% 3.96/1.09      | v1_funct_1(X0) != iProver_top ),
% 3.96/1.09      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_95,plain,
% 3.96/1.09      ( v1_relat_1(k2_funct_1(sK4)) = iProver_top
% 3.96/1.09      | v1_relat_1(sK4) != iProver_top
% 3.96/1.09      | v1_funct_1(sK4) != iProver_top ),
% 3.96/1.09      inference(instantiation,[status(thm)],[c_93]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_0,plain,
% 3.96/1.09      ( ~ v1_relat_1(X0)
% 3.96/1.09      | ~ v1_funct_1(X0)
% 3.96/1.09      | v1_funct_1(k2_funct_1(X0)) ),
% 3.96/1.09      inference(cnf_transformation,[],[f37]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_96,plain,
% 3.96/1.09      ( v1_relat_1(X0) != iProver_top
% 3.96/1.09      | v1_funct_1(X0) != iProver_top
% 3.96/1.09      | v1_funct_1(k2_funct_1(X0)) = iProver_top ),
% 3.96/1.09      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_98,plain,
% 3.96/1.09      ( v1_relat_1(sK4) != iProver_top
% 3.96/1.09      | v1_funct_1(k2_funct_1(sK4)) = iProver_top
% 3.96/1.09      | v1_funct_1(sK4) != iProver_top ),
% 3.96/1.09      inference(instantiation,[status(thm)],[c_96]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_3549,plain,
% 3.96/1.09      ( v1_funct_1(X0_44) != iProver_top
% 3.96/1.09      | k1_relat_1(X0_44) != k2_relat_1(sK4)
% 3.96/1.09      | k2_funct_1(sK4) = X0_44
% 3.96/1.09      | r2_hidden(sK3(X0_44,k2_funct_1(sK4)),k1_relat_1(X0_44)) = iProver_top
% 3.96/1.09      | v1_relat_1(X0_44) != iProver_top ),
% 3.96/1.09      inference(global_propositional_subsumption,
% 3.96/1.09                [status(thm)],
% 3.96/1.09                [c_2216,c_30,c_31,c_95,c_98]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_3550,plain,
% 3.96/1.09      ( k1_relat_1(X0_44) != k2_relat_1(sK4)
% 3.96/1.09      | k2_funct_1(sK4) = X0_44
% 3.96/1.09      | r2_hidden(sK3(X0_44,k2_funct_1(sK4)),k1_relat_1(X0_44)) = iProver_top
% 3.96/1.09      | v1_relat_1(X0_44) != iProver_top
% 3.96/1.09      | v1_funct_1(X0_44) != iProver_top ),
% 3.96/1.09      inference(renaming,[status(thm)],[c_3549]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_3556,plain,
% 3.96/1.09      ( k1_relat_1(X0_44) != k1_relat_1(sK5)
% 3.96/1.09      | k2_funct_1(sK4) = X0_44
% 3.96/1.09      | r2_hidden(sK3(X0_44,k2_funct_1(sK4)),k1_relat_1(X0_44)) = iProver_top
% 3.96/1.09      | v1_relat_1(X0_44) != iProver_top
% 3.96/1.09      | v1_funct_1(X0_44) != iProver_top ),
% 3.96/1.09      inference(superposition,[status(thm)],[c_1170,c_3550]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_3626,plain,
% 3.96/1.09      ( k2_funct_1(sK4) = sK5
% 3.96/1.09      | r2_hidden(sK3(sK5,k2_funct_1(sK4)),k1_relat_1(sK5)) = iProver_top
% 3.96/1.09      | v1_relat_1(sK5) != iProver_top
% 3.96/1.09      | v1_funct_1(sK5) != iProver_top ),
% 3.96/1.09      inference(equality_resolution,[status(thm)],[c_3556]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_27,negated_conjecture,
% 3.96/1.09      ( v1_relat_1(sK5) ),
% 3.96/1.09      inference(cnf_transformation,[],[f58]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_32,plain,
% 3.96/1.09      ( v1_relat_1(sK5) = iProver_top ),
% 3.96/1.09      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_26,negated_conjecture,
% 3.96/1.09      ( v1_funct_1(sK5) ),
% 3.96/1.09      inference(cnf_transformation,[],[f59]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_33,plain,
% 3.96/1.09      ( v1_funct_1(sK5) = iProver_top ),
% 3.96/1.09      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_20,negated_conjecture,
% 3.96/1.09      ( k2_funct_1(sK4) != sK5 ),
% 3.96/1.09      inference(cnf_transformation,[],[f65]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_1173,negated_conjecture,
% 3.96/1.09      ( k2_funct_1(sK4) != sK5 ),
% 3.96/1.09      inference(subtyping,[status(esa)],[c_20]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_1805,plain,
% 3.96/1.09      ( r2_hidden(sK3(sK5,k2_funct_1(sK4)),k1_relat_1(sK5))
% 3.96/1.09      | ~ v1_relat_1(k2_funct_1(sK4))
% 3.96/1.09      | ~ v1_relat_1(sK5)
% 3.96/1.09      | ~ v1_funct_1(k2_funct_1(sK4))
% 3.96/1.09      | ~ v1_funct_1(sK5)
% 3.96/1.09      | k1_relat_1(k2_funct_1(sK4)) != k1_relat_1(sK5)
% 3.96/1.09      | k2_funct_1(sK4) = sK5 ),
% 3.96/1.09      inference(instantiation,[status(thm)],[c_1174]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_1806,plain,
% 3.96/1.09      ( k1_relat_1(k2_funct_1(sK4)) != k1_relat_1(sK5)
% 3.96/1.09      | k2_funct_1(sK4) = sK5
% 3.96/1.09      | r2_hidden(sK3(sK5,k2_funct_1(sK4)),k1_relat_1(sK5)) = iProver_top
% 3.96/1.09      | v1_relat_1(k2_funct_1(sK4)) != iProver_top
% 3.96/1.09      | v1_relat_1(sK5) != iProver_top
% 3.96/1.09      | v1_funct_1(k2_funct_1(sK4)) != iProver_top
% 3.96/1.09      | v1_funct_1(sK5) != iProver_top ),
% 3.96/1.09      inference(predicate_to_equality,[status(thm)],[c_1805]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_1189,plain,
% 3.96/1.09      ( X0_45 != X1_45 | X2_45 != X1_45 | X2_45 = X0_45 ),
% 3.96/1.09      theory(equality) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_1821,plain,
% 3.96/1.09      ( k1_relat_1(k2_funct_1(sK4)) != X0_45
% 3.96/1.09      | k1_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK5)
% 3.96/1.09      | k1_relat_1(sK5) != X0_45 ),
% 3.96/1.09      inference(instantiation,[status(thm)],[c_1189]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_1852,plain,
% 3.96/1.09      ( k1_relat_1(k2_funct_1(sK4)) != k2_relat_1(sK4)
% 3.96/1.09      | k1_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK5)
% 3.96/1.09      | k1_relat_1(sK5) != k2_relat_1(sK4) ),
% 3.96/1.09      inference(instantiation,[status(thm)],[c_1821]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_3727,plain,
% 3.96/1.09      ( r2_hidden(sK3(sK5,k2_funct_1(sK4)),k1_relat_1(sK5)) = iProver_top ),
% 3.96/1.09      inference(global_propositional_subsumption,
% 3.96/1.09                [status(thm)],
% 3.96/1.09                [c_3626,c_30,c_31,c_32,c_33,c_95,c_98,c_1173,c_1170,
% 3.96/1.09                 c_1164,c_1806,c_1852]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_17,plain,
% 3.96/1.09      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 3.96/1.09      | ~ v2_funct_1(X1)
% 3.96/1.09      | ~ v1_relat_1(X1)
% 3.96/1.09      | ~ v1_funct_1(X1)
% 3.96/1.09      | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 ),
% 3.96/1.09      inference(cnf_transformation,[],[f52]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_407,plain,
% 3.96/1.09      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 3.96/1.09      | ~ v1_relat_1(X1)
% 3.96/1.09      | ~ v1_funct_1(X1)
% 3.96/1.09      | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0
% 3.96/1.09      | sK4 != X1 ),
% 3.96/1.09      inference(resolution_lifted,[status(thm)],[c_17,c_25]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_408,plain,
% 3.96/1.09      ( ~ r2_hidden(X0,k2_relat_1(sK4))
% 3.96/1.09      | ~ v1_relat_1(sK4)
% 3.96/1.09      | ~ v1_funct_1(sK4)
% 3.96/1.09      | k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),X0)) = X0 ),
% 3.96/1.09      inference(unflattening,[status(thm)],[c_407]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_412,plain,
% 3.96/1.09      ( ~ r2_hidden(X0,k2_relat_1(sK4))
% 3.96/1.09      | k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),X0)) = X0 ),
% 3.96/1.09      inference(global_propositional_subsumption,
% 3.96/1.09                [status(thm)],
% 3.96/1.09                [c_408,c_29,c_28]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_1159,plain,
% 3.96/1.09      ( ~ r2_hidden(X0_43,k2_relat_1(sK4))
% 3.96/1.09      | k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),X0_43)) = X0_43 ),
% 3.96/1.09      inference(subtyping,[status(esa)],[c_412]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_1679,plain,
% 3.96/1.09      ( k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),X0_43)) = X0_43
% 3.96/1.09      | r2_hidden(X0_43,k2_relat_1(sK4)) != iProver_top ),
% 3.96/1.09      inference(predicate_to_equality,[status(thm)],[c_1159]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_3311,plain,
% 3.96/1.09      ( k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),X0_43)) = X0_43
% 3.96/1.09      | r2_hidden(X0_43,k1_relat_1(sK5)) != iProver_top ),
% 3.96/1.09      inference(superposition,[status(thm)],[c_1170,c_1679]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_3732,plain,
% 3.96/1.09      ( k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),sK3(sK5,k2_funct_1(sK4)))) = sK3(sK5,k2_funct_1(sK4)) ),
% 3.96/1.09      inference(superposition,[status(thm)],[c_3727,c_3311]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_2,plain,
% 3.96/1.09      ( sP0(k1_funct_1(X0,X1),X1,X0,X2)
% 3.96/1.09      | ~ r2_hidden(X1,k1_relat_1(X0)) ),
% 3.96/1.09      inference(cnf_transformation,[],[f66]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_1180,plain,
% 3.96/1.09      ( sP0(k1_funct_1(X0_44,X0_43),X0_43,X0_44,X1_44)
% 3.96/1.09      | ~ r2_hidden(X0_43,k1_relat_1(X0_44)) ),
% 3.96/1.09      inference(subtyping,[status(esa)],[c_2]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_1663,plain,
% 3.96/1.09      ( sP0(k1_funct_1(X0_44,X0_43),X0_43,X0_44,X1_44) = iProver_top
% 3.96/1.09      | r2_hidden(X0_43,k1_relat_1(X0_44)) != iProver_top ),
% 3.96/1.09      inference(predicate_to_equality,[status(thm)],[c_1180]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_3923,plain,
% 3.96/1.09      ( sP0(sK3(sK5,k2_funct_1(sK4)),k1_funct_1(k2_funct_1(sK4),sK3(sK5,k2_funct_1(sK4))),sK4,X0_44) = iProver_top
% 3.96/1.09      | r2_hidden(k1_funct_1(k2_funct_1(sK4),sK3(sK5,k2_funct_1(sK4))),k1_relat_1(sK4)) != iProver_top ),
% 3.96/1.09      inference(superposition,[status(thm)],[c_3732,c_1663]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_1197,plain,
% 3.96/1.09      ( k2_relat_1(X0_44) = k2_relat_1(X1_44) | X0_44 != X1_44 ),
% 3.96/1.09      theory(equality) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_1208,plain,
% 3.96/1.09      ( k2_relat_1(sK4) = k2_relat_1(sK4) | sK4 != sK4 ),
% 3.96/1.09      inference(instantiation,[status(thm)],[c_1197]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_1185,plain,( X0_44 = X0_44 ),theory(equality) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_1214,plain,
% 3.96/1.09      ( sK4 = sK4 ),
% 3.96/1.09      inference(instantiation,[status(thm)],[c_1185]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_1783,plain,
% 3.96/1.09      ( k2_relat_1(sK4) != X0_45
% 3.96/1.09      | k2_relat_1(sK4) = k1_relat_1(X0_44)
% 3.96/1.09      | k1_relat_1(X0_44) != X0_45 ),
% 3.96/1.09      inference(instantiation,[status(thm)],[c_1189]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_1836,plain,
% 3.96/1.09      ( k2_relat_1(sK4) != k2_relat_1(sK4)
% 3.96/1.09      | k2_relat_1(sK4) = k1_relat_1(X0_44)
% 3.96/1.09      | k1_relat_1(X0_44) != k2_relat_1(sK4) ),
% 3.96/1.09      inference(instantiation,[status(thm)],[c_1783]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_1873,plain,
% 3.96/1.09      ( k2_relat_1(sK4) != k2_relat_1(sK4)
% 3.96/1.09      | k2_relat_1(sK4) = k1_relat_1(sK5)
% 3.96/1.09      | k1_relat_1(sK5) != k2_relat_1(sK4) ),
% 3.96/1.09      inference(instantiation,[status(thm)],[c_1836]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_1184,plain,( X0_43 = X0_43 ),theory(equality) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_1986,plain,
% 3.96/1.09      ( sK3(sK5,k2_funct_1(sK4)) = sK3(sK5,k2_funct_1(sK4)) ),
% 3.96/1.09      inference(instantiation,[status(thm)],[c_1184]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_1196,plain,
% 3.96/1.09      ( ~ r2_hidden(X0_43,X0_45)
% 3.96/1.09      | r2_hidden(X1_43,X1_45)
% 3.96/1.09      | X1_45 != X0_45
% 3.96/1.09      | X1_43 != X0_43 ),
% 3.96/1.09      theory(equality) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_1816,plain,
% 3.96/1.09      ( r2_hidden(X0_43,X0_45)
% 3.96/1.09      | ~ r2_hidden(sK3(sK5,k2_funct_1(sK4)),k1_relat_1(sK5))
% 3.96/1.09      | X0_45 != k1_relat_1(sK5)
% 3.96/1.09      | X0_43 != sK3(sK5,k2_funct_1(sK4)) ),
% 3.96/1.09      inference(instantiation,[status(thm)],[c_1196]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_1985,plain,
% 3.96/1.09      ( r2_hidden(sK3(sK5,k2_funct_1(sK4)),X0_45)
% 3.96/1.09      | ~ r2_hidden(sK3(sK5,k2_funct_1(sK4)),k1_relat_1(sK5))
% 3.96/1.09      | X0_45 != k1_relat_1(sK5)
% 3.96/1.09      | sK3(sK5,k2_funct_1(sK4)) != sK3(sK5,k2_funct_1(sK4)) ),
% 3.96/1.09      inference(instantiation,[status(thm)],[c_1816]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_2103,plain,
% 3.96/1.09      ( r2_hidden(sK3(sK5,k2_funct_1(sK4)),k2_relat_1(sK4))
% 3.96/1.09      | ~ r2_hidden(sK3(sK5,k2_funct_1(sK4)),k1_relat_1(sK5))
% 3.96/1.09      | k2_relat_1(sK4) != k1_relat_1(sK5)
% 3.96/1.09      | sK3(sK5,k2_funct_1(sK4)) != sK3(sK5,k2_funct_1(sK4)) ),
% 3.96/1.09      inference(instantiation,[status(thm)],[c_1985]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_2104,plain,
% 3.96/1.09      ( k2_relat_1(sK4) != k1_relat_1(sK5)
% 3.96/1.09      | sK3(sK5,k2_funct_1(sK4)) != sK3(sK5,k2_funct_1(sK4))
% 3.96/1.09      | r2_hidden(sK3(sK5,k2_funct_1(sK4)),k2_relat_1(sK4)) = iProver_top
% 3.96/1.09      | r2_hidden(sK3(sK5,k2_funct_1(sK4)),k1_relat_1(sK5)) != iProver_top ),
% 3.96/1.09      inference(predicate_to_equality,[status(thm)],[c_2103]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_6,plain,
% 3.96/1.09      ( ~ sP0(X0,k1_funct_1(X1,X0),X2,X1)
% 3.96/1.09      | ~ r2_hidden(X0,k2_relat_1(X2))
% 3.96/1.09      | r2_hidden(k1_funct_1(X1,X0),k1_relat_1(X2)) ),
% 3.96/1.09      inference(cnf_transformation,[],[f68]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_1176,plain,
% 3.96/1.09      ( ~ sP0(X0_43,k1_funct_1(X0_44,X0_43),X1_44,X0_44)
% 3.96/1.09      | ~ r2_hidden(X0_43,k2_relat_1(X1_44))
% 3.96/1.09      | r2_hidden(k1_funct_1(X0_44,X0_43),k1_relat_1(X1_44)) ),
% 3.96/1.09      inference(subtyping,[status(esa)],[c_6]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_2301,plain,
% 3.96/1.09      ( ~ sP0(sK3(sK5,k2_funct_1(sK4)),k1_funct_1(X0_44,sK3(sK5,k2_funct_1(sK4))),sK4,X0_44)
% 3.96/1.09      | ~ r2_hidden(sK3(sK5,k2_funct_1(sK4)),k2_relat_1(sK4))
% 3.96/1.09      | r2_hidden(k1_funct_1(X0_44,sK3(sK5,k2_funct_1(sK4))),k1_relat_1(sK4)) ),
% 3.96/1.09      inference(instantiation,[status(thm)],[c_1176]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_3250,plain,
% 3.96/1.09      ( ~ sP0(sK3(sK5,k2_funct_1(sK4)),k1_funct_1(k2_funct_1(sK4),sK3(sK5,k2_funct_1(sK4))),sK4,k2_funct_1(sK4))
% 3.96/1.09      | ~ r2_hidden(sK3(sK5,k2_funct_1(sK4)),k2_relat_1(sK4))
% 3.96/1.09      | r2_hidden(k1_funct_1(k2_funct_1(sK4),sK3(sK5,k2_funct_1(sK4))),k1_relat_1(sK4)) ),
% 3.96/1.09      inference(instantiation,[status(thm)],[c_2301]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_3252,plain,
% 3.96/1.09      ( sP0(sK3(sK5,k2_funct_1(sK4)),k1_funct_1(k2_funct_1(sK4),sK3(sK5,k2_funct_1(sK4))),sK4,k2_funct_1(sK4)) != iProver_top
% 3.96/1.09      | r2_hidden(sK3(sK5,k2_funct_1(sK4)),k2_relat_1(sK4)) != iProver_top
% 3.96/1.09      | r2_hidden(k1_funct_1(k2_funct_1(sK4),sK3(sK5,k2_funct_1(sK4))),k1_relat_1(sK4)) = iProver_top ),
% 3.96/1.09      inference(predicate_to_equality,[status(thm)],[c_3250]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_12,plain,
% 3.96/1.09      ( sP0(X0,X1,X2,k2_funct_1(X2))
% 3.96/1.09      | ~ v2_funct_1(X2)
% 3.96/1.09      | ~ v1_relat_1(X2)
% 3.96/1.09      | ~ v1_relat_1(k2_funct_1(X2))
% 3.96/1.09      | ~ v1_funct_1(X2)
% 3.96/1.09      | ~ v1_funct_1(k2_funct_1(X2)) ),
% 3.96/1.09      inference(cnf_transformation,[],[f73]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_479,plain,
% 3.96/1.09      ( sP0(X0,X1,X2,k2_funct_1(X2))
% 3.96/1.09      | ~ v1_relat_1(X2)
% 3.96/1.09      | ~ v1_relat_1(k2_funct_1(X2))
% 3.96/1.09      | ~ v1_funct_1(X2)
% 3.96/1.09      | ~ v1_funct_1(k2_funct_1(X2))
% 3.96/1.09      | sK4 != X2 ),
% 3.96/1.09      inference(resolution_lifted,[status(thm)],[c_12,c_25]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_480,plain,
% 3.96/1.09      ( sP0(X0,X1,sK4,k2_funct_1(sK4))
% 3.96/1.09      | ~ v1_relat_1(k2_funct_1(sK4))
% 3.96/1.09      | ~ v1_relat_1(sK4)
% 3.96/1.09      | ~ v1_funct_1(k2_funct_1(sK4))
% 3.96/1.09      | ~ v1_funct_1(sK4) ),
% 3.96/1.09      inference(unflattening,[status(thm)],[c_479]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_94,plain,
% 3.96/1.09      ( v1_relat_1(k2_funct_1(sK4))
% 3.96/1.09      | ~ v1_relat_1(sK4)
% 3.96/1.09      | ~ v1_funct_1(sK4) ),
% 3.96/1.09      inference(instantiation,[status(thm)],[c_1]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_97,plain,
% 3.96/1.09      ( ~ v1_relat_1(sK4)
% 3.96/1.09      | v1_funct_1(k2_funct_1(sK4))
% 3.96/1.09      | ~ v1_funct_1(sK4) ),
% 3.96/1.09      inference(instantiation,[status(thm)],[c_0]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_484,plain,
% 3.96/1.09      ( sP0(X0,X1,sK4,k2_funct_1(sK4)) ),
% 3.96/1.09      inference(global_propositional_subsumption,
% 3.96/1.09                [status(thm)],
% 3.96/1.09                [c_480,c_29,c_28,c_94,c_97]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_1155,plain,
% 3.96/1.09      ( sP0(X0_43,X1_43,sK4,k2_funct_1(sK4)) ),
% 3.96/1.09      inference(subtyping,[status(esa)],[c_484]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_3251,plain,
% 3.96/1.09      ( sP0(sK3(sK5,k2_funct_1(sK4)),k1_funct_1(k2_funct_1(sK4),sK3(sK5,k2_funct_1(sK4))),sK4,k2_funct_1(sK4)) ),
% 3.96/1.09      inference(instantiation,[status(thm)],[c_1155]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_3254,plain,
% 3.96/1.09      ( sP0(sK3(sK5,k2_funct_1(sK4)),k1_funct_1(k2_funct_1(sK4),sK3(sK5,k2_funct_1(sK4))),sK4,k2_funct_1(sK4)) = iProver_top ),
% 3.96/1.09      inference(predicate_to_equality,[status(thm)],[c_3251]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_4261,plain,
% 3.96/1.09      ( sP0(sK3(sK5,k2_funct_1(sK4)),k1_funct_1(k2_funct_1(sK4),sK3(sK5,k2_funct_1(sK4))),sK4,X0_44) = iProver_top ),
% 3.96/1.09      inference(global_propositional_subsumption,
% 3.96/1.09                [status(thm)],
% 3.96/1.09                [c_3923,c_30,c_31,c_32,c_33,c_95,c_98,c_1208,c_1214,
% 3.96/1.09                 c_1173,c_1170,c_1164,c_1806,c_1852,c_1873,c_1986,c_2104,
% 3.96/1.09                 c_3252,c_3254]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_1667,plain,
% 3.96/1.09      ( sP0(X0_43,k1_funct_1(X0_44,X0_43),X1_44,X0_44) != iProver_top
% 3.96/1.09      | r2_hidden(X0_43,k2_relat_1(X1_44)) != iProver_top
% 3.96/1.09      | r2_hidden(k1_funct_1(X0_44,X0_43),k1_relat_1(X1_44)) = iProver_top ),
% 3.96/1.09      inference(predicate_to_equality,[status(thm)],[c_1176]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_4267,plain,
% 3.96/1.09      ( r2_hidden(sK3(sK5,k2_funct_1(sK4)),k2_relat_1(sK4)) != iProver_top
% 3.96/1.09      | r2_hidden(k1_funct_1(k2_funct_1(sK4),sK3(sK5,k2_funct_1(sK4))),k1_relat_1(sK4)) = iProver_top ),
% 3.96/1.09      inference(superposition,[status(thm)],[c_4261,c_1667]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_4271,plain,
% 3.96/1.09      ( r2_hidden(k1_funct_1(k2_funct_1(sK4),sK3(sK5,k2_funct_1(sK4))),k1_relat_1(sK4)) = iProver_top ),
% 3.96/1.09      inference(global_propositional_subsumption,
% 3.96/1.09                [status(thm)],
% 3.96/1.09                [c_4267,c_30,c_31,c_32,c_33,c_95,c_98,c_1208,c_1214,
% 3.96/1.09                 c_1173,c_1170,c_1164,c_1806,c_1852,c_1873,c_1986,c_2104,
% 3.96/1.09                 c_3252,c_3254]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_11,plain,
% 3.96/1.09      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.96/1.09      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 3.96/1.09      | ~ v2_funct_1(X1)
% 3.96/1.09      | ~ v1_relat_1(X1)
% 3.96/1.09      | ~ v1_relat_1(k2_funct_1(X1))
% 3.96/1.09      | ~ v1_funct_1(X1)
% 3.96/1.09      | ~ v1_funct_1(k2_funct_1(X1)) ),
% 3.96/1.09      inference(cnf_transformation,[],[f72]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_443,plain,
% 3.96/1.09      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.96/1.09      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 3.96/1.09      | ~ v1_relat_1(X1)
% 3.96/1.09      | ~ v1_relat_1(k2_funct_1(X1))
% 3.96/1.09      | ~ v1_funct_1(X1)
% 3.96/1.09      | ~ v1_funct_1(k2_funct_1(X1))
% 3.96/1.09      | sK4 != X1 ),
% 3.96/1.09      inference(resolution_lifted,[status(thm)],[c_11,c_25]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_444,plain,
% 3.96/1.09      ( ~ r2_hidden(X0,k1_relat_1(sK4))
% 3.96/1.09      | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4))
% 3.96/1.09      | ~ v1_relat_1(k2_funct_1(sK4))
% 3.96/1.09      | ~ v1_relat_1(sK4)
% 3.96/1.09      | ~ v1_funct_1(k2_funct_1(sK4))
% 3.96/1.09      | ~ v1_funct_1(sK4) ),
% 3.96/1.09      inference(unflattening,[status(thm)],[c_443]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_448,plain,
% 3.96/1.09      ( ~ r2_hidden(X0,k1_relat_1(sK4))
% 3.96/1.09      | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) ),
% 3.96/1.09      inference(global_propositional_subsumption,
% 3.96/1.09                [status(thm)],
% 3.96/1.09                [c_444,c_29,c_28,c_94,c_97]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_1157,plain,
% 3.96/1.09      ( ~ r2_hidden(X0_43,k1_relat_1(sK4))
% 3.96/1.09      | r2_hidden(k1_funct_1(sK4,X0_43),k2_relat_1(sK4)) ),
% 3.96/1.09      inference(subtyping,[status(esa)],[c_448]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_1681,plain,
% 3.96/1.09      ( r2_hidden(X0_43,k1_relat_1(sK4)) != iProver_top
% 3.96/1.09      | r2_hidden(k1_funct_1(sK4,X0_43),k2_relat_1(sK4)) = iProver_top ),
% 3.96/1.09      inference(predicate_to_equality,[status(thm)],[c_1157]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_3830,plain,
% 3.96/1.09      ( r2_hidden(X0_43,k1_relat_1(sK4)) != iProver_top
% 3.96/1.09      | r2_hidden(k1_funct_1(sK4,X0_43),k1_relat_1(sK5)) = iProver_top ),
% 3.96/1.09      inference(superposition,[status(thm)],[c_1170,c_1681]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_22,negated_conjecture,
% 3.96/1.09      ( ~ r2_hidden(X0,k1_relat_1(sK4))
% 3.96/1.09      | ~ r2_hidden(k1_funct_1(sK4,X0),k1_relat_1(sK5))
% 3.96/1.09      | k1_funct_1(sK5,k1_funct_1(sK4,X0)) = X0 ),
% 3.96/1.09      inference(cnf_transformation,[],[f76]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_1171,negated_conjecture,
% 3.96/1.09      ( ~ r2_hidden(X0_43,k1_relat_1(sK4))
% 3.96/1.09      | ~ r2_hidden(k1_funct_1(sK4,X0_43),k1_relat_1(sK5))
% 3.96/1.09      | k1_funct_1(sK5,k1_funct_1(sK4,X0_43)) = X0_43 ),
% 3.96/1.09      inference(subtyping,[status(esa)],[c_22]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_1671,plain,
% 3.96/1.09      ( k1_funct_1(sK5,k1_funct_1(sK4,X0_43)) = X0_43
% 3.96/1.09      | r2_hidden(X0_43,k1_relat_1(sK4)) != iProver_top
% 3.96/1.09      | r2_hidden(k1_funct_1(sK4,X0_43),k1_relat_1(sK5)) != iProver_top ),
% 3.96/1.09      inference(predicate_to_equality,[status(thm)],[c_1171]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_3843,plain,
% 3.96/1.09      ( k1_funct_1(sK5,k1_funct_1(sK4,X0_43)) = X0_43
% 3.96/1.09      | r2_hidden(X0_43,k1_relat_1(sK4)) != iProver_top ),
% 3.96/1.09      inference(superposition,[status(thm)],[c_3830,c_1671]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_4276,plain,
% 3.96/1.09      ( k1_funct_1(sK5,k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),sK3(sK5,k2_funct_1(sK4))))) = k1_funct_1(k2_funct_1(sK4),sK3(sK5,k2_funct_1(sK4))) ),
% 3.96/1.09      inference(superposition,[status(thm)],[c_4271,c_3843]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_6178,plain,
% 3.96/1.09      ( k1_funct_1(k2_funct_1(sK4),sK3(sK5,k2_funct_1(sK4))) = k1_funct_1(sK5,sK3(sK5,k2_funct_1(sK4))) ),
% 3.96/1.09      inference(superposition,[status(thm)],[c_3732,c_4276]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_18,plain,
% 3.96/1.09      ( ~ v1_relat_1(X0)
% 3.96/1.09      | ~ v1_relat_1(X1)
% 3.96/1.09      | ~ v1_funct_1(X0)
% 3.96/1.09      | ~ v1_funct_1(X1)
% 3.96/1.09      | X1 = X0
% 3.96/1.09      | k1_funct_1(X1,sK3(X0,X1)) != k1_funct_1(X0,sK3(X0,X1))
% 3.96/1.09      | k1_relat_1(X1) != k1_relat_1(X0) ),
% 3.96/1.09      inference(cnf_transformation,[],[f55]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_1175,plain,
% 3.96/1.09      ( ~ v1_relat_1(X0_44)
% 3.96/1.09      | ~ v1_relat_1(X1_44)
% 3.96/1.09      | ~ v1_funct_1(X0_44)
% 3.96/1.09      | ~ v1_funct_1(X1_44)
% 3.96/1.09      | k1_relat_1(X1_44) != k1_relat_1(X0_44)
% 3.96/1.09      | X1_44 = X0_44
% 3.96/1.09      | k1_funct_1(X1_44,sK3(X0_44,X1_44)) != k1_funct_1(X0_44,sK3(X0_44,X1_44)) ),
% 3.96/1.09      inference(subtyping,[status(esa)],[c_18]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(c_1808,plain,
% 3.96/1.09      ( ~ v1_relat_1(k2_funct_1(sK4))
% 3.96/1.09      | ~ v1_relat_1(sK5)
% 3.96/1.09      | ~ v1_funct_1(k2_funct_1(sK4))
% 3.96/1.09      | ~ v1_funct_1(sK5)
% 3.96/1.09      | k1_relat_1(k2_funct_1(sK4)) != k1_relat_1(sK5)
% 3.96/1.09      | k2_funct_1(sK4) = sK5
% 3.96/1.09      | k1_funct_1(k2_funct_1(sK4),sK3(sK5,k2_funct_1(sK4))) != k1_funct_1(sK5,sK3(sK5,k2_funct_1(sK4))) ),
% 3.96/1.09      inference(instantiation,[status(thm)],[c_1175]) ).
% 3.96/1.09  
% 3.96/1.09  cnf(contradiction,plain,
% 3.96/1.09      ( $false ),
% 3.96/1.09      inference(minisat,
% 3.96/1.09                [status(thm)],
% 3.96/1.09                [c_6178,c_1852,c_1808,c_1164,c_1170,c_1173,c_97,c_94,
% 3.96/1.09                 c_26,c_27,c_28,c_29]) ).
% 3.96/1.09  
% 3.96/1.09  
% 3.96/1.09  % SZS output end CNFRefutation for theBenchmark.p
% 3.96/1.09  
% 3.96/1.09  ------                               Statistics
% 3.96/1.09  
% 3.96/1.09  ------ Selected
% 3.96/1.09  
% 3.96/1.09  total_time:                             0.192
% 3.96/1.09  
%------------------------------------------------------------------------------
