%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0653+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:49 EST 2020

% Result     : Theorem 27.75s
% Output     : CNFRefutation 27.75s
% Verified   : 
% Statistics : Number of formulae       :  188 (2910 expanded)
%              Number of clauses        :  132 ( 698 expanded)
%              Number of leaves         :   14 ( 745 expanded)
%              Depth                    :   28
%              Number of atoms          :  932 (31957 expanded)
%              Number of equality atoms :  444 (14919 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   28 (   3 average)
%              Maximal term depth       :    5 (   2 average)

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

fof(f19,plain,(
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

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f21,plain,(
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
    inference(rectify,[],[f20])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | k1_funct_1(X3,X0) = X1 ) ),
    inference(cnf_transformation,[],[f21])).

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
                & k2_relat_1(X0) = k1_relat_1(X1) ) ) ) ) ) ),
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
              & k2_relat_1(X0) = k1_relat_1(X1) ) )
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
              & k2_relat_1(X0) = k1_relat_1(X1) ) )
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
              & k2_relat_1(X0) = k1_relat_1(X1) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f8,f11])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k2_funct_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) != X3
                      | ~ r2_hidden(X2,k2_relat_1(X0)) )
                    & k1_funct_1(X0,X3) = X2
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ sP0(X2,X3,X0,X1) )
              | k2_relat_1(X0) != k1_relat_1(X1) )
            & ( ( ! [X2,X3] :
                    ( ( ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) )
                      | k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                    & sP0(X2,X3,X0,X1) )
                & k2_relat_1(X0) = k1_relat_1(X1) )
              | k2_funct_1(X0) != X1 ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k2_funct_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) != X3
                      | ~ r2_hidden(X2,k2_relat_1(X0)) )
                    & k1_funct_1(X0,X3) = X2
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ sP0(X2,X3,X0,X1) )
              | k2_relat_1(X0) != k1_relat_1(X1) )
            & ( ( ! [X2,X3] :
                    ( ( ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) )
                      | k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                    & sP0(X2,X3,X0,X1) )
                & k2_relat_1(X0) = k1_relat_1(X1) )
              | k2_funct_1(X0) != X1 ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k2_funct_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) != X3
                      | ~ r2_hidden(X2,k2_relat_1(X0)) )
                    & k1_funct_1(X0,X3) = X2
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ sP0(X2,X3,X0,X1) )
              | k2_relat_1(X0) != k1_relat_1(X1) )
            & ( ( ! [X4,X5] :
                    ( ( ( k1_funct_1(X1,X4) = X5
                        & r2_hidden(X4,k2_relat_1(X0)) )
                      | k1_funct_1(X0,X5) != X4
                      | ~ r2_hidden(X5,k1_relat_1(X0)) )
                    & sP0(X4,X5,X0,X1) )
                & k2_relat_1(X0) = k1_relat_1(X1) )
              | k2_funct_1(X0) != X1 ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ( k1_funct_1(X1,X2) != X3
              | ~ r2_hidden(X2,k2_relat_1(X0)) )
            & k1_funct_1(X0,X3) = X2
            & r2_hidden(X3,k1_relat_1(X0)) )
          | ~ sP0(X2,X3,X0,X1) )
     => ( ( ( k1_funct_1(X1,sK4(X0,X1)) != sK5(X0,X1)
            | ~ r2_hidden(sK4(X0,X1),k2_relat_1(X0)) )
          & k1_funct_1(X0,sK5(X0,X1)) = sK4(X0,X1)
          & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) )
        | ~ sP0(sK4(X0,X1),sK5(X0,X1),X0,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k2_funct_1(X0) = X1
              | ( ( k1_funct_1(X1,sK4(X0,X1)) != sK5(X0,X1)
                  | ~ r2_hidden(sK4(X0,X1),k2_relat_1(X0)) )
                & k1_funct_1(X0,sK5(X0,X1)) = sK4(X0,X1)
                & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) )
              | ~ sP0(sK4(X0,X1),sK5(X0,X1),X0,X1)
              | k2_relat_1(X0) != k1_relat_1(X1) )
            & ( ( ! [X4,X5] :
                    ( ( ( k1_funct_1(X1,X4) = X5
                        & r2_hidden(X4,k2_relat_1(X0)) )
                      | k1_funct_1(X0,X5) != X4
                      | ~ r2_hidden(X5,k1_relat_1(X0)) )
                    & sP0(X4,X5,X0,X1) )
                & k2_relat_1(X0) = k1_relat_1(X1) )
              | k2_funct_1(X0) != X1 ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f24,f25])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | r2_hidden(sK5(X0,X1),k1_relat_1(X0))
      | ~ sP0(sK4(X0,X1),sK5(X0,X1),X0,X1)
      | k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

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
              & k2_relat_1(X0) = k1_relat_1(X1)
              & k2_relat_1(X1) = k1_relat_1(X0)
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
                & k2_relat_1(X0) = k1_relat_1(X1)
                & k2_relat_1(X1) = k1_relat_1(X0)
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
          & k2_relat_1(X0) = k1_relat_1(X1)
          & k2_relat_1(X1) = k1_relat_1(X0)
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
          & k2_relat_1(X0) = k1_relat_1(X1)
          & k2_relat_1(X1) = k1_relat_1(X0)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f27,plain,(
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
          & k2_relat_1(X0) = k1_relat_1(X1)
          & k2_relat_1(X1) = k1_relat_1(X0)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f29,plain,(
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
          & k2_relat_1(X0) = k1_relat_1(X1)
          & k2_relat_1(X1) = k1_relat_1(X0)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( k2_funct_1(X0) != sK7
        & ! [X3,X2] :
            ( ( ( k1_funct_1(X0,X2) = X3
                | k1_funct_1(sK7,X3) != X2 )
              & ( k1_funct_1(sK7,X3) = X2
                | k1_funct_1(X0,X2) != X3 ) )
            | ~ r2_hidden(X3,k1_relat_1(sK7))
            | ~ r2_hidden(X2,k1_relat_1(X0)) )
        & k2_relat_1(X0) = k1_relat_1(sK7)
        & k2_relat_1(sK7) = k1_relat_1(X0)
        & v2_funct_1(X0)
        & v1_funct_1(sK7)
        & v1_relat_1(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
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
            & k2_relat_1(X0) = k1_relat_1(X1)
            & k2_relat_1(X1) = k1_relat_1(X0)
            & v2_funct_1(X0)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k2_funct_1(sK6) != X1
          & ! [X3,X2] :
              ( ( ( k1_funct_1(sK6,X2) = X3
                  | k1_funct_1(X1,X3) != X2 )
                & ( k1_funct_1(X1,X3) = X2
                  | k1_funct_1(sK6,X2) != X3 ) )
              | ~ r2_hidden(X3,k1_relat_1(X1))
              | ~ r2_hidden(X2,k1_relat_1(sK6)) )
          & k2_relat_1(sK6) = k1_relat_1(X1)
          & k2_relat_1(X1) = k1_relat_1(sK6)
          & v2_funct_1(sK6)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK6)
      & v1_relat_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( k2_funct_1(sK6) != sK7
    & ! [X2,X3] :
        ( ( ( k1_funct_1(sK6,X2) = X3
            | k1_funct_1(sK7,X3) != X2 )
          & ( k1_funct_1(sK7,X3) = X2
            | k1_funct_1(sK6,X2) != X3 ) )
        | ~ r2_hidden(X3,k1_relat_1(sK7))
        | ~ r2_hidden(X2,k1_relat_1(sK6)) )
    & k2_relat_1(sK6) = k1_relat_1(sK7)
    & k2_relat_1(sK7) = k1_relat_1(sK6)
    & v2_funct_1(sK6)
    & v1_funct_1(sK7)
    & v1_relat_1(sK7)
    & v1_funct_1(sK6)
    & v1_relat_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f27,f29,f28])).

fof(f53,plain,(
    v2_funct_1(sK6) ),
    inference(cnf_transformation,[],[f30])).

fof(f49,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f30])).

fof(f50,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f30])).

fof(f52,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f30])).

fof(f51,plain,(
    v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f30])).

fof(f58,plain,(
    k2_funct_1(sK6) != sK7 ),
    inference(cnf_transformation,[],[f30])).

fof(f55,plain,(
    k2_relat_1(sK6) = k1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f30])).

fof(f54,plain,(
    k2_relat_1(sK7) = k1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f30])).

fof(f56,plain,(
    ! [X2,X3] :
      ( k1_funct_1(sK7,X3) = X2
      | k1_funct_1(sK6,X2) != X3
      | ~ r2_hidden(X3,k1_relat_1(sK7))
      | ~ r2_hidden(X2,k1_relat_1(sK6)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f73,plain,(
    ! [X2] :
      ( k1_funct_1(sK7,k1_funct_1(sK6,X2)) = X2
      | ~ r2_hidden(k1_funct_1(sK6,X2),k1_relat_1(sK7))
      | ~ r2_hidden(X2,k1_relat_1(sK6)) ) ),
    inference(equality_resolution,[],[f56])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f6,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f5])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X2
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ? [X7] :
                      ( k1_funct_1(X0,X7) = X5
                      & r2_hidden(X7,k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f13])).

fof(f17,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X5)) = X5
        & r2_hidden(sK3(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1)) = X2
        & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( k1_funct_1(X0,X4) = X2
                & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( k1_funct_1(X0,X3) != sK1(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK1(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK1(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK1(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1)
                  & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK1(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK3(X0,X5)) = X5
                    & r2_hidden(sK3(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f14,f17,f16,f15])).

fof(f33,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f59,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f60,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f59])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k1_funct_1(X0,sK5(X0,X1)) = sK4(X0,X1)
      | ~ sP0(sK4(X0,X1),sK5(X0,X1),X0,X1)
      | k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | r2_hidden(X0,k2_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f31,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK3(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f62,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK3(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f31])).

fof(f32,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK3(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f61,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK3(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f32])).

fof(f57,plain,(
    ! [X2,X3] :
      ( k1_funct_1(sK6,X2) = X3
      | k1_funct_1(sK7,X3) != X2
      | ~ r2_hidden(X3,k1_relat_1(sK7))
      | ~ r2_hidden(X2,k1_relat_1(sK6)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f72,plain,(
    ! [X3] :
      ( k1_funct_1(sK6,k1_funct_1(sK7,X3)) = X3
      | ~ r2_hidden(X3,k1_relat_1(sK7))
      | ~ r2_hidden(k1_funct_1(sK7,X3),k1_relat_1(sK6)) ) ),
    inference(equality_resolution,[],[f57])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | k1_funct_1(X2,X1) != X0
      | ~ r2_hidden(X1,k1_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f63,plain,(
    ! [X2,X3,X1] :
      ( sP0(k1_funct_1(X2,X1),X1,X2,X3)
      | ~ r2_hidden(X1,k1_relat_1(X2)) ) ),
    inference(equality_resolution,[],[f41])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k1_funct_1(X1,sK4(X0,X1)) != sK5(X0,X1)
      | ~ r2_hidden(sK4(X0,X1),k2_relat_1(X0))
      | ~ sP0(sK4(X0,X1),sK5(X0,X1),X0,X1)
      | k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_1315,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1887,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k1_relat_1(sK6))
    | X2 != X0
    | k1_relat_1(sK6) != X1 ),
    inference(instantiation,[status(thm)],[c_1315])).

cnf(c_6059,plain,
    ( r2_hidden(X0,k1_relat_1(sK6))
    | ~ r2_hidden(sK5(sK6,sK7),k2_relat_1(sK7))
    | X0 != sK5(sK6,sK7)
    | k1_relat_1(sK6) != k2_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_1887])).

cnf(c_67223,plain,
    ( r2_hidden(sK5(sK6,sK7),k1_relat_1(sK6))
    | ~ r2_hidden(sK5(sK6,sK7),k2_relat_1(sK7))
    | sK5(sK6,sK7) != sK5(sK6,sK7)
    | k1_relat_1(sK6) != k2_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_6059])).

cnf(c_7,plain,
    ( sP0(X0,X1,X2,X3)
    | k1_funct_1(X3,X0) = X1 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1777,plain,
    ( k1_funct_1(X0,X1) = X2
    | sP0(X1,X2,X3,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_13,plain,
    ( ~ sP0(sK4(X0,X1),sK5(X0,X1),X0,X1)
    | r2_hidden(sK5(X0,X1),k1_relat_1(X0))
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | k2_funct_1(X0) = X1
    | k1_relat_1(X1) != k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_23,negated_conjecture,
    ( v2_funct_1(sK6) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_300,plain,
    ( ~ sP0(sK4(X0,X1),sK5(X0,X1),X0,X1)
    | r2_hidden(sK5(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | k2_funct_1(X0) = X1
    | k1_relat_1(X1) != k2_relat_1(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_23])).

cnf(c_301,plain,
    ( ~ sP0(sK4(sK6,X0),sK5(sK6,X0),sK6,X0)
    | r2_hidden(sK5(sK6,X0),k1_relat_1(sK6))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK6)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK6)
    | k2_funct_1(sK6) = X0
    | k1_relat_1(X0) != k2_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_300])).

cnf(c_27,negated_conjecture,
    ( v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_305,plain,
    ( ~ v1_funct_1(X0)
    | ~ sP0(sK4(sK6,X0),sK5(sK6,X0),sK6,X0)
    | r2_hidden(sK5(sK6,X0),k1_relat_1(sK6))
    | ~ v1_relat_1(X0)
    | k2_funct_1(sK6) = X0
    | k1_relat_1(X0) != k2_relat_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_301,c_27,c_26])).

cnf(c_306,plain,
    ( ~ sP0(sK4(sK6,X0),sK5(sK6,X0),sK6,X0)
    | r2_hidden(sK5(sK6,X0),k1_relat_1(sK6))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_funct_1(sK6) = X0
    | k1_relat_1(X0) != k2_relat_1(sK6) ),
    inference(renaming,[status(thm)],[c_305])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_504,plain,
    ( ~ sP0(sK4(sK6,X0),sK5(sK6,X0),sK6,X0)
    | r2_hidden(sK5(sK6,X0),k1_relat_1(sK6))
    | ~ v1_relat_1(X0)
    | k2_funct_1(sK6) = X0
    | k1_relat_1(X0) != k2_relat_1(sK6)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_306,c_24])).

cnf(c_505,plain,
    ( ~ sP0(sK4(sK6,sK7),sK5(sK6,sK7),sK6,sK7)
    | r2_hidden(sK5(sK6,sK7),k1_relat_1(sK6))
    | ~ v1_relat_1(sK7)
    | k2_funct_1(sK6) = sK7
    | k1_relat_1(sK7) != k2_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_504])).

cnf(c_25,negated_conjecture,
    ( v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_18,negated_conjecture,
    ( k2_funct_1(sK6) != sK7 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_507,plain,
    ( ~ sP0(sK4(sK6,sK7),sK5(sK6,sK7),sK6,sK7)
    | r2_hidden(sK5(sK6,sK7),k1_relat_1(sK6))
    | k1_relat_1(sK7) != k2_relat_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_505,c_25,c_18])).

cnf(c_1769,plain,
    ( k1_relat_1(sK7) != k2_relat_1(sK6)
    | sP0(sK4(sK6,sK7),sK5(sK6,sK7),sK6,sK7) != iProver_top
    | r2_hidden(sK5(sK6,sK7),k1_relat_1(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_507])).

cnf(c_21,negated_conjecture,
    ( k2_relat_1(sK6) = k1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_22,negated_conjecture,
    ( k2_relat_1(sK7) = k1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1788,plain,
    ( k2_relat_1(sK6) != k2_relat_1(sK6)
    | sP0(sK4(sK6,sK7),sK5(sK6,sK7),sK6,sK7) != iProver_top
    | r2_hidden(sK5(sK6,sK7),k2_relat_1(sK7)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1769,c_21,c_22])).

cnf(c_1789,plain,
    ( sP0(sK4(sK6,sK7),sK5(sK6,sK7),sK6,sK7) != iProver_top
    | r2_hidden(sK5(sK6,sK7),k2_relat_1(sK7)) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_1788])).

cnf(c_2914,plain,
    ( k1_funct_1(sK7,sK4(sK6,sK7)) = sK5(sK6,sK7)
    | r2_hidden(sK5(sK6,sK7),k2_relat_1(sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1777,c_1789])).

cnf(c_20,negated_conjecture,
    ( ~ r2_hidden(X0,k1_relat_1(sK6))
    | ~ r2_hidden(k1_funct_1(sK6,X0),k1_relat_1(sK7))
    | k1_funct_1(sK7,k1_funct_1(sK6,X0)) = X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1772,plain,
    ( k1_funct_1(sK7,k1_funct_1(sK6,X0)) = X0
    | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k1_funct_1(sK6,X0),k1_relat_1(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1786,plain,
    ( k1_funct_1(sK7,k1_funct_1(sK6,X0)) = X0
    | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
    | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1772,c_21,c_22])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_782,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_26])).

cnf(c_783,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK6))
    | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6))
    | ~ v1_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_782])).

cnf(c_787,plain,
    ( r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6))
    | ~ r2_hidden(X0,k1_relat_1(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_783,c_27])).

cnf(c_788,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK6))
    | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) ),
    inference(renaming,[status(thm)],[c_787])).

cnf(c_1755,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_788])).

cnf(c_1779,plain,
    ( r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
    | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1755,c_22])).

cnf(c_2227,plain,
    ( r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
    | k1_funct_1(sK7,k1_funct_1(sK6,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1786,c_1779])).

cnf(c_2228,plain,
    ( k1_funct_1(sK7,k1_funct_1(sK6,X0)) = X0
    | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2227])).

cnf(c_3023,plain,
    ( k1_funct_1(sK7,sK4(sK6,sK7)) = sK5(sK6,sK7)
    | k1_funct_1(sK7,k1_funct_1(sK6,sK5(sK6,sK7))) = sK5(sK6,sK7) ),
    inference(superposition,[status(thm)],[c_2914,c_2228])).

cnf(c_12,plain,
    ( ~ sP0(sK4(X0,X1),sK5(X0,X1),X0,X1)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | k1_funct_1(X0,sK5(X0,X1)) = sK4(X0,X1)
    | k2_funct_1(X0) = X1
    | k1_relat_1(X1) != k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_328,plain,
    ( ~ sP0(sK4(X0,X1),sK5(X0,X1),X0,X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | k1_funct_1(X0,sK5(X0,X1)) = sK4(X0,X1)
    | k2_funct_1(X0) = X1
    | k1_relat_1(X1) != k2_relat_1(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_23])).

cnf(c_329,plain,
    ( ~ sP0(sK4(sK6,X0),sK5(sK6,X0),sK6,X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK6)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK6)
    | k1_funct_1(sK6,sK5(sK6,X0)) = sK4(sK6,X0)
    | k2_funct_1(sK6) = X0
    | k1_relat_1(X0) != k2_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_328])).

cnf(c_333,plain,
    ( ~ v1_funct_1(X0)
    | ~ sP0(sK4(sK6,X0),sK5(sK6,X0),sK6,X0)
    | ~ v1_relat_1(X0)
    | k1_funct_1(sK6,sK5(sK6,X0)) = sK4(sK6,X0)
    | k2_funct_1(sK6) = X0
    | k1_relat_1(X0) != k2_relat_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_329,c_27,c_26])).

cnf(c_334,plain,
    ( ~ sP0(sK4(sK6,X0),sK5(sK6,X0),sK6,X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_funct_1(sK6,sK5(sK6,X0)) = sK4(sK6,X0)
    | k2_funct_1(sK6) = X0
    | k1_relat_1(X0) != k2_relat_1(sK6) ),
    inference(renaming,[status(thm)],[c_333])).

cnf(c_487,plain,
    ( ~ sP0(sK4(sK6,X0),sK5(sK6,X0),sK6,X0)
    | ~ v1_relat_1(X0)
    | k1_funct_1(sK6,sK5(sK6,X0)) = sK4(sK6,X0)
    | k2_funct_1(sK6) = X0
    | k1_relat_1(X0) != k2_relat_1(sK6)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_334,c_24])).

cnf(c_488,plain,
    ( ~ sP0(sK4(sK6,sK7),sK5(sK6,sK7),sK6,sK7)
    | ~ v1_relat_1(sK7)
    | k1_funct_1(sK6,sK5(sK6,sK7)) = sK4(sK6,sK7)
    | k2_funct_1(sK6) = sK7
    | k1_relat_1(sK7) != k2_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_487])).

cnf(c_490,plain,
    ( k1_funct_1(sK6,sK5(sK6,sK7)) = sK4(sK6,sK7)
    | ~ sP0(sK4(sK6,sK7),sK5(sK6,sK7),sK6,sK7)
    | k1_relat_1(sK7) != k2_relat_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_488,c_25,c_18])).

cnf(c_491,plain,
    ( ~ sP0(sK4(sK6,sK7),sK5(sK6,sK7),sK6,sK7)
    | k1_funct_1(sK6,sK5(sK6,sK7)) = sK4(sK6,sK7)
    | k1_relat_1(sK7) != k2_relat_1(sK6) ),
    inference(renaming,[status(thm)],[c_490])).

cnf(c_1770,plain,
    ( k1_funct_1(sK6,sK5(sK6,sK7)) = sK4(sK6,sK7)
    | k1_relat_1(sK7) != k2_relat_1(sK6)
    | sP0(sK4(sK6,sK7),sK5(sK6,sK7),sK6,sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_491])).

cnf(c_1790,plain,
    ( k1_funct_1(sK6,sK5(sK6,sK7)) = sK4(sK6,sK7)
    | k2_relat_1(sK6) != k2_relat_1(sK6)
    | sP0(sK4(sK6,sK7),sK5(sK6,sK7),sK6,sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1770,c_21])).

cnf(c_1791,plain,
    ( k1_funct_1(sK6,sK5(sK6,sK7)) = sK4(sK6,sK7)
    | sP0(sK4(sK6,sK7),sK5(sK6,sK7),sK6,sK7) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_1790])).

cnf(c_3079,plain,
    ( k1_funct_1(sK7,sK4(sK6,sK7)) = sK5(sK6,sK7)
    | k1_funct_1(sK6,sK5(sK6,sK7)) = sK4(sK6,sK7) ),
    inference(superposition,[status(thm)],[c_1777,c_1791])).

cnf(c_8,plain,
    ( sP0(X0,X1,X2,X3)
    | r2_hidden(X0,k2_relat_1(X2)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1776,plain,
    ( sP0(X0,X1,X2,X3) = iProver_top
    | r2_hidden(X0,k2_relat_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2913,plain,
    ( r2_hidden(sK5(sK6,sK7),k2_relat_1(sK7)) = iProver_top
    | r2_hidden(sK4(sK6,sK7),k2_relat_1(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1776,c_1789])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK3(X1,X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_668,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK3(X1,X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_24])).

cnf(c_669,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK7))
    | r2_hidden(sK3(sK7,X0),k1_relat_1(sK7))
    | ~ v1_relat_1(sK7) ),
    inference(unflattening,[status(thm)],[c_668])).

cnf(c_673,plain,
    ( r2_hidden(sK3(sK7,X0),k1_relat_1(sK7))
    | ~ r2_hidden(X0,k2_relat_1(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_669,c_25])).

cnf(c_674,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK7))
    | r2_hidden(sK3(sK7,X0),k1_relat_1(sK7)) ),
    inference(renaming,[status(thm)],[c_673])).

cnf(c_1761,plain,
    ( r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
    | r2_hidden(sK3(sK7,X0),k1_relat_1(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_674])).

cnf(c_1782,plain,
    ( r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
    | r2_hidden(sK3(sK7,X0),k2_relat_1(sK6)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1761,c_21])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k1_funct_1(X1,sK3(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_764,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK3(X1,X0)) = X0
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_26])).

cnf(c_765,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK6))
    | ~ v1_relat_1(sK6)
    | k1_funct_1(sK6,sK3(sK6,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_764])).

cnf(c_769,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK6))
    | k1_funct_1(sK6,sK3(sK6,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_765,c_27])).

cnf(c_1756,plain,
    ( k1_funct_1(sK6,sK3(sK6,X0)) = X0
    | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_769])).

cnf(c_2367,plain,
    ( k1_funct_1(sK6,sK3(sK6,sK3(sK7,X0))) = sK3(sK7,X0)
    | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1782,c_1756])).

cnf(c_3005,plain,
    ( k1_funct_1(sK6,sK3(sK6,sK3(sK7,sK5(sK6,sK7)))) = sK3(sK7,sK5(sK6,sK7))
    | r2_hidden(sK4(sK6,sK7),k2_relat_1(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2913,c_2367])).

cnf(c_1159,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK5(sK6,sK7),k1_relat_1(sK6))
    | sK5(sK6,sK7) != X2
    | sK4(sK6,sK7) != X0
    | k1_relat_1(sK7) != k2_relat_1(sK6)
    | sK7 != X3
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_507])).

cnf(c_1160,plain,
    ( r2_hidden(sK5(sK6,sK7),k1_relat_1(sK6))
    | r2_hidden(sK4(sK6,sK7),k2_relat_1(sK6))
    | k1_relat_1(sK7) != k2_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_1159])).

cnf(c_1161,plain,
    ( k1_relat_1(sK7) != k2_relat_1(sK6)
    | r2_hidden(sK5(sK6,sK7),k1_relat_1(sK6)) = iProver_top
    | r2_hidden(sK4(sK6,sK7),k2_relat_1(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1160])).

cnf(c_1172,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | sK5(sK6,sK7) != X2
    | sK4(sK6,sK7) != X0
    | k1_funct_1(sK6,sK5(sK6,sK7)) = sK4(sK6,sK7)
    | k1_relat_1(sK7) != k2_relat_1(sK6)
    | sK7 != X3
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_491])).

cnf(c_1173,plain,
    ( r2_hidden(sK4(sK6,sK7),k2_relat_1(sK6))
    | k1_funct_1(sK6,sK5(sK6,sK7)) = sK4(sK6,sK7)
    | k1_relat_1(sK7) != k2_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_1172])).

cnf(c_1174,plain,
    ( k1_funct_1(sK6,sK5(sK6,sK7)) = sK4(sK6,sK7)
    | k1_relat_1(sK7) != k2_relat_1(sK6)
    | r2_hidden(sK4(sK6,sK7),k2_relat_1(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1173])).

cnf(c_1310,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1897,plain,
    ( k1_relat_1(sK7) != X0
    | k1_relat_1(sK7) = k2_relat_1(sK6)
    | k2_relat_1(sK6) != X0 ),
    inference(instantiation,[status(thm)],[c_1310])).

cnf(c_1972,plain,
    ( k1_relat_1(sK7) != k1_relat_1(sK7)
    | k1_relat_1(sK7) = k2_relat_1(sK6)
    | k2_relat_1(sK6) != k1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_1897])).

cnf(c_1309,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2049,plain,
    ( k1_relat_1(sK7) = k1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_1309])).

cnf(c_2320,plain,
    ( sK4(sK6,sK7) = sK4(sK6,sK7) ),
    inference(instantiation,[status(thm)],[c_1309])).

cnf(c_2436,plain,
    ( ~ r2_hidden(sK5(sK6,sK7),k1_relat_1(sK6))
    | r2_hidden(k1_funct_1(sK6,sK5(sK6,sK7)),k2_relat_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_788])).

cnf(c_2440,plain,
    ( r2_hidden(sK5(sK6,sK7),k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k1_funct_1(sK6,sK5(sK6,sK7)),k2_relat_1(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2436])).

cnf(c_1997,plain,
    ( X0 != X1
    | sK4(sK6,sK7) != X1
    | sK4(sK6,sK7) = X0 ),
    inference(instantiation,[status(thm)],[c_1310])).

cnf(c_2327,plain,
    ( X0 != sK4(sK6,sK7)
    | sK4(sK6,sK7) = X0
    | sK4(sK6,sK7) != sK4(sK6,sK7) ),
    inference(instantiation,[status(thm)],[c_1997])).

cnf(c_4223,plain,
    ( sK4(sK6,sK7) != sK4(sK6,sK7)
    | sK4(sK6,sK7) = k1_funct_1(sK6,sK5(sK6,sK7))
    | k1_funct_1(sK6,sK5(sK6,sK7)) != sK4(sK6,sK7) ),
    inference(instantiation,[status(thm)],[c_2327])).

cnf(c_1877,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k1_relat_1(sK7))
    | X2 != X0
    | k1_relat_1(sK7) != X1 ),
    inference(instantiation,[status(thm)],[c_1315])).

cnf(c_3124,plain,
    ( r2_hidden(X0,k1_relat_1(sK7))
    | ~ r2_hidden(k1_funct_1(sK6,sK5(sK6,sK7)),k2_relat_1(sK6))
    | X0 != k1_funct_1(sK6,sK5(sK6,sK7))
    | k1_relat_1(sK7) != k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_1877])).

cnf(c_5492,plain,
    ( r2_hidden(sK4(sK6,sK7),k1_relat_1(sK7))
    | ~ r2_hidden(k1_funct_1(sK6,sK5(sK6,sK7)),k2_relat_1(sK6))
    | sK4(sK6,sK7) != k1_funct_1(sK6,sK5(sK6,sK7))
    | k1_relat_1(sK7) != k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_3124])).

cnf(c_5493,plain,
    ( sK4(sK6,sK7) != k1_funct_1(sK6,sK5(sK6,sK7))
    | k1_relat_1(sK7) != k2_relat_1(sK6)
    | r2_hidden(sK4(sK6,sK7),k1_relat_1(sK7)) = iProver_top
    | r2_hidden(k1_funct_1(sK6,sK5(sK6,sK7)),k2_relat_1(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5492])).

cnf(c_1892,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK4(sK6,sK7),k2_relat_1(sK6))
    | sK4(sK6,sK7) != X0
    | k2_relat_1(sK6) != X1 ),
    inference(instantiation,[status(thm)],[c_1315])).

cnf(c_1992,plain,
    ( ~ r2_hidden(sK4(sK6,sK7),X0)
    | r2_hidden(sK4(sK6,sK7),k2_relat_1(sK6))
    | sK4(sK6,sK7) != sK4(sK6,sK7)
    | k2_relat_1(sK6) != X0 ),
    inference(instantiation,[status(thm)],[c_1892])).

cnf(c_12239,plain,
    ( ~ r2_hidden(sK4(sK6,sK7),k1_relat_1(sK7))
    | r2_hidden(sK4(sK6,sK7),k2_relat_1(sK6))
    | sK4(sK6,sK7) != sK4(sK6,sK7)
    | k2_relat_1(sK6) != k1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_1992])).

cnf(c_12240,plain,
    ( sK4(sK6,sK7) != sK4(sK6,sK7)
    | k2_relat_1(sK6) != k1_relat_1(sK7)
    | r2_hidden(sK4(sK6,sK7),k1_relat_1(sK7)) != iProver_top
    | r2_hidden(sK4(sK6,sK7),k2_relat_1(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12239])).

cnf(c_26016,plain,
    ( r2_hidden(sK4(sK6,sK7),k2_relat_1(sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3005,c_21,c_1161,c_1174,c_1972,c_2049,c_2320,c_2440,c_4223,c_5493,c_12240])).

cnf(c_19,negated_conjecture,
    ( ~ r2_hidden(X0,k1_relat_1(sK7))
    | ~ r2_hidden(k1_funct_1(sK7,X0),k1_relat_1(sK6))
    | k1_funct_1(sK6,k1_funct_1(sK7,X0)) = X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1773,plain,
    ( k1_funct_1(sK6,k1_funct_1(sK7,X0)) = X0
    | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | r2_hidden(k1_funct_1(sK7,X0),k1_relat_1(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1787,plain,
    ( k1_funct_1(sK6,k1_funct_1(sK7,X0)) = X0
    | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
    | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1773,c_21,c_22])).

cnf(c_704,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_24])).

cnf(c_705,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK7))
    | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7))
    | ~ v1_relat_1(sK7) ),
    inference(unflattening,[status(thm)],[c_704])).

cnf(c_709,plain,
    ( r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7))
    | ~ r2_hidden(X0,k1_relat_1(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_705,c_25])).

cnf(c_710,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK7))
    | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7)) ),
    inference(renaming,[status(thm)],[c_709])).

cnf(c_1759,plain,
    ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_710])).

cnf(c_1781,plain,
    ( r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
    | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1759,c_21])).

cnf(c_2248,plain,
    ( r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
    | k1_funct_1(sK6,k1_funct_1(sK7,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1787,c_1781])).

cnf(c_2249,plain,
    ( k1_funct_1(sK6,k1_funct_1(sK7,X0)) = X0
    | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2248])).

cnf(c_26115,plain,
    ( k1_funct_1(sK6,k1_funct_1(sK7,sK4(sK6,sK7))) = sK4(sK6,sK7) ),
    inference(superposition,[status(thm)],[c_26016,c_2249])).

cnf(c_26580,plain,
    ( k1_funct_1(sK6,sK5(sK6,sK7)) = sK4(sK6,sK7) ),
    inference(superposition,[status(thm)],[c_3079,c_26115])).

cnf(c_44941,plain,
    ( k1_funct_1(sK7,sK4(sK6,sK7)) = sK5(sK6,sK7) ),
    inference(light_normalisation,[status(thm)],[c_3023,c_26580])).

cnf(c_44952,plain,
    ( r2_hidden(sK5(sK6,sK7),k2_relat_1(sK7)) = iProver_top
    | r2_hidden(sK4(sK6,sK7),k2_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_44941,c_1781])).

cnf(c_44958,plain,
    ( r2_hidden(sK5(sK6,sK7),k2_relat_1(sK7))
    | ~ r2_hidden(sK4(sK6,sK7),k2_relat_1(sK6)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_44952])).

cnf(c_26018,plain,
    ( r2_hidden(sK4(sK6,sK7),k2_relat_1(sK6)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_26016])).

cnf(c_6143,plain,
    ( sK5(sK6,sK7) = sK5(sK6,sK7) ),
    inference(instantiation,[status(thm)],[c_1309])).

cnf(c_1977,plain,
    ( X0 != X1
    | k1_relat_1(sK6) != X1
    | k1_relat_1(sK6) = X0 ),
    inference(instantiation,[status(thm)],[c_1310])).

cnf(c_2084,plain,
    ( X0 != k1_relat_1(sK6)
    | k1_relat_1(sK6) = X0
    | k1_relat_1(sK6) != k1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_1977])).

cnf(c_2467,plain,
    ( k1_relat_1(sK6) != k1_relat_1(sK6)
    | k1_relat_1(sK6) = k2_relat_1(sK7)
    | k2_relat_1(sK7) != k1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_2084])).

cnf(c_1334,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_1309])).

cnf(c_1314,plain,
    ( X0 != X1
    | k1_relat_1(X0) = k1_relat_1(X1) ),
    theory(equality)).

cnf(c_1325,plain,
    ( k1_relat_1(sK6) = k1_relat_1(sK6)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_1314])).

cnf(c_6,plain,
    ( sP0(k1_funct_1(X0,X1),X1,X0,X2)
    | ~ r2_hidden(X1,k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_11,plain,
    ( ~ sP0(sK4(X0,X1),sK5(X0,X1),X0,X1)
    | ~ r2_hidden(sK4(X0,X1),k2_relat_1(X0))
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | k1_funct_1(X1,sK4(X0,X1)) != sK5(X0,X1)
    | k2_funct_1(X0) = X1
    | k1_relat_1(X1) != k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_356,plain,
    ( ~ sP0(sK4(X0,X1),sK5(X0,X1),X0,X1)
    | ~ r2_hidden(sK4(X0,X1),k2_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | k1_funct_1(X1,sK4(X0,X1)) != sK5(X0,X1)
    | k2_funct_1(X0) = X1
    | k1_relat_1(X1) != k2_relat_1(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_23])).

cnf(c_357,plain,
    ( ~ sP0(sK4(sK6,X0),sK5(sK6,X0),sK6,X0)
    | ~ r2_hidden(sK4(sK6,X0),k2_relat_1(sK6))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK6)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK6)
    | k1_funct_1(X0,sK4(sK6,X0)) != sK5(sK6,X0)
    | k2_funct_1(sK6) = X0
    | k1_relat_1(X0) != k2_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_356])).

cnf(c_361,plain,
    ( ~ v1_funct_1(X0)
    | ~ sP0(sK4(sK6,X0),sK5(sK6,X0),sK6,X0)
    | ~ r2_hidden(sK4(sK6,X0),k2_relat_1(sK6))
    | ~ v1_relat_1(X0)
    | k1_funct_1(X0,sK4(sK6,X0)) != sK5(sK6,X0)
    | k2_funct_1(sK6) = X0
    | k1_relat_1(X0) != k2_relat_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_357,c_27,c_26])).

cnf(c_362,plain,
    ( ~ sP0(sK4(sK6,X0),sK5(sK6,X0),sK6,X0)
    | ~ r2_hidden(sK4(sK6,X0),k2_relat_1(sK6))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_funct_1(X0,sK4(sK6,X0)) != sK5(sK6,X0)
    | k2_funct_1(sK6) = X0
    | k1_relat_1(X0) != k2_relat_1(sK6) ),
    inference(renaming,[status(thm)],[c_361])).

cnf(c_467,plain,
    ( ~ sP0(sK4(sK6,X0),sK5(sK6,X0),sK6,X0)
    | ~ r2_hidden(sK4(sK6,X0),k2_relat_1(sK6))
    | ~ v1_relat_1(X0)
    | k1_funct_1(X0,sK4(sK6,X0)) != sK5(sK6,X0)
    | k2_funct_1(sK6) = X0
    | k1_relat_1(X0) != k2_relat_1(sK6)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_362,c_24])).

cnf(c_468,plain,
    ( ~ sP0(sK4(sK6,sK7),sK5(sK6,sK7),sK6,sK7)
    | ~ r2_hidden(sK4(sK6,sK7),k2_relat_1(sK6))
    | ~ v1_relat_1(sK7)
    | k1_funct_1(sK7,sK4(sK6,sK7)) != sK5(sK6,sK7)
    | k2_funct_1(sK6) = sK7
    | k1_relat_1(sK7) != k2_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_467])).

cnf(c_470,plain,
    ( k1_funct_1(sK7,sK4(sK6,sK7)) != sK5(sK6,sK7)
    | ~ sP0(sK4(sK6,sK7),sK5(sK6,sK7),sK6,sK7)
    | ~ r2_hidden(sK4(sK6,sK7),k2_relat_1(sK6))
    | k1_relat_1(sK7) != k2_relat_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_468,c_25,c_18])).

cnf(c_471,plain,
    ( ~ sP0(sK4(sK6,sK7),sK5(sK6,sK7),sK6,sK7)
    | ~ r2_hidden(sK4(sK6,sK7),k2_relat_1(sK6))
    | k1_funct_1(sK7,sK4(sK6,sK7)) != sK5(sK6,sK7)
    | k1_relat_1(sK7) != k2_relat_1(sK6) ),
    inference(renaming,[status(thm)],[c_470])).

cnf(c_1066,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(sK4(sK6,sK7),k2_relat_1(sK6))
    | sK5(sK6,sK7) != X0
    | k1_funct_1(X1,X0) != sK4(sK6,sK7)
    | k1_funct_1(sK7,sK4(sK6,sK7)) != sK5(sK6,sK7)
    | k1_relat_1(sK7) != k2_relat_1(sK6)
    | sK7 != X2
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_471])).

cnf(c_1067,plain,
    ( ~ r2_hidden(sK5(sK6,sK7),k1_relat_1(sK6))
    | ~ r2_hidden(sK4(sK6,sK7),k2_relat_1(sK6))
    | k1_funct_1(sK7,sK4(sK6,sK7)) != sK5(sK6,sK7)
    | k1_funct_1(sK6,sK5(sK6,sK7)) != sK4(sK6,sK7)
    | k1_relat_1(sK7) != k2_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_1066])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_67223,c_44958,c_44941,c_26580,c_26018,c_6143,c_2467,c_2049,c_1972,c_1334,c_1325,c_1067,c_21,c_22])).


%------------------------------------------------------------------------------
