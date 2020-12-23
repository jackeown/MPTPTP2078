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
% DateTime   : Thu Dec  3 11:50:40 EST 2020

% Result     : Theorem 27.47s
% Output     : CNFRefutation 27.47s
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
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:44:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 27.47/3.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.47/3.99  
% 27.47/3.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.47/3.99  
% 27.47/3.99  ------  iProver source info
% 27.47/3.99  
% 27.47/3.99  git: date: 2020-06-30 10:37:57 +0100
% 27.47/3.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.47/3.99  git: non_committed_changes: false
% 27.47/3.99  git: last_make_outside_of_git: false
% 27.47/3.99  
% 27.47/3.99  ------ 
% 27.47/3.99  
% 27.47/3.99  ------ Input Options
% 27.47/3.99  
% 27.47/3.99  --out_options                           all
% 27.47/3.99  --tptp_safe_out                         true
% 27.47/3.99  --problem_path                          ""
% 27.47/3.99  --include_path                          ""
% 27.47/3.99  --clausifier                            res/vclausify_rel
% 27.47/3.99  --clausifier_options                    ""
% 27.47/3.99  --stdin                                 false
% 27.47/3.99  --stats_out                             all
% 27.47/3.99  
% 27.47/3.99  ------ General Options
% 27.47/3.99  
% 27.47/3.99  --fof                                   false
% 27.47/3.99  --time_out_real                         305.
% 27.47/3.99  --time_out_virtual                      -1.
% 27.47/3.99  --symbol_type_check                     false
% 27.47/3.99  --clausify_out                          false
% 27.47/3.99  --sig_cnt_out                           false
% 27.47/3.99  --trig_cnt_out                          false
% 27.47/3.99  --trig_cnt_out_tolerance                1.
% 27.47/3.99  --trig_cnt_out_sk_spl                   false
% 27.47/3.99  --abstr_cl_out                          false
% 27.47/3.99  
% 27.47/3.99  ------ Global Options
% 27.47/3.99  
% 27.47/3.99  --schedule                              default
% 27.47/3.99  --add_important_lit                     false
% 27.47/3.99  --prop_solver_per_cl                    1000
% 27.47/3.99  --min_unsat_core                        false
% 27.47/3.99  --soft_assumptions                      false
% 27.47/3.99  --soft_lemma_size                       3
% 27.47/3.99  --prop_impl_unit_size                   0
% 27.47/3.99  --prop_impl_unit                        []
% 27.47/3.99  --share_sel_clauses                     true
% 27.47/3.99  --reset_solvers                         false
% 27.47/3.99  --bc_imp_inh                            [conj_cone]
% 27.47/3.99  --conj_cone_tolerance                   3.
% 27.47/3.99  --extra_neg_conj                        none
% 27.47/3.99  --large_theory_mode                     true
% 27.47/3.99  --prolific_symb_bound                   200
% 27.47/3.99  --lt_threshold                          2000
% 27.47/3.99  --clause_weak_htbl                      true
% 27.47/3.99  --gc_record_bc_elim                     false
% 27.47/3.99  
% 27.47/3.99  ------ Preprocessing Options
% 27.47/3.99  
% 27.47/3.99  --preprocessing_flag                    true
% 27.47/3.99  --time_out_prep_mult                    0.1
% 27.47/3.99  --splitting_mode                        input
% 27.47/3.99  --splitting_grd                         true
% 27.47/3.99  --splitting_cvd                         false
% 27.47/3.99  --splitting_cvd_svl                     false
% 27.47/3.99  --splitting_nvd                         32
% 27.47/3.99  --sub_typing                            true
% 27.47/3.99  --prep_gs_sim                           true
% 27.47/3.99  --prep_unflatten                        true
% 27.47/3.99  --prep_res_sim                          true
% 27.47/3.99  --prep_upred                            true
% 27.47/3.99  --prep_sem_filter                       exhaustive
% 27.47/3.99  --prep_sem_filter_out                   false
% 27.47/3.99  --pred_elim                             true
% 27.47/3.99  --res_sim_input                         true
% 27.47/3.99  --eq_ax_congr_red                       true
% 27.47/3.99  --pure_diseq_elim                       true
% 27.47/3.99  --brand_transform                       false
% 27.47/3.99  --non_eq_to_eq                          false
% 27.47/3.99  --prep_def_merge                        true
% 27.47/3.99  --prep_def_merge_prop_impl              false
% 27.47/3.99  --prep_def_merge_mbd                    true
% 27.47/3.99  --prep_def_merge_tr_red                 false
% 27.47/3.99  --prep_def_merge_tr_cl                  false
% 27.47/3.99  --smt_preprocessing                     true
% 27.47/3.99  --smt_ac_axioms                         fast
% 27.47/3.99  --preprocessed_out                      false
% 27.47/3.99  --preprocessed_stats                    false
% 27.47/3.99  
% 27.47/3.99  ------ Abstraction refinement Options
% 27.47/3.99  
% 27.47/3.99  --abstr_ref                             []
% 27.47/3.99  --abstr_ref_prep                        false
% 27.47/3.99  --abstr_ref_until_sat                   false
% 27.47/3.99  --abstr_ref_sig_restrict                funpre
% 27.47/3.99  --abstr_ref_af_restrict_to_split_sk     false
% 27.47/3.99  --abstr_ref_under                       []
% 27.47/3.99  
% 27.47/3.99  ------ SAT Options
% 27.47/3.99  
% 27.47/3.99  --sat_mode                              false
% 27.47/3.99  --sat_fm_restart_options                ""
% 27.47/3.99  --sat_gr_def                            false
% 27.47/3.99  --sat_epr_types                         true
% 27.47/3.99  --sat_non_cyclic_types                  false
% 27.47/3.99  --sat_finite_models                     false
% 27.47/3.99  --sat_fm_lemmas                         false
% 27.47/3.99  --sat_fm_prep                           false
% 27.47/3.99  --sat_fm_uc_incr                        true
% 27.47/3.99  --sat_out_model                         small
% 27.47/3.99  --sat_out_clauses                       false
% 27.47/3.99  
% 27.47/3.99  ------ QBF Options
% 27.47/3.99  
% 27.47/3.99  --qbf_mode                              false
% 27.47/3.99  --qbf_elim_univ                         false
% 27.47/3.99  --qbf_dom_inst                          none
% 27.47/3.99  --qbf_dom_pre_inst                      false
% 27.47/3.99  --qbf_sk_in                             false
% 27.47/3.99  --qbf_pred_elim                         true
% 27.47/3.99  --qbf_split                             512
% 27.47/3.99  
% 27.47/3.99  ------ BMC1 Options
% 27.47/3.99  
% 27.47/3.99  --bmc1_incremental                      false
% 27.47/3.99  --bmc1_axioms                           reachable_all
% 27.47/3.99  --bmc1_min_bound                        0
% 27.47/3.99  --bmc1_max_bound                        -1
% 27.47/3.99  --bmc1_max_bound_default                -1
% 27.47/3.99  --bmc1_symbol_reachability              true
% 27.47/3.99  --bmc1_property_lemmas                  false
% 27.47/3.99  --bmc1_k_induction                      false
% 27.47/3.99  --bmc1_non_equiv_states                 false
% 27.47/3.99  --bmc1_deadlock                         false
% 27.47/3.99  --bmc1_ucm                              false
% 27.47/3.99  --bmc1_add_unsat_core                   none
% 27.47/3.99  --bmc1_unsat_core_children              false
% 27.47/3.99  --bmc1_unsat_core_extrapolate_axioms    false
% 27.47/3.99  --bmc1_out_stat                         full
% 27.47/3.99  --bmc1_ground_init                      false
% 27.47/3.99  --bmc1_pre_inst_next_state              false
% 27.47/3.99  --bmc1_pre_inst_state                   false
% 27.47/3.99  --bmc1_pre_inst_reach_state             false
% 27.47/3.99  --bmc1_out_unsat_core                   false
% 27.47/3.99  --bmc1_aig_witness_out                  false
% 27.47/3.99  --bmc1_verbose                          false
% 27.47/3.99  --bmc1_dump_clauses_tptp                false
% 27.47/3.99  --bmc1_dump_unsat_core_tptp             false
% 27.47/3.99  --bmc1_dump_file                        -
% 27.47/3.99  --bmc1_ucm_expand_uc_limit              128
% 27.47/3.99  --bmc1_ucm_n_expand_iterations          6
% 27.47/3.99  --bmc1_ucm_extend_mode                  1
% 27.47/3.99  --bmc1_ucm_init_mode                    2
% 27.47/3.99  --bmc1_ucm_cone_mode                    none
% 27.47/3.99  --bmc1_ucm_reduced_relation_type        0
% 27.47/3.99  --bmc1_ucm_relax_model                  4
% 27.47/3.99  --bmc1_ucm_full_tr_after_sat            true
% 27.47/3.99  --bmc1_ucm_expand_neg_assumptions       false
% 27.47/3.99  --bmc1_ucm_layered_model                none
% 27.47/3.99  --bmc1_ucm_max_lemma_size               10
% 27.47/3.99  
% 27.47/3.99  ------ AIG Options
% 27.47/3.99  
% 27.47/3.99  --aig_mode                              false
% 27.47/3.99  
% 27.47/3.99  ------ Instantiation Options
% 27.47/3.99  
% 27.47/3.99  --instantiation_flag                    true
% 27.47/3.99  --inst_sos_flag                         true
% 27.47/3.99  --inst_sos_phase                        true
% 27.47/3.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.47/3.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.47/3.99  --inst_lit_sel_side                     num_symb
% 27.47/3.99  --inst_solver_per_active                1400
% 27.47/3.99  --inst_solver_calls_frac                1.
% 27.47/3.99  --inst_passive_queue_type               priority_queues
% 27.47/3.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.47/3.99  --inst_passive_queues_freq              [25;2]
% 27.47/3.99  --inst_dismatching                      true
% 27.47/3.99  --inst_eager_unprocessed_to_passive     true
% 27.47/3.99  --inst_prop_sim_given                   true
% 27.47/3.99  --inst_prop_sim_new                     false
% 27.47/3.99  --inst_subs_new                         false
% 27.47/3.99  --inst_eq_res_simp                      false
% 27.47/3.99  --inst_subs_given                       false
% 27.47/3.99  --inst_orphan_elimination               true
% 27.47/3.99  --inst_learning_loop_flag               true
% 27.47/3.99  --inst_learning_start                   3000
% 27.47/3.99  --inst_learning_factor                  2
% 27.47/3.99  --inst_start_prop_sim_after_learn       3
% 27.47/3.99  --inst_sel_renew                        solver
% 27.47/3.99  --inst_lit_activity_flag                true
% 27.47/3.99  --inst_restr_to_given                   false
% 27.47/3.99  --inst_activity_threshold               500
% 27.47/3.99  --inst_out_proof                        true
% 27.47/3.99  
% 27.47/3.99  ------ Resolution Options
% 27.47/3.99  
% 27.47/3.99  --resolution_flag                       true
% 27.47/3.99  --res_lit_sel                           adaptive
% 27.47/3.99  --res_lit_sel_side                      none
% 27.47/3.99  --res_ordering                          kbo
% 27.47/3.99  --res_to_prop_solver                    active
% 27.47/3.99  --res_prop_simpl_new                    false
% 27.47/3.99  --res_prop_simpl_given                  true
% 27.47/3.99  --res_passive_queue_type                priority_queues
% 27.47/3.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.47/3.99  --res_passive_queues_freq               [15;5]
% 27.47/3.99  --res_forward_subs                      full
% 27.47/3.99  --res_backward_subs                     full
% 27.47/3.99  --res_forward_subs_resolution           true
% 27.47/3.99  --res_backward_subs_resolution          true
% 27.47/3.99  --res_orphan_elimination                true
% 27.47/3.99  --res_time_limit                        2.
% 27.47/3.99  --res_out_proof                         true
% 27.47/3.99  
% 27.47/3.99  ------ Superposition Options
% 27.47/3.99  
% 27.47/3.99  --superposition_flag                    true
% 27.47/3.99  --sup_passive_queue_type                priority_queues
% 27.47/3.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.47/3.99  --sup_passive_queues_freq               [8;1;4]
% 27.47/3.99  --demod_completeness_check              fast
% 27.47/3.99  --demod_use_ground                      true
% 27.47/3.99  --sup_to_prop_solver                    passive
% 27.47/3.99  --sup_prop_simpl_new                    true
% 27.47/3.99  --sup_prop_simpl_given                  true
% 27.47/3.99  --sup_fun_splitting                     true
% 27.47/3.99  --sup_smt_interval                      50000
% 27.47/3.99  
% 27.47/3.99  ------ Superposition Simplification Setup
% 27.47/3.99  
% 27.47/3.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 27.47/3.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 27.47/3.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 27.47/3.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 27.47/3.99  --sup_full_triv                         [TrivRules;PropSubs]
% 27.47/3.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 27.47/3.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 27.47/3.99  --sup_immed_triv                        [TrivRules]
% 27.47/3.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.47/3.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.47/3.99  --sup_immed_bw_main                     []
% 27.47/3.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 27.47/3.99  --sup_input_triv                        [Unflattening;TrivRules]
% 27.47/3.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.47/3.99  --sup_input_bw                          []
% 27.47/3.99  
% 27.47/3.99  ------ Combination Options
% 27.47/3.99  
% 27.47/3.99  --comb_res_mult                         3
% 27.47/3.99  --comb_sup_mult                         2
% 27.47/3.99  --comb_inst_mult                        10
% 27.47/3.99  
% 27.47/3.99  ------ Debug Options
% 27.47/3.99  
% 27.47/3.99  --dbg_backtrace                         false
% 27.47/3.99  --dbg_dump_prop_clauses                 false
% 27.47/3.99  --dbg_dump_prop_clauses_file            -
% 27.47/3.99  --dbg_out_stat                          false
% 27.47/3.99  ------ Parsing...
% 27.47/3.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.47/3.99  
% 27.47/3.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 27.47/3.99  
% 27.47/3.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.47/3.99  
% 27.47/3.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.47/3.99  ------ Proving...
% 27.47/3.99  ------ Problem Properties 
% 27.47/3.99  
% 27.47/3.99  
% 27.47/3.99  clauses                                 31
% 27.47/3.99  conjectures                             5
% 27.47/3.99  EPR                                     0
% 27.47/3.99  Horn                                    23
% 27.47/3.99  unary                                   3
% 27.47/3.99  binary                                  11
% 27.47/3.99  lits                                    83
% 27.47/3.99  lits eq                                 37
% 27.47/3.99  fd_pure                                 0
% 27.47/3.99  fd_pseudo                               0
% 27.47/3.99  fd_cond                                 6
% 27.47/3.99  fd_pseudo_cond                          1
% 27.47/3.99  AC symbols                              0
% 27.47/3.99  
% 27.47/3.99  ------ Schedule dynamic 5 is on 
% 27.47/3.99  
% 27.47/3.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 27.47/3.99  
% 27.47/3.99  
% 27.47/3.99  ------ 
% 27.47/3.99  Current options:
% 27.47/3.99  ------ 
% 27.47/3.99  
% 27.47/3.99  ------ Input Options
% 27.47/3.99  
% 27.47/3.99  --out_options                           all
% 27.47/3.99  --tptp_safe_out                         true
% 27.47/3.99  --problem_path                          ""
% 27.47/3.99  --include_path                          ""
% 27.47/3.99  --clausifier                            res/vclausify_rel
% 27.47/3.99  --clausifier_options                    ""
% 27.47/3.99  --stdin                                 false
% 27.47/3.99  --stats_out                             all
% 27.47/3.99  
% 27.47/3.99  ------ General Options
% 27.47/3.99  
% 27.47/3.99  --fof                                   false
% 27.47/3.99  --time_out_real                         305.
% 27.47/3.99  --time_out_virtual                      -1.
% 27.47/3.99  --symbol_type_check                     false
% 27.47/3.99  --clausify_out                          false
% 27.47/3.99  --sig_cnt_out                           false
% 27.47/3.99  --trig_cnt_out                          false
% 27.47/3.99  --trig_cnt_out_tolerance                1.
% 27.47/3.99  --trig_cnt_out_sk_spl                   false
% 27.47/3.99  --abstr_cl_out                          false
% 27.47/3.99  
% 27.47/3.99  ------ Global Options
% 27.47/3.99  
% 27.47/3.99  --schedule                              default
% 27.47/3.99  --add_important_lit                     false
% 27.47/3.99  --prop_solver_per_cl                    1000
% 27.47/3.99  --min_unsat_core                        false
% 27.47/3.99  --soft_assumptions                      false
% 27.47/3.99  --soft_lemma_size                       3
% 27.47/3.99  --prop_impl_unit_size                   0
% 27.47/3.99  --prop_impl_unit                        []
% 27.47/3.99  --share_sel_clauses                     true
% 27.47/3.99  --reset_solvers                         false
% 27.47/3.99  --bc_imp_inh                            [conj_cone]
% 27.47/3.99  --conj_cone_tolerance                   3.
% 27.47/3.99  --extra_neg_conj                        none
% 27.47/3.99  --large_theory_mode                     true
% 27.47/3.99  --prolific_symb_bound                   200
% 27.47/3.99  --lt_threshold                          2000
% 27.47/3.99  --clause_weak_htbl                      true
% 27.47/3.99  --gc_record_bc_elim                     false
% 27.47/3.99  
% 27.47/3.99  ------ Preprocessing Options
% 27.47/3.99  
% 27.47/3.99  --preprocessing_flag                    true
% 27.47/3.99  --time_out_prep_mult                    0.1
% 27.47/3.99  --splitting_mode                        input
% 27.47/3.99  --splitting_grd                         true
% 27.47/3.99  --splitting_cvd                         false
% 27.47/3.99  --splitting_cvd_svl                     false
% 27.47/3.99  --splitting_nvd                         32
% 27.47/3.99  --sub_typing                            true
% 27.47/3.99  --prep_gs_sim                           true
% 27.47/3.99  --prep_unflatten                        true
% 27.47/3.99  --prep_res_sim                          true
% 27.47/3.99  --prep_upred                            true
% 27.47/3.99  --prep_sem_filter                       exhaustive
% 27.47/3.99  --prep_sem_filter_out                   false
% 27.47/3.99  --pred_elim                             true
% 27.47/3.99  --res_sim_input                         true
% 27.47/3.99  --eq_ax_congr_red                       true
% 27.47/3.99  --pure_diseq_elim                       true
% 27.47/3.99  --brand_transform                       false
% 27.47/3.99  --non_eq_to_eq                          false
% 27.47/3.99  --prep_def_merge                        true
% 27.47/3.99  --prep_def_merge_prop_impl              false
% 27.47/3.99  --prep_def_merge_mbd                    true
% 27.47/3.99  --prep_def_merge_tr_red                 false
% 27.47/3.99  --prep_def_merge_tr_cl                  false
% 27.47/3.99  --smt_preprocessing                     true
% 27.47/3.99  --smt_ac_axioms                         fast
% 27.47/3.99  --preprocessed_out                      false
% 27.47/3.99  --preprocessed_stats                    false
% 27.47/3.99  
% 27.47/3.99  ------ Abstraction refinement Options
% 27.47/3.99  
% 27.47/3.99  --abstr_ref                             []
% 27.47/3.99  --abstr_ref_prep                        false
% 27.47/3.99  --abstr_ref_until_sat                   false
% 27.47/3.99  --abstr_ref_sig_restrict                funpre
% 27.47/3.99  --abstr_ref_af_restrict_to_split_sk     false
% 27.47/3.99  --abstr_ref_under                       []
% 27.47/3.99  
% 27.47/3.99  ------ SAT Options
% 27.47/3.99  
% 27.47/3.99  --sat_mode                              false
% 27.47/3.99  --sat_fm_restart_options                ""
% 27.47/3.99  --sat_gr_def                            false
% 27.47/3.99  --sat_epr_types                         true
% 27.47/3.99  --sat_non_cyclic_types                  false
% 27.47/3.99  --sat_finite_models                     false
% 27.47/3.99  --sat_fm_lemmas                         false
% 27.47/3.99  --sat_fm_prep                           false
% 27.47/3.99  --sat_fm_uc_incr                        true
% 27.47/3.99  --sat_out_model                         small
% 27.47/3.99  --sat_out_clauses                       false
% 27.47/3.99  
% 27.47/3.99  ------ QBF Options
% 27.47/3.99  
% 27.47/3.99  --qbf_mode                              false
% 27.47/3.99  --qbf_elim_univ                         false
% 27.47/3.99  --qbf_dom_inst                          none
% 27.47/3.99  --qbf_dom_pre_inst                      false
% 27.47/3.99  --qbf_sk_in                             false
% 27.47/3.99  --qbf_pred_elim                         true
% 27.47/3.99  --qbf_split                             512
% 27.47/3.99  
% 27.47/3.99  ------ BMC1 Options
% 27.47/3.99  
% 27.47/3.99  --bmc1_incremental                      false
% 27.47/3.99  --bmc1_axioms                           reachable_all
% 27.47/3.99  --bmc1_min_bound                        0
% 27.47/3.99  --bmc1_max_bound                        -1
% 27.47/3.99  --bmc1_max_bound_default                -1
% 27.47/3.99  --bmc1_symbol_reachability              true
% 27.47/3.99  --bmc1_property_lemmas                  false
% 27.47/3.99  --bmc1_k_induction                      false
% 27.47/3.99  --bmc1_non_equiv_states                 false
% 27.47/3.99  --bmc1_deadlock                         false
% 27.47/3.99  --bmc1_ucm                              false
% 27.47/3.99  --bmc1_add_unsat_core                   none
% 27.47/3.99  --bmc1_unsat_core_children              false
% 27.47/3.99  --bmc1_unsat_core_extrapolate_axioms    false
% 27.47/3.99  --bmc1_out_stat                         full
% 27.47/3.99  --bmc1_ground_init                      false
% 27.47/3.99  --bmc1_pre_inst_next_state              false
% 27.47/3.99  --bmc1_pre_inst_state                   false
% 27.47/3.99  --bmc1_pre_inst_reach_state             false
% 27.47/3.99  --bmc1_out_unsat_core                   false
% 27.47/3.99  --bmc1_aig_witness_out                  false
% 27.47/3.99  --bmc1_verbose                          false
% 27.47/3.99  --bmc1_dump_clauses_tptp                false
% 27.47/3.99  --bmc1_dump_unsat_core_tptp             false
% 27.47/3.99  --bmc1_dump_file                        -
% 27.47/3.99  --bmc1_ucm_expand_uc_limit              128
% 27.47/3.99  --bmc1_ucm_n_expand_iterations          6
% 27.47/3.99  --bmc1_ucm_extend_mode                  1
% 27.47/3.99  --bmc1_ucm_init_mode                    2
% 27.47/3.99  --bmc1_ucm_cone_mode                    none
% 27.47/3.99  --bmc1_ucm_reduced_relation_type        0
% 27.47/3.99  --bmc1_ucm_relax_model                  4
% 27.47/3.99  --bmc1_ucm_full_tr_after_sat            true
% 27.47/3.99  --bmc1_ucm_expand_neg_assumptions       false
% 27.47/3.99  --bmc1_ucm_layered_model                none
% 27.47/3.99  --bmc1_ucm_max_lemma_size               10
% 27.47/3.99  
% 27.47/3.99  ------ AIG Options
% 27.47/3.99  
% 27.47/3.99  --aig_mode                              false
% 27.47/3.99  
% 27.47/3.99  ------ Instantiation Options
% 27.47/3.99  
% 27.47/3.99  --instantiation_flag                    true
% 27.47/3.99  --inst_sos_flag                         true
% 27.47/3.99  --inst_sos_phase                        true
% 27.47/3.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.47/3.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.47/3.99  --inst_lit_sel_side                     none
% 27.47/3.99  --inst_solver_per_active                1400
% 27.47/3.99  --inst_solver_calls_frac                1.
% 27.47/3.99  --inst_passive_queue_type               priority_queues
% 27.47/3.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.47/3.99  --inst_passive_queues_freq              [25;2]
% 27.47/3.99  --inst_dismatching                      true
% 27.47/3.99  --inst_eager_unprocessed_to_passive     true
% 27.47/3.99  --inst_prop_sim_given                   true
% 27.47/3.99  --inst_prop_sim_new                     false
% 27.47/3.99  --inst_subs_new                         false
% 27.47/3.99  --inst_eq_res_simp                      false
% 27.47/3.99  --inst_subs_given                       false
% 27.47/3.99  --inst_orphan_elimination               true
% 27.47/3.99  --inst_learning_loop_flag               true
% 27.47/3.99  --inst_learning_start                   3000
% 27.47/3.99  --inst_learning_factor                  2
% 27.47/3.99  --inst_start_prop_sim_after_learn       3
% 27.47/3.99  --inst_sel_renew                        solver
% 27.47/3.99  --inst_lit_activity_flag                true
% 27.47/3.99  --inst_restr_to_given                   false
% 27.47/3.99  --inst_activity_threshold               500
% 27.47/3.99  --inst_out_proof                        true
% 27.47/3.99  
% 27.47/3.99  ------ Resolution Options
% 27.47/3.99  
% 27.47/3.99  --resolution_flag                       false
% 27.47/3.99  --res_lit_sel                           adaptive
% 27.47/3.99  --res_lit_sel_side                      none
% 27.47/3.99  --res_ordering                          kbo
% 27.47/3.99  --res_to_prop_solver                    active
% 27.47/3.99  --res_prop_simpl_new                    false
% 27.47/3.99  --res_prop_simpl_given                  true
% 27.47/3.99  --res_passive_queue_type                priority_queues
% 27.47/3.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.47/3.99  --res_passive_queues_freq               [15;5]
% 27.47/3.99  --res_forward_subs                      full
% 27.47/3.99  --res_backward_subs                     full
% 27.47/3.99  --res_forward_subs_resolution           true
% 27.47/3.99  --res_backward_subs_resolution          true
% 27.47/3.99  --res_orphan_elimination                true
% 27.47/3.99  --res_time_limit                        2.
% 27.47/3.99  --res_out_proof                         true
% 27.47/3.99  
% 27.47/3.99  ------ Superposition Options
% 27.47/3.99  
% 27.47/3.99  --superposition_flag                    true
% 27.47/3.99  --sup_passive_queue_type                priority_queues
% 27.47/3.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.47/3.99  --sup_passive_queues_freq               [8;1;4]
% 27.47/3.99  --demod_completeness_check              fast
% 27.47/3.99  --demod_use_ground                      true
% 27.47/3.99  --sup_to_prop_solver                    passive
% 27.47/3.99  --sup_prop_simpl_new                    true
% 27.47/3.99  --sup_prop_simpl_given                  true
% 27.47/3.99  --sup_fun_splitting                     true
% 27.47/3.99  --sup_smt_interval                      50000
% 27.47/3.99  
% 27.47/3.99  ------ Superposition Simplification Setup
% 27.47/3.99  
% 27.47/3.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 27.47/3.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 27.47/3.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 27.47/3.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 27.47/3.99  --sup_full_triv                         [TrivRules;PropSubs]
% 27.47/3.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 27.47/3.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 27.47/3.99  --sup_immed_triv                        [TrivRules]
% 27.47/3.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.47/3.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.47/3.99  --sup_immed_bw_main                     []
% 27.47/3.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 27.47/3.99  --sup_input_triv                        [Unflattening;TrivRules]
% 27.47/3.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.47/3.99  --sup_input_bw                          []
% 27.47/3.99  
% 27.47/3.99  ------ Combination Options
% 27.47/3.99  
% 27.47/3.99  --comb_res_mult                         3
% 27.47/3.99  --comb_sup_mult                         2
% 27.47/3.99  --comb_inst_mult                        10
% 27.47/3.99  
% 27.47/3.99  ------ Debug Options
% 27.47/3.99  
% 27.47/3.99  --dbg_backtrace                         false
% 27.47/3.99  --dbg_dump_prop_clauses                 false
% 27.47/3.99  --dbg_dump_prop_clauses_file            -
% 27.47/3.99  --dbg_out_stat                          false
% 27.47/3.99  
% 27.47/3.99  
% 27.47/3.99  
% 27.47/3.99  
% 27.47/3.99  ------ Proving...
% 27.47/3.99  
% 27.47/3.99  
% 27.47/3.99  % SZS status Theorem for theBenchmark.p
% 27.47/3.99  
% 27.47/3.99  % SZS output start CNFRefutation for theBenchmark.p
% 27.47/3.99  
% 27.47/3.99  fof(f11,plain,(
% 27.47/3.99    ! [X2,X3,X0,X1] : (sP0(X2,X3,X0,X1) <=> ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))))),
% 27.47/3.99    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 27.47/3.99  
% 27.47/3.99  fof(f19,plain,(
% 27.47/3.99    ! [X2,X3,X0,X1] : ((sP0(X2,X3,X0,X1) | ((k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0)))) & (((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))) | ~sP0(X2,X3,X0,X1)))),
% 27.47/3.99    inference(nnf_transformation,[],[f11])).
% 27.47/3.99  
% 27.47/3.99  fof(f20,plain,(
% 27.47/3.99    ! [X2,X3,X0,X1] : ((sP0(X2,X3,X0,X1) | ((k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0)))) & ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0)) | ~sP0(X2,X3,X0,X1)))),
% 27.47/3.99    inference(flattening,[],[f19])).
% 27.47/3.99  
% 27.47/3.99  fof(f21,plain,(
% 27.47/3.99    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ((k1_funct_1(X2,X1) != X0 | ~r2_hidden(X1,k1_relat_1(X2))) & k1_funct_1(X3,X0) = X1 & r2_hidden(X0,k2_relat_1(X2)))) & ((k1_funct_1(X2,X1) = X0 & r2_hidden(X1,k1_relat_1(X2))) | k1_funct_1(X3,X0) != X1 | ~r2_hidden(X0,k2_relat_1(X2)) | ~sP0(X0,X1,X2,X3)))),
% 27.47/3.99    inference(rectify,[],[f20])).
% 27.47/3.99  
% 27.47/3.99  fof(f40,plain,(
% 27.47/3.99    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2,X3) | k1_funct_1(X3,X0) = X1) )),
% 27.47/3.99    inference(cnf_transformation,[],[f21])).
% 27.47/3.99  
% 27.47/3.99  fof(f2,axiom,(
% 27.47/3.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) => (k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0)))) & ((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) => (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) & k2_relat_1(X0) = k1_relat_1(X1))))))),
% 27.47/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.47/3.99  
% 27.47/3.99  fof(f7,plain,(
% 27.47/3.99    ! [X0] : ((! [X1] : ((k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | (k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))))) & k2_relat_1(X0) = k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 27.47/3.99    inference(ennf_transformation,[],[f2])).
% 27.47/3.99  
% 27.47/3.99  fof(f8,plain,(
% 27.47/3.99    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0)))) & k2_relat_1(X0) = k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 27.47/3.99    inference(flattening,[],[f7])).
% 27.47/3.99  
% 27.47/3.99  fof(f12,plain,(
% 27.47/3.99    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & sP0(X2,X3,X0,X1)) & k2_relat_1(X0) = k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 27.47/3.99    inference(definition_folding,[],[f8,f11])).
% 27.47/3.99  
% 27.47/3.99  fof(f22,plain,(
% 27.47/3.99    ! [X0] : (! [X1] : (((k2_funct_1(X0) = X1 | (? [X2,X3] : (((k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))) & k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X2,X3,X0,X1)) | k2_relat_1(X0) != k1_relat_1(X1))) & ((! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & sP0(X2,X3,X0,X1)) & k2_relat_1(X0) = k1_relat_1(X1)) | k2_funct_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 27.47/3.99    inference(nnf_transformation,[],[f12])).
% 27.47/3.99  
% 27.47/3.99  fof(f23,plain,(
% 27.47/3.99    ! [X0] : (! [X1] : (((k2_funct_1(X0) = X1 | ? [X2,X3] : (((k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))) & k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X2,X3,X0,X1)) | k2_relat_1(X0) != k1_relat_1(X1)) & ((! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & sP0(X2,X3,X0,X1)) & k2_relat_1(X0) = k1_relat_1(X1)) | k2_funct_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 27.47/3.99    inference(flattening,[],[f22])).
% 27.47/3.99  
% 27.47/3.99  fof(f24,plain,(
% 27.47/3.99    ! [X0] : (! [X1] : (((k2_funct_1(X0) = X1 | ? [X2,X3] : (((k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))) & k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X2,X3,X0,X1)) | k2_relat_1(X0) != k1_relat_1(X1)) & ((! [X4,X5] : (((k1_funct_1(X1,X4) = X5 & r2_hidden(X4,k2_relat_1(X0))) | k1_funct_1(X0,X5) != X4 | ~r2_hidden(X5,k1_relat_1(X0))) & sP0(X4,X5,X0,X1)) & k2_relat_1(X0) = k1_relat_1(X1)) | k2_funct_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 27.47/3.99    inference(rectify,[],[f23])).
% 27.47/3.99  
% 27.47/3.99  fof(f25,plain,(
% 27.47/3.99    ! [X1,X0] : (? [X2,X3] : (((k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))) & k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X2,X3,X0,X1)) => (((k1_funct_1(X1,sK4(X0,X1)) != sK5(X0,X1) | ~r2_hidden(sK4(X0,X1),k2_relat_1(X0))) & k1_funct_1(X0,sK5(X0,X1)) = sK4(X0,X1) & r2_hidden(sK5(X0,X1),k1_relat_1(X0))) | ~sP0(sK4(X0,X1),sK5(X0,X1),X0,X1)))),
% 27.47/3.99    introduced(choice_axiom,[])).
% 27.47/3.99  
% 27.47/3.99  fof(f26,plain,(
% 27.47/3.99    ! [X0] : (! [X1] : (((k2_funct_1(X0) = X1 | (((k1_funct_1(X1,sK4(X0,X1)) != sK5(X0,X1) | ~r2_hidden(sK4(X0,X1),k2_relat_1(X0))) & k1_funct_1(X0,sK5(X0,X1)) = sK4(X0,X1) & r2_hidden(sK5(X0,X1),k1_relat_1(X0))) | ~sP0(sK4(X0,X1),sK5(X0,X1),X0,X1)) | k2_relat_1(X0) != k1_relat_1(X1)) & ((! [X4,X5] : (((k1_funct_1(X1,X4) = X5 & r2_hidden(X4,k2_relat_1(X0))) | k1_funct_1(X0,X5) != X4 | ~r2_hidden(X5,k1_relat_1(X0))) & sP0(X4,X5,X0,X1)) & k2_relat_1(X0) = k1_relat_1(X1)) | k2_funct_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 27.47/3.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f24,f25])).
% 27.47/3.99  
% 27.47/3.99  fof(f46,plain,(
% 27.47/3.99    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | r2_hidden(sK5(X0,X1),k1_relat_1(X0)) | ~sP0(sK4(X0,X1),sK5(X0,X1),X0,X1) | k2_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 27.47/3.99    inference(cnf_transformation,[],[f26])).
% 27.47/3.99  
% 27.47/3.99  fof(f3,conjecture,(
% 27.47/3.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2,X3] : ((r2_hidden(X3,k1_relat_1(X1)) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,X2) = X3 <=> k1_funct_1(X1,X3) = X2)) & k2_relat_1(X0) = k1_relat_1(X1) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 27.47/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.47/3.99  
% 27.47/3.99  fof(f4,negated_conjecture,(
% 27.47/3.99    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2,X3] : ((r2_hidden(X3,k1_relat_1(X1)) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,X2) = X3 <=> k1_funct_1(X1,X3) = X2)) & k2_relat_1(X0) = k1_relat_1(X1) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 27.47/3.99    inference(negated_conjecture,[],[f3])).
% 27.47/3.99  
% 27.47/3.99  fof(f9,plain,(
% 27.47/3.99    ? [X0] : (? [X1] : ((k2_funct_1(X0) != X1 & (! [X2,X3] : ((k1_funct_1(X0,X2) = X3 <=> k1_funct_1(X1,X3) = X2) | (~r2_hidden(X3,k1_relat_1(X1)) | ~r2_hidden(X2,k1_relat_1(X0)))) & k2_relat_1(X0) = k1_relat_1(X1) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 27.47/3.99    inference(ennf_transformation,[],[f4])).
% 27.47/3.99  
% 27.47/3.99  fof(f10,plain,(
% 27.47/3.99    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & ! [X2,X3] : ((k1_funct_1(X0,X2) = X3 <=> k1_funct_1(X1,X3) = X2) | ~r2_hidden(X3,k1_relat_1(X1)) | ~r2_hidden(X2,k1_relat_1(X0))) & k2_relat_1(X0) = k1_relat_1(X1) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 27.47/3.99    inference(flattening,[],[f9])).
% 27.47/3.99  
% 27.47/3.99  fof(f27,plain,(
% 27.47/3.99    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & ! [X2,X3] : (((k1_funct_1(X0,X2) = X3 | k1_funct_1(X1,X3) != X2) & (k1_funct_1(X1,X3) = X2 | k1_funct_1(X0,X2) != X3)) | ~r2_hidden(X3,k1_relat_1(X1)) | ~r2_hidden(X2,k1_relat_1(X0))) & k2_relat_1(X0) = k1_relat_1(X1) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 27.47/3.99    inference(nnf_transformation,[],[f10])).
% 27.47/3.99  
% 27.47/3.99  fof(f29,plain,(
% 27.47/3.99    ( ! [X0] : (? [X1] : (k2_funct_1(X0) != X1 & ! [X2,X3] : (((k1_funct_1(X0,X2) = X3 | k1_funct_1(X1,X3) != X2) & (k1_funct_1(X1,X3) = X2 | k1_funct_1(X0,X2) != X3)) | ~r2_hidden(X3,k1_relat_1(X1)) | ~r2_hidden(X2,k1_relat_1(X0))) & k2_relat_1(X0) = k1_relat_1(X1) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) => (k2_funct_1(X0) != sK7 & ! [X3,X2] : (((k1_funct_1(X0,X2) = X3 | k1_funct_1(sK7,X3) != X2) & (k1_funct_1(sK7,X3) = X2 | k1_funct_1(X0,X2) != X3)) | ~r2_hidden(X3,k1_relat_1(sK7)) | ~r2_hidden(X2,k1_relat_1(X0))) & k2_relat_1(X0) = k1_relat_1(sK7) & k2_relat_1(sK7) = k1_relat_1(X0) & v2_funct_1(X0) & v1_funct_1(sK7) & v1_relat_1(sK7))) )),
% 27.47/3.99    introduced(choice_axiom,[])).
% 27.47/3.99  
% 27.47/3.99  fof(f28,plain,(
% 27.47/3.99    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & ! [X2,X3] : (((k1_funct_1(X0,X2) = X3 | k1_funct_1(X1,X3) != X2) & (k1_funct_1(X1,X3) = X2 | k1_funct_1(X0,X2) != X3)) | ~r2_hidden(X3,k1_relat_1(X1)) | ~r2_hidden(X2,k1_relat_1(X0))) & k2_relat_1(X0) = k1_relat_1(X1) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k2_funct_1(sK6) != X1 & ! [X3,X2] : (((k1_funct_1(sK6,X2) = X3 | k1_funct_1(X1,X3) != X2) & (k1_funct_1(X1,X3) = X2 | k1_funct_1(sK6,X2) != X3)) | ~r2_hidden(X3,k1_relat_1(X1)) | ~r2_hidden(X2,k1_relat_1(sK6))) & k2_relat_1(sK6) = k1_relat_1(X1) & k2_relat_1(X1) = k1_relat_1(sK6) & v2_funct_1(sK6) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK6) & v1_relat_1(sK6))),
% 27.47/3.99    introduced(choice_axiom,[])).
% 27.47/3.99  
% 27.47/3.99  fof(f30,plain,(
% 27.47/3.99    (k2_funct_1(sK6) != sK7 & ! [X2,X3] : (((k1_funct_1(sK6,X2) = X3 | k1_funct_1(sK7,X3) != X2) & (k1_funct_1(sK7,X3) = X2 | k1_funct_1(sK6,X2) != X3)) | ~r2_hidden(X3,k1_relat_1(sK7)) | ~r2_hidden(X2,k1_relat_1(sK6))) & k2_relat_1(sK6) = k1_relat_1(sK7) & k2_relat_1(sK7) = k1_relat_1(sK6) & v2_funct_1(sK6) & v1_funct_1(sK7) & v1_relat_1(sK7)) & v1_funct_1(sK6) & v1_relat_1(sK6)),
% 27.47/3.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f27,f29,f28])).
% 27.47/3.99  
% 27.47/3.99  fof(f53,plain,(
% 27.47/3.99    v2_funct_1(sK6)),
% 27.47/3.99    inference(cnf_transformation,[],[f30])).
% 27.47/3.99  
% 27.47/3.99  fof(f49,plain,(
% 27.47/3.99    v1_relat_1(sK6)),
% 27.47/3.99    inference(cnf_transformation,[],[f30])).
% 27.47/3.99  
% 27.47/3.99  fof(f50,plain,(
% 27.47/3.99    v1_funct_1(sK6)),
% 27.47/3.99    inference(cnf_transformation,[],[f30])).
% 27.47/3.99  
% 27.47/3.99  fof(f52,plain,(
% 27.47/3.99    v1_funct_1(sK7)),
% 27.47/3.99    inference(cnf_transformation,[],[f30])).
% 27.47/3.99  
% 27.47/3.99  fof(f51,plain,(
% 27.47/3.99    v1_relat_1(sK7)),
% 27.47/3.99    inference(cnf_transformation,[],[f30])).
% 27.47/3.99  
% 27.47/3.99  fof(f58,plain,(
% 27.47/3.99    k2_funct_1(sK6) != sK7),
% 27.47/3.99    inference(cnf_transformation,[],[f30])).
% 27.47/3.99  
% 27.47/3.99  fof(f55,plain,(
% 27.47/3.99    k2_relat_1(sK6) = k1_relat_1(sK7)),
% 27.47/3.99    inference(cnf_transformation,[],[f30])).
% 27.47/3.99  
% 27.47/3.99  fof(f54,plain,(
% 27.47/3.99    k2_relat_1(sK7) = k1_relat_1(sK6)),
% 27.47/3.99    inference(cnf_transformation,[],[f30])).
% 27.47/3.99  
% 27.47/3.99  fof(f56,plain,(
% 27.47/3.99    ( ! [X2,X3] : (k1_funct_1(sK7,X3) = X2 | k1_funct_1(sK6,X2) != X3 | ~r2_hidden(X3,k1_relat_1(sK7)) | ~r2_hidden(X2,k1_relat_1(sK6))) )),
% 27.47/3.99    inference(cnf_transformation,[],[f30])).
% 27.47/3.99  
% 27.47/3.99  fof(f73,plain,(
% 27.47/3.99    ( ! [X2] : (k1_funct_1(sK7,k1_funct_1(sK6,X2)) = X2 | ~r2_hidden(k1_funct_1(sK6,X2),k1_relat_1(sK7)) | ~r2_hidden(X2,k1_relat_1(sK6))) )),
% 27.47/3.99    inference(equality_resolution,[],[f56])).
% 27.47/3.99  
% 27.47/3.99  fof(f1,axiom,(
% 27.47/3.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 27.47/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.47/3.99  
% 27.47/3.99  fof(f5,plain,(
% 27.47/3.99    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 27.47/3.99    inference(ennf_transformation,[],[f1])).
% 27.47/3.99  
% 27.47/3.99  fof(f6,plain,(
% 27.47/3.99    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 27.47/3.99    inference(flattening,[],[f5])).
% 27.47/3.99  
% 27.47/3.99  fof(f13,plain,(
% 27.47/3.99    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 27.47/3.99    inference(nnf_transformation,[],[f6])).
% 27.47/3.99  
% 27.47/3.99  fof(f14,plain,(
% 27.47/3.99    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 27.47/3.99    inference(rectify,[],[f13])).
% 27.47/3.99  
% 27.47/3.99  fof(f17,plain,(
% 27.47/3.99    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))))),
% 27.47/3.99    introduced(choice_axiom,[])).
% 27.47/3.99  
% 27.47/3.99  fof(f16,plain,(
% 27.47/3.99    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X1)) = X2 & r2_hidden(sK2(X0,X1),k1_relat_1(X0))))) )),
% 27.47/3.99    introduced(choice_axiom,[])).
% 27.47/3.99  
% 27.47/3.99  fof(f15,plain,(
% 27.47/3.99    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK1(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1))))),
% 27.47/3.99    introduced(choice_axiom,[])).
% 27.47/3.99  
% 27.47/3.99  fof(f18,plain,(
% 27.47/3.99    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & ((k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 27.47/3.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f14,f17,f16,f15])).
% 27.47/3.99  
% 27.47/3.99  fof(f33,plain,(
% 27.47/3.99    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 27.47/3.99    inference(cnf_transformation,[],[f18])).
% 27.47/3.99  
% 27.47/3.99  fof(f59,plain,(
% 27.47/3.99    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 27.47/3.99    inference(equality_resolution,[],[f33])).
% 27.47/3.99  
% 27.47/3.99  fof(f60,plain,(
% 27.47/3.99    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 27.47/3.99    inference(equality_resolution,[],[f59])).
% 27.47/3.99  
% 27.47/3.99  fof(f47,plain,(
% 27.47/3.99    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k1_funct_1(X0,sK5(X0,X1)) = sK4(X0,X1) | ~sP0(sK4(X0,X1),sK5(X0,X1),X0,X1) | k2_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 27.47/3.99    inference(cnf_transformation,[],[f26])).
% 27.47/3.99  
% 27.47/3.99  fof(f39,plain,(
% 27.47/3.99    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2,X3) | r2_hidden(X0,k2_relat_1(X2))) )),
% 27.47/3.99    inference(cnf_transformation,[],[f21])).
% 27.47/3.99  
% 27.47/3.99  fof(f31,plain,(
% 27.47/3.99    ( ! [X0,X5,X1] : (r2_hidden(sK3(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 27.47/3.99    inference(cnf_transformation,[],[f18])).
% 27.47/3.99  
% 27.47/3.99  fof(f62,plain,(
% 27.47/3.99    ( ! [X0,X5] : (r2_hidden(sK3(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 27.47/3.99    inference(equality_resolution,[],[f31])).
% 27.47/3.99  
% 27.47/3.99  fof(f32,plain,(
% 27.47/3.99    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK3(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 27.47/3.99    inference(cnf_transformation,[],[f18])).
% 27.47/3.99  
% 27.47/3.99  fof(f61,plain,(
% 27.47/3.99    ( ! [X0,X5] : (k1_funct_1(X0,sK3(X0,X5)) = X5 | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 27.47/3.99    inference(equality_resolution,[],[f32])).
% 27.47/3.99  
% 27.47/3.99  fof(f57,plain,(
% 27.47/3.99    ( ! [X2,X3] : (k1_funct_1(sK6,X2) = X3 | k1_funct_1(sK7,X3) != X2 | ~r2_hidden(X3,k1_relat_1(sK7)) | ~r2_hidden(X2,k1_relat_1(sK6))) )),
% 27.47/3.99    inference(cnf_transformation,[],[f30])).
% 27.47/3.99  
% 27.47/3.99  fof(f72,plain,(
% 27.47/3.99    ( ! [X3] : (k1_funct_1(sK6,k1_funct_1(sK7,X3)) = X3 | ~r2_hidden(X3,k1_relat_1(sK7)) | ~r2_hidden(k1_funct_1(sK7,X3),k1_relat_1(sK6))) )),
% 27.47/3.99    inference(equality_resolution,[],[f57])).
% 27.47/3.99  
% 27.47/3.99  fof(f41,plain,(
% 27.47/3.99    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2,X3) | k1_funct_1(X2,X1) != X0 | ~r2_hidden(X1,k1_relat_1(X2))) )),
% 27.47/3.99    inference(cnf_transformation,[],[f21])).
% 27.47/3.99  
% 27.47/3.99  fof(f63,plain,(
% 27.47/3.99    ( ! [X2,X3,X1] : (sP0(k1_funct_1(X2,X1),X1,X2,X3) | ~r2_hidden(X1,k1_relat_1(X2))) )),
% 27.47/3.99    inference(equality_resolution,[],[f41])).
% 27.47/3.99  
% 27.47/3.99  fof(f48,plain,(
% 27.47/3.99    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k1_funct_1(X1,sK4(X0,X1)) != sK5(X0,X1) | ~r2_hidden(sK4(X0,X1),k2_relat_1(X0)) | ~sP0(sK4(X0,X1),sK5(X0,X1),X0,X1) | k2_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 27.47/3.99    inference(cnf_transformation,[],[f26])).
% 27.47/3.99  
% 27.47/3.99  cnf(c_1315,plain,
% 27.47/3.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 27.47/3.99      theory(equality) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_1887,plain,
% 27.47/3.99      ( ~ r2_hidden(X0,X1)
% 27.47/3.99      | r2_hidden(X2,k1_relat_1(sK6))
% 27.47/3.99      | X2 != X0
% 27.47/3.99      | k1_relat_1(sK6) != X1 ),
% 27.47/3.99      inference(instantiation,[status(thm)],[c_1315]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_6059,plain,
% 27.47/3.99      ( r2_hidden(X0,k1_relat_1(sK6))
% 27.47/3.99      | ~ r2_hidden(sK5(sK6,sK7),k2_relat_1(sK7))
% 27.47/3.99      | X0 != sK5(sK6,sK7)
% 27.47/3.99      | k1_relat_1(sK6) != k2_relat_1(sK7) ),
% 27.47/3.99      inference(instantiation,[status(thm)],[c_1887]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_67223,plain,
% 27.47/3.99      ( r2_hidden(sK5(sK6,sK7),k1_relat_1(sK6))
% 27.47/3.99      | ~ r2_hidden(sK5(sK6,sK7),k2_relat_1(sK7))
% 27.47/3.99      | sK5(sK6,sK7) != sK5(sK6,sK7)
% 27.47/3.99      | k1_relat_1(sK6) != k2_relat_1(sK7) ),
% 27.47/3.99      inference(instantiation,[status(thm)],[c_6059]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_7,plain,
% 27.47/3.99      ( sP0(X0,X1,X2,X3) | k1_funct_1(X3,X0) = X1 ),
% 27.47/3.99      inference(cnf_transformation,[],[f40]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_1777,plain,
% 27.47/3.99      ( k1_funct_1(X0,X1) = X2 | sP0(X1,X2,X3,X0) = iProver_top ),
% 27.47/3.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_13,plain,
% 27.47/3.99      ( ~ sP0(sK4(X0,X1),sK5(X0,X1),X0,X1)
% 27.47/3.99      | r2_hidden(sK5(X0,X1),k1_relat_1(X0))
% 27.47/3.99      | ~ v2_funct_1(X0)
% 27.47/3.99      | ~ v1_relat_1(X0)
% 27.47/3.99      | ~ v1_relat_1(X1)
% 27.47/3.99      | ~ v1_funct_1(X0)
% 27.47/3.99      | ~ v1_funct_1(X1)
% 27.47/3.99      | k2_funct_1(X0) = X1
% 27.47/3.99      | k1_relat_1(X1) != k2_relat_1(X0) ),
% 27.47/3.99      inference(cnf_transformation,[],[f46]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_23,negated_conjecture,
% 27.47/3.99      ( v2_funct_1(sK6) ),
% 27.47/3.99      inference(cnf_transformation,[],[f53]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_300,plain,
% 27.47/3.99      ( ~ sP0(sK4(X0,X1),sK5(X0,X1),X0,X1)
% 27.47/3.99      | r2_hidden(sK5(X0,X1),k1_relat_1(X0))
% 27.47/3.99      | ~ v1_relat_1(X0)
% 27.47/3.99      | ~ v1_relat_1(X1)
% 27.47/3.99      | ~ v1_funct_1(X0)
% 27.47/3.99      | ~ v1_funct_1(X1)
% 27.47/3.99      | k2_funct_1(X0) = X1
% 27.47/3.99      | k1_relat_1(X1) != k2_relat_1(X0)
% 27.47/3.99      | sK6 != X0 ),
% 27.47/3.99      inference(resolution_lifted,[status(thm)],[c_13,c_23]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_301,plain,
% 27.47/3.99      ( ~ sP0(sK4(sK6,X0),sK5(sK6,X0),sK6,X0)
% 27.47/3.99      | r2_hidden(sK5(sK6,X0),k1_relat_1(sK6))
% 27.47/3.99      | ~ v1_relat_1(X0)
% 27.47/3.99      | ~ v1_relat_1(sK6)
% 27.47/3.99      | ~ v1_funct_1(X0)
% 27.47/3.99      | ~ v1_funct_1(sK6)
% 27.47/3.99      | k2_funct_1(sK6) = X0
% 27.47/3.99      | k1_relat_1(X0) != k2_relat_1(sK6) ),
% 27.47/3.99      inference(unflattening,[status(thm)],[c_300]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_27,negated_conjecture,
% 27.47/3.99      ( v1_relat_1(sK6) ),
% 27.47/3.99      inference(cnf_transformation,[],[f49]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_26,negated_conjecture,
% 27.47/3.99      ( v1_funct_1(sK6) ),
% 27.47/3.99      inference(cnf_transformation,[],[f50]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_305,plain,
% 27.47/3.99      ( ~ v1_funct_1(X0)
% 27.47/3.99      | ~ sP0(sK4(sK6,X0),sK5(sK6,X0),sK6,X0)
% 27.47/3.99      | r2_hidden(sK5(sK6,X0),k1_relat_1(sK6))
% 27.47/3.99      | ~ v1_relat_1(X0)
% 27.47/3.99      | k2_funct_1(sK6) = X0
% 27.47/3.99      | k1_relat_1(X0) != k2_relat_1(sK6) ),
% 27.47/3.99      inference(global_propositional_subsumption,
% 27.47/3.99                [status(thm)],
% 27.47/3.99                [c_301,c_27,c_26]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_306,plain,
% 27.47/3.99      ( ~ sP0(sK4(sK6,X0),sK5(sK6,X0),sK6,X0)
% 27.47/3.99      | r2_hidden(sK5(sK6,X0),k1_relat_1(sK6))
% 27.47/3.99      | ~ v1_relat_1(X0)
% 27.47/3.99      | ~ v1_funct_1(X0)
% 27.47/3.99      | k2_funct_1(sK6) = X0
% 27.47/3.99      | k1_relat_1(X0) != k2_relat_1(sK6) ),
% 27.47/3.99      inference(renaming,[status(thm)],[c_305]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_24,negated_conjecture,
% 27.47/3.99      ( v1_funct_1(sK7) ),
% 27.47/3.99      inference(cnf_transformation,[],[f52]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_504,plain,
% 27.47/3.99      ( ~ sP0(sK4(sK6,X0),sK5(sK6,X0),sK6,X0)
% 27.47/3.99      | r2_hidden(sK5(sK6,X0),k1_relat_1(sK6))
% 27.47/3.99      | ~ v1_relat_1(X0)
% 27.47/3.99      | k2_funct_1(sK6) = X0
% 27.47/3.99      | k1_relat_1(X0) != k2_relat_1(sK6)
% 27.47/3.99      | sK7 != X0 ),
% 27.47/3.99      inference(resolution_lifted,[status(thm)],[c_306,c_24]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_505,plain,
% 27.47/3.99      ( ~ sP0(sK4(sK6,sK7),sK5(sK6,sK7),sK6,sK7)
% 27.47/3.99      | r2_hidden(sK5(sK6,sK7),k1_relat_1(sK6))
% 27.47/3.99      | ~ v1_relat_1(sK7)
% 27.47/3.99      | k2_funct_1(sK6) = sK7
% 27.47/3.99      | k1_relat_1(sK7) != k2_relat_1(sK6) ),
% 27.47/3.99      inference(unflattening,[status(thm)],[c_504]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_25,negated_conjecture,
% 27.47/3.99      ( v1_relat_1(sK7) ),
% 27.47/3.99      inference(cnf_transformation,[],[f51]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_18,negated_conjecture,
% 27.47/3.99      ( k2_funct_1(sK6) != sK7 ),
% 27.47/3.99      inference(cnf_transformation,[],[f58]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_507,plain,
% 27.47/3.99      ( ~ sP0(sK4(sK6,sK7),sK5(sK6,sK7),sK6,sK7)
% 27.47/3.99      | r2_hidden(sK5(sK6,sK7),k1_relat_1(sK6))
% 27.47/3.99      | k1_relat_1(sK7) != k2_relat_1(sK6) ),
% 27.47/3.99      inference(global_propositional_subsumption,
% 27.47/3.99                [status(thm)],
% 27.47/3.99                [c_505,c_25,c_18]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_1769,plain,
% 27.47/3.99      ( k1_relat_1(sK7) != k2_relat_1(sK6)
% 27.47/3.99      | sP0(sK4(sK6,sK7),sK5(sK6,sK7),sK6,sK7) != iProver_top
% 27.47/3.99      | r2_hidden(sK5(sK6,sK7),k1_relat_1(sK6)) = iProver_top ),
% 27.47/3.99      inference(predicate_to_equality,[status(thm)],[c_507]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_21,negated_conjecture,
% 27.47/3.99      ( k2_relat_1(sK6) = k1_relat_1(sK7) ),
% 27.47/3.99      inference(cnf_transformation,[],[f55]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_22,negated_conjecture,
% 27.47/3.99      ( k2_relat_1(sK7) = k1_relat_1(sK6) ),
% 27.47/3.99      inference(cnf_transformation,[],[f54]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_1788,plain,
% 27.47/3.99      ( k2_relat_1(sK6) != k2_relat_1(sK6)
% 27.47/3.99      | sP0(sK4(sK6,sK7),sK5(sK6,sK7),sK6,sK7) != iProver_top
% 27.47/3.99      | r2_hidden(sK5(sK6,sK7),k2_relat_1(sK7)) = iProver_top ),
% 27.47/3.99      inference(light_normalisation,[status(thm)],[c_1769,c_21,c_22]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_1789,plain,
% 27.47/3.99      ( sP0(sK4(sK6,sK7),sK5(sK6,sK7),sK6,sK7) != iProver_top
% 27.47/3.99      | r2_hidden(sK5(sK6,sK7),k2_relat_1(sK7)) = iProver_top ),
% 27.47/3.99      inference(equality_resolution_simp,[status(thm)],[c_1788]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_2914,plain,
% 27.47/3.99      ( k1_funct_1(sK7,sK4(sK6,sK7)) = sK5(sK6,sK7)
% 27.47/3.99      | r2_hidden(sK5(sK6,sK7),k2_relat_1(sK7)) = iProver_top ),
% 27.47/3.99      inference(superposition,[status(thm)],[c_1777,c_1789]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_20,negated_conjecture,
% 27.47/3.99      ( ~ r2_hidden(X0,k1_relat_1(sK6))
% 27.47/3.99      | ~ r2_hidden(k1_funct_1(sK6,X0),k1_relat_1(sK7))
% 27.47/3.99      | k1_funct_1(sK7,k1_funct_1(sK6,X0)) = X0 ),
% 27.47/3.99      inference(cnf_transformation,[],[f73]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_1772,plain,
% 27.47/3.99      ( k1_funct_1(sK7,k1_funct_1(sK6,X0)) = X0
% 27.47/3.99      | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 27.47/3.99      | r2_hidden(k1_funct_1(sK6,X0),k1_relat_1(sK7)) != iProver_top ),
% 27.47/3.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_1786,plain,
% 27.47/3.99      ( k1_funct_1(sK7,k1_funct_1(sK6,X0)) = X0
% 27.47/3.99      | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
% 27.47/3.99      | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) != iProver_top ),
% 27.47/3.99      inference(light_normalisation,[status(thm)],[c_1772,c_21,c_22]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_3,plain,
% 27.47/3.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 27.47/3.99      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 27.47/3.99      | ~ v1_relat_1(X1)
% 27.47/3.99      | ~ v1_funct_1(X1) ),
% 27.47/3.99      inference(cnf_transformation,[],[f60]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_782,plain,
% 27.47/3.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 27.47/3.99      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 27.47/3.99      | ~ v1_relat_1(X1)
% 27.47/3.99      | sK6 != X1 ),
% 27.47/3.99      inference(resolution_lifted,[status(thm)],[c_3,c_26]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_783,plain,
% 27.47/3.99      ( ~ r2_hidden(X0,k1_relat_1(sK6))
% 27.47/3.99      | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6))
% 27.47/3.99      | ~ v1_relat_1(sK6) ),
% 27.47/3.99      inference(unflattening,[status(thm)],[c_782]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_787,plain,
% 27.47/3.99      ( r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6))
% 27.47/3.99      | ~ r2_hidden(X0,k1_relat_1(sK6)) ),
% 27.47/3.99      inference(global_propositional_subsumption,
% 27.47/3.99                [status(thm)],
% 27.47/3.99                [c_783,c_27]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_788,plain,
% 27.47/3.99      ( ~ r2_hidden(X0,k1_relat_1(sK6))
% 27.47/3.99      | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) ),
% 27.47/3.99      inference(renaming,[status(thm)],[c_787]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_1755,plain,
% 27.47/3.99      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 27.47/3.99      | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) = iProver_top ),
% 27.47/3.99      inference(predicate_to_equality,[status(thm)],[c_788]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_1779,plain,
% 27.47/3.99      ( r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
% 27.47/3.99      | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) = iProver_top ),
% 27.47/3.99      inference(light_normalisation,[status(thm)],[c_1755,c_22]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_2227,plain,
% 27.47/3.99      ( r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
% 27.47/3.99      | k1_funct_1(sK7,k1_funct_1(sK6,X0)) = X0 ),
% 27.47/3.99      inference(global_propositional_subsumption,
% 27.47/3.99                [status(thm)],
% 27.47/3.99                [c_1786,c_1779]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_2228,plain,
% 27.47/3.99      ( k1_funct_1(sK7,k1_funct_1(sK6,X0)) = X0
% 27.47/3.99      | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
% 27.47/3.99      inference(renaming,[status(thm)],[c_2227]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_3023,plain,
% 27.47/3.99      ( k1_funct_1(sK7,sK4(sK6,sK7)) = sK5(sK6,sK7)
% 27.47/3.99      | k1_funct_1(sK7,k1_funct_1(sK6,sK5(sK6,sK7))) = sK5(sK6,sK7) ),
% 27.47/3.99      inference(superposition,[status(thm)],[c_2914,c_2228]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_12,plain,
% 27.47/3.99      ( ~ sP0(sK4(X0,X1),sK5(X0,X1),X0,X1)
% 27.47/3.99      | ~ v2_funct_1(X0)
% 27.47/3.99      | ~ v1_relat_1(X0)
% 27.47/3.99      | ~ v1_relat_1(X1)
% 27.47/3.99      | ~ v1_funct_1(X0)
% 27.47/3.99      | ~ v1_funct_1(X1)
% 27.47/3.99      | k1_funct_1(X0,sK5(X0,X1)) = sK4(X0,X1)
% 27.47/3.99      | k2_funct_1(X0) = X1
% 27.47/3.99      | k1_relat_1(X1) != k2_relat_1(X0) ),
% 27.47/3.99      inference(cnf_transformation,[],[f47]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_328,plain,
% 27.47/3.99      ( ~ sP0(sK4(X0,X1),sK5(X0,X1),X0,X1)
% 27.47/3.99      | ~ v1_relat_1(X0)
% 27.47/3.99      | ~ v1_relat_1(X1)
% 27.47/3.99      | ~ v1_funct_1(X0)
% 27.47/3.99      | ~ v1_funct_1(X1)
% 27.47/3.99      | k1_funct_1(X0,sK5(X0,X1)) = sK4(X0,X1)
% 27.47/3.99      | k2_funct_1(X0) = X1
% 27.47/3.99      | k1_relat_1(X1) != k2_relat_1(X0)
% 27.47/3.99      | sK6 != X0 ),
% 27.47/3.99      inference(resolution_lifted,[status(thm)],[c_12,c_23]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_329,plain,
% 27.47/3.99      ( ~ sP0(sK4(sK6,X0),sK5(sK6,X0),sK6,X0)
% 27.47/3.99      | ~ v1_relat_1(X0)
% 27.47/3.99      | ~ v1_relat_1(sK6)
% 27.47/3.99      | ~ v1_funct_1(X0)
% 27.47/3.99      | ~ v1_funct_1(sK6)
% 27.47/3.99      | k1_funct_1(sK6,sK5(sK6,X0)) = sK4(sK6,X0)
% 27.47/3.99      | k2_funct_1(sK6) = X0
% 27.47/3.99      | k1_relat_1(X0) != k2_relat_1(sK6) ),
% 27.47/3.99      inference(unflattening,[status(thm)],[c_328]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_333,plain,
% 27.47/3.99      ( ~ v1_funct_1(X0)
% 27.47/3.99      | ~ sP0(sK4(sK6,X0),sK5(sK6,X0),sK6,X0)
% 27.47/3.99      | ~ v1_relat_1(X0)
% 27.47/3.99      | k1_funct_1(sK6,sK5(sK6,X0)) = sK4(sK6,X0)
% 27.47/3.99      | k2_funct_1(sK6) = X0
% 27.47/3.99      | k1_relat_1(X0) != k2_relat_1(sK6) ),
% 27.47/3.99      inference(global_propositional_subsumption,
% 27.47/3.99                [status(thm)],
% 27.47/3.99                [c_329,c_27,c_26]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_334,plain,
% 27.47/3.99      ( ~ sP0(sK4(sK6,X0),sK5(sK6,X0),sK6,X0)
% 27.47/3.99      | ~ v1_relat_1(X0)
% 27.47/3.99      | ~ v1_funct_1(X0)
% 27.47/3.99      | k1_funct_1(sK6,sK5(sK6,X0)) = sK4(sK6,X0)
% 27.47/3.99      | k2_funct_1(sK6) = X0
% 27.47/3.99      | k1_relat_1(X0) != k2_relat_1(sK6) ),
% 27.47/3.99      inference(renaming,[status(thm)],[c_333]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_487,plain,
% 27.47/3.99      ( ~ sP0(sK4(sK6,X0),sK5(sK6,X0),sK6,X0)
% 27.47/3.99      | ~ v1_relat_1(X0)
% 27.47/3.99      | k1_funct_1(sK6,sK5(sK6,X0)) = sK4(sK6,X0)
% 27.47/3.99      | k2_funct_1(sK6) = X0
% 27.47/3.99      | k1_relat_1(X0) != k2_relat_1(sK6)
% 27.47/3.99      | sK7 != X0 ),
% 27.47/3.99      inference(resolution_lifted,[status(thm)],[c_334,c_24]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_488,plain,
% 27.47/3.99      ( ~ sP0(sK4(sK6,sK7),sK5(sK6,sK7),sK6,sK7)
% 27.47/3.99      | ~ v1_relat_1(sK7)
% 27.47/3.99      | k1_funct_1(sK6,sK5(sK6,sK7)) = sK4(sK6,sK7)
% 27.47/3.99      | k2_funct_1(sK6) = sK7
% 27.47/3.99      | k1_relat_1(sK7) != k2_relat_1(sK6) ),
% 27.47/3.99      inference(unflattening,[status(thm)],[c_487]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_490,plain,
% 27.47/3.99      ( k1_funct_1(sK6,sK5(sK6,sK7)) = sK4(sK6,sK7)
% 27.47/3.99      | ~ sP0(sK4(sK6,sK7),sK5(sK6,sK7),sK6,sK7)
% 27.47/3.99      | k1_relat_1(sK7) != k2_relat_1(sK6) ),
% 27.47/3.99      inference(global_propositional_subsumption,
% 27.47/3.99                [status(thm)],
% 27.47/3.99                [c_488,c_25,c_18]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_491,plain,
% 27.47/3.99      ( ~ sP0(sK4(sK6,sK7),sK5(sK6,sK7),sK6,sK7)
% 27.47/3.99      | k1_funct_1(sK6,sK5(sK6,sK7)) = sK4(sK6,sK7)
% 27.47/3.99      | k1_relat_1(sK7) != k2_relat_1(sK6) ),
% 27.47/3.99      inference(renaming,[status(thm)],[c_490]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_1770,plain,
% 27.47/3.99      ( k1_funct_1(sK6,sK5(sK6,sK7)) = sK4(sK6,sK7)
% 27.47/3.99      | k1_relat_1(sK7) != k2_relat_1(sK6)
% 27.47/3.99      | sP0(sK4(sK6,sK7),sK5(sK6,sK7),sK6,sK7) != iProver_top ),
% 27.47/3.99      inference(predicate_to_equality,[status(thm)],[c_491]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_1790,plain,
% 27.47/3.99      ( k1_funct_1(sK6,sK5(sK6,sK7)) = sK4(sK6,sK7)
% 27.47/3.99      | k2_relat_1(sK6) != k2_relat_1(sK6)
% 27.47/3.99      | sP0(sK4(sK6,sK7),sK5(sK6,sK7),sK6,sK7) != iProver_top ),
% 27.47/3.99      inference(light_normalisation,[status(thm)],[c_1770,c_21]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_1791,plain,
% 27.47/3.99      ( k1_funct_1(sK6,sK5(sK6,sK7)) = sK4(sK6,sK7)
% 27.47/3.99      | sP0(sK4(sK6,sK7),sK5(sK6,sK7),sK6,sK7) != iProver_top ),
% 27.47/3.99      inference(equality_resolution_simp,[status(thm)],[c_1790]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_3079,plain,
% 27.47/3.99      ( k1_funct_1(sK7,sK4(sK6,sK7)) = sK5(sK6,sK7)
% 27.47/3.99      | k1_funct_1(sK6,sK5(sK6,sK7)) = sK4(sK6,sK7) ),
% 27.47/3.99      inference(superposition,[status(thm)],[c_1777,c_1791]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_8,plain,
% 27.47/3.99      ( sP0(X0,X1,X2,X3) | r2_hidden(X0,k2_relat_1(X2)) ),
% 27.47/3.99      inference(cnf_transformation,[],[f39]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_1776,plain,
% 27.47/3.99      ( sP0(X0,X1,X2,X3) = iProver_top
% 27.47/3.99      | r2_hidden(X0,k2_relat_1(X2)) = iProver_top ),
% 27.47/3.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_2913,plain,
% 27.47/3.99      ( r2_hidden(sK5(sK6,sK7),k2_relat_1(sK7)) = iProver_top
% 27.47/3.99      | r2_hidden(sK4(sK6,sK7),k2_relat_1(sK6)) = iProver_top ),
% 27.47/3.99      inference(superposition,[status(thm)],[c_1776,c_1789]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_5,plain,
% 27.47/3.99      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 27.47/3.99      | r2_hidden(sK3(X1,X0),k1_relat_1(X1))
% 27.47/3.99      | ~ v1_relat_1(X1)
% 27.47/3.99      | ~ v1_funct_1(X1) ),
% 27.47/3.99      inference(cnf_transformation,[],[f62]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_668,plain,
% 27.47/3.99      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 27.47/3.99      | r2_hidden(sK3(X1,X0),k1_relat_1(X1))
% 27.47/3.99      | ~ v1_relat_1(X1)
% 27.47/3.99      | sK7 != X1 ),
% 27.47/3.99      inference(resolution_lifted,[status(thm)],[c_5,c_24]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_669,plain,
% 27.47/3.99      ( ~ r2_hidden(X0,k2_relat_1(sK7))
% 27.47/3.99      | r2_hidden(sK3(sK7,X0),k1_relat_1(sK7))
% 27.47/3.99      | ~ v1_relat_1(sK7) ),
% 27.47/3.99      inference(unflattening,[status(thm)],[c_668]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_673,plain,
% 27.47/3.99      ( r2_hidden(sK3(sK7,X0),k1_relat_1(sK7))
% 27.47/3.99      | ~ r2_hidden(X0,k2_relat_1(sK7)) ),
% 27.47/3.99      inference(global_propositional_subsumption,
% 27.47/3.99                [status(thm)],
% 27.47/3.99                [c_669,c_25]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_674,plain,
% 27.47/3.99      ( ~ r2_hidden(X0,k2_relat_1(sK7))
% 27.47/3.99      | r2_hidden(sK3(sK7,X0),k1_relat_1(sK7)) ),
% 27.47/3.99      inference(renaming,[status(thm)],[c_673]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_1761,plain,
% 27.47/3.99      ( r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
% 27.47/3.99      | r2_hidden(sK3(sK7,X0),k1_relat_1(sK7)) = iProver_top ),
% 27.47/3.99      inference(predicate_to_equality,[status(thm)],[c_674]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_1782,plain,
% 27.47/3.99      ( r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
% 27.47/3.99      | r2_hidden(sK3(sK7,X0),k2_relat_1(sK6)) = iProver_top ),
% 27.47/3.99      inference(light_normalisation,[status(thm)],[c_1761,c_21]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_4,plain,
% 27.47/3.99      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 27.47/3.99      | ~ v1_relat_1(X1)
% 27.47/3.99      | ~ v1_funct_1(X1)
% 27.47/3.99      | k1_funct_1(X1,sK3(X1,X0)) = X0 ),
% 27.47/3.99      inference(cnf_transformation,[],[f61]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_764,plain,
% 27.47/3.99      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 27.47/3.99      | ~ v1_relat_1(X1)
% 27.47/3.99      | k1_funct_1(X1,sK3(X1,X0)) = X0
% 27.47/3.99      | sK6 != X1 ),
% 27.47/3.99      inference(resolution_lifted,[status(thm)],[c_4,c_26]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_765,plain,
% 27.47/3.99      ( ~ r2_hidden(X0,k2_relat_1(sK6))
% 27.47/3.99      | ~ v1_relat_1(sK6)
% 27.47/3.99      | k1_funct_1(sK6,sK3(sK6,X0)) = X0 ),
% 27.47/3.99      inference(unflattening,[status(thm)],[c_764]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_769,plain,
% 27.47/3.99      ( ~ r2_hidden(X0,k2_relat_1(sK6))
% 27.47/3.99      | k1_funct_1(sK6,sK3(sK6,X0)) = X0 ),
% 27.47/3.99      inference(global_propositional_subsumption,
% 27.47/3.99                [status(thm)],
% 27.47/3.99                [c_765,c_27]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_1756,plain,
% 27.47/3.99      ( k1_funct_1(sK6,sK3(sK6,X0)) = X0
% 27.47/3.99      | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top ),
% 27.47/3.99      inference(predicate_to_equality,[status(thm)],[c_769]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_2367,plain,
% 27.47/3.99      ( k1_funct_1(sK6,sK3(sK6,sK3(sK7,X0))) = sK3(sK7,X0)
% 27.47/3.99      | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
% 27.47/3.99      inference(superposition,[status(thm)],[c_1782,c_1756]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_3005,plain,
% 27.47/3.99      ( k1_funct_1(sK6,sK3(sK6,sK3(sK7,sK5(sK6,sK7)))) = sK3(sK7,sK5(sK6,sK7))
% 27.47/3.99      | r2_hidden(sK4(sK6,sK7),k2_relat_1(sK6)) = iProver_top ),
% 27.47/3.99      inference(superposition,[status(thm)],[c_2913,c_2367]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_1159,plain,
% 27.47/3.99      ( r2_hidden(X0,k2_relat_1(X1))
% 27.47/3.99      | r2_hidden(sK5(sK6,sK7),k1_relat_1(sK6))
% 27.47/3.99      | sK5(sK6,sK7) != X2
% 27.47/3.99      | sK4(sK6,sK7) != X0
% 27.47/3.99      | k1_relat_1(sK7) != k2_relat_1(sK6)
% 27.47/3.99      | sK7 != X3
% 27.47/3.99      | sK6 != X1 ),
% 27.47/3.99      inference(resolution_lifted,[status(thm)],[c_8,c_507]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_1160,plain,
% 27.47/3.99      ( r2_hidden(sK5(sK6,sK7),k1_relat_1(sK6))
% 27.47/3.99      | r2_hidden(sK4(sK6,sK7),k2_relat_1(sK6))
% 27.47/3.99      | k1_relat_1(sK7) != k2_relat_1(sK6) ),
% 27.47/3.99      inference(unflattening,[status(thm)],[c_1159]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_1161,plain,
% 27.47/3.99      ( k1_relat_1(sK7) != k2_relat_1(sK6)
% 27.47/3.99      | r2_hidden(sK5(sK6,sK7),k1_relat_1(sK6)) = iProver_top
% 27.47/3.99      | r2_hidden(sK4(sK6,sK7),k2_relat_1(sK6)) = iProver_top ),
% 27.47/3.99      inference(predicate_to_equality,[status(thm)],[c_1160]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_1172,plain,
% 27.47/3.99      ( r2_hidden(X0,k2_relat_1(X1))
% 27.47/3.99      | sK5(sK6,sK7) != X2
% 27.47/3.99      | sK4(sK6,sK7) != X0
% 27.47/3.99      | k1_funct_1(sK6,sK5(sK6,sK7)) = sK4(sK6,sK7)
% 27.47/3.99      | k1_relat_1(sK7) != k2_relat_1(sK6)
% 27.47/3.99      | sK7 != X3
% 27.47/3.99      | sK6 != X1 ),
% 27.47/3.99      inference(resolution_lifted,[status(thm)],[c_8,c_491]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_1173,plain,
% 27.47/3.99      ( r2_hidden(sK4(sK6,sK7),k2_relat_1(sK6))
% 27.47/3.99      | k1_funct_1(sK6,sK5(sK6,sK7)) = sK4(sK6,sK7)
% 27.47/3.99      | k1_relat_1(sK7) != k2_relat_1(sK6) ),
% 27.47/3.99      inference(unflattening,[status(thm)],[c_1172]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_1174,plain,
% 27.47/3.99      ( k1_funct_1(sK6,sK5(sK6,sK7)) = sK4(sK6,sK7)
% 27.47/3.99      | k1_relat_1(sK7) != k2_relat_1(sK6)
% 27.47/3.99      | r2_hidden(sK4(sK6,sK7),k2_relat_1(sK6)) = iProver_top ),
% 27.47/3.99      inference(predicate_to_equality,[status(thm)],[c_1173]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_1310,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_1897,plain,
% 27.47/3.99      ( k1_relat_1(sK7) != X0
% 27.47/3.99      | k1_relat_1(sK7) = k2_relat_1(sK6)
% 27.47/3.99      | k2_relat_1(sK6) != X0 ),
% 27.47/3.99      inference(instantiation,[status(thm)],[c_1310]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_1972,plain,
% 27.47/3.99      ( k1_relat_1(sK7) != k1_relat_1(sK7)
% 27.47/3.99      | k1_relat_1(sK7) = k2_relat_1(sK6)
% 27.47/3.99      | k2_relat_1(sK6) != k1_relat_1(sK7) ),
% 27.47/3.99      inference(instantiation,[status(thm)],[c_1897]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_1309,plain,( X0 = X0 ),theory(equality) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_2049,plain,
% 27.47/3.99      ( k1_relat_1(sK7) = k1_relat_1(sK7) ),
% 27.47/3.99      inference(instantiation,[status(thm)],[c_1309]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_2320,plain,
% 27.47/3.99      ( sK4(sK6,sK7) = sK4(sK6,sK7) ),
% 27.47/3.99      inference(instantiation,[status(thm)],[c_1309]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_2436,plain,
% 27.47/3.99      ( ~ r2_hidden(sK5(sK6,sK7),k1_relat_1(sK6))
% 27.47/3.99      | r2_hidden(k1_funct_1(sK6,sK5(sK6,sK7)),k2_relat_1(sK6)) ),
% 27.47/3.99      inference(instantiation,[status(thm)],[c_788]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_2440,plain,
% 27.47/3.99      ( r2_hidden(sK5(sK6,sK7),k1_relat_1(sK6)) != iProver_top
% 27.47/3.99      | r2_hidden(k1_funct_1(sK6,sK5(sK6,sK7)),k2_relat_1(sK6)) = iProver_top ),
% 27.47/3.99      inference(predicate_to_equality,[status(thm)],[c_2436]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_1997,plain,
% 27.47/3.99      ( X0 != X1 | sK4(sK6,sK7) != X1 | sK4(sK6,sK7) = X0 ),
% 27.47/3.99      inference(instantiation,[status(thm)],[c_1310]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_2327,plain,
% 27.47/3.99      ( X0 != sK4(sK6,sK7)
% 27.47/3.99      | sK4(sK6,sK7) = X0
% 27.47/3.99      | sK4(sK6,sK7) != sK4(sK6,sK7) ),
% 27.47/3.99      inference(instantiation,[status(thm)],[c_1997]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_4223,plain,
% 27.47/3.99      ( sK4(sK6,sK7) != sK4(sK6,sK7)
% 27.47/3.99      | sK4(sK6,sK7) = k1_funct_1(sK6,sK5(sK6,sK7))
% 27.47/3.99      | k1_funct_1(sK6,sK5(sK6,sK7)) != sK4(sK6,sK7) ),
% 27.47/3.99      inference(instantiation,[status(thm)],[c_2327]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_1877,plain,
% 27.47/3.99      ( ~ r2_hidden(X0,X1)
% 27.47/3.99      | r2_hidden(X2,k1_relat_1(sK7))
% 27.47/3.99      | X2 != X0
% 27.47/3.99      | k1_relat_1(sK7) != X1 ),
% 27.47/3.99      inference(instantiation,[status(thm)],[c_1315]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_3124,plain,
% 27.47/3.99      ( r2_hidden(X0,k1_relat_1(sK7))
% 27.47/3.99      | ~ r2_hidden(k1_funct_1(sK6,sK5(sK6,sK7)),k2_relat_1(sK6))
% 27.47/3.99      | X0 != k1_funct_1(sK6,sK5(sK6,sK7))
% 27.47/3.99      | k1_relat_1(sK7) != k2_relat_1(sK6) ),
% 27.47/3.99      inference(instantiation,[status(thm)],[c_1877]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_5492,plain,
% 27.47/3.99      ( r2_hidden(sK4(sK6,sK7),k1_relat_1(sK7))
% 27.47/3.99      | ~ r2_hidden(k1_funct_1(sK6,sK5(sK6,sK7)),k2_relat_1(sK6))
% 27.47/3.99      | sK4(sK6,sK7) != k1_funct_1(sK6,sK5(sK6,sK7))
% 27.47/3.99      | k1_relat_1(sK7) != k2_relat_1(sK6) ),
% 27.47/3.99      inference(instantiation,[status(thm)],[c_3124]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_5493,plain,
% 27.47/3.99      ( sK4(sK6,sK7) != k1_funct_1(sK6,sK5(sK6,sK7))
% 27.47/3.99      | k1_relat_1(sK7) != k2_relat_1(sK6)
% 27.47/3.99      | r2_hidden(sK4(sK6,sK7),k1_relat_1(sK7)) = iProver_top
% 27.47/3.99      | r2_hidden(k1_funct_1(sK6,sK5(sK6,sK7)),k2_relat_1(sK6)) != iProver_top ),
% 27.47/3.99      inference(predicate_to_equality,[status(thm)],[c_5492]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_1892,plain,
% 27.47/3.99      ( ~ r2_hidden(X0,X1)
% 27.47/3.99      | r2_hidden(sK4(sK6,sK7),k2_relat_1(sK6))
% 27.47/3.99      | sK4(sK6,sK7) != X0
% 27.47/3.99      | k2_relat_1(sK6) != X1 ),
% 27.47/3.99      inference(instantiation,[status(thm)],[c_1315]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_1992,plain,
% 27.47/3.99      ( ~ r2_hidden(sK4(sK6,sK7),X0)
% 27.47/3.99      | r2_hidden(sK4(sK6,sK7),k2_relat_1(sK6))
% 27.47/3.99      | sK4(sK6,sK7) != sK4(sK6,sK7)
% 27.47/3.99      | k2_relat_1(sK6) != X0 ),
% 27.47/3.99      inference(instantiation,[status(thm)],[c_1892]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_12239,plain,
% 27.47/3.99      ( ~ r2_hidden(sK4(sK6,sK7),k1_relat_1(sK7))
% 27.47/3.99      | r2_hidden(sK4(sK6,sK7),k2_relat_1(sK6))
% 27.47/3.99      | sK4(sK6,sK7) != sK4(sK6,sK7)
% 27.47/3.99      | k2_relat_1(sK6) != k1_relat_1(sK7) ),
% 27.47/3.99      inference(instantiation,[status(thm)],[c_1992]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_12240,plain,
% 27.47/3.99      ( sK4(sK6,sK7) != sK4(sK6,sK7)
% 27.47/3.99      | k2_relat_1(sK6) != k1_relat_1(sK7)
% 27.47/3.99      | r2_hidden(sK4(sK6,sK7),k1_relat_1(sK7)) != iProver_top
% 27.47/3.99      | r2_hidden(sK4(sK6,sK7),k2_relat_1(sK6)) = iProver_top ),
% 27.47/3.99      inference(predicate_to_equality,[status(thm)],[c_12239]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_26016,plain,
% 27.47/3.99      ( r2_hidden(sK4(sK6,sK7),k2_relat_1(sK6)) = iProver_top ),
% 27.47/3.99      inference(global_propositional_subsumption,
% 27.47/3.99                [status(thm)],
% 27.47/3.99                [c_3005,c_21,c_1161,c_1174,c_1972,c_2049,c_2320,c_2440,
% 27.47/3.99                 c_4223,c_5493,c_12240]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_19,negated_conjecture,
% 27.47/3.99      ( ~ r2_hidden(X0,k1_relat_1(sK7))
% 27.47/3.99      | ~ r2_hidden(k1_funct_1(sK7,X0),k1_relat_1(sK6))
% 27.47/3.99      | k1_funct_1(sK6,k1_funct_1(sK7,X0)) = X0 ),
% 27.47/3.99      inference(cnf_transformation,[],[f72]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_1773,plain,
% 27.47/3.99      ( k1_funct_1(sK6,k1_funct_1(sK7,X0)) = X0
% 27.47/3.99      | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 27.47/3.99      | r2_hidden(k1_funct_1(sK7,X0),k1_relat_1(sK6)) != iProver_top ),
% 27.47/3.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_1787,plain,
% 27.47/3.99      ( k1_funct_1(sK6,k1_funct_1(sK7,X0)) = X0
% 27.47/3.99      | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
% 27.47/3.99      | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7)) != iProver_top ),
% 27.47/3.99      inference(light_normalisation,[status(thm)],[c_1773,c_21,c_22]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_704,plain,
% 27.47/3.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 27.47/3.99      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 27.47/3.99      | ~ v1_relat_1(X1)
% 27.47/3.99      | sK7 != X1 ),
% 27.47/3.99      inference(resolution_lifted,[status(thm)],[c_3,c_24]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_705,plain,
% 27.47/3.99      ( ~ r2_hidden(X0,k1_relat_1(sK7))
% 27.47/3.99      | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7))
% 27.47/3.99      | ~ v1_relat_1(sK7) ),
% 27.47/3.99      inference(unflattening,[status(thm)],[c_704]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_709,plain,
% 27.47/3.99      ( r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7))
% 27.47/3.99      | ~ r2_hidden(X0,k1_relat_1(sK7)) ),
% 27.47/3.99      inference(global_propositional_subsumption,
% 27.47/3.99                [status(thm)],
% 27.47/3.99                [c_705,c_25]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_710,plain,
% 27.47/3.99      ( ~ r2_hidden(X0,k1_relat_1(sK7))
% 27.47/3.99      | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7)) ),
% 27.47/3.99      inference(renaming,[status(thm)],[c_709]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_1759,plain,
% 27.47/3.99      ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 27.47/3.99      | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7)) = iProver_top ),
% 27.47/3.99      inference(predicate_to_equality,[status(thm)],[c_710]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_1781,plain,
% 27.47/3.99      ( r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
% 27.47/3.99      | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7)) = iProver_top ),
% 27.47/3.99      inference(light_normalisation,[status(thm)],[c_1759,c_21]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_2248,plain,
% 27.47/3.99      ( r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
% 27.47/3.99      | k1_funct_1(sK6,k1_funct_1(sK7,X0)) = X0 ),
% 27.47/3.99      inference(global_propositional_subsumption,
% 27.47/3.99                [status(thm)],
% 27.47/3.99                [c_1787,c_1781]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_2249,plain,
% 27.47/3.99      ( k1_funct_1(sK6,k1_funct_1(sK7,X0)) = X0
% 27.47/3.99      | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top ),
% 27.47/3.99      inference(renaming,[status(thm)],[c_2248]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_26115,plain,
% 27.47/3.99      ( k1_funct_1(sK6,k1_funct_1(sK7,sK4(sK6,sK7))) = sK4(sK6,sK7) ),
% 27.47/3.99      inference(superposition,[status(thm)],[c_26016,c_2249]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_26580,plain,
% 27.47/3.99      ( k1_funct_1(sK6,sK5(sK6,sK7)) = sK4(sK6,sK7) ),
% 27.47/3.99      inference(superposition,[status(thm)],[c_3079,c_26115]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_44941,plain,
% 27.47/3.99      ( k1_funct_1(sK7,sK4(sK6,sK7)) = sK5(sK6,sK7) ),
% 27.47/3.99      inference(light_normalisation,[status(thm)],[c_3023,c_26580]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_44952,plain,
% 27.47/3.99      ( r2_hidden(sK5(sK6,sK7),k2_relat_1(sK7)) = iProver_top
% 27.47/3.99      | r2_hidden(sK4(sK6,sK7),k2_relat_1(sK6)) != iProver_top ),
% 27.47/3.99      inference(superposition,[status(thm)],[c_44941,c_1781]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_44958,plain,
% 27.47/3.99      ( r2_hidden(sK5(sK6,sK7),k2_relat_1(sK7))
% 27.47/3.99      | ~ r2_hidden(sK4(sK6,sK7),k2_relat_1(sK6)) ),
% 27.47/3.99      inference(predicate_to_equality_rev,[status(thm)],[c_44952]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_26018,plain,
% 27.47/3.99      ( r2_hidden(sK4(sK6,sK7),k2_relat_1(sK6)) ),
% 27.47/3.99      inference(predicate_to_equality_rev,[status(thm)],[c_26016]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_6143,plain,
% 27.47/3.99      ( sK5(sK6,sK7) = sK5(sK6,sK7) ),
% 27.47/3.99      inference(instantiation,[status(thm)],[c_1309]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_1977,plain,
% 27.47/3.99      ( X0 != X1 | k1_relat_1(sK6) != X1 | k1_relat_1(sK6) = X0 ),
% 27.47/3.99      inference(instantiation,[status(thm)],[c_1310]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_2084,plain,
% 27.47/3.99      ( X0 != k1_relat_1(sK6)
% 27.47/3.99      | k1_relat_1(sK6) = X0
% 27.47/3.99      | k1_relat_1(sK6) != k1_relat_1(sK6) ),
% 27.47/3.99      inference(instantiation,[status(thm)],[c_1977]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_2467,plain,
% 27.47/3.99      ( k1_relat_1(sK6) != k1_relat_1(sK6)
% 27.47/3.99      | k1_relat_1(sK6) = k2_relat_1(sK7)
% 27.47/3.99      | k2_relat_1(sK7) != k1_relat_1(sK6) ),
% 27.47/3.99      inference(instantiation,[status(thm)],[c_2084]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_1334,plain,
% 27.47/3.99      ( sK6 = sK6 ),
% 27.47/3.99      inference(instantiation,[status(thm)],[c_1309]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_1314,plain,
% 27.47/3.99      ( X0 != X1 | k1_relat_1(X0) = k1_relat_1(X1) ),
% 27.47/3.99      theory(equality) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_1325,plain,
% 27.47/3.99      ( k1_relat_1(sK6) = k1_relat_1(sK6) | sK6 != sK6 ),
% 27.47/3.99      inference(instantiation,[status(thm)],[c_1314]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_6,plain,
% 27.47/3.99      ( sP0(k1_funct_1(X0,X1),X1,X0,X2)
% 27.47/3.99      | ~ r2_hidden(X1,k1_relat_1(X0)) ),
% 27.47/3.99      inference(cnf_transformation,[],[f63]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_11,plain,
% 27.47/3.99      ( ~ sP0(sK4(X0,X1),sK5(X0,X1),X0,X1)
% 27.47/3.99      | ~ r2_hidden(sK4(X0,X1),k2_relat_1(X0))
% 27.47/3.99      | ~ v2_funct_1(X0)
% 27.47/3.99      | ~ v1_relat_1(X0)
% 27.47/3.99      | ~ v1_relat_1(X1)
% 27.47/3.99      | ~ v1_funct_1(X0)
% 27.47/3.99      | ~ v1_funct_1(X1)
% 27.47/3.99      | k1_funct_1(X1,sK4(X0,X1)) != sK5(X0,X1)
% 27.47/3.99      | k2_funct_1(X0) = X1
% 27.47/3.99      | k1_relat_1(X1) != k2_relat_1(X0) ),
% 27.47/3.99      inference(cnf_transformation,[],[f48]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_356,plain,
% 27.47/3.99      ( ~ sP0(sK4(X0,X1),sK5(X0,X1),X0,X1)
% 27.47/3.99      | ~ r2_hidden(sK4(X0,X1),k2_relat_1(X0))
% 27.47/3.99      | ~ v1_relat_1(X0)
% 27.47/3.99      | ~ v1_relat_1(X1)
% 27.47/3.99      | ~ v1_funct_1(X0)
% 27.47/3.99      | ~ v1_funct_1(X1)
% 27.47/3.99      | k1_funct_1(X1,sK4(X0,X1)) != sK5(X0,X1)
% 27.47/3.99      | k2_funct_1(X0) = X1
% 27.47/3.99      | k1_relat_1(X1) != k2_relat_1(X0)
% 27.47/3.99      | sK6 != X0 ),
% 27.47/3.99      inference(resolution_lifted,[status(thm)],[c_11,c_23]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_357,plain,
% 27.47/3.99      ( ~ sP0(sK4(sK6,X0),sK5(sK6,X0),sK6,X0)
% 27.47/3.99      | ~ r2_hidden(sK4(sK6,X0),k2_relat_1(sK6))
% 27.47/3.99      | ~ v1_relat_1(X0)
% 27.47/3.99      | ~ v1_relat_1(sK6)
% 27.47/3.99      | ~ v1_funct_1(X0)
% 27.47/3.99      | ~ v1_funct_1(sK6)
% 27.47/3.99      | k1_funct_1(X0,sK4(sK6,X0)) != sK5(sK6,X0)
% 27.47/3.99      | k2_funct_1(sK6) = X0
% 27.47/3.99      | k1_relat_1(X0) != k2_relat_1(sK6) ),
% 27.47/3.99      inference(unflattening,[status(thm)],[c_356]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_361,plain,
% 27.47/3.99      ( ~ v1_funct_1(X0)
% 27.47/3.99      | ~ sP0(sK4(sK6,X0),sK5(sK6,X0),sK6,X0)
% 27.47/3.99      | ~ r2_hidden(sK4(sK6,X0),k2_relat_1(sK6))
% 27.47/3.99      | ~ v1_relat_1(X0)
% 27.47/3.99      | k1_funct_1(X0,sK4(sK6,X0)) != sK5(sK6,X0)
% 27.47/3.99      | k2_funct_1(sK6) = X0
% 27.47/3.99      | k1_relat_1(X0) != k2_relat_1(sK6) ),
% 27.47/3.99      inference(global_propositional_subsumption,
% 27.47/3.99                [status(thm)],
% 27.47/3.99                [c_357,c_27,c_26]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_362,plain,
% 27.47/3.99      ( ~ sP0(sK4(sK6,X0),sK5(sK6,X0),sK6,X0)
% 27.47/3.99      | ~ r2_hidden(sK4(sK6,X0),k2_relat_1(sK6))
% 27.47/3.99      | ~ v1_relat_1(X0)
% 27.47/3.99      | ~ v1_funct_1(X0)
% 27.47/3.99      | k1_funct_1(X0,sK4(sK6,X0)) != sK5(sK6,X0)
% 27.47/3.99      | k2_funct_1(sK6) = X0
% 27.47/3.99      | k1_relat_1(X0) != k2_relat_1(sK6) ),
% 27.47/3.99      inference(renaming,[status(thm)],[c_361]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_467,plain,
% 27.47/3.99      ( ~ sP0(sK4(sK6,X0),sK5(sK6,X0),sK6,X0)
% 27.47/3.99      | ~ r2_hidden(sK4(sK6,X0),k2_relat_1(sK6))
% 27.47/3.99      | ~ v1_relat_1(X0)
% 27.47/3.99      | k1_funct_1(X0,sK4(sK6,X0)) != sK5(sK6,X0)
% 27.47/3.99      | k2_funct_1(sK6) = X0
% 27.47/3.99      | k1_relat_1(X0) != k2_relat_1(sK6)
% 27.47/3.99      | sK7 != X0 ),
% 27.47/3.99      inference(resolution_lifted,[status(thm)],[c_362,c_24]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_468,plain,
% 27.47/3.99      ( ~ sP0(sK4(sK6,sK7),sK5(sK6,sK7),sK6,sK7)
% 27.47/3.99      | ~ r2_hidden(sK4(sK6,sK7),k2_relat_1(sK6))
% 27.47/3.99      | ~ v1_relat_1(sK7)
% 27.47/3.99      | k1_funct_1(sK7,sK4(sK6,sK7)) != sK5(sK6,sK7)
% 27.47/3.99      | k2_funct_1(sK6) = sK7
% 27.47/3.99      | k1_relat_1(sK7) != k2_relat_1(sK6) ),
% 27.47/3.99      inference(unflattening,[status(thm)],[c_467]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_470,plain,
% 27.47/3.99      ( k1_funct_1(sK7,sK4(sK6,sK7)) != sK5(sK6,sK7)
% 27.47/3.99      | ~ sP0(sK4(sK6,sK7),sK5(sK6,sK7),sK6,sK7)
% 27.47/3.99      | ~ r2_hidden(sK4(sK6,sK7),k2_relat_1(sK6))
% 27.47/3.99      | k1_relat_1(sK7) != k2_relat_1(sK6) ),
% 27.47/3.99      inference(global_propositional_subsumption,
% 27.47/3.99                [status(thm)],
% 27.47/3.99                [c_468,c_25,c_18]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_471,plain,
% 27.47/3.99      ( ~ sP0(sK4(sK6,sK7),sK5(sK6,sK7),sK6,sK7)
% 27.47/3.99      | ~ r2_hidden(sK4(sK6,sK7),k2_relat_1(sK6))
% 27.47/3.99      | k1_funct_1(sK7,sK4(sK6,sK7)) != sK5(sK6,sK7)
% 27.47/3.99      | k1_relat_1(sK7) != k2_relat_1(sK6) ),
% 27.47/3.99      inference(renaming,[status(thm)],[c_470]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_1066,plain,
% 27.47/3.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 27.47/3.99      | ~ r2_hidden(sK4(sK6,sK7),k2_relat_1(sK6))
% 27.47/3.99      | sK5(sK6,sK7) != X0
% 27.47/3.99      | k1_funct_1(X1,X0) != sK4(sK6,sK7)
% 27.47/3.99      | k1_funct_1(sK7,sK4(sK6,sK7)) != sK5(sK6,sK7)
% 27.47/3.99      | k1_relat_1(sK7) != k2_relat_1(sK6)
% 27.47/3.99      | sK7 != X2
% 27.47/3.99      | sK6 != X1 ),
% 27.47/3.99      inference(resolution_lifted,[status(thm)],[c_6,c_471]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(c_1067,plain,
% 27.47/3.99      ( ~ r2_hidden(sK5(sK6,sK7),k1_relat_1(sK6))
% 27.47/3.99      | ~ r2_hidden(sK4(sK6,sK7),k2_relat_1(sK6))
% 27.47/3.99      | k1_funct_1(sK7,sK4(sK6,sK7)) != sK5(sK6,sK7)
% 27.47/3.99      | k1_funct_1(sK6,sK5(sK6,sK7)) != sK4(sK6,sK7)
% 27.47/3.99      | k1_relat_1(sK7) != k2_relat_1(sK6) ),
% 27.47/3.99      inference(unflattening,[status(thm)],[c_1066]) ).
% 27.47/3.99  
% 27.47/3.99  cnf(contradiction,plain,
% 27.47/3.99      ( $false ),
% 27.47/3.99      inference(minisat,
% 27.47/3.99                [status(thm)],
% 27.47/3.99                [c_67223,c_44958,c_44941,c_26580,c_26018,c_6143,c_2467,
% 27.47/3.99                 c_2049,c_1972,c_1334,c_1325,c_1067,c_21,c_22]) ).
% 27.47/3.99  
% 27.47/3.99  
% 27.47/3.99  % SZS output end CNFRefutation for theBenchmark.p
% 27.47/3.99  
% 27.47/3.99  ------                               Statistics
% 27.47/3.99  
% 27.47/3.99  ------ General
% 27.47/3.99  
% 27.47/3.99  abstr_ref_over_cycles:                  0
% 27.47/3.99  abstr_ref_under_cycles:                 0
% 27.47/3.99  gc_basic_clause_elim:                   0
% 27.47/3.99  forced_gc_time:                         0
% 27.47/3.99  parsing_time:                           0.014
% 27.47/3.99  unif_index_cands_time:                  0.
% 27.47/3.99  unif_index_add_time:                    0.
% 27.47/3.99  orderings_time:                         0.
% 27.47/3.99  out_proof_time:                         0.017
% 27.47/3.99  total_time:                             3.288
% 27.47/3.99  num_of_symbols:                         47
% 27.47/3.99  num_of_terms:                           30285
% 27.47/3.99  
% 27.47/3.99  ------ Preprocessing
% 27.47/3.99  
% 27.47/3.99  num_of_splits:                          0
% 27.47/3.99  num_of_split_atoms:                     0
% 27.47/3.99  num_of_reused_defs:                     0
% 27.47/3.99  num_eq_ax_congr_red:                    14
% 27.47/3.99  num_of_sem_filtered_clauses:            1
% 27.47/3.99  num_of_subtypes:                        0
% 27.47/3.99  monotx_restored_types:                  0
% 27.47/3.99  sat_num_of_epr_types:                   0
% 27.47/3.99  sat_num_of_non_cyclic_types:            0
% 27.47/3.99  sat_guarded_non_collapsed_types:        0
% 27.47/3.99  num_pure_diseq_elim:                    0
% 27.47/3.99  simp_replaced_by:                       0
% 27.47/3.99  res_preprocessed:                       116
% 27.47/3.99  prep_upred:                             0
% 27.47/3.99  prep_unflattend:                        132
% 27.47/3.99  smt_new_axioms:                         0
% 27.47/3.99  pred_elim_cands:                        5
% 27.47/3.99  pred_elim:                              3
% 27.47/3.99  pred_elim_cl:                           -4
% 27.47/3.99  pred_elim_cycles:                       4
% 27.47/3.99  merged_defs:                            0
% 27.47/3.99  merged_defs_ncl:                        0
% 27.47/3.99  bin_hyper_res:                          0
% 27.47/3.99  prep_cycles:                            3
% 27.47/3.99  pred_elim_time:                         0.032
% 27.47/3.99  splitting_time:                         0.
% 27.47/3.99  sem_filter_time:                        0.
% 27.47/3.99  monotx_time:                            0.001
% 27.47/3.99  subtype_inf_time:                       0.
% 27.47/3.99  
% 27.47/3.99  ------ Problem properties
% 27.47/3.99  
% 27.47/3.99  clauses:                                31
% 27.47/3.99  conjectures:                            5
% 27.47/3.99  epr:                                    0
% 27.47/3.99  horn:                                   23
% 27.47/3.99  ground:                                 10
% 27.47/3.99  unary:                                  3
% 27.47/3.99  binary:                                 11
% 27.47/3.99  lits:                                   83
% 27.47/3.99  lits_eq:                                37
% 27.47/3.99  fd_pure:                                0
% 27.47/3.99  fd_pseudo:                              0
% 27.47/3.99  fd_cond:                                6
% 27.47/3.99  fd_pseudo_cond:                         1
% 27.47/3.99  ac_symbols:                             0
% 27.47/3.99  
% 27.47/3.99  ------ Propositional Solver
% 27.47/3.99  
% 27.47/3.99  prop_solver_calls:                      36
% 27.47/3.99  prop_fast_solver_calls:                 2310
% 27.47/3.99  smt_solver_calls:                       0
% 27.47/3.99  smt_fast_solver_calls:                  0
% 27.47/3.99  prop_num_of_clauses:                    35494
% 27.47/3.99  prop_preprocess_simplified:             24662
% 27.47/3.99  prop_fo_subsumed:                       58
% 27.47/3.99  prop_solver_time:                       0.
% 27.47/3.99  smt_solver_time:                        0.
% 27.47/3.99  smt_fast_solver_time:                   0.
% 27.47/3.99  prop_fast_solver_time:                  0.
% 27.47/3.99  prop_unsat_core_time:                   0.001
% 27.47/3.99  
% 27.47/3.99  ------ QBF
% 27.47/3.99  
% 27.47/3.99  qbf_q_res:                              0
% 27.47/3.99  qbf_num_tautologies:                    0
% 27.47/3.99  qbf_prep_cycles:                        0
% 27.47/3.99  
% 27.47/3.99  ------ BMC1
% 27.47/3.99  
% 27.47/3.99  bmc1_current_bound:                     -1
% 27.47/3.99  bmc1_last_solved_bound:                 -1
% 27.47/3.99  bmc1_unsat_core_size:                   -1
% 27.47/3.99  bmc1_unsat_core_parents_size:           -1
% 27.47/3.99  bmc1_merge_next_fun:                    0
% 27.47/3.99  bmc1_unsat_core_clauses_time:           0.
% 27.47/3.99  
% 27.47/3.99  ------ Instantiation
% 27.47/3.99  
% 27.47/3.99  inst_num_of_clauses:                    4175
% 27.47/3.99  inst_num_in_passive:                    1675
% 27.47/3.99  inst_num_in_active:                     2155
% 27.47/3.99  inst_num_in_unprocessed:                344
% 27.47/3.99  inst_num_of_loops:                      2892
% 27.47/3.99  inst_num_of_learning_restarts:          0
% 27.47/3.99  inst_num_moves_active_passive:          731
% 27.47/3.99  inst_lit_activity:                      0
% 27.47/3.99  inst_lit_activity_moves:                1
% 27.47/3.99  inst_num_tautologies:                   0
% 27.47/3.99  inst_num_prop_implied:                  0
% 27.47/3.99  inst_num_existing_simplified:           0
% 27.47/3.99  inst_num_eq_res_simplified:             0
% 27.47/3.99  inst_num_child_elim:                    0
% 27.47/3.99  inst_num_of_dismatching_blockings:      1874
% 27.47/3.99  inst_num_of_non_proper_insts:           4862
% 27.47/3.99  inst_num_of_duplicates:                 0
% 27.47/3.99  inst_inst_num_from_inst_to_res:         0
% 27.47/3.99  inst_dismatching_checking_time:         0.
% 27.47/3.99  
% 27.47/3.99  ------ Resolution
% 27.47/3.99  
% 27.47/3.99  res_num_of_clauses:                     0
% 27.47/3.99  res_num_in_passive:                     0
% 27.47/3.99  res_num_in_active:                      0
% 27.47/3.99  res_num_of_loops:                       119
% 27.47/3.99  res_forward_subset_subsumed:            333
% 27.47/3.99  res_backward_subset_subsumed:           0
% 27.47/3.99  res_forward_subsumed:                   0
% 27.47/3.99  res_backward_subsumed:                  0
% 27.47/3.99  res_forward_subsumption_resolution:     0
% 27.47/3.99  res_backward_subsumption_resolution:    0
% 27.47/3.99  res_clause_to_clause_subsumption:       26103
% 27.47/3.99  res_orphan_elimination:                 0
% 27.47/3.99  res_tautology_del:                      708
% 27.47/3.99  res_num_eq_res_simplified:              0
% 27.47/3.99  res_num_sel_changes:                    0
% 27.47/3.99  res_moves_from_active_to_pass:          0
% 27.47/3.99  
% 27.47/3.99  ------ Superposition
% 27.47/3.99  
% 27.47/3.99  sup_time_total:                         0.
% 27.47/3.99  sup_time_generating:                    0.
% 27.47/3.99  sup_time_sim_full:                      0.
% 27.47/3.99  sup_time_sim_immed:                     0.
% 27.47/3.99  
% 27.47/3.99  sup_num_of_clauses:                     20158
% 27.47/3.99  sup_num_in_active:                      559
% 27.47/3.99  sup_num_in_passive:                     19599
% 27.47/3.99  sup_num_of_loops:                       578
% 27.47/3.99  sup_fw_superposition:                   19329
% 27.47/3.99  sup_bw_superposition:                   16059
% 27.47/3.99  sup_immediate_simplified:               586
% 27.47/3.99  sup_given_eliminated:                   0
% 27.47/3.99  comparisons_done:                       0
% 27.47/3.99  comparisons_avoided:                    292
% 27.47/3.99  
% 27.47/3.99  ------ Simplifications
% 27.47/3.99  
% 27.47/3.99  
% 27.47/3.99  sim_fw_subset_subsumed:                 12
% 27.47/3.99  sim_bw_subset_subsumed:                 334
% 27.47/3.99  sim_fw_subsumed:                        2
% 27.47/3.99  sim_bw_subsumed:                        3
% 27.47/3.99  sim_fw_subsumption_res:                 0
% 27.47/3.99  sim_bw_subsumption_res:                 0
% 27.47/3.99  sim_tautology_del:                      9
% 27.47/3.99  sim_eq_tautology_del:                   13727
% 27.47/3.99  sim_eq_res_simp:                        4
% 27.47/3.99  sim_fw_demodulated:                     190
% 27.47/3.99  sim_bw_demodulated:                     6
% 27.47/3.99  sim_light_normalised:                   402
% 27.47/3.99  sim_joinable_taut:                      0
% 27.47/3.99  sim_joinable_simp:                      0
% 27.47/3.99  sim_ac_normalised:                      0
% 27.47/3.99  sim_smt_subsumption:                    0
% 27.47/3.99  
%------------------------------------------------------------------------------
