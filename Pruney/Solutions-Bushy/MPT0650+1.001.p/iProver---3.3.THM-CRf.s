%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0650+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:48 EST 2020

% Result     : Theorem 1.61s
% Output     : CNFRefutation 1.75s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 195 expanded)
%              Number of clauses        :   48 (  60 expanded)
%              Number of leaves         :   11 (  40 expanded)
%              Depth                    :   17
%              Number of atoms          :  468 (1133 expanded)
%              Number of equality atoms :  160 ( 373 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   19 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f17,plain,(
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
    inference(nnf_transformation,[],[f17])).

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

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(X2,X1) = X0
      | k1_funct_1(X3,X0) != X1
      | ~ r2_hidden(X0,k2_relat_1(X2))
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f52,plain,(
    ! [X2,X0,X3] :
      ( k1_funct_1(X2,k1_funct_1(X3,X0)) = X0
      | ~ r2_hidden(X0,k2_relat_1(X2))
      | ~ sP0(X0,k1_funct_1(X3,X0),X2,X3) ) ),
    inference(equality_resolution,[],[f33])).

fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f3])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f18,plain,(
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
    inference(definition_folding,[],[f12,f17])).

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
    inference(nnf_transformation,[],[f18])).

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
    inference(rectify,[],[f23])).

fof(f25,plain,(
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

fof(f26,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f24,f25])).

fof(f38,plain,(
    ! [X4,X0,X5,X1] :
      ( sP0(X4,X5,X0,X1)
      | k2_funct_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f58,plain,(
    ! [X4,X0,X5] :
      ( sP0(X4,X5,X0,k2_funct_1(X0))
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f38])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k2_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
          & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( r2_hidden(X0,k2_relat_1(X1))
            & v2_funct_1(X1) )
         => ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
            & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0
        | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0 )
      & r2_hidden(X0,k2_relat_1(X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0
        | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0 )
      & r2_hidden(X0,k2_relat_1(X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f27,plain,
    ( ? [X0,X1] :
        ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0
          | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0 )
        & r2_hidden(X0,k2_relat_1(X1))
        & v2_funct_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ( k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) != sK3
        | k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),sK3)) != sK3 )
      & r2_hidden(sK3,k2_relat_1(sK4))
      & v2_funct_1(sK4)
      & v1_funct_1(sK4)
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ( k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) != sK3
      | k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),sK3)) != sK3 )
    & r2_hidden(sK3,k2_relat_1(sK4))
    & v2_funct_1(sK4)
    & v1_funct_1(sK4)
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f16,f27])).

fof(f48,plain,(
    v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f28])).

fof(f46,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f28])).

fof(f47,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f28])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f8,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f29,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f30,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = k2_relat_1(X0)
      | k2_funct_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f59,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f44,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f50,plain,
    ( k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) != sK3
    | k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),sK3)) != sK3 ),
    inference(cnf_transformation,[],[f28])).

fof(f49,plain,(
    r2_hidden(sK3,k2_relat_1(sK4)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_1055,plain,
    ( X0_42 != X1_42
    | X2_42 != X1_42
    | X2_42 = X0_42 ),
    theory(equality)).

cnf(c_1622,plain,
    ( X0_42 != X1_42
    | k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) != X1_42
    | k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) = X0_42 ),
    inference(instantiation,[status(thm)],[c_1055])).

cnf(c_2090,plain,
    ( X0_42 != k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),sK3))
    | k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) = X0_42
    | k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) != k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),sK3)) ),
    inference(instantiation,[status(thm)],[c_1622])).

cnf(c_2093,plain,
    ( k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) != k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),sK3))
    | k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) = sK3
    | sK3 != k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),sK3)) ),
    inference(instantiation,[status(thm)],[c_2090])).

cnf(c_1764,plain,
    ( k1_funct_1(X0_43,X0_42) != X1_42
    | sK3 != X1_42
    | sK3 = k1_funct_1(X0_43,X0_42) ),
    inference(instantiation,[status(thm)],[c_1055])).

cnf(c_2073,plain,
    ( k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),X0_42)) != X0_42
    | sK3 != X0_42
    | sK3 = k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),X0_42)) ),
    inference(instantiation,[status(thm)],[c_1764])).

cnf(c_2074,plain,
    ( k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),sK3)) != sK3
    | sK3 = k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),sK3))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2073])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_1048,plain,
    ( ~ r2_hidden(X0_42,k1_relat_1(X0_43))
    | ~ v1_relat_1(X0_43)
    | ~ v1_relat_1(X1_43)
    | ~ v1_funct_1(X0_43)
    | ~ v1_funct_1(X1_43)
    | k1_funct_1(k5_relat_1(X0_43,X1_43),X0_42) = k1_funct_1(X1_43,k1_funct_1(X0_43,X0_42)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1722,plain,
    ( ~ r2_hidden(X0_42,k1_relat_1(k2_funct_1(sK4)))
    | ~ v1_relat_1(X0_43)
    | ~ v1_relat_1(k2_funct_1(sK4))
    | ~ v1_funct_1(X0_43)
    | ~ v1_funct_1(k2_funct_1(sK4))
    | k1_funct_1(k5_relat_1(k2_funct_1(sK4),X0_43),X0_42) = k1_funct_1(X0_43,k1_funct_1(k2_funct_1(sK4),X0_42)) ),
    inference(instantiation,[status(thm)],[c_1048])).

cnf(c_1729,plain,
    ( ~ r2_hidden(sK3,k1_relat_1(k2_funct_1(sK4)))
    | ~ v1_relat_1(k2_funct_1(sK4))
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(k2_funct_1(sK4))
    | ~ v1_funct_1(sK4)
    | k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) = k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),sK3)) ),
    inference(instantiation,[status(thm)],[c_1722])).

cnf(c_6,plain,
    ( ~ sP0(X0,k1_funct_1(X1,X0),X2,X1)
    | ~ r2_hidden(X0,k2_relat_1(X2))
    | k1_funct_1(X2,k1_funct_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1044,plain,
    ( ~ sP0(X0_42,k1_funct_1(X0_43,X0_42),X1_43,X0_43)
    | ~ r2_hidden(X0_42,k2_relat_1(X1_43))
    | k1_funct_1(X1_43,k1_funct_1(X0_43,X0_42)) = X0_42 ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1647,plain,
    ( ~ sP0(X0_42,k1_funct_1(k2_funct_1(sK4),X0_42),sK4,k2_funct_1(sK4))
    | ~ r2_hidden(X0_42,k2_relat_1(sK4))
    | k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),X0_42)) = X0_42 ),
    inference(instantiation,[status(thm)],[c_1044])).

cnf(c_1650,plain,
    ( ~ sP0(sK3,k1_funct_1(k2_funct_1(sK4),sK3),sK4,k2_funct_1(sK4))
    | ~ r2_hidden(sK3,k2_relat_1(sK4))
    | k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),sK3)) = sK3 ),
    inference(instantiation,[status(thm)],[c_1647])).

cnf(c_1064,plain,
    ( ~ r2_hidden(X0_42,X0_44)
    | r2_hidden(X1_42,X1_44)
    | X1_44 != X0_44
    | X1_42 != X0_42 ),
    theory(equality)).

cnf(c_1589,plain,
    ( r2_hidden(X0_42,X0_44)
    | ~ r2_hidden(sK3,k2_relat_1(sK4))
    | X0_44 != k2_relat_1(sK4)
    | X0_42 != sK3 ),
    inference(instantiation,[status(thm)],[c_1064])).

cnf(c_1627,plain,
    ( r2_hidden(X0_42,k1_relat_1(k2_funct_1(sK4)))
    | ~ r2_hidden(sK3,k2_relat_1(sK4))
    | k1_relat_1(k2_funct_1(sK4)) != k2_relat_1(sK4)
    | X0_42 != sK3 ),
    inference(instantiation,[status(thm)],[c_1589])).

cnf(c_1629,plain,
    ( ~ r2_hidden(sK3,k2_relat_1(sK4))
    | r2_hidden(sK3,k1_relat_1(k2_funct_1(sK4)))
    | k1_relat_1(k2_funct_1(sK4)) != k2_relat_1(sK4)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1627])).

cnf(c_13,plain,
    ( sP0(X0,X1,X2,k2_funct_1(X2))
    | ~ v2_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(k2_funct_1(X2))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(k2_funct_1(X2)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_19,negated_conjecture,
    ( v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_377,plain,
    ( sP0(X0,X1,X2,k2_funct_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(k2_funct_1(X2))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(k2_funct_1(X2))
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_19])).

cnf(c_378,plain,
    ( sP0(X0,X1,sK4,k2_funct_1(sK4))
    | ~ v1_relat_1(k2_funct_1(sK4))
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(k2_funct_1(sK4))
    | ~ v1_funct_1(sK4) ),
    inference(unflattening,[status(thm)],[c_377])).

cnf(c_21,negated_conjecture,
    ( v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_70,plain,
    ( v1_relat_1(k2_funct_1(sK4))
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_73,plain,
    ( ~ v1_relat_1(sK4)
    | v1_funct_1(k2_funct_1(sK4))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_382,plain,
    ( sP0(X0,X1,sK4,k2_funct_1(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_378,c_21,c_20,c_70,c_73])).

cnf(c_1031,plain,
    ( sP0(X0_42,X1_42,sK4,k2_funct_1(sK4)) ),
    inference(subtyping,[status(esa)],[c_382])).

cnf(c_1598,plain,
    ( sP0(X0_42,k1_funct_1(k2_funct_1(sK4),X0_42),sK4,k2_funct_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_1031])).

cnf(c_1604,plain,
    ( sP0(sK3,k1_funct_1(k2_funct_1(sK4),sK3),sK4,k2_funct_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_1598])).

cnf(c_14,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(X0))
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_16,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_124,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14,c_16])).

cnf(c_125,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(renaming,[status(thm)],[c_124])).

cnf(c_238,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_125,c_19])).

cnf(c_239,plain,
    ( ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK4)
    | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_238])).

cnf(c_27,plain,
    ( ~ v2_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK4)
    | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_241,plain,
    ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_239,c_21,c_20,c_19,c_27])).

cnf(c_1038,plain,
    ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
    inference(subtyping,[status(esa)],[c_241])).

cnf(c_17,negated_conjecture,
    ( k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) != sK3
    | k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),sK3)) != sK3 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1042,negated_conjecture,
    ( k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) != sK3
    | k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),sK3)) != sK3 ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1052,plain,
    ( X0_42 = X0_42 ),
    theory(equality)).

cnf(c_1081,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1052])).

cnf(c_18,negated_conjecture,
    ( r2_hidden(sK3,k2_relat_1(sK4)) ),
    inference(cnf_transformation,[],[f49])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2093,c_2074,c_1729,c_1650,c_1629,c_1604,c_1038,c_1042,c_1081,c_73,c_70,c_18,c_20,c_21])).


%------------------------------------------------------------------------------
