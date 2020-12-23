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
% DateTime   : Thu Dec  3 11:50:21 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 274 expanded)
%              Number of clauses        :   51 (  76 expanded)
%              Number of leaves         :   10 (  55 expanded)
%              Depth                    :   20
%              Number of atoms          :  541 (1745 expanded)
%              Number of equality atoms :  157 ( 526 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   19 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
           => k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0)
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0)
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f4,axiom,(
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

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f17,plain,(
    ! [X2,X3,X0,X1] :
      ( sP0(X2,X3,X0,X1)
    <=> ( ( k1_funct_1(X0,X3) = X2
          & r2_hidden(X3,k1_relat_1(X0)) )
        | k1_funct_1(X1,X2) != X3
        | ~ r2_hidden(X2,k2_relat_1(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

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
    inference(definition_folding,[],[f14,f17])).

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
    inference(flattening,[],[f24])).

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
    inference(rectify,[],[f25])).

fof(f27,plain,(
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

fof(f28,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f26,f27])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = k2_relat_1(X0)
      | k2_funct_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f62,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f42])).

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

fof(f31,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f32,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k1_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
          & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( r2_hidden(X0,k1_relat_1(X1))
            & v2_funct_1(X1) )
         => ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
            & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) != X0
        | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) != X0 )
      & r2_hidden(X0,k1_relat_1(X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) != X0
        | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) != X0 )
      & r2_hidden(X0,k1_relat_1(X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f29,plain,
    ( ? [X0,X1] :
        ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) != X0
          | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) != X0 )
        & r2_hidden(X0,k1_relat_1(X1))
        & v2_funct_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ( k1_funct_1(k5_relat_1(sK4,k2_funct_1(sK4)),sK3) != sK3
        | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK3)) != sK3 )
      & r2_hidden(sK3,k1_relat_1(sK4))
      & v2_funct_1(sK4)
      & v1_funct_1(sK4)
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ( k1_funct_1(k5_relat_1(sK4,k2_funct_1(sK4)),sK3) != sK3
      | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK3)) != sK3 )
    & r2_hidden(sK3,k1_relat_1(sK4))
    & v2_funct_1(sK4)
    & v1_funct_1(sK4)
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f16,f29])).

fof(f51,plain,(
    v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f30])).

fof(f49,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f30])).

fof(f50,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
              | ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              | ~ r2_hidden(X0,k1_relat_1(X2)) )
            & ( ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
                & r2_hidden(X0,k1_relat_1(X2)) )
              | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
              | ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              | ~ r2_hidden(X0,k1_relat_1(X2)) )
            & ( ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
                & r2_hidden(X0,k1_relat_1(X2)) )
              | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f45,plain,(
    ! [X4,X0,X5,X1] :
      ( k1_funct_1(X1,X4) = X5
      | k1_funct_1(X0,X5) != X4
      | ~ r2_hidden(X5,k1_relat_1(X0))
      | k2_funct_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f57,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X1,k1_funct_1(X0,X5)) = X5
      | ~ r2_hidden(X5,k1_relat_1(X0))
      | k2_funct_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f58,plain,(
    ! [X0,X5] :
      ( k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X5)) = X5
      | ~ r2_hidden(X5,k1_relat_1(X0))
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f44,plain,(
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
    inference(cnf_transformation,[],[f28])).

fof(f59,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k1_funct_1(X0,X5),k2_relat_1(X0))
      | ~ r2_hidden(X5,k1_relat_1(X0))
      | k2_funct_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f60,plain,(
    ! [X0,X5] :
      ( r2_hidden(k1_funct_1(X0,X5),k2_relat_1(X0))
      | ~ r2_hidden(X5,k1_relat_1(X0))
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f59])).

fof(f53,plain,
    ( k1_funct_1(k5_relat_1(sK4,k2_funct_1(sK4)),sK3) != sK3
    | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK3)) != sK3 ),
    inference(cnf_transformation,[],[f30])).

fof(f52,plain,(
    r2_hidden(sK3,k1_relat_1(sK4)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X1,X2)))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1074,plain,
    ( ~ r2_hidden(X0_42,k1_relat_1(k5_relat_1(X0_43,X1_43)))
    | ~ v1_relat_1(X0_43)
    | ~ v1_relat_1(X1_43)
    | ~ v1_funct_1(X0_43)
    | ~ v1_funct_1(X1_43)
    | k1_funct_1(k5_relat_1(X0_43,X1_43),X0_42) = k1_funct_1(X1_43,k1_funct_1(X0_43,X0_42)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_2899,plain,
    ( ~ r2_hidden(X0_42,k1_relat_1(k5_relat_1(sK4,k2_funct_1(sK4))))
    | ~ v1_relat_1(k2_funct_1(sK4))
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(k2_funct_1(sK4))
    | ~ v1_funct_1(sK4)
    | k1_funct_1(k5_relat_1(sK4,k2_funct_1(sK4)),X0_42) = k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0_42)) ),
    inference(instantiation,[status(thm)],[c_1074])).

cnf(c_2906,plain,
    ( ~ r2_hidden(sK3,k1_relat_1(k5_relat_1(sK4,k2_funct_1(sK4))))
    | ~ v1_relat_1(k2_funct_1(sK4))
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(k2_funct_1(sK4))
    | ~ v1_funct_1(sK4)
    | k1_funct_1(k5_relat_1(sK4,k2_funct_1(sK4)),sK3) = k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK3)) ),
    inference(instantiation,[status(thm)],[c_2899])).

cnf(c_1084,plain,
    ( X0_42 != X1_42
    | X2_42 != X1_42
    | X2_42 = X0_42 ),
    theory(equality)).

cnf(c_1703,plain,
    ( k1_funct_1(k5_relat_1(sK4,k2_funct_1(sK4)),sK3) != X0_42
    | k1_funct_1(k5_relat_1(sK4,k2_funct_1(sK4)),sK3) = sK3
    | sK3 != X0_42 ),
    inference(instantiation,[status(thm)],[c_1084])).

cnf(c_1754,plain,
    ( k1_funct_1(k5_relat_1(sK4,k2_funct_1(sK4)),sK3) != k1_funct_1(X0_43,X0_42)
    | k1_funct_1(k5_relat_1(sK4,k2_funct_1(sK4)),sK3) = sK3
    | sK3 != k1_funct_1(X0_43,X0_42) ),
    inference(instantiation,[status(thm)],[c_1703])).

cnf(c_2398,plain,
    ( k1_funct_1(k5_relat_1(sK4,k2_funct_1(sK4)),sK3) != k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0_42))
    | k1_funct_1(k5_relat_1(sK4,k2_funct_1(sK4)),sK3) = sK3
    | sK3 != k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0_42)) ),
    inference(instantiation,[status(thm)],[c_1754])).

cnf(c_2399,plain,
    ( k1_funct_1(k5_relat_1(sK4,k2_funct_1(sK4)),sK3) != k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK3))
    | k1_funct_1(k5_relat_1(sK4,k2_funct_1(sK4)),sK3) = sK3
    | sK3 != k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK3)) ),
    inference(instantiation,[status(thm)],[c_2398])).

cnf(c_1865,plain,
    ( k1_funct_1(X0_43,X0_42) != X1_42
    | sK3 != X1_42
    | sK3 = k1_funct_1(X0_43,X0_42) ),
    inference(instantiation,[status(thm)],[c_1084])).

cnf(c_2240,plain,
    ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0_42)) != X0_42
    | sK3 != X0_42
    | sK3 = k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0_42)) ),
    inference(instantiation,[status(thm)],[c_1865])).

cnf(c_2241,plain,
    ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK3)) != sK3
    | sK3 = k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK3))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2240])).

cnf(c_17,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(X0))
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_130,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17,c_1,c_0])).

cnf(c_131,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(renaming,[status(thm)],[c_130])).

cnf(c_20,negated_conjecture,
    ( v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_256,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_131,c_20])).

cnf(c_257,plain,
    ( ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK4)
    | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_256])).

cnf(c_22,negated_conjecture,
    ( v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_28,plain,
    ( ~ v2_funct_1(sK4)
    | ~ v1_relat_1(k2_funct_1(sK4))
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(k2_funct_1(sK4))
    | ~ v1_funct_1(sK4)
    | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_76,plain,
    ( v1_relat_1(k2_funct_1(sK4))
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_79,plain,
    ( ~ v1_relat_1(sK4)
    | v1_funct_1(k2_funct_1(sK4))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_259,plain,
    ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_257,c_22,c_21,c_20,c_28,c_76,c_79])).

cnf(c_1064,plain,
    ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
    inference(subtyping,[status(esa)],[c_259])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(X0,k1_relat_1(k5_relat_1(X1,X2)))
    | ~ r2_hidden(k1_funct_1(X1,X0),k1_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1077,plain,
    ( ~ r2_hidden(X0_42,k1_relat_1(X0_43))
    | r2_hidden(X0_42,k1_relat_1(k5_relat_1(X0_43,X1_43)))
    | ~ r2_hidden(k1_funct_1(X0_43,X0_42),k1_relat_1(X1_43))
    | ~ v1_relat_1(X0_43)
    | ~ v1_relat_1(X1_43)
    | ~ v1_funct_1(X0_43)
    | ~ v1_funct_1(X1_43) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1487,plain,
    ( r2_hidden(X0_42,k1_relat_1(X0_43)) != iProver_top
    | r2_hidden(X0_42,k1_relat_1(k5_relat_1(X0_43,X1_43))) = iProver_top
    | r2_hidden(k1_funct_1(X0_43,X0_42),k1_relat_1(X1_43)) != iProver_top
    | v1_relat_1(X0_43) != iProver_top
    | v1_relat_1(X1_43) != iProver_top
    | v1_funct_1(X0_43) != iProver_top
    | v1_funct_1(X1_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1077])).

cnf(c_2198,plain,
    ( r2_hidden(X0_42,k1_relat_1(X0_43)) != iProver_top
    | r2_hidden(X0_42,k1_relat_1(k5_relat_1(X0_43,k2_funct_1(sK4)))) = iProver_top
    | r2_hidden(k1_funct_1(X0_43,X0_42),k2_relat_1(sK4)) != iProver_top
    | v1_relat_1(X0_43) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top
    | v1_funct_1(X0_43) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1064,c_1487])).

cnf(c_2228,plain,
    ( ~ r2_hidden(X0_42,k1_relat_1(X0_43))
    | r2_hidden(X0_42,k1_relat_1(k5_relat_1(X0_43,k2_funct_1(sK4))))
    | ~ r2_hidden(k1_funct_1(X0_43,X0_42),k2_relat_1(sK4))
    | ~ v1_relat_1(X0_43)
    | ~ v1_relat_1(k2_funct_1(sK4))
    | ~ v1_funct_1(X0_43)
    | ~ v1_funct_1(k2_funct_1(sK4)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2198])).

cnf(c_2230,plain,
    ( ~ r2_hidden(k1_funct_1(sK4,sK3),k2_relat_1(sK4))
    | r2_hidden(sK3,k1_relat_1(k5_relat_1(sK4,k2_funct_1(sK4))))
    | ~ r2_hidden(sK3,k1_relat_1(sK4))
    | ~ v1_relat_1(k2_funct_1(sK4))
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(k2_funct_1(sK4))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2228])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(X1))
    | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_369,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(X1))
    | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_20])).

cnf(c_370,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | ~ v1_relat_1(k2_funct_1(sK4))
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(k2_funct_1(sK4))
    | ~ v1_funct_1(sK4)
    | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_369])).

cnf(c_374,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_370,c_22,c_21,c_76,c_79])).

cnf(c_1059,plain,
    ( ~ r2_hidden(X0_42,k1_relat_1(sK4))
    | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0_42)) = X0_42 ),
    inference(subtyping,[status(esa)],[c_374])).

cnf(c_1156,plain,
    ( ~ r2_hidden(sK3,k1_relat_1(sK4))
    | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK3)) = sK3 ),
    inference(instantiation,[status(thm)],[c_1059])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(X1)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_351,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(X1))
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_20])).

cnf(c_352,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4))
    | ~ v1_relat_1(k2_funct_1(sK4))
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(k2_funct_1(sK4))
    | ~ v1_funct_1(sK4) ),
    inference(unflattening,[status(thm)],[c_351])).

cnf(c_356,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_352,c_22,c_21,c_76,c_79])).

cnf(c_1060,plain,
    ( ~ r2_hidden(X0_42,k1_relat_1(sK4))
    | r2_hidden(k1_funct_1(sK4,X0_42),k2_relat_1(sK4)) ),
    inference(subtyping,[status(esa)],[c_356])).

cnf(c_1153,plain,
    ( r2_hidden(k1_funct_1(sK4,sK3),k2_relat_1(sK4))
    | ~ r2_hidden(sK3,k1_relat_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_1060])).

cnf(c_18,negated_conjecture,
    ( k1_funct_1(k5_relat_1(sK4,k2_funct_1(sK4)),sK3) != sK3
    | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK3)) != sK3 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1068,negated_conjecture,
    ( k1_funct_1(k5_relat_1(sK4,k2_funct_1(sK4)),sK3) != sK3
    | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK3)) != sK3 ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1081,plain,
    ( X0_42 = X0_42 ),
    theory(equality)).

cnf(c_1110,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1081])).

cnf(c_19,negated_conjecture,
    ( r2_hidden(sK3,k1_relat_1(sK4)) ),
    inference(cnf_transformation,[],[f52])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2906,c_2399,c_2241,c_2230,c_1156,c_1153,c_1068,c_1110,c_79,c_76,c_19,c_21,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:05:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 2.09/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.01  
% 2.09/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.09/1.01  
% 2.09/1.01  ------  iProver source info
% 2.09/1.01  
% 2.09/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.09/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.09/1.01  git: non_committed_changes: false
% 2.09/1.01  git: last_make_outside_of_git: false
% 2.09/1.01  
% 2.09/1.01  ------ 
% 2.09/1.01  
% 2.09/1.01  ------ Input Options
% 2.09/1.01  
% 2.09/1.01  --out_options                           all
% 2.09/1.01  --tptp_safe_out                         true
% 2.09/1.01  --problem_path                          ""
% 2.09/1.01  --include_path                          ""
% 2.09/1.01  --clausifier                            res/vclausify_rel
% 2.09/1.01  --clausifier_options                    --mode clausify
% 2.09/1.01  --stdin                                 false
% 2.09/1.01  --stats_out                             all
% 2.09/1.01  
% 2.09/1.01  ------ General Options
% 2.09/1.01  
% 2.09/1.01  --fof                                   false
% 2.09/1.01  --time_out_real                         305.
% 2.09/1.01  --time_out_virtual                      -1.
% 2.09/1.01  --symbol_type_check                     false
% 2.09/1.01  --clausify_out                          false
% 2.09/1.01  --sig_cnt_out                           false
% 2.09/1.01  --trig_cnt_out                          false
% 2.09/1.01  --trig_cnt_out_tolerance                1.
% 2.09/1.01  --trig_cnt_out_sk_spl                   false
% 2.09/1.01  --abstr_cl_out                          false
% 2.09/1.01  
% 2.09/1.01  ------ Global Options
% 2.09/1.01  
% 2.09/1.01  --schedule                              default
% 2.09/1.01  --add_important_lit                     false
% 2.09/1.01  --prop_solver_per_cl                    1000
% 2.09/1.01  --min_unsat_core                        false
% 2.09/1.01  --soft_assumptions                      false
% 2.09/1.01  --soft_lemma_size                       3
% 2.09/1.01  --prop_impl_unit_size                   0
% 2.09/1.01  --prop_impl_unit                        []
% 2.09/1.01  --share_sel_clauses                     true
% 2.09/1.01  --reset_solvers                         false
% 2.09/1.01  --bc_imp_inh                            [conj_cone]
% 2.09/1.01  --conj_cone_tolerance                   3.
% 2.09/1.01  --extra_neg_conj                        none
% 2.09/1.01  --large_theory_mode                     true
% 2.09/1.01  --prolific_symb_bound                   200
% 2.09/1.01  --lt_threshold                          2000
% 2.09/1.01  --clause_weak_htbl                      true
% 2.09/1.01  --gc_record_bc_elim                     false
% 2.09/1.01  
% 2.09/1.01  ------ Preprocessing Options
% 2.09/1.01  
% 2.09/1.01  --preprocessing_flag                    true
% 2.09/1.01  --time_out_prep_mult                    0.1
% 2.09/1.01  --splitting_mode                        input
% 2.09/1.01  --splitting_grd                         true
% 2.09/1.01  --splitting_cvd                         false
% 2.09/1.01  --splitting_cvd_svl                     false
% 2.09/1.01  --splitting_nvd                         32
% 2.09/1.01  --sub_typing                            true
% 2.09/1.01  --prep_gs_sim                           true
% 2.09/1.01  --prep_unflatten                        true
% 2.09/1.01  --prep_res_sim                          true
% 2.09/1.01  --prep_upred                            true
% 2.09/1.01  --prep_sem_filter                       exhaustive
% 2.09/1.01  --prep_sem_filter_out                   false
% 2.09/1.01  --pred_elim                             true
% 2.09/1.01  --res_sim_input                         true
% 2.09/1.01  --eq_ax_congr_red                       true
% 2.09/1.01  --pure_diseq_elim                       true
% 2.09/1.01  --brand_transform                       false
% 2.09/1.01  --non_eq_to_eq                          false
% 2.09/1.01  --prep_def_merge                        true
% 2.09/1.01  --prep_def_merge_prop_impl              false
% 2.09/1.01  --prep_def_merge_mbd                    true
% 2.09/1.01  --prep_def_merge_tr_red                 false
% 2.09/1.01  --prep_def_merge_tr_cl                  false
% 2.09/1.01  --smt_preprocessing                     true
% 2.09/1.01  --smt_ac_axioms                         fast
% 2.09/1.01  --preprocessed_out                      false
% 2.09/1.01  --preprocessed_stats                    false
% 2.09/1.01  
% 2.09/1.01  ------ Abstraction refinement Options
% 2.09/1.01  
% 2.09/1.01  --abstr_ref                             []
% 2.09/1.01  --abstr_ref_prep                        false
% 2.09/1.01  --abstr_ref_until_sat                   false
% 2.09/1.01  --abstr_ref_sig_restrict                funpre
% 2.09/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.09/1.01  --abstr_ref_under                       []
% 2.09/1.01  
% 2.09/1.01  ------ SAT Options
% 2.09/1.01  
% 2.09/1.01  --sat_mode                              false
% 2.09/1.01  --sat_fm_restart_options                ""
% 2.09/1.01  --sat_gr_def                            false
% 2.09/1.01  --sat_epr_types                         true
% 2.09/1.01  --sat_non_cyclic_types                  false
% 2.09/1.01  --sat_finite_models                     false
% 2.09/1.01  --sat_fm_lemmas                         false
% 2.09/1.01  --sat_fm_prep                           false
% 2.09/1.01  --sat_fm_uc_incr                        true
% 2.09/1.01  --sat_out_model                         small
% 2.09/1.01  --sat_out_clauses                       false
% 2.09/1.01  
% 2.09/1.01  ------ QBF Options
% 2.09/1.01  
% 2.09/1.01  --qbf_mode                              false
% 2.09/1.01  --qbf_elim_univ                         false
% 2.09/1.01  --qbf_dom_inst                          none
% 2.09/1.01  --qbf_dom_pre_inst                      false
% 2.09/1.01  --qbf_sk_in                             false
% 2.09/1.01  --qbf_pred_elim                         true
% 2.09/1.01  --qbf_split                             512
% 2.09/1.01  
% 2.09/1.01  ------ BMC1 Options
% 2.09/1.01  
% 2.09/1.01  --bmc1_incremental                      false
% 2.09/1.01  --bmc1_axioms                           reachable_all
% 2.09/1.01  --bmc1_min_bound                        0
% 2.09/1.01  --bmc1_max_bound                        -1
% 2.09/1.01  --bmc1_max_bound_default                -1
% 2.09/1.01  --bmc1_symbol_reachability              true
% 2.09/1.01  --bmc1_property_lemmas                  false
% 2.09/1.01  --bmc1_k_induction                      false
% 2.09/1.01  --bmc1_non_equiv_states                 false
% 2.09/1.01  --bmc1_deadlock                         false
% 2.09/1.01  --bmc1_ucm                              false
% 2.09/1.01  --bmc1_add_unsat_core                   none
% 2.09/1.01  --bmc1_unsat_core_children              false
% 2.09/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.09/1.01  --bmc1_out_stat                         full
% 2.09/1.01  --bmc1_ground_init                      false
% 2.09/1.01  --bmc1_pre_inst_next_state              false
% 2.09/1.01  --bmc1_pre_inst_state                   false
% 2.09/1.01  --bmc1_pre_inst_reach_state             false
% 2.09/1.01  --bmc1_out_unsat_core                   false
% 2.09/1.01  --bmc1_aig_witness_out                  false
% 2.09/1.01  --bmc1_verbose                          false
% 2.09/1.01  --bmc1_dump_clauses_tptp                false
% 2.09/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.09/1.01  --bmc1_dump_file                        -
% 2.09/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.09/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.09/1.01  --bmc1_ucm_extend_mode                  1
% 2.09/1.01  --bmc1_ucm_init_mode                    2
% 2.09/1.01  --bmc1_ucm_cone_mode                    none
% 2.09/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.09/1.01  --bmc1_ucm_relax_model                  4
% 2.09/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.09/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.09/1.01  --bmc1_ucm_layered_model                none
% 2.09/1.01  --bmc1_ucm_max_lemma_size               10
% 2.09/1.01  
% 2.09/1.01  ------ AIG Options
% 2.09/1.01  
% 2.09/1.01  --aig_mode                              false
% 2.09/1.01  
% 2.09/1.01  ------ Instantiation Options
% 2.09/1.01  
% 2.09/1.01  --instantiation_flag                    true
% 2.09/1.01  --inst_sos_flag                         false
% 2.09/1.01  --inst_sos_phase                        true
% 2.09/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.09/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.09/1.01  --inst_lit_sel_side                     num_symb
% 2.09/1.01  --inst_solver_per_active                1400
% 2.09/1.01  --inst_solver_calls_frac                1.
% 2.09/1.01  --inst_passive_queue_type               priority_queues
% 2.09/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.09/1.01  --inst_passive_queues_freq              [25;2]
% 2.09/1.01  --inst_dismatching                      true
% 2.09/1.01  --inst_eager_unprocessed_to_passive     true
% 2.09/1.01  --inst_prop_sim_given                   true
% 2.09/1.01  --inst_prop_sim_new                     false
% 2.09/1.01  --inst_subs_new                         false
% 2.09/1.01  --inst_eq_res_simp                      false
% 2.09/1.01  --inst_subs_given                       false
% 2.09/1.01  --inst_orphan_elimination               true
% 2.09/1.01  --inst_learning_loop_flag               true
% 2.09/1.01  --inst_learning_start                   3000
% 2.09/1.01  --inst_learning_factor                  2
% 2.09/1.01  --inst_start_prop_sim_after_learn       3
% 2.09/1.01  --inst_sel_renew                        solver
% 2.09/1.01  --inst_lit_activity_flag                true
% 2.09/1.01  --inst_restr_to_given                   false
% 2.09/1.01  --inst_activity_threshold               500
% 2.09/1.01  --inst_out_proof                        true
% 2.09/1.01  
% 2.09/1.01  ------ Resolution Options
% 2.09/1.01  
% 2.09/1.01  --resolution_flag                       true
% 2.09/1.01  --res_lit_sel                           adaptive
% 2.09/1.01  --res_lit_sel_side                      none
% 2.09/1.01  --res_ordering                          kbo
% 2.09/1.01  --res_to_prop_solver                    active
% 2.09/1.01  --res_prop_simpl_new                    false
% 2.09/1.01  --res_prop_simpl_given                  true
% 2.09/1.01  --res_passive_queue_type                priority_queues
% 2.09/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.09/1.01  --res_passive_queues_freq               [15;5]
% 2.09/1.01  --res_forward_subs                      full
% 2.09/1.01  --res_backward_subs                     full
% 2.09/1.01  --res_forward_subs_resolution           true
% 2.09/1.01  --res_backward_subs_resolution          true
% 2.09/1.01  --res_orphan_elimination                true
% 2.09/1.01  --res_time_limit                        2.
% 2.09/1.01  --res_out_proof                         true
% 2.09/1.01  
% 2.09/1.01  ------ Superposition Options
% 2.09/1.01  
% 2.09/1.01  --superposition_flag                    true
% 2.09/1.01  --sup_passive_queue_type                priority_queues
% 2.09/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.09/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.09/1.01  --demod_completeness_check              fast
% 2.09/1.01  --demod_use_ground                      true
% 2.09/1.01  --sup_to_prop_solver                    passive
% 2.09/1.01  --sup_prop_simpl_new                    true
% 2.09/1.01  --sup_prop_simpl_given                  true
% 2.09/1.01  --sup_fun_splitting                     false
% 2.09/1.01  --sup_smt_interval                      50000
% 2.09/1.01  
% 2.09/1.01  ------ Superposition Simplification Setup
% 2.09/1.01  
% 2.09/1.01  --sup_indices_passive                   []
% 2.09/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.09/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.09/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.09/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.09/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.09/1.01  --sup_full_bw                           [BwDemod]
% 2.09/1.01  --sup_immed_triv                        [TrivRules]
% 2.09/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.09/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.09/1.01  --sup_immed_bw_main                     []
% 2.09/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.09/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.09/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.09/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.09/1.01  
% 2.09/1.01  ------ Combination Options
% 2.09/1.01  
% 2.09/1.01  --comb_res_mult                         3
% 2.09/1.01  --comb_sup_mult                         2
% 2.09/1.01  --comb_inst_mult                        10
% 2.09/1.01  
% 2.09/1.01  ------ Debug Options
% 2.09/1.01  
% 2.09/1.01  --dbg_backtrace                         false
% 2.09/1.01  --dbg_dump_prop_clauses                 false
% 2.09/1.01  --dbg_dump_prop_clauses_file            -
% 2.09/1.01  --dbg_out_stat                          false
% 2.09/1.01  ------ Parsing...
% 2.09/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.09/1.01  
% 2.09/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.09/1.01  
% 2.09/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.09/1.01  
% 2.09/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.09/1.01  ------ Proving...
% 2.09/1.01  ------ Problem Properties 
% 2.09/1.01  
% 2.09/1.01  
% 2.09/1.01  clauses                                 22
% 2.09/1.01  conjectures                             4
% 2.09/1.01  EPR                                     2
% 2.09/1.01  Horn                                    18
% 2.09/1.01  unary                                   5
% 2.09/1.01  binary                                  6
% 2.09/1.01  lits                                    73
% 2.09/1.01  lits eq                                 15
% 2.09/1.01  fd_pure                                 0
% 2.09/1.01  fd_pseudo                               0
% 2.09/1.01  fd_cond                                 3
% 2.09/1.01  fd_pseudo_cond                          1
% 2.09/1.01  AC symbols                              0
% 2.09/1.01  
% 2.09/1.01  ------ Schedule dynamic 5 is on 
% 2.09/1.01  
% 2.09/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.09/1.01  
% 2.09/1.01  
% 2.09/1.01  ------ 
% 2.09/1.01  Current options:
% 2.09/1.01  ------ 
% 2.09/1.01  
% 2.09/1.01  ------ Input Options
% 2.09/1.01  
% 2.09/1.01  --out_options                           all
% 2.09/1.01  --tptp_safe_out                         true
% 2.09/1.01  --problem_path                          ""
% 2.09/1.01  --include_path                          ""
% 2.09/1.01  --clausifier                            res/vclausify_rel
% 2.09/1.01  --clausifier_options                    --mode clausify
% 2.09/1.01  --stdin                                 false
% 2.09/1.01  --stats_out                             all
% 2.09/1.01  
% 2.09/1.02  ------ General Options
% 2.09/1.02  
% 2.09/1.02  --fof                                   false
% 2.09/1.02  --time_out_real                         305.
% 2.09/1.02  --time_out_virtual                      -1.
% 2.09/1.02  --symbol_type_check                     false
% 2.09/1.02  --clausify_out                          false
% 2.09/1.02  --sig_cnt_out                           false
% 2.09/1.02  --trig_cnt_out                          false
% 2.09/1.02  --trig_cnt_out_tolerance                1.
% 2.09/1.02  --trig_cnt_out_sk_spl                   false
% 2.09/1.02  --abstr_cl_out                          false
% 2.09/1.02  
% 2.09/1.02  ------ Global Options
% 2.09/1.02  
% 2.09/1.02  --schedule                              default
% 2.09/1.02  --add_important_lit                     false
% 2.09/1.02  --prop_solver_per_cl                    1000
% 2.09/1.02  --min_unsat_core                        false
% 2.09/1.02  --soft_assumptions                      false
% 2.09/1.02  --soft_lemma_size                       3
% 2.09/1.02  --prop_impl_unit_size                   0
% 2.09/1.02  --prop_impl_unit                        []
% 2.09/1.02  --share_sel_clauses                     true
% 2.09/1.02  --reset_solvers                         false
% 2.09/1.02  --bc_imp_inh                            [conj_cone]
% 2.09/1.02  --conj_cone_tolerance                   3.
% 2.09/1.02  --extra_neg_conj                        none
% 2.09/1.02  --large_theory_mode                     true
% 2.09/1.02  --prolific_symb_bound                   200
% 2.09/1.02  --lt_threshold                          2000
% 2.09/1.02  --clause_weak_htbl                      true
% 2.09/1.02  --gc_record_bc_elim                     false
% 2.09/1.02  
% 2.09/1.02  ------ Preprocessing Options
% 2.09/1.02  
% 2.09/1.02  --preprocessing_flag                    true
% 2.09/1.02  --time_out_prep_mult                    0.1
% 2.09/1.02  --splitting_mode                        input
% 2.09/1.02  --splitting_grd                         true
% 2.09/1.02  --splitting_cvd                         false
% 2.09/1.02  --splitting_cvd_svl                     false
% 2.09/1.02  --splitting_nvd                         32
% 2.09/1.02  --sub_typing                            true
% 2.09/1.02  --prep_gs_sim                           true
% 2.09/1.02  --prep_unflatten                        true
% 2.09/1.02  --prep_res_sim                          true
% 2.09/1.02  --prep_upred                            true
% 2.09/1.02  --prep_sem_filter                       exhaustive
% 2.09/1.02  --prep_sem_filter_out                   false
% 2.09/1.02  --pred_elim                             true
% 2.09/1.02  --res_sim_input                         true
% 2.09/1.02  --eq_ax_congr_red                       true
% 2.09/1.02  --pure_diseq_elim                       true
% 2.09/1.02  --brand_transform                       false
% 2.09/1.02  --non_eq_to_eq                          false
% 2.09/1.02  --prep_def_merge                        true
% 2.09/1.02  --prep_def_merge_prop_impl              false
% 2.09/1.02  --prep_def_merge_mbd                    true
% 2.09/1.02  --prep_def_merge_tr_red                 false
% 2.09/1.02  --prep_def_merge_tr_cl                  false
% 2.09/1.02  --smt_preprocessing                     true
% 2.09/1.02  --smt_ac_axioms                         fast
% 2.09/1.02  --preprocessed_out                      false
% 2.09/1.02  --preprocessed_stats                    false
% 2.09/1.02  
% 2.09/1.02  ------ Abstraction refinement Options
% 2.09/1.02  
% 2.09/1.02  --abstr_ref                             []
% 2.09/1.02  --abstr_ref_prep                        false
% 2.09/1.02  --abstr_ref_until_sat                   false
% 2.09/1.02  --abstr_ref_sig_restrict                funpre
% 2.09/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.09/1.02  --abstr_ref_under                       []
% 2.09/1.02  
% 2.09/1.02  ------ SAT Options
% 2.09/1.02  
% 2.09/1.02  --sat_mode                              false
% 2.09/1.02  --sat_fm_restart_options                ""
% 2.09/1.02  --sat_gr_def                            false
% 2.09/1.02  --sat_epr_types                         true
% 2.09/1.02  --sat_non_cyclic_types                  false
% 2.09/1.02  --sat_finite_models                     false
% 2.09/1.02  --sat_fm_lemmas                         false
% 2.09/1.02  --sat_fm_prep                           false
% 2.09/1.02  --sat_fm_uc_incr                        true
% 2.09/1.02  --sat_out_model                         small
% 2.09/1.02  --sat_out_clauses                       false
% 2.09/1.02  
% 2.09/1.02  ------ QBF Options
% 2.09/1.02  
% 2.09/1.02  --qbf_mode                              false
% 2.09/1.02  --qbf_elim_univ                         false
% 2.09/1.02  --qbf_dom_inst                          none
% 2.09/1.02  --qbf_dom_pre_inst                      false
% 2.09/1.02  --qbf_sk_in                             false
% 2.09/1.02  --qbf_pred_elim                         true
% 2.09/1.02  --qbf_split                             512
% 2.09/1.02  
% 2.09/1.02  ------ BMC1 Options
% 2.09/1.02  
% 2.09/1.02  --bmc1_incremental                      false
% 2.09/1.02  --bmc1_axioms                           reachable_all
% 2.09/1.02  --bmc1_min_bound                        0
% 2.09/1.02  --bmc1_max_bound                        -1
% 2.09/1.02  --bmc1_max_bound_default                -1
% 2.09/1.02  --bmc1_symbol_reachability              true
% 2.09/1.02  --bmc1_property_lemmas                  false
% 2.09/1.02  --bmc1_k_induction                      false
% 2.09/1.02  --bmc1_non_equiv_states                 false
% 2.09/1.02  --bmc1_deadlock                         false
% 2.09/1.02  --bmc1_ucm                              false
% 2.09/1.02  --bmc1_add_unsat_core                   none
% 2.09/1.02  --bmc1_unsat_core_children              false
% 2.09/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.09/1.02  --bmc1_out_stat                         full
% 2.09/1.02  --bmc1_ground_init                      false
% 2.09/1.02  --bmc1_pre_inst_next_state              false
% 2.09/1.02  --bmc1_pre_inst_state                   false
% 2.09/1.02  --bmc1_pre_inst_reach_state             false
% 2.09/1.02  --bmc1_out_unsat_core                   false
% 2.09/1.02  --bmc1_aig_witness_out                  false
% 2.09/1.02  --bmc1_verbose                          false
% 2.09/1.02  --bmc1_dump_clauses_tptp                false
% 2.09/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.09/1.02  --bmc1_dump_file                        -
% 2.09/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.09/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.09/1.02  --bmc1_ucm_extend_mode                  1
% 2.09/1.02  --bmc1_ucm_init_mode                    2
% 2.09/1.02  --bmc1_ucm_cone_mode                    none
% 2.09/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.09/1.02  --bmc1_ucm_relax_model                  4
% 2.09/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.09/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.09/1.02  --bmc1_ucm_layered_model                none
% 2.09/1.02  --bmc1_ucm_max_lemma_size               10
% 2.09/1.02  
% 2.09/1.02  ------ AIG Options
% 2.09/1.02  
% 2.09/1.02  --aig_mode                              false
% 2.09/1.02  
% 2.09/1.02  ------ Instantiation Options
% 2.09/1.02  
% 2.09/1.02  --instantiation_flag                    true
% 2.09/1.02  --inst_sos_flag                         false
% 2.09/1.02  --inst_sos_phase                        true
% 2.09/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.09/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.09/1.02  --inst_lit_sel_side                     none
% 2.09/1.02  --inst_solver_per_active                1400
% 2.09/1.02  --inst_solver_calls_frac                1.
% 2.09/1.02  --inst_passive_queue_type               priority_queues
% 2.09/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.09/1.02  --inst_passive_queues_freq              [25;2]
% 2.09/1.02  --inst_dismatching                      true
% 2.09/1.02  --inst_eager_unprocessed_to_passive     true
% 2.09/1.02  --inst_prop_sim_given                   true
% 2.09/1.02  --inst_prop_sim_new                     false
% 2.09/1.02  --inst_subs_new                         false
% 2.09/1.02  --inst_eq_res_simp                      false
% 2.09/1.02  --inst_subs_given                       false
% 2.09/1.02  --inst_orphan_elimination               true
% 2.09/1.02  --inst_learning_loop_flag               true
% 2.09/1.02  --inst_learning_start                   3000
% 2.09/1.02  --inst_learning_factor                  2
% 2.09/1.02  --inst_start_prop_sim_after_learn       3
% 2.09/1.02  --inst_sel_renew                        solver
% 2.09/1.02  --inst_lit_activity_flag                true
% 2.09/1.02  --inst_restr_to_given                   false
% 2.09/1.02  --inst_activity_threshold               500
% 2.09/1.02  --inst_out_proof                        true
% 2.09/1.02  
% 2.09/1.02  ------ Resolution Options
% 2.09/1.02  
% 2.09/1.02  --resolution_flag                       false
% 2.09/1.02  --res_lit_sel                           adaptive
% 2.09/1.02  --res_lit_sel_side                      none
% 2.09/1.02  --res_ordering                          kbo
% 2.09/1.02  --res_to_prop_solver                    active
% 2.09/1.02  --res_prop_simpl_new                    false
% 2.09/1.02  --res_prop_simpl_given                  true
% 2.09/1.02  --res_passive_queue_type                priority_queues
% 2.09/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.09/1.02  --res_passive_queues_freq               [15;5]
% 2.09/1.02  --res_forward_subs                      full
% 2.09/1.02  --res_backward_subs                     full
% 2.09/1.02  --res_forward_subs_resolution           true
% 2.09/1.02  --res_backward_subs_resolution          true
% 2.09/1.02  --res_orphan_elimination                true
% 2.09/1.02  --res_time_limit                        2.
% 2.09/1.02  --res_out_proof                         true
% 2.09/1.02  
% 2.09/1.02  ------ Superposition Options
% 2.09/1.02  
% 2.09/1.02  --superposition_flag                    true
% 2.09/1.02  --sup_passive_queue_type                priority_queues
% 2.09/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.09/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.09/1.02  --demod_completeness_check              fast
% 2.09/1.02  --demod_use_ground                      true
% 2.09/1.02  --sup_to_prop_solver                    passive
% 2.09/1.02  --sup_prop_simpl_new                    true
% 2.09/1.02  --sup_prop_simpl_given                  true
% 2.09/1.02  --sup_fun_splitting                     false
% 2.09/1.02  --sup_smt_interval                      50000
% 2.09/1.02  
% 2.09/1.02  ------ Superposition Simplification Setup
% 2.09/1.02  
% 2.09/1.02  --sup_indices_passive                   []
% 2.09/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.09/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.09/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.09/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.09/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.09/1.02  --sup_full_bw                           [BwDemod]
% 2.09/1.02  --sup_immed_triv                        [TrivRules]
% 2.09/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.09/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.09/1.02  --sup_immed_bw_main                     []
% 2.09/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.09/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.09/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.09/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.09/1.02  
% 2.09/1.02  ------ Combination Options
% 2.09/1.02  
% 2.09/1.02  --comb_res_mult                         3
% 2.09/1.02  --comb_sup_mult                         2
% 2.09/1.02  --comb_inst_mult                        10
% 2.09/1.02  
% 2.09/1.02  ------ Debug Options
% 2.09/1.02  
% 2.09/1.02  --dbg_backtrace                         false
% 2.09/1.02  --dbg_dump_prop_clauses                 false
% 2.09/1.02  --dbg_dump_prop_clauses_file            -
% 2.09/1.02  --dbg_out_stat                          false
% 2.09/1.02  
% 2.09/1.02  
% 2.09/1.02  
% 2.09/1.02  
% 2.09/1.02  ------ Proving...
% 2.09/1.02  
% 2.09/1.02  
% 2.09/1.02  % SZS status Theorem for theBenchmark.p
% 2.09/1.02  
% 2.09/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 2.09/1.02  
% 2.09/1.02  fof(f3,axiom,(
% 2.09/1.02    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) => k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0))))),
% 2.09/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/1.02  
% 2.09/1.02  fof(f11,plain,(
% 2.09/1.02    ! [X0,X1] : (! [X2] : ((k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.09/1.02    inference(ennf_transformation,[],[f3])).
% 2.09/1.02  
% 2.09/1.02  fof(f12,plain,(
% 2.09/1.02    ! [X0,X1] : (! [X2] : (k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.09/1.02    inference(flattening,[],[f11])).
% 2.09/1.02  
% 2.09/1.02  fof(f36,plain,(
% 2.09/1.02    ( ! [X2,X0,X1] : (k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.09/1.02    inference(cnf_transformation,[],[f12])).
% 2.09/1.02  
% 2.09/1.02  fof(f4,axiom,(
% 2.09/1.02    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) => (k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0)))) & ((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) => (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) & k1_relat_1(X1) = k2_relat_1(X0))))))),
% 2.09/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/1.02  
% 2.09/1.02  fof(f13,plain,(
% 2.09/1.02    ! [X0] : ((! [X1] : ((k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | (k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))))) & k1_relat_1(X1) = k2_relat_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.09/1.02    inference(ennf_transformation,[],[f4])).
% 2.09/1.02  
% 2.09/1.02  fof(f14,plain,(
% 2.09/1.02    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0)))) & k1_relat_1(X1) = k2_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.09/1.02    inference(flattening,[],[f13])).
% 2.09/1.02  
% 2.09/1.02  fof(f17,plain,(
% 2.09/1.02    ! [X2,X3,X0,X1] : (sP0(X2,X3,X0,X1) <=> ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))))),
% 2.09/1.02    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.09/1.02  
% 2.09/1.02  fof(f18,plain,(
% 2.09/1.02    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & sP0(X2,X3,X0,X1)) & k1_relat_1(X1) = k2_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.09/1.02    inference(definition_folding,[],[f14,f17])).
% 2.09/1.02  
% 2.09/1.02  fof(f24,plain,(
% 2.09/1.02    ! [X0] : (! [X1] : (((k2_funct_1(X0) = X1 | (? [X2,X3] : (((k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))) & k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X2,X3,X0,X1)) | k1_relat_1(X1) != k2_relat_1(X0))) & ((! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & sP0(X2,X3,X0,X1)) & k1_relat_1(X1) = k2_relat_1(X0)) | k2_funct_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.09/1.02    inference(nnf_transformation,[],[f18])).
% 2.09/1.02  
% 2.09/1.02  fof(f25,plain,(
% 2.09/1.02    ! [X0] : (! [X1] : (((k2_funct_1(X0) = X1 | ? [X2,X3] : (((k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))) & k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X2,X3,X0,X1)) | k1_relat_1(X1) != k2_relat_1(X0)) & ((! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & sP0(X2,X3,X0,X1)) & k1_relat_1(X1) = k2_relat_1(X0)) | k2_funct_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.09/1.02    inference(flattening,[],[f24])).
% 2.09/1.02  
% 2.09/1.02  fof(f26,plain,(
% 2.09/1.02    ! [X0] : (! [X1] : (((k2_funct_1(X0) = X1 | ? [X2,X3] : (((k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))) & k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X2,X3,X0,X1)) | k1_relat_1(X1) != k2_relat_1(X0)) & ((! [X4,X5] : (((k1_funct_1(X1,X4) = X5 & r2_hidden(X4,k2_relat_1(X0))) | k1_funct_1(X0,X5) != X4 | ~r2_hidden(X5,k1_relat_1(X0))) & sP0(X4,X5,X0,X1)) & k1_relat_1(X1) = k2_relat_1(X0)) | k2_funct_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.09/1.02    inference(rectify,[],[f25])).
% 2.09/1.02  
% 2.09/1.02  fof(f27,plain,(
% 2.09/1.02    ! [X1,X0] : (? [X2,X3] : (((k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))) & k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X2,X3,X0,X1)) => (((k1_funct_1(X1,sK1(X0,X1)) != sK2(X0,X1) | ~r2_hidden(sK1(X0,X1),k2_relat_1(X0))) & k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))) | ~sP0(sK1(X0,X1),sK2(X0,X1),X0,X1)))),
% 2.09/1.02    introduced(choice_axiom,[])).
% 2.09/1.02  
% 2.09/1.02  fof(f28,plain,(
% 2.09/1.02    ! [X0] : (! [X1] : (((k2_funct_1(X0) = X1 | (((k1_funct_1(X1,sK1(X0,X1)) != sK2(X0,X1) | ~r2_hidden(sK1(X0,X1),k2_relat_1(X0))) & k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))) | ~sP0(sK1(X0,X1),sK2(X0,X1),X0,X1)) | k1_relat_1(X1) != k2_relat_1(X0)) & ((! [X4,X5] : (((k1_funct_1(X1,X4) = X5 & r2_hidden(X4,k2_relat_1(X0))) | k1_funct_1(X0,X5) != X4 | ~r2_hidden(X5,k1_relat_1(X0))) & sP0(X4,X5,X0,X1)) & k1_relat_1(X1) = k2_relat_1(X0)) | k2_funct_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.09/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f26,f27])).
% 2.09/1.02  
% 2.09/1.02  fof(f42,plain,(
% 2.09/1.02    ( ! [X0,X1] : (k1_relat_1(X1) = k2_relat_1(X0) | k2_funct_1(X0) != X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.09/1.02    inference(cnf_transformation,[],[f28])).
% 2.09/1.02  
% 2.09/1.02  fof(f62,plain,(
% 2.09/1.02    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v1_funct_1(k2_funct_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.09/1.02    inference(equality_resolution,[],[f42])).
% 2.09/1.02  
% 2.09/1.02  fof(f1,axiom,(
% 2.09/1.02    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.09/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/1.02  
% 2.09/1.02  fof(f7,plain,(
% 2.09/1.02    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.09/1.02    inference(ennf_transformation,[],[f1])).
% 2.09/1.02  
% 2.09/1.02  fof(f8,plain,(
% 2.09/1.02    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.09/1.02    inference(flattening,[],[f7])).
% 2.09/1.02  
% 2.09/1.02  fof(f31,plain,(
% 2.09/1.02    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.09/1.02    inference(cnf_transformation,[],[f8])).
% 2.09/1.02  
% 2.09/1.02  fof(f32,plain,(
% 2.09/1.02    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.09/1.02    inference(cnf_transformation,[],[f8])).
% 2.09/1.02  
% 2.09/1.02  fof(f5,conjecture,(
% 2.09/1.02    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0)))),
% 2.09/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/1.02  
% 2.09/1.02  fof(f6,negated_conjecture,(
% 2.09/1.02    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0)))),
% 2.09/1.02    inference(negated_conjecture,[],[f5])).
% 2.09/1.02  
% 2.09/1.02  fof(f15,plain,(
% 2.09/1.02    ? [X0,X1] : (((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) != X0 | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) != X0) & (r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 2.09/1.02    inference(ennf_transformation,[],[f6])).
% 2.09/1.02  
% 2.09/1.02  fof(f16,plain,(
% 2.09/1.02    ? [X0,X1] : ((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) != X0 | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) != X0) & r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 2.09/1.02    inference(flattening,[],[f15])).
% 2.09/1.02  
% 2.09/1.02  fof(f29,plain,(
% 2.09/1.02    ? [X0,X1] : ((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) != X0 | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) != X0) & r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => ((k1_funct_1(k5_relat_1(sK4,k2_funct_1(sK4)),sK3) != sK3 | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK3)) != sK3) & r2_hidden(sK3,k1_relat_1(sK4)) & v2_funct_1(sK4) & v1_funct_1(sK4) & v1_relat_1(sK4))),
% 2.09/1.02    introduced(choice_axiom,[])).
% 2.09/1.02  
% 2.09/1.02  fof(f30,plain,(
% 2.09/1.02    (k1_funct_1(k5_relat_1(sK4,k2_funct_1(sK4)),sK3) != sK3 | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK3)) != sK3) & r2_hidden(sK3,k1_relat_1(sK4)) & v2_funct_1(sK4) & v1_funct_1(sK4) & v1_relat_1(sK4)),
% 2.09/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f16,f29])).
% 2.09/1.02  
% 2.09/1.02  fof(f51,plain,(
% 2.09/1.02    v2_funct_1(sK4)),
% 2.09/1.02    inference(cnf_transformation,[],[f30])).
% 2.09/1.02  
% 2.09/1.02  fof(f49,plain,(
% 2.09/1.02    v1_relat_1(sK4)),
% 2.09/1.02    inference(cnf_transformation,[],[f30])).
% 2.09/1.02  
% 2.09/1.02  fof(f50,plain,(
% 2.09/1.02    v1_funct_1(sK4)),
% 2.09/1.02    inference(cnf_transformation,[],[f30])).
% 2.09/1.02  
% 2.09/1.02  fof(f2,axiom,(
% 2.09/1.02    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))))))),
% 2.09/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/1.02  
% 2.09/1.02  fof(f9,plain,(
% 2.09/1.02    ! [X0,X1] : (! [X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.09/1.02    inference(ennf_transformation,[],[f2])).
% 2.09/1.02  
% 2.09/1.02  fof(f10,plain,(
% 2.09/1.02    ! [X0,X1] : (! [X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.09/1.02    inference(flattening,[],[f9])).
% 2.09/1.02  
% 2.09/1.02  fof(f19,plain,(
% 2.09/1.02    ! [X0,X1] : (! [X2] : (((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | (~r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X2)))) & ((r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.09/1.02    inference(nnf_transformation,[],[f10])).
% 2.09/1.02  
% 2.09/1.02  fof(f20,plain,(
% 2.09/1.02    ! [X0,X1] : (! [X2] : (((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X2))) & ((r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.09/1.02    inference(flattening,[],[f19])).
% 2.09/1.02  
% 2.09/1.02  fof(f35,plain,(
% 2.09/1.02    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.09/1.02    inference(cnf_transformation,[],[f20])).
% 2.09/1.02  
% 2.09/1.02  fof(f45,plain,(
% 2.09/1.02    ( ! [X4,X0,X5,X1] : (k1_funct_1(X1,X4) = X5 | k1_funct_1(X0,X5) != X4 | ~r2_hidden(X5,k1_relat_1(X0)) | k2_funct_1(X0) != X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.09/1.02    inference(cnf_transformation,[],[f28])).
% 2.09/1.02  
% 2.09/1.02  fof(f57,plain,(
% 2.09/1.02    ( ! [X0,X5,X1] : (k1_funct_1(X1,k1_funct_1(X0,X5)) = X5 | ~r2_hidden(X5,k1_relat_1(X0)) | k2_funct_1(X0) != X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.09/1.02    inference(equality_resolution,[],[f45])).
% 2.09/1.02  
% 2.09/1.02  fof(f58,plain,(
% 2.09/1.02    ( ! [X0,X5] : (k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X5)) = X5 | ~r2_hidden(X5,k1_relat_1(X0)) | ~v1_funct_1(k2_funct_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.09/1.02    inference(equality_resolution,[],[f57])).
% 2.09/1.02  
% 2.09/1.02  fof(f44,plain,(
% 2.09/1.02    ( ! [X4,X0,X5,X1] : (r2_hidden(X4,k2_relat_1(X0)) | k1_funct_1(X0,X5) != X4 | ~r2_hidden(X5,k1_relat_1(X0)) | k2_funct_1(X0) != X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.09/1.02    inference(cnf_transformation,[],[f28])).
% 2.09/1.02  
% 2.09/1.02  fof(f59,plain,(
% 2.09/1.02    ( ! [X0,X5,X1] : (r2_hidden(k1_funct_1(X0,X5),k2_relat_1(X0)) | ~r2_hidden(X5,k1_relat_1(X0)) | k2_funct_1(X0) != X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.09/1.02    inference(equality_resolution,[],[f44])).
% 2.09/1.02  
% 2.09/1.02  fof(f60,plain,(
% 2.09/1.02    ( ! [X0,X5] : (r2_hidden(k1_funct_1(X0,X5),k2_relat_1(X0)) | ~r2_hidden(X5,k1_relat_1(X0)) | ~v1_funct_1(k2_funct_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.09/1.02    inference(equality_resolution,[],[f59])).
% 2.09/1.02  
% 2.09/1.02  fof(f53,plain,(
% 2.09/1.02    k1_funct_1(k5_relat_1(sK4,k2_funct_1(sK4)),sK3) != sK3 | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK3)) != sK3),
% 2.09/1.02    inference(cnf_transformation,[],[f30])).
% 2.09/1.02  
% 2.09/1.02  fof(f52,plain,(
% 2.09/1.02    r2_hidden(sK3,k1_relat_1(sK4))),
% 2.09/1.02    inference(cnf_transformation,[],[f30])).
% 2.09/1.02  
% 2.09/1.02  cnf(c_5,plain,
% 2.09/1.02      ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X1,X2)))
% 2.09/1.02      | ~ v1_relat_1(X1)
% 2.09/1.02      | ~ v1_relat_1(X2)
% 2.09/1.02      | ~ v1_funct_1(X1)
% 2.09/1.02      | ~ v1_funct_1(X2)
% 2.09/1.02      | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ),
% 2.09/1.02      inference(cnf_transformation,[],[f36]) ).
% 2.09/1.02  
% 2.09/1.02  cnf(c_1074,plain,
% 2.09/1.02      ( ~ r2_hidden(X0_42,k1_relat_1(k5_relat_1(X0_43,X1_43)))
% 2.09/1.02      | ~ v1_relat_1(X0_43)
% 2.09/1.02      | ~ v1_relat_1(X1_43)
% 2.09/1.02      | ~ v1_funct_1(X0_43)
% 2.09/1.02      | ~ v1_funct_1(X1_43)
% 2.09/1.02      | k1_funct_1(k5_relat_1(X0_43,X1_43),X0_42) = k1_funct_1(X1_43,k1_funct_1(X0_43,X0_42)) ),
% 2.09/1.02      inference(subtyping,[status(esa)],[c_5]) ).
% 2.09/1.02  
% 2.09/1.02  cnf(c_2899,plain,
% 2.09/1.02      ( ~ r2_hidden(X0_42,k1_relat_1(k5_relat_1(sK4,k2_funct_1(sK4))))
% 2.09/1.02      | ~ v1_relat_1(k2_funct_1(sK4))
% 2.09/1.02      | ~ v1_relat_1(sK4)
% 2.09/1.02      | ~ v1_funct_1(k2_funct_1(sK4))
% 2.09/1.02      | ~ v1_funct_1(sK4)
% 2.09/1.02      | k1_funct_1(k5_relat_1(sK4,k2_funct_1(sK4)),X0_42) = k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0_42)) ),
% 2.09/1.02      inference(instantiation,[status(thm)],[c_1074]) ).
% 2.09/1.02  
% 2.09/1.02  cnf(c_2906,plain,
% 2.09/1.02      ( ~ r2_hidden(sK3,k1_relat_1(k5_relat_1(sK4,k2_funct_1(sK4))))
% 2.09/1.02      | ~ v1_relat_1(k2_funct_1(sK4))
% 2.09/1.02      | ~ v1_relat_1(sK4)
% 2.09/1.02      | ~ v1_funct_1(k2_funct_1(sK4))
% 2.09/1.02      | ~ v1_funct_1(sK4)
% 2.09/1.02      | k1_funct_1(k5_relat_1(sK4,k2_funct_1(sK4)),sK3) = k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK3)) ),
% 2.09/1.02      inference(instantiation,[status(thm)],[c_2899]) ).
% 2.09/1.02  
% 2.09/1.02  cnf(c_1084,plain,
% 2.09/1.02      ( X0_42 != X1_42 | X2_42 != X1_42 | X2_42 = X0_42 ),
% 2.09/1.02      theory(equality) ).
% 2.09/1.02  
% 2.09/1.02  cnf(c_1703,plain,
% 2.09/1.02      ( k1_funct_1(k5_relat_1(sK4,k2_funct_1(sK4)),sK3) != X0_42
% 2.09/1.02      | k1_funct_1(k5_relat_1(sK4,k2_funct_1(sK4)),sK3) = sK3
% 2.09/1.02      | sK3 != X0_42 ),
% 2.09/1.02      inference(instantiation,[status(thm)],[c_1084]) ).
% 2.09/1.02  
% 2.09/1.02  cnf(c_1754,plain,
% 2.09/1.02      ( k1_funct_1(k5_relat_1(sK4,k2_funct_1(sK4)),sK3) != k1_funct_1(X0_43,X0_42)
% 2.09/1.02      | k1_funct_1(k5_relat_1(sK4,k2_funct_1(sK4)),sK3) = sK3
% 2.09/1.02      | sK3 != k1_funct_1(X0_43,X0_42) ),
% 2.09/1.02      inference(instantiation,[status(thm)],[c_1703]) ).
% 2.09/1.02  
% 2.09/1.02  cnf(c_2398,plain,
% 2.09/1.02      ( k1_funct_1(k5_relat_1(sK4,k2_funct_1(sK4)),sK3) != k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0_42))
% 2.09/1.02      | k1_funct_1(k5_relat_1(sK4,k2_funct_1(sK4)),sK3) = sK3
% 2.09/1.02      | sK3 != k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0_42)) ),
% 2.09/1.02      inference(instantiation,[status(thm)],[c_1754]) ).
% 2.09/1.02  
% 2.09/1.02  cnf(c_2399,plain,
% 2.09/1.02      ( k1_funct_1(k5_relat_1(sK4,k2_funct_1(sK4)),sK3) != k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK3))
% 2.09/1.02      | k1_funct_1(k5_relat_1(sK4,k2_funct_1(sK4)),sK3) = sK3
% 2.09/1.02      | sK3 != k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK3)) ),
% 2.09/1.02      inference(instantiation,[status(thm)],[c_2398]) ).
% 2.09/1.02  
% 2.09/1.02  cnf(c_1865,plain,
% 2.09/1.02      ( k1_funct_1(X0_43,X0_42) != X1_42
% 2.09/1.02      | sK3 != X1_42
% 2.09/1.02      | sK3 = k1_funct_1(X0_43,X0_42) ),
% 2.09/1.02      inference(instantiation,[status(thm)],[c_1084]) ).
% 2.09/1.02  
% 2.09/1.02  cnf(c_2240,plain,
% 2.09/1.02      ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0_42)) != X0_42
% 2.09/1.02      | sK3 != X0_42
% 2.09/1.02      | sK3 = k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0_42)) ),
% 2.09/1.02      inference(instantiation,[status(thm)],[c_1865]) ).
% 2.09/1.02  
% 2.09/1.02  cnf(c_2241,plain,
% 2.09/1.02      ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK3)) != sK3
% 2.09/1.02      | sK3 = k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK3))
% 2.09/1.02      | sK3 != sK3 ),
% 2.09/1.02      inference(instantiation,[status(thm)],[c_2240]) ).
% 2.09/1.02  
% 2.09/1.02  cnf(c_17,plain,
% 2.09/1.02      ( ~ v2_funct_1(X0)
% 2.09/1.02      | ~ v1_relat_1(X0)
% 2.09/1.02      | ~ v1_relat_1(k2_funct_1(X0))
% 2.09/1.02      | ~ v1_funct_1(X0)
% 2.09/1.02      | ~ v1_funct_1(k2_funct_1(X0))
% 2.09/1.02      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 2.09/1.02      inference(cnf_transformation,[],[f62]) ).
% 2.09/1.02  
% 2.09/1.02  cnf(c_1,plain,
% 2.09/1.02      ( ~ v1_relat_1(X0)
% 2.09/1.02      | v1_relat_1(k2_funct_1(X0))
% 2.09/1.02      | ~ v1_funct_1(X0) ),
% 2.09/1.02      inference(cnf_transformation,[],[f31]) ).
% 2.09/1.02  
% 2.09/1.02  cnf(c_0,plain,
% 2.09/1.02      ( ~ v1_relat_1(X0)
% 2.09/1.02      | ~ v1_funct_1(X0)
% 2.09/1.02      | v1_funct_1(k2_funct_1(X0)) ),
% 2.09/1.02      inference(cnf_transformation,[],[f32]) ).
% 2.09/1.02  
% 2.09/1.02  cnf(c_130,plain,
% 2.09/1.02      ( ~ v1_funct_1(X0)
% 2.09/1.02      | ~ v2_funct_1(X0)
% 2.09/1.02      | ~ v1_relat_1(X0)
% 2.09/1.02      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 2.09/1.02      inference(global_propositional_subsumption,
% 2.09/1.02                [status(thm)],
% 2.09/1.02                [c_17,c_1,c_0]) ).
% 2.09/1.02  
% 2.09/1.02  cnf(c_131,plain,
% 2.09/1.02      ( ~ v2_funct_1(X0)
% 2.09/1.02      | ~ v1_relat_1(X0)
% 2.09/1.02      | ~ v1_funct_1(X0)
% 2.09/1.02      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 2.09/1.02      inference(renaming,[status(thm)],[c_130]) ).
% 2.09/1.02  
% 2.09/1.02  cnf(c_20,negated_conjecture,
% 2.09/1.02      ( v2_funct_1(sK4) ),
% 2.09/1.02      inference(cnf_transformation,[],[f51]) ).
% 2.09/1.02  
% 2.09/1.02  cnf(c_256,plain,
% 2.09/1.02      ( ~ v1_relat_1(X0)
% 2.09/1.02      | ~ v1_funct_1(X0)
% 2.09/1.02      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 2.09/1.02      | sK4 != X0 ),
% 2.09/1.02      inference(resolution_lifted,[status(thm)],[c_131,c_20]) ).
% 2.09/1.02  
% 2.09/1.02  cnf(c_257,plain,
% 2.09/1.02      ( ~ v1_relat_1(sK4)
% 2.09/1.02      | ~ v1_funct_1(sK4)
% 2.09/1.02      | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
% 2.09/1.02      inference(unflattening,[status(thm)],[c_256]) ).
% 2.09/1.02  
% 2.09/1.02  cnf(c_22,negated_conjecture,
% 2.09/1.02      ( v1_relat_1(sK4) ),
% 2.09/1.02      inference(cnf_transformation,[],[f49]) ).
% 2.09/1.02  
% 2.09/1.02  cnf(c_21,negated_conjecture,
% 2.09/1.02      ( v1_funct_1(sK4) ),
% 2.09/1.02      inference(cnf_transformation,[],[f50]) ).
% 2.09/1.02  
% 2.09/1.02  cnf(c_28,plain,
% 2.09/1.02      ( ~ v2_funct_1(sK4)
% 2.09/1.02      | ~ v1_relat_1(k2_funct_1(sK4))
% 2.09/1.02      | ~ v1_relat_1(sK4)
% 2.09/1.02      | ~ v1_funct_1(k2_funct_1(sK4))
% 2.09/1.02      | ~ v1_funct_1(sK4)
% 2.09/1.02      | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
% 2.09/1.02      inference(instantiation,[status(thm)],[c_17]) ).
% 2.09/1.02  
% 2.09/1.02  cnf(c_76,plain,
% 2.09/1.02      ( v1_relat_1(k2_funct_1(sK4))
% 2.09/1.02      | ~ v1_relat_1(sK4)
% 2.09/1.02      | ~ v1_funct_1(sK4) ),
% 2.09/1.02      inference(instantiation,[status(thm)],[c_1]) ).
% 2.09/1.02  
% 2.09/1.02  cnf(c_79,plain,
% 2.09/1.02      ( ~ v1_relat_1(sK4)
% 2.09/1.02      | v1_funct_1(k2_funct_1(sK4))
% 2.09/1.02      | ~ v1_funct_1(sK4) ),
% 2.09/1.02      inference(instantiation,[status(thm)],[c_0]) ).
% 2.09/1.02  
% 2.09/1.02  cnf(c_259,plain,
% 2.09/1.02      ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
% 2.09/1.02      inference(global_propositional_subsumption,
% 2.09/1.02                [status(thm)],
% 2.09/1.02                [c_257,c_22,c_21,c_20,c_28,c_76,c_79]) ).
% 2.09/1.02  
% 2.09/1.02  cnf(c_1064,plain,
% 2.09/1.02      ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
% 2.09/1.02      inference(subtyping,[status(esa)],[c_259]) ).
% 2.09/1.02  
% 2.09/1.02  cnf(c_2,plain,
% 2.09/1.02      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.09/1.02      | r2_hidden(X0,k1_relat_1(k5_relat_1(X1,X2)))
% 2.09/1.02      | ~ r2_hidden(k1_funct_1(X1,X0),k1_relat_1(X2))
% 2.09/1.02      | ~ v1_relat_1(X1)
% 2.09/1.02      | ~ v1_relat_1(X2)
% 2.09/1.02      | ~ v1_funct_1(X1)
% 2.09/1.02      | ~ v1_funct_1(X2) ),
% 2.09/1.02      inference(cnf_transformation,[],[f35]) ).
% 2.09/1.02  
% 2.09/1.02  cnf(c_1077,plain,
% 2.09/1.02      ( ~ r2_hidden(X0_42,k1_relat_1(X0_43))
% 2.09/1.02      | r2_hidden(X0_42,k1_relat_1(k5_relat_1(X0_43,X1_43)))
% 2.09/1.02      | ~ r2_hidden(k1_funct_1(X0_43,X0_42),k1_relat_1(X1_43))
% 2.09/1.02      | ~ v1_relat_1(X0_43)
% 2.09/1.02      | ~ v1_relat_1(X1_43)
% 2.09/1.02      | ~ v1_funct_1(X0_43)
% 2.09/1.02      | ~ v1_funct_1(X1_43) ),
% 2.09/1.02      inference(subtyping,[status(esa)],[c_2]) ).
% 2.09/1.02  
% 2.09/1.02  cnf(c_1487,plain,
% 2.09/1.02      ( r2_hidden(X0_42,k1_relat_1(X0_43)) != iProver_top
% 2.09/1.02      | r2_hidden(X0_42,k1_relat_1(k5_relat_1(X0_43,X1_43))) = iProver_top
% 2.09/1.02      | r2_hidden(k1_funct_1(X0_43,X0_42),k1_relat_1(X1_43)) != iProver_top
% 2.09/1.02      | v1_relat_1(X0_43) != iProver_top
% 2.09/1.02      | v1_relat_1(X1_43) != iProver_top
% 2.09/1.02      | v1_funct_1(X0_43) != iProver_top
% 2.09/1.02      | v1_funct_1(X1_43) != iProver_top ),
% 2.09/1.02      inference(predicate_to_equality,[status(thm)],[c_1077]) ).
% 2.09/1.02  
% 2.09/1.02  cnf(c_2198,plain,
% 2.09/1.02      ( r2_hidden(X0_42,k1_relat_1(X0_43)) != iProver_top
% 2.09/1.02      | r2_hidden(X0_42,k1_relat_1(k5_relat_1(X0_43,k2_funct_1(sK4)))) = iProver_top
% 2.09/1.02      | r2_hidden(k1_funct_1(X0_43,X0_42),k2_relat_1(sK4)) != iProver_top
% 2.09/1.02      | v1_relat_1(X0_43) != iProver_top
% 2.09/1.02      | v1_relat_1(k2_funct_1(sK4)) != iProver_top
% 2.09/1.02      | v1_funct_1(X0_43) != iProver_top
% 2.09/1.02      | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
% 2.09/1.02      inference(superposition,[status(thm)],[c_1064,c_1487]) ).
% 2.09/1.02  
% 2.09/1.02  cnf(c_2228,plain,
% 2.09/1.02      ( ~ r2_hidden(X0_42,k1_relat_1(X0_43))
% 2.09/1.02      | r2_hidden(X0_42,k1_relat_1(k5_relat_1(X0_43,k2_funct_1(sK4))))
% 2.09/1.02      | ~ r2_hidden(k1_funct_1(X0_43,X0_42),k2_relat_1(sK4))
% 2.09/1.02      | ~ v1_relat_1(X0_43)
% 2.09/1.02      | ~ v1_relat_1(k2_funct_1(sK4))
% 2.09/1.02      | ~ v1_funct_1(X0_43)
% 2.09/1.02      | ~ v1_funct_1(k2_funct_1(sK4)) ),
% 2.09/1.02      inference(predicate_to_equality_rev,[status(thm)],[c_2198]) ).
% 2.09/1.02  
% 2.09/1.02  cnf(c_2230,plain,
% 2.09/1.02      ( ~ r2_hidden(k1_funct_1(sK4,sK3),k2_relat_1(sK4))
% 2.09/1.02      | r2_hidden(sK3,k1_relat_1(k5_relat_1(sK4,k2_funct_1(sK4))))
% 2.09/1.02      | ~ r2_hidden(sK3,k1_relat_1(sK4))
% 2.09/1.02      | ~ v1_relat_1(k2_funct_1(sK4))
% 2.09/1.02      | ~ v1_relat_1(sK4)
% 2.09/1.02      | ~ v1_funct_1(k2_funct_1(sK4))
% 2.09/1.02      | ~ v1_funct_1(sK4) ),
% 2.09/1.02      inference(instantiation,[status(thm)],[c_2228]) ).
% 2.09/1.02  
% 2.09/1.02  cnf(c_14,plain,
% 2.09/1.02      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.09/1.02      | ~ v2_funct_1(X1)
% 2.09/1.02      | ~ v1_relat_1(X1)
% 2.09/1.02      | ~ v1_relat_1(k2_funct_1(X1))
% 2.09/1.02      | ~ v1_funct_1(X1)
% 2.09/1.02      | ~ v1_funct_1(k2_funct_1(X1))
% 2.09/1.02      | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ),
% 2.09/1.02      inference(cnf_transformation,[],[f58]) ).
% 2.09/1.02  
% 2.09/1.02  cnf(c_369,plain,
% 2.09/1.02      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.09/1.02      | ~ v1_relat_1(X1)
% 2.09/1.02      | ~ v1_relat_1(k2_funct_1(X1))
% 2.09/1.02      | ~ v1_funct_1(X1)
% 2.09/1.02      | ~ v1_funct_1(k2_funct_1(X1))
% 2.09/1.02      | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0
% 2.09/1.02      | sK4 != X1 ),
% 2.09/1.02      inference(resolution_lifted,[status(thm)],[c_14,c_20]) ).
% 2.09/1.02  
% 2.09/1.02  cnf(c_370,plain,
% 2.09/1.02      ( ~ r2_hidden(X0,k1_relat_1(sK4))
% 2.09/1.02      | ~ v1_relat_1(k2_funct_1(sK4))
% 2.09/1.02      | ~ v1_relat_1(sK4)
% 2.09/1.02      | ~ v1_funct_1(k2_funct_1(sK4))
% 2.09/1.02      | ~ v1_funct_1(sK4)
% 2.09/1.02      | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0)) = X0 ),
% 2.09/1.02      inference(unflattening,[status(thm)],[c_369]) ).
% 2.09/1.02  
% 2.09/1.02  cnf(c_374,plain,
% 2.09/1.02      ( ~ r2_hidden(X0,k1_relat_1(sK4))
% 2.09/1.02      | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0)) = X0 ),
% 2.09/1.02      inference(global_propositional_subsumption,
% 2.09/1.02                [status(thm)],
% 2.09/1.02                [c_370,c_22,c_21,c_76,c_79]) ).
% 2.09/1.02  
% 2.09/1.02  cnf(c_1059,plain,
% 2.09/1.02      ( ~ r2_hidden(X0_42,k1_relat_1(sK4))
% 2.09/1.02      | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0_42)) = X0_42 ),
% 2.09/1.02      inference(subtyping,[status(esa)],[c_374]) ).
% 2.09/1.02  
% 2.09/1.02  cnf(c_1156,plain,
% 2.09/1.02      ( ~ r2_hidden(sK3,k1_relat_1(sK4))
% 2.09/1.02      | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK3)) = sK3 ),
% 2.09/1.02      inference(instantiation,[status(thm)],[c_1059]) ).
% 2.09/1.02  
% 2.09/1.02  cnf(c_15,plain,
% 2.09/1.02      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.09/1.02      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 2.09/1.02      | ~ v2_funct_1(X1)
% 2.09/1.02      | ~ v1_relat_1(X1)
% 2.09/1.02      | ~ v1_relat_1(k2_funct_1(X1))
% 2.09/1.02      | ~ v1_funct_1(X1)
% 2.09/1.02      | ~ v1_funct_1(k2_funct_1(X1)) ),
% 2.09/1.02      inference(cnf_transformation,[],[f60]) ).
% 2.09/1.02  
% 2.09/1.02  cnf(c_351,plain,
% 2.09/1.02      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.09/1.02      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 2.09/1.02      | ~ v1_relat_1(X1)
% 2.09/1.02      | ~ v1_relat_1(k2_funct_1(X1))
% 2.09/1.02      | ~ v1_funct_1(X1)
% 2.09/1.02      | ~ v1_funct_1(k2_funct_1(X1))
% 2.09/1.02      | sK4 != X1 ),
% 2.09/1.02      inference(resolution_lifted,[status(thm)],[c_15,c_20]) ).
% 2.09/1.02  
% 2.09/1.02  cnf(c_352,plain,
% 2.09/1.02      ( ~ r2_hidden(X0,k1_relat_1(sK4))
% 2.09/1.02      | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4))
% 2.09/1.02      | ~ v1_relat_1(k2_funct_1(sK4))
% 2.09/1.02      | ~ v1_relat_1(sK4)
% 2.09/1.02      | ~ v1_funct_1(k2_funct_1(sK4))
% 2.09/1.02      | ~ v1_funct_1(sK4) ),
% 2.09/1.02      inference(unflattening,[status(thm)],[c_351]) ).
% 2.09/1.02  
% 2.09/1.02  cnf(c_356,plain,
% 2.09/1.02      ( ~ r2_hidden(X0,k1_relat_1(sK4))
% 2.09/1.02      | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) ),
% 2.09/1.02      inference(global_propositional_subsumption,
% 2.09/1.02                [status(thm)],
% 2.09/1.02                [c_352,c_22,c_21,c_76,c_79]) ).
% 2.09/1.02  
% 2.09/1.02  cnf(c_1060,plain,
% 2.09/1.02      ( ~ r2_hidden(X0_42,k1_relat_1(sK4))
% 2.09/1.02      | r2_hidden(k1_funct_1(sK4,X0_42),k2_relat_1(sK4)) ),
% 2.09/1.02      inference(subtyping,[status(esa)],[c_356]) ).
% 2.09/1.02  
% 2.09/1.02  cnf(c_1153,plain,
% 2.09/1.02      ( r2_hidden(k1_funct_1(sK4,sK3),k2_relat_1(sK4))
% 2.09/1.02      | ~ r2_hidden(sK3,k1_relat_1(sK4)) ),
% 2.09/1.02      inference(instantiation,[status(thm)],[c_1060]) ).
% 2.09/1.02  
% 2.09/1.02  cnf(c_18,negated_conjecture,
% 2.09/1.02      ( k1_funct_1(k5_relat_1(sK4,k2_funct_1(sK4)),sK3) != sK3
% 2.09/1.02      | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK3)) != sK3 ),
% 2.09/1.02      inference(cnf_transformation,[],[f53]) ).
% 2.09/1.02  
% 2.09/1.02  cnf(c_1068,negated_conjecture,
% 2.09/1.02      ( k1_funct_1(k5_relat_1(sK4,k2_funct_1(sK4)),sK3) != sK3
% 2.09/1.02      | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK3)) != sK3 ),
% 2.09/1.02      inference(subtyping,[status(esa)],[c_18]) ).
% 2.09/1.02  
% 2.09/1.02  cnf(c_1081,plain,( X0_42 = X0_42 ),theory(equality) ).
% 2.09/1.02  
% 2.09/1.02  cnf(c_1110,plain,
% 2.09/1.02      ( sK3 = sK3 ),
% 2.09/1.02      inference(instantiation,[status(thm)],[c_1081]) ).
% 2.09/1.02  
% 2.09/1.02  cnf(c_19,negated_conjecture,
% 2.09/1.02      ( r2_hidden(sK3,k1_relat_1(sK4)) ),
% 2.09/1.02      inference(cnf_transformation,[],[f52]) ).
% 2.09/1.02  
% 2.09/1.02  cnf(contradiction,plain,
% 2.09/1.02      ( $false ),
% 2.09/1.02      inference(minisat,
% 2.09/1.02                [status(thm)],
% 2.09/1.02                [c_2906,c_2399,c_2241,c_2230,c_1156,c_1153,c_1068,c_1110,
% 2.09/1.02                 c_79,c_76,c_19,c_21,c_22]) ).
% 2.09/1.02  
% 2.09/1.02  
% 2.09/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 2.09/1.02  
% 2.09/1.02  ------                               Statistics
% 2.09/1.02  
% 2.09/1.02  ------ General
% 2.09/1.02  
% 2.09/1.02  abstr_ref_over_cycles:                  0
% 2.09/1.02  abstr_ref_under_cycles:                 0
% 2.09/1.02  gc_basic_clause_elim:                   0
% 2.09/1.02  forced_gc_time:                         0
% 2.09/1.02  parsing_time:                           0.01
% 2.09/1.02  unif_index_cands_time:                  0.
% 2.09/1.02  unif_index_add_time:                    0.
% 2.09/1.02  orderings_time:                         0.
% 2.09/1.02  out_proof_time:                         0.006
% 2.09/1.02  total_time:                             0.127
% 2.09/1.02  num_of_symbols:                         48
% 2.09/1.02  num_of_terms:                           2422
% 2.09/1.02  
% 2.09/1.02  ------ Preprocessing
% 2.09/1.02  
% 2.09/1.02  num_of_splits:                          0
% 2.09/1.02  num_of_split_atoms:                     0
% 2.09/1.02  num_of_reused_defs:                     0
% 2.09/1.02  num_eq_ax_congr_red:                    10
% 2.09/1.02  num_of_sem_filtered_clauses:            1
% 2.09/1.02  num_of_subtypes:                        3
% 2.09/1.02  monotx_restored_types:                  1
% 2.09/1.02  sat_num_of_epr_types:                   0
% 2.09/1.02  sat_num_of_non_cyclic_types:            0
% 2.09/1.02  sat_guarded_non_collapsed_types:        1
% 2.09/1.02  num_pure_diseq_elim:                    0
% 2.09/1.02  simp_replaced_by:                       0
% 2.09/1.02  res_preprocessed:                       124
% 2.09/1.02  prep_upred:                             0
% 2.09/1.02  prep_unflattend:                        151
% 2.09/1.02  smt_new_axioms:                         0
% 2.09/1.02  pred_elim_cands:                        4
% 2.09/1.02  pred_elim:                              1
% 2.09/1.02  pred_elim_cl:                           1
% 2.09/1.02  pred_elim_cycles:                       3
% 2.09/1.02  merged_defs:                            0
% 2.09/1.02  merged_defs_ncl:                        0
% 2.09/1.02  bin_hyper_res:                          0
% 2.09/1.02  prep_cycles:                            4
% 2.09/1.02  pred_elim_time:                         0.015
% 2.09/1.02  splitting_time:                         0.
% 2.09/1.02  sem_filter_time:                        0.
% 2.09/1.02  monotx_time:                            0.
% 2.09/1.02  subtype_inf_time:                       0.001
% 2.09/1.02  
% 2.09/1.02  ------ Problem properties
% 2.09/1.02  
% 2.09/1.02  clauses:                                22
% 2.09/1.02  conjectures:                            4
% 2.09/1.02  epr:                                    2
% 2.09/1.02  horn:                                   18
% 2.09/1.02  ground:                                 5
% 2.09/1.02  unary:                                  5
% 2.09/1.02  binary:                                 6
% 2.09/1.02  lits:                                   73
% 2.09/1.02  lits_eq:                                15
% 2.09/1.02  fd_pure:                                0
% 2.09/1.02  fd_pseudo:                              0
% 2.09/1.02  fd_cond:                                3
% 2.09/1.02  fd_pseudo_cond:                         1
% 2.09/1.02  ac_symbols:                             0
% 2.09/1.02  
% 2.09/1.02  ------ Propositional Solver
% 2.09/1.02  
% 2.09/1.02  prop_solver_calls:                      26
% 2.09/1.02  prop_fast_solver_calls:                 1096
% 2.09/1.02  smt_solver_calls:                       0
% 2.09/1.02  smt_fast_solver_calls:                  0
% 2.09/1.02  prop_num_of_clauses:                    718
% 2.09/1.02  prop_preprocess_simplified:             3900
% 2.09/1.02  prop_fo_subsumed:                       35
% 2.09/1.02  prop_solver_time:                       0.
% 2.09/1.02  smt_solver_time:                        0.
% 2.09/1.02  smt_fast_solver_time:                   0.
% 2.09/1.02  prop_fast_solver_time:                  0.
% 2.09/1.02  prop_unsat_core_time:                   0.
% 2.09/1.02  
% 2.09/1.02  ------ QBF
% 2.09/1.02  
% 2.09/1.02  qbf_q_res:                              0
% 2.09/1.02  qbf_num_tautologies:                    0
% 2.09/1.02  qbf_prep_cycles:                        0
% 2.09/1.02  
% 2.09/1.02  ------ BMC1
% 2.09/1.02  
% 2.09/1.02  bmc1_current_bound:                     -1
% 2.09/1.02  bmc1_last_solved_bound:                 -1
% 2.09/1.02  bmc1_unsat_core_size:                   -1
% 2.09/1.02  bmc1_unsat_core_parents_size:           -1
% 2.09/1.02  bmc1_merge_next_fun:                    0
% 2.09/1.02  bmc1_unsat_core_clauses_time:           0.
% 2.09/1.02  
% 2.09/1.02  ------ Instantiation
% 2.09/1.02  
% 2.09/1.02  inst_num_of_clauses:                    214
% 2.09/1.02  inst_num_in_passive:                    24
% 2.09/1.02  inst_num_in_active:                     137
% 2.09/1.02  inst_num_in_unprocessed:                52
% 2.09/1.02  inst_num_of_loops:                      151
% 2.09/1.02  inst_num_of_learning_restarts:          0
% 2.09/1.02  inst_num_moves_active_passive:          10
% 2.09/1.02  inst_lit_activity:                      0
% 2.09/1.02  inst_lit_activity_moves:                0
% 2.09/1.02  inst_num_tautologies:                   0
% 2.09/1.02  inst_num_prop_implied:                  0
% 2.09/1.02  inst_num_existing_simplified:           0
% 2.09/1.02  inst_num_eq_res_simplified:             0
% 2.09/1.02  inst_num_child_elim:                    0
% 2.09/1.02  inst_num_of_dismatching_blockings:      100
% 2.09/1.02  inst_num_of_non_proper_insts:           226
% 2.09/1.02  inst_num_of_duplicates:                 0
% 2.09/1.02  inst_inst_num_from_inst_to_res:         0
% 2.09/1.02  inst_dismatching_checking_time:         0.
% 2.09/1.02  
% 2.09/1.02  ------ Resolution
% 2.09/1.02  
% 2.09/1.02  res_num_of_clauses:                     0
% 2.09/1.02  res_num_in_passive:                     0
% 2.09/1.02  res_num_in_active:                      0
% 2.09/1.02  res_num_of_loops:                       128
% 2.09/1.02  res_forward_subset_subsumed:            30
% 2.09/1.02  res_backward_subset_subsumed:           0
% 2.09/1.02  res_forward_subsumed:                   0
% 2.09/1.02  res_backward_subsumed:                  0
% 2.09/1.02  res_forward_subsumption_resolution:     0
% 2.09/1.02  res_backward_subsumption_resolution:    0
% 2.09/1.02  res_clause_to_clause_subsumption:       64
% 2.09/1.02  res_orphan_elimination:                 0
% 2.09/1.02  res_tautology_del:                      53
% 2.09/1.02  res_num_eq_res_simplified:              0
% 2.09/1.02  res_num_sel_changes:                    0
% 2.09/1.02  res_moves_from_active_to_pass:          0
% 2.09/1.02  
% 2.09/1.02  ------ Superposition
% 2.09/1.02  
% 2.09/1.02  sup_time_total:                         0.
% 2.09/1.02  sup_time_generating:                    0.
% 2.09/1.02  sup_time_sim_full:                      0.
% 2.09/1.02  sup_time_sim_immed:                     0.
% 2.09/1.02  
% 2.09/1.02  sup_num_of_clauses:                     42
% 2.09/1.02  sup_num_in_active:                      30
% 2.09/1.02  sup_num_in_passive:                     12
% 2.09/1.02  sup_num_of_loops:                       30
% 2.09/1.02  sup_fw_superposition:                   18
% 2.09/1.02  sup_bw_superposition:                   15
% 2.09/1.02  sup_immediate_simplified:               15
% 2.09/1.02  sup_given_eliminated:                   0
% 2.09/1.02  comparisons_done:                       0
% 2.09/1.02  comparisons_avoided:                    0
% 2.09/1.02  
% 2.09/1.02  ------ Simplifications
% 2.09/1.02  
% 2.09/1.02  
% 2.09/1.02  sim_fw_subset_subsumed:                 3
% 2.09/1.02  sim_bw_subset_subsumed:                 0
% 2.09/1.02  sim_fw_subsumed:                        1
% 2.09/1.02  sim_bw_subsumed:                        0
% 2.09/1.02  sim_fw_subsumption_res:                 0
% 2.09/1.02  sim_bw_subsumption_res:                 0
% 2.09/1.02  sim_tautology_del:                      6
% 2.09/1.02  sim_eq_tautology_del:                   5
% 2.09/1.02  sim_eq_res_simp:                        0
% 2.09/1.02  sim_fw_demodulated:                     0
% 2.09/1.02  sim_bw_demodulated:                     0
% 2.09/1.02  sim_light_normalised:                   12
% 2.09/1.02  sim_joinable_taut:                      0
% 2.09/1.02  sim_joinable_simp:                      0
% 2.09/1.02  sim_ac_normalised:                      0
% 2.09/1.02  sim_smt_subsumption:                    0
% 2.09/1.02  
%------------------------------------------------------------------------------
