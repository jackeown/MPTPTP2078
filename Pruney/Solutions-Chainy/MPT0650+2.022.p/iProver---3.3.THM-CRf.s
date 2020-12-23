%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:50:25 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 369 expanded)
%              Number of clauses        :   70 ( 109 expanded)
%              Number of leaves         :   13 (  77 expanded)
%              Depth                    :   21
%              Number of atoms          :  541 (2114 expanded)
%              Number of equality atoms :  180 ( 678 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   19 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f21,plain,(
    ! [X2,X3,X0,X1] :
      ( sP0(X2,X3,X0,X1)
    <=> ( ( k1_funct_1(X0,X3) = X2
          & r2_hidden(X3,k1_relat_1(X0)) )
        | k1_funct_1(X1,X2) != X3
        | ~ r2_hidden(X2,k2_relat_1(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

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
    inference(nnf_transformation,[],[f21])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(X2,X1) = X0
      | k1_funct_1(X3,X0) != X1
      | ~ r2_hidden(X0,k2_relat_1(X2))
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f58,plain,(
    ! [X2,X0,X3] :
      ( k1_funct_1(X2,k1_funct_1(X3,X0)) = X0
      | ~ r2_hidden(X0,k2_relat_1(X2))
      | ~ sP0(X0,k1_funct_1(X3,X0),X2,X3) ) ),
    inference(equality_resolution,[],[f41])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f22,plain,(
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
    inference(definition_folding,[],[f18,f21])).

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
    inference(nnf_transformation,[],[f22])).

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
    inference(flattening,[],[f26])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f29,plain,(
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

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k2_funct_1(X0) = X1
              | ( ( k1_funct_1(X1,sK1(X0,X1)) != sK2(X0,X1)
                  | ~ r2_hidden(sK1(X0,X1),k2_relat_1(X0)) )
                & k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1)
                & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) )
              | ~ sP0(sK1(X0,X1),sK2(X0,X1),X0,X1)
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f28,f29])).

fof(f46,plain,(
    ! [X4,X0,X5,X1] :
      ( sP0(X4,X5,X0,X1)
      | k2_funct_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f64,plain,(
    ! [X4,X0,X5] :
      ( sP0(X4,X5,X0,k2_funct_1(X0))
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k2_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
          & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( r2_hidden(X0,k2_relat_1(X1))
            & v2_funct_1(X1) )
         => ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
            & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0
        | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0 )
      & r2_hidden(X0,k2_relat_1(X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0
        | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0 )
      & r2_hidden(X0,k2_relat_1(X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f31,plain,
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

fof(f32,plain,
    ( ( k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) != sK3
      | k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),sK3)) != sK3 )
    & r2_hidden(sK3,k2_relat_1(sK4))
    & v2_funct_1(sK4)
    & v1_funct_1(sK4)
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f20,f31])).

fof(f54,plain,(
    v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f32])).

fof(f52,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f32])).

fof(f53,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f12,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f36,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k4_relat_1(X0))
        & v1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ( v1_funct_1(k4_relat_1(X0))
        & v1_relat_1(k4_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,(
    ! [X0] :
      ( ( v1_funct_1(k4_relat_1(X0))
        & v1_relat_1(k4_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f38,plain,(
    ! [X0] :
      ( v1_funct_1(k4_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k1_relat_1(X1)
      | k2_funct_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f65,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f56,plain,
    ( k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) != sK3
    | k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),sK3)) != sK3 ),
    inference(cnf_transformation,[],[f32])).

fof(f37,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f55,plain,(
    r2_hidden(sK3,k2_relat_1(sK4)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1177,plain,
    ( ~ r2_hidden(X0_43,k1_relat_1(X0_44))
    | ~ v1_funct_1(X0_44)
    | ~ v1_funct_1(X1_44)
    | ~ v1_relat_1(X0_44)
    | ~ v1_relat_1(X1_44)
    | k1_funct_1(k5_relat_1(X0_44,X1_44),X0_43) = k1_funct_1(X1_44,k1_funct_1(X0_44,X0_43)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_3379,plain,
    ( ~ r2_hidden(X0_43,k1_relat_1(k2_funct_1(sK4)))
    | ~ v1_funct_1(X0_44)
    | ~ v1_funct_1(k2_funct_1(sK4))
    | ~ v1_relat_1(X0_44)
    | ~ v1_relat_1(k2_funct_1(sK4))
    | k1_funct_1(k5_relat_1(k2_funct_1(sK4),X0_44),X0_43) = k1_funct_1(X0_44,k1_funct_1(k2_funct_1(sK4),X0_43)) ),
    inference(instantiation,[status(thm)],[c_1177])).

cnf(c_3386,plain,
    ( ~ r2_hidden(sK3,k1_relat_1(k2_funct_1(sK4)))
    | ~ v1_funct_1(k2_funct_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(k2_funct_1(sK4))
    | ~ v1_relat_1(sK4)
    | k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) = k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),sK3)) ),
    inference(instantiation,[status(thm)],[c_3379])).

cnf(c_1191,plain,
    ( X0_43 != X1_43
    | X2_43 != X1_43
    | X2_43 = X0_43 ),
    theory(equality)).

cnf(c_1889,plain,
    ( k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) != X0_43
    | k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) = sK3
    | sK3 != X0_43 ),
    inference(instantiation,[status(thm)],[c_1191])).

cnf(c_1947,plain,
    ( k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) != k1_funct_1(X0_44,X0_43)
    | k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) = sK3
    | sK3 != k1_funct_1(X0_44,X0_43) ),
    inference(instantiation,[status(thm)],[c_1889])).

cnf(c_2990,plain,
    ( k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) != k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),X0_43))
    | k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) = sK3
    | sK3 != k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),X0_43)) ),
    inference(instantiation,[status(thm)],[c_1947])).

cnf(c_2991,plain,
    ( k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) != k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),sK3))
    | k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) = sK3
    | sK3 != k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),sK3)) ),
    inference(instantiation,[status(thm)],[c_2990])).

cnf(c_1202,plain,
    ( ~ r2_hidden(X0_43,X0_45)
    | r2_hidden(X1_43,X1_45)
    | X1_45 != X0_45
    | X1_43 != X0_43 ),
    theory(equality)).

cnf(c_1896,plain,
    ( r2_hidden(X0_43,X0_45)
    | ~ r2_hidden(sK3,k2_relat_1(sK4))
    | X0_45 != k2_relat_1(sK4)
    | X0_43 != sK3 ),
    inference(instantiation,[status(thm)],[c_1202])).

cnf(c_2584,plain,
    ( r2_hidden(X0_43,k1_relat_1(k2_funct_1(sK4)))
    | ~ r2_hidden(sK3,k2_relat_1(sK4))
    | k1_relat_1(k2_funct_1(sK4)) != k2_relat_1(sK4)
    | X0_43 != sK3 ),
    inference(instantiation,[status(thm)],[c_1896])).

cnf(c_2586,plain,
    ( r2_hidden(sK3,k1_relat_1(k2_funct_1(sK4)))
    | ~ r2_hidden(sK3,k2_relat_1(sK4))
    | k1_relat_1(k2_funct_1(sK4)) != k2_relat_1(sK4)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2584])).

cnf(c_2118,plain,
    ( k1_funct_1(X0_44,X0_43) != X1_43
    | sK3 != X1_43
    | sK3 = k1_funct_1(X0_44,X0_43) ),
    inference(instantiation,[status(thm)],[c_1191])).

cnf(c_2431,plain,
    ( k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),X0_43)) != X0_43
    | sK3 != X0_43
    | sK3 = k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),X0_43)) ),
    inference(instantiation,[status(thm)],[c_2118])).

cnf(c_2432,plain,
    ( k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),sK3)) != sK3
    | sK3 = k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),sK3))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2431])).

cnf(c_1195,plain,
    ( ~ v1_relat_1(X0_44)
    | v1_relat_1(X1_44)
    | X1_44 != X0_44 ),
    theory(equality)).

cnf(c_2084,plain,
    ( ~ v1_relat_1(X0_44)
    | v1_relat_1(k2_funct_1(sK4))
    | k2_funct_1(sK4) != X0_44 ),
    inference(instantiation,[status(thm)],[c_1195])).

cnf(c_2296,plain,
    ( v1_relat_1(k2_funct_1(sK4))
    | ~ v1_relat_1(k4_relat_1(sK4))
    | k2_funct_1(sK4) != k4_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2084])).

cnf(c_10,plain,
    ( ~ sP0(X0,k1_funct_1(X1,X0),X2,X1)
    | ~ r2_hidden(X0,k2_relat_1(X2))
    | k1_funct_1(X2,k1_funct_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1173,plain,
    ( ~ sP0(X0_43,k1_funct_1(X0_44,X0_43),X1_44,X0_44)
    | ~ r2_hidden(X0_43,k2_relat_1(X1_44))
    | k1_funct_1(X1_44,k1_funct_1(X0_44,X0_43)) = X0_43 ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1978,plain,
    ( ~ sP0(X0_43,k1_funct_1(k2_funct_1(sK4),X0_43),sK4,k2_funct_1(sK4))
    | ~ r2_hidden(X0_43,k2_relat_1(sK4))
    | k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),X0_43)) = X0_43 ),
    inference(instantiation,[status(thm)],[c_1173])).

cnf(c_1981,plain,
    ( ~ sP0(sK3,k1_funct_1(k2_funct_1(sK4),sK3),sK4,k2_funct_1(sK4))
    | ~ r2_hidden(sK3,k2_relat_1(sK4))
    | k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),sK3)) = sK3 ),
    inference(instantiation,[status(thm)],[c_1978])).

cnf(c_1199,plain,
    ( ~ v1_funct_1(X0_44)
    | v1_funct_1(X1_44)
    | X1_44 != X0_44 ),
    theory(equality)).

cnf(c_1879,plain,
    ( ~ v1_funct_1(X0_44)
    | v1_funct_1(k2_funct_1(sK4))
    | k2_funct_1(sK4) != X0_44 ),
    inference(instantiation,[status(thm)],[c_1199])).

cnf(c_1969,plain,
    ( v1_funct_1(k2_funct_1(sK4))
    | ~ v1_funct_1(k4_relat_1(sK4))
    | k2_funct_1(sK4) != k4_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1879])).

cnf(c_17,plain,
    ( sP0(X0,X1,X2,k2_funct_1(X2))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(k2_funct_1(X2))
    | ~ v2_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(k2_funct_1(X2)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_21,negated_conjecture,
    ( v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_436,plain,
    ( sP0(X0,X1,X2,k2_funct_1(X2))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(k2_funct_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(k2_funct_1(X2))
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_21])).

cnf(c_437,plain,
    ( sP0(X0,X1,sK4,k2_funct_1(sK4))
    | ~ v1_funct_1(k2_funct_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(k2_funct_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_436])).

cnf(c_23,negated_conjecture,
    ( v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_441,plain,
    ( ~ v1_relat_1(k2_funct_1(sK4))
    | sP0(X0,X1,sK4,k2_funct_1(sK4))
    | ~ v1_funct_1(k2_funct_1(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_437,c_23,c_22])).

cnf(c_442,plain,
    ( sP0(X0,X1,sK4,k2_funct_1(sK4))
    | ~ v1_funct_1(k2_funct_1(sK4))
    | ~ v1_relat_1(k2_funct_1(sK4)) ),
    inference(renaming,[status(thm)],[c_441])).

cnf(c_1159,plain,
    ( sP0(X0_43,X1_43,sK4,k2_funct_1(sK4))
    | ~ v1_funct_1(k2_funct_1(sK4))
    | ~ v1_relat_1(k2_funct_1(sK4)) ),
    inference(subtyping,[status(esa)],[c_442])).

cnf(c_1185,plain,
    ( sP0(X0_43,X1_43,sK4,k2_funct_1(sK4))
    | ~ sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP2_iProver_split])],[c_1159])).

cnf(c_1905,plain,
    ( sP0(X0_43,k1_funct_1(k2_funct_1(sK4),X0_43),sK4,k2_funct_1(sK4))
    | ~ sP2_iProver_split ),
    inference(instantiation,[status(thm)],[c_1185])).

cnf(c_1911,plain,
    ( sP0(sK3,k1_funct_1(k2_funct_1(sK4),sK3),sK4,k2_funct_1(sK4))
    | ~ sP2_iProver_split ),
    inference(instantiation,[status(thm)],[c_1905])).

cnf(c_1186,plain,
    ( ~ v1_funct_1(k2_funct_1(sK4))
    | ~ v1_relat_1(k2_funct_1(sK4))
    | sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_1159])).

cnf(c_1657,plain,
    ( v1_funct_1(k2_funct_1(sK4)) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top
    | sP2_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1186])).

cnf(c_3,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_380,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_21])).

cnf(c_381,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k2_funct_1(sK4) = k4_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_380])).

cnf(c_74,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v2_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k2_funct_1(sK4) = k4_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_383,plain,
    ( k2_funct_1(sK4) = k4_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_381,c_23,c_22,c_21,c_74])).

cnf(c_1162,plain,
    ( k2_funct_1(sK4) = k4_relat_1(sK4) ),
    inference(subtyping,[status(esa)],[c_383])).

cnf(c_1712,plain,
    ( v1_funct_1(k4_relat_1(sK4)) != iProver_top
    | v1_relat_1(k4_relat_1(sK4)) != iProver_top
    | sP2_iProver_split = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1657,c_1162])).

cnf(c_4,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k4_relat_1(X0))
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_369,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k4_relat_1(X0))
    | ~ v1_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_21])).

cnf(c_370,plain,
    ( v1_funct_1(k4_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_369])).

cnf(c_71,plain,
    ( v1_funct_1(k4_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v2_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_372,plain,
    ( v1_funct_1(k4_relat_1(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_370,c_23,c_22,c_21,c_71])).

cnf(c_1163,plain,
    ( v1_funct_1(k4_relat_1(sK4)) ),
    inference(subtyping,[status(esa)],[c_372])).

cnf(c_1652,plain,
    ( v1_funct_1(k4_relat_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1163])).

cnf(c_1716,plain,
    ( v1_relat_1(k4_relat_1(sK4)) != iProver_top
    | sP2_iProver_split = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1712,c_1652])).

cnf(c_1831,plain,
    ( ~ v1_relat_1(k4_relat_1(sK4))
    | sP2_iProver_split ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1716])).

cnf(c_18,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(k2_funct_1(X0))
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_265,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(k2_funct_1(X0))
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_21])).

cnf(c_266,plain,
    ( ~ v1_funct_1(k2_funct_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(k2_funct_1(sK4))
    | ~ v1_relat_1(sK4)
    | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_265])).

cnf(c_268,plain,
    ( ~ v1_relat_1(k2_funct_1(sK4))
    | ~ v1_funct_1(k2_funct_1(sK4))
    | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_266,c_23,c_22])).

cnf(c_269,plain,
    ( ~ v1_funct_1(k2_funct_1(sK4))
    | ~ v1_relat_1(k2_funct_1(sK4))
    | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
    inference(renaming,[status(thm)],[c_268])).

cnf(c_1167,plain,
    ( ~ v1_funct_1(k2_funct_1(sK4))
    | ~ v1_relat_1(k2_funct_1(sK4))
    | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
    inference(subtyping,[status(esa)],[c_269])).

cnf(c_19,negated_conjecture,
    ( k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) != sK3
    | k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),sK3)) != sK3 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1171,negated_conjecture,
    ( k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) != sK3
    | k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),sK3)) != sK3 ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1188,plain,
    ( X0_43 = X0_43 ),
    theory(equality)).

cnf(c_1219,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1188])).

cnf(c_5,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k4_relat_1(X0)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_68,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v2_funct_1(sK4)
    | v1_relat_1(k4_relat_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_20,negated_conjecture,
    ( r2_hidden(sK3,k2_relat_1(sK4)) ),
    inference(cnf_transformation,[],[f55])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3386,c_2991,c_2586,c_2432,c_2296,c_1981,c_1969,c_1911,c_1831,c_1162,c_1167,c_1171,c_1219,c_71,c_68,c_20,c_21,c_22,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:51:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.16/1.04  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.04  
% 2.16/1.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.16/1.04  
% 2.16/1.04  ------  iProver source info
% 2.16/1.04  
% 2.16/1.04  git: date: 2020-06-30 10:37:57 +0100
% 2.16/1.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.16/1.04  git: non_committed_changes: false
% 2.16/1.04  git: last_make_outside_of_git: false
% 2.16/1.04  
% 2.16/1.04  ------ 
% 2.16/1.04  
% 2.16/1.04  ------ Input Options
% 2.16/1.04  
% 2.16/1.04  --out_options                           all
% 2.16/1.04  --tptp_safe_out                         true
% 2.16/1.04  --problem_path                          ""
% 2.16/1.04  --include_path                          ""
% 2.16/1.04  --clausifier                            res/vclausify_rel
% 2.16/1.04  --clausifier_options                    --mode clausify
% 2.16/1.04  --stdin                                 false
% 2.16/1.04  --stats_out                             all
% 2.16/1.04  
% 2.16/1.04  ------ General Options
% 2.16/1.04  
% 2.16/1.04  --fof                                   false
% 2.16/1.04  --time_out_real                         305.
% 2.16/1.04  --time_out_virtual                      -1.
% 2.16/1.04  --symbol_type_check                     false
% 2.16/1.04  --clausify_out                          false
% 2.16/1.04  --sig_cnt_out                           false
% 2.16/1.04  --trig_cnt_out                          false
% 2.16/1.04  --trig_cnt_out_tolerance                1.
% 2.16/1.04  --trig_cnt_out_sk_spl                   false
% 2.16/1.04  --abstr_cl_out                          false
% 2.16/1.04  
% 2.16/1.04  ------ Global Options
% 2.16/1.04  
% 2.16/1.04  --schedule                              default
% 2.16/1.04  --add_important_lit                     false
% 2.16/1.04  --prop_solver_per_cl                    1000
% 2.16/1.04  --min_unsat_core                        false
% 2.16/1.04  --soft_assumptions                      false
% 2.16/1.04  --soft_lemma_size                       3
% 2.16/1.04  --prop_impl_unit_size                   0
% 2.16/1.04  --prop_impl_unit                        []
% 2.16/1.04  --share_sel_clauses                     true
% 2.16/1.04  --reset_solvers                         false
% 2.16/1.04  --bc_imp_inh                            [conj_cone]
% 2.16/1.04  --conj_cone_tolerance                   3.
% 2.16/1.04  --extra_neg_conj                        none
% 2.16/1.04  --large_theory_mode                     true
% 2.16/1.04  --prolific_symb_bound                   200
% 2.16/1.04  --lt_threshold                          2000
% 2.16/1.04  --clause_weak_htbl                      true
% 2.16/1.04  --gc_record_bc_elim                     false
% 2.16/1.04  
% 2.16/1.04  ------ Preprocessing Options
% 2.16/1.04  
% 2.16/1.04  --preprocessing_flag                    true
% 2.16/1.04  --time_out_prep_mult                    0.1
% 2.16/1.04  --splitting_mode                        input
% 2.16/1.04  --splitting_grd                         true
% 2.16/1.04  --splitting_cvd                         false
% 2.16/1.04  --splitting_cvd_svl                     false
% 2.16/1.04  --splitting_nvd                         32
% 2.16/1.04  --sub_typing                            true
% 2.16/1.04  --prep_gs_sim                           true
% 2.16/1.04  --prep_unflatten                        true
% 2.16/1.04  --prep_res_sim                          true
% 2.16/1.04  --prep_upred                            true
% 2.16/1.04  --prep_sem_filter                       exhaustive
% 2.16/1.04  --prep_sem_filter_out                   false
% 2.16/1.04  --pred_elim                             true
% 2.16/1.04  --res_sim_input                         true
% 2.16/1.04  --eq_ax_congr_red                       true
% 2.16/1.04  --pure_diseq_elim                       true
% 2.16/1.04  --brand_transform                       false
% 2.16/1.04  --non_eq_to_eq                          false
% 2.16/1.04  --prep_def_merge                        true
% 2.16/1.04  --prep_def_merge_prop_impl              false
% 2.16/1.04  --prep_def_merge_mbd                    true
% 2.16/1.04  --prep_def_merge_tr_red                 false
% 2.16/1.04  --prep_def_merge_tr_cl                  false
% 2.16/1.04  --smt_preprocessing                     true
% 2.16/1.04  --smt_ac_axioms                         fast
% 2.16/1.04  --preprocessed_out                      false
% 2.16/1.04  --preprocessed_stats                    false
% 2.16/1.04  
% 2.16/1.04  ------ Abstraction refinement Options
% 2.16/1.04  
% 2.16/1.04  --abstr_ref                             []
% 2.16/1.04  --abstr_ref_prep                        false
% 2.16/1.04  --abstr_ref_until_sat                   false
% 2.16/1.04  --abstr_ref_sig_restrict                funpre
% 2.16/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 2.16/1.04  --abstr_ref_under                       []
% 2.16/1.04  
% 2.16/1.04  ------ SAT Options
% 2.16/1.04  
% 2.16/1.04  --sat_mode                              false
% 2.16/1.04  --sat_fm_restart_options                ""
% 2.16/1.04  --sat_gr_def                            false
% 2.16/1.04  --sat_epr_types                         true
% 2.16/1.04  --sat_non_cyclic_types                  false
% 2.16/1.04  --sat_finite_models                     false
% 2.16/1.04  --sat_fm_lemmas                         false
% 2.16/1.04  --sat_fm_prep                           false
% 2.16/1.04  --sat_fm_uc_incr                        true
% 2.16/1.04  --sat_out_model                         small
% 2.16/1.04  --sat_out_clauses                       false
% 2.16/1.04  
% 2.16/1.04  ------ QBF Options
% 2.16/1.04  
% 2.16/1.04  --qbf_mode                              false
% 2.16/1.04  --qbf_elim_univ                         false
% 2.16/1.04  --qbf_dom_inst                          none
% 2.16/1.04  --qbf_dom_pre_inst                      false
% 2.16/1.04  --qbf_sk_in                             false
% 2.16/1.04  --qbf_pred_elim                         true
% 2.16/1.04  --qbf_split                             512
% 2.16/1.04  
% 2.16/1.04  ------ BMC1 Options
% 2.16/1.04  
% 2.16/1.04  --bmc1_incremental                      false
% 2.16/1.04  --bmc1_axioms                           reachable_all
% 2.16/1.04  --bmc1_min_bound                        0
% 2.16/1.04  --bmc1_max_bound                        -1
% 2.16/1.04  --bmc1_max_bound_default                -1
% 2.16/1.04  --bmc1_symbol_reachability              true
% 2.16/1.04  --bmc1_property_lemmas                  false
% 2.16/1.04  --bmc1_k_induction                      false
% 2.16/1.04  --bmc1_non_equiv_states                 false
% 2.16/1.04  --bmc1_deadlock                         false
% 2.16/1.04  --bmc1_ucm                              false
% 2.16/1.04  --bmc1_add_unsat_core                   none
% 2.16/1.04  --bmc1_unsat_core_children              false
% 2.16/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 2.16/1.04  --bmc1_out_stat                         full
% 2.16/1.04  --bmc1_ground_init                      false
% 2.16/1.04  --bmc1_pre_inst_next_state              false
% 2.16/1.04  --bmc1_pre_inst_state                   false
% 2.16/1.04  --bmc1_pre_inst_reach_state             false
% 2.16/1.04  --bmc1_out_unsat_core                   false
% 2.16/1.04  --bmc1_aig_witness_out                  false
% 2.16/1.04  --bmc1_verbose                          false
% 2.16/1.04  --bmc1_dump_clauses_tptp                false
% 2.16/1.04  --bmc1_dump_unsat_core_tptp             false
% 2.16/1.04  --bmc1_dump_file                        -
% 2.16/1.04  --bmc1_ucm_expand_uc_limit              128
% 2.16/1.04  --bmc1_ucm_n_expand_iterations          6
% 2.16/1.04  --bmc1_ucm_extend_mode                  1
% 2.16/1.04  --bmc1_ucm_init_mode                    2
% 2.16/1.04  --bmc1_ucm_cone_mode                    none
% 2.16/1.04  --bmc1_ucm_reduced_relation_type        0
% 2.16/1.04  --bmc1_ucm_relax_model                  4
% 2.16/1.04  --bmc1_ucm_full_tr_after_sat            true
% 2.16/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 2.16/1.04  --bmc1_ucm_layered_model                none
% 2.16/1.04  --bmc1_ucm_max_lemma_size               10
% 2.16/1.04  
% 2.16/1.04  ------ AIG Options
% 2.16/1.04  
% 2.16/1.04  --aig_mode                              false
% 2.16/1.04  
% 2.16/1.04  ------ Instantiation Options
% 2.16/1.04  
% 2.16/1.04  --instantiation_flag                    true
% 2.16/1.04  --inst_sos_flag                         false
% 2.16/1.04  --inst_sos_phase                        true
% 2.16/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.16/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.16/1.04  --inst_lit_sel_side                     num_symb
% 2.16/1.04  --inst_solver_per_active                1400
% 2.16/1.04  --inst_solver_calls_frac                1.
% 2.16/1.04  --inst_passive_queue_type               priority_queues
% 2.16/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.16/1.04  --inst_passive_queues_freq              [25;2]
% 2.16/1.04  --inst_dismatching                      true
% 2.16/1.04  --inst_eager_unprocessed_to_passive     true
% 2.16/1.04  --inst_prop_sim_given                   true
% 2.16/1.04  --inst_prop_sim_new                     false
% 2.16/1.04  --inst_subs_new                         false
% 2.16/1.04  --inst_eq_res_simp                      false
% 2.16/1.04  --inst_subs_given                       false
% 2.16/1.04  --inst_orphan_elimination               true
% 2.16/1.04  --inst_learning_loop_flag               true
% 2.16/1.04  --inst_learning_start                   3000
% 2.16/1.04  --inst_learning_factor                  2
% 2.16/1.04  --inst_start_prop_sim_after_learn       3
% 2.16/1.04  --inst_sel_renew                        solver
% 2.16/1.04  --inst_lit_activity_flag                true
% 2.16/1.04  --inst_restr_to_given                   false
% 2.16/1.04  --inst_activity_threshold               500
% 2.16/1.04  --inst_out_proof                        true
% 2.16/1.04  
% 2.16/1.04  ------ Resolution Options
% 2.16/1.04  
% 2.16/1.04  --resolution_flag                       true
% 2.16/1.04  --res_lit_sel                           adaptive
% 2.16/1.04  --res_lit_sel_side                      none
% 2.16/1.04  --res_ordering                          kbo
% 2.16/1.04  --res_to_prop_solver                    active
% 2.16/1.04  --res_prop_simpl_new                    false
% 2.16/1.04  --res_prop_simpl_given                  true
% 2.16/1.04  --res_passive_queue_type                priority_queues
% 2.16/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.16/1.04  --res_passive_queues_freq               [15;5]
% 2.16/1.04  --res_forward_subs                      full
% 2.16/1.04  --res_backward_subs                     full
% 2.16/1.04  --res_forward_subs_resolution           true
% 2.16/1.04  --res_backward_subs_resolution          true
% 2.16/1.04  --res_orphan_elimination                true
% 2.16/1.04  --res_time_limit                        2.
% 2.16/1.04  --res_out_proof                         true
% 2.16/1.04  
% 2.16/1.04  ------ Superposition Options
% 2.16/1.04  
% 2.16/1.04  --superposition_flag                    true
% 2.16/1.04  --sup_passive_queue_type                priority_queues
% 2.16/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.16/1.04  --sup_passive_queues_freq               [8;1;4]
% 2.16/1.04  --demod_completeness_check              fast
% 2.16/1.04  --demod_use_ground                      true
% 2.16/1.04  --sup_to_prop_solver                    passive
% 2.16/1.04  --sup_prop_simpl_new                    true
% 2.16/1.04  --sup_prop_simpl_given                  true
% 2.16/1.04  --sup_fun_splitting                     false
% 2.16/1.04  --sup_smt_interval                      50000
% 2.16/1.04  
% 2.16/1.04  ------ Superposition Simplification Setup
% 2.16/1.04  
% 2.16/1.04  --sup_indices_passive                   []
% 2.16/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 2.16/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/1.04  --sup_full_bw                           [BwDemod]
% 2.16/1.04  --sup_immed_triv                        [TrivRules]
% 2.16/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.16/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/1.04  --sup_immed_bw_main                     []
% 2.16/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.16/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 2.16/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.16/1.04  
% 2.16/1.04  ------ Combination Options
% 2.16/1.04  
% 2.16/1.04  --comb_res_mult                         3
% 2.16/1.04  --comb_sup_mult                         2
% 2.16/1.04  --comb_inst_mult                        10
% 2.16/1.04  
% 2.16/1.04  ------ Debug Options
% 2.16/1.04  
% 2.16/1.04  --dbg_backtrace                         false
% 2.16/1.04  --dbg_dump_prop_clauses                 false
% 2.16/1.04  --dbg_dump_prop_clauses_file            -
% 2.16/1.04  --dbg_out_stat                          false
% 2.16/1.04  ------ Parsing...
% 2.16/1.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.16/1.04  
% 2.16/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.16/1.04  
% 2.16/1.04  ------ Preprocessing... gs_s  sp: 3 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.16/1.04  
% 2.16/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.16/1.04  ------ Proving...
% 2.16/1.04  ------ Problem Properties 
% 2.16/1.04  
% 2.16/1.04  
% 2.16/1.04  clauses                                 25
% 2.16/1.04  conjectures                             4
% 2.16/1.04  EPR                                     2
% 2.16/1.04  Horn                                    21
% 2.16/1.04  unary                                   5
% 2.16/1.04  binary                                  8
% 2.16/1.04  lits                                    70
% 2.16/1.04  lits eq                                 18
% 2.16/1.04  fd_pure                                 0
% 2.16/1.04  fd_pseudo                               0
% 2.16/1.04  fd_cond                                 3
% 2.16/1.04  fd_pseudo_cond                          1
% 2.16/1.04  AC symbols                              0
% 2.16/1.04  
% 2.16/1.04  ------ Schedule dynamic 5 is on 
% 2.16/1.04  
% 2.16/1.04  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.16/1.04  
% 2.16/1.04  
% 2.16/1.04  ------ 
% 2.16/1.04  Current options:
% 2.16/1.04  ------ 
% 2.16/1.04  
% 2.16/1.04  ------ Input Options
% 2.16/1.04  
% 2.16/1.04  --out_options                           all
% 2.16/1.04  --tptp_safe_out                         true
% 2.16/1.04  --problem_path                          ""
% 2.16/1.04  --include_path                          ""
% 2.16/1.04  --clausifier                            res/vclausify_rel
% 2.16/1.04  --clausifier_options                    --mode clausify
% 2.16/1.04  --stdin                                 false
% 2.16/1.04  --stats_out                             all
% 2.16/1.04  
% 2.16/1.04  ------ General Options
% 2.16/1.04  
% 2.16/1.04  --fof                                   false
% 2.16/1.04  --time_out_real                         305.
% 2.16/1.04  --time_out_virtual                      -1.
% 2.16/1.04  --symbol_type_check                     false
% 2.16/1.04  --clausify_out                          false
% 2.16/1.04  --sig_cnt_out                           false
% 2.16/1.04  --trig_cnt_out                          false
% 2.16/1.04  --trig_cnt_out_tolerance                1.
% 2.16/1.04  --trig_cnt_out_sk_spl                   false
% 2.16/1.04  --abstr_cl_out                          false
% 2.16/1.04  
% 2.16/1.04  ------ Global Options
% 2.16/1.04  
% 2.16/1.04  --schedule                              default
% 2.16/1.04  --add_important_lit                     false
% 2.16/1.04  --prop_solver_per_cl                    1000
% 2.16/1.04  --min_unsat_core                        false
% 2.16/1.04  --soft_assumptions                      false
% 2.16/1.04  --soft_lemma_size                       3
% 2.16/1.04  --prop_impl_unit_size                   0
% 2.16/1.04  --prop_impl_unit                        []
% 2.16/1.04  --share_sel_clauses                     true
% 2.16/1.04  --reset_solvers                         false
% 2.16/1.04  --bc_imp_inh                            [conj_cone]
% 2.16/1.04  --conj_cone_tolerance                   3.
% 2.16/1.04  --extra_neg_conj                        none
% 2.16/1.04  --large_theory_mode                     true
% 2.16/1.04  --prolific_symb_bound                   200
% 2.16/1.04  --lt_threshold                          2000
% 2.16/1.04  --clause_weak_htbl                      true
% 2.16/1.04  --gc_record_bc_elim                     false
% 2.16/1.04  
% 2.16/1.04  ------ Preprocessing Options
% 2.16/1.04  
% 2.16/1.04  --preprocessing_flag                    true
% 2.16/1.04  --time_out_prep_mult                    0.1
% 2.16/1.04  --splitting_mode                        input
% 2.16/1.04  --splitting_grd                         true
% 2.16/1.04  --splitting_cvd                         false
% 2.16/1.04  --splitting_cvd_svl                     false
% 2.16/1.04  --splitting_nvd                         32
% 2.16/1.04  --sub_typing                            true
% 2.16/1.04  --prep_gs_sim                           true
% 2.16/1.04  --prep_unflatten                        true
% 2.16/1.04  --prep_res_sim                          true
% 2.16/1.04  --prep_upred                            true
% 2.16/1.04  --prep_sem_filter                       exhaustive
% 2.16/1.04  --prep_sem_filter_out                   false
% 2.16/1.04  --pred_elim                             true
% 2.16/1.04  --res_sim_input                         true
% 2.16/1.04  --eq_ax_congr_red                       true
% 2.16/1.04  --pure_diseq_elim                       true
% 2.16/1.04  --brand_transform                       false
% 2.16/1.04  --non_eq_to_eq                          false
% 2.16/1.04  --prep_def_merge                        true
% 2.16/1.04  --prep_def_merge_prop_impl              false
% 2.16/1.04  --prep_def_merge_mbd                    true
% 2.16/1.04  --prep_def_merge_tr_red                 false
% 2.16/1.04  --prep_def_merge_tr_cl                  false
% 2.16/1.04  --smt_preprocessing                     true
% 2.16/1.04  --smt_ac_axioms                         fast
% 2.16/1.04  --preprocessed_out                      false
% 2.16/1.04  --preprocessed_stats                    false
% 2.16/1.04  
% 2.16/1.04  ------ Abstraction refinement Options
% 2.16/1.04  
% 2.16/1.04  --abstr_ref                             []
% 2.16/1.04  --abstr_ref_prep                        false
% 2.16/1.04  --abstr_ref_until_sat                   false
% 2.16/1.04  --abstr_ref_sig_restrict                funpre
% 2.16/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 2.16/1.04  --abstr_ref_under                       []
% 2.16/1.04  
% 2.16/1.04  ------ SAT Options
% 2.16/1.04  
% 2.16/1.04  --sat_mode                              false
% 2.16/1.04  --sat_fm_restart_options                ""
% 2.16/1.04  --sat_gr_def                            false
% 2.16/1.04  --sat_epr_types                         true
% 2.16/1.04  --sat_non_cyclic_types                  false
% 2.16/1.04  --sat_finite_models                     false
% 2.16/1.04  --sat_fm_lemmas                         false
% 2.16/1.04  --sat_fm_prep                           false
% 2.16/1.04  --sat_fm_uc_incr                        true
% 2.16/1.04  --sat_out_model                         small
% 2.16/1.04  --sat_out_clauses                       false
% 2.16/1.04  
% 2.16/1.04  ------ QBF Options
% 2.16/1.04  
% 2.16/1.04  --qbf_mode                              false
% 2.16/1.04  --qbf_elim_univ                         false
% 2.16/1.04  --qbf_dom_inst                          none
% 2.16/1.04  --qbf_dom_pre_inst                      false
% 2.16/1.04  --qbf_sk_in                             false
% 2.16/1.04  --qbf_pred_elim                         true
% 2.16/1.04  --qbf_split                             512
% 2.16/1.04  
% 2.16/1.04  ------ BMC1 Options
% 2.16/1.04  
% 2.16/1.04  --bmc1_incremental                      false
% 2.16/1.04  --bmc1_axioms                           reachable_all
% 2.16/1.04  --bmc1_min_bound                        0
% 2.16/1.04  --bmc1_max_bound                        -1
% 2.16/1.04  --bmc1_max_bound_default                -1
% 2.16/1.04  --bmc1_symbol_reachability              true
% 2.16/1.04  --bmc1_property_lemmas                  false
% 2.16/1.04  --bmc1_k_induction                      false
% 2.16/1.04  --bmc1_non_equiv_states                 false
% 2.16/1.04  --bmc1_deadlock                         false
% 2.16/1.04  --bmc1_ucm                              false
% 2.16/1.04  --bmc1_add_unsat_core                   none
% 2.16/1.04  --bmc1_unsat_core_children              false
% 2.16/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 2.16/1.04  --bmc1_out_stat                         full
% 2.16/1.04  --bmc1_ground_init                      false
% 2.16/1.04  --bmc1_pre_inst_next_state              false
% 2.16/1.04  --bmc1_pre_inst_state                   false
% 2.16/1.04  --bmc1_pre_inst_reach_state             false
% 2.16/1.04  --bmc1_out_unsat_core                   false
% 2.16/1.04  --bmc1_aig_witness_out                  false
% 2.16/1.04  --bmc1_verbose                          false
% 2.16/1.04  --bmc1_dump_clauses_tptp                false
% 2.16/1.04  --bmc1_dump_unsat_core_tptp             false
% 2.16/1.04  --bmc1_dump_file                        -
% 2.16/1.04  --bmc1_ucm_expand_uc_limit              128
% 2.16/1.04  --bmc1_ucm_n_expand_iterations          6
% 2.16/1.04  --bmc1_ucm_extend_mode                  1
% 2.16/1.04  --bmc1_ucm_init_mode                    2
% 2.16/1.04  --bmc1_ucm_cone_mode                    none
% 2.16/1.04  --bmc1_ucm_reduced_relation_type        0
% 2.16/1.04  --bmc1_ucm_relax_model                  4
% 2.16/1.04  --bmc1_ucm_full_tr_after_sat            true
% 2.16/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 2.16/1.04  --bmc1_ucm_layered_model                none
% 2.16/1.04  --bmc1_ucm_max_lemma_size               10
% 2.16/1.04  
% 2.16/1.04  ------ AIG Options
% 2.16/1.04  
% 2.16/1.04  --aig_mode                              false
% 2.16/1.04  
% 2.16/1.04  ------ Instantiation Options
% 2.16/1.04  
% 2.16/1.04  --instantiation_flag                    true
% 2.16/1.04  --inst_sos_flag                         false
% 2.16/1.04  --inst_sos_phase                        true
% 2.16/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.16/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.16/1.04  --inst_lit_sel_side                     none
% 2.16/1.04  --inst_solver_per_active                1400
% 2.16/1.04  --inst_solver_calls_frac                1.
% 2.16/1.04  --inst_passive_queue_type               priority_queues
% 2.16/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.16/1.04  --inst_passive_queues_freq              [25;2]
% 2.16/1.04  --inst_dismatching                      true
% 2.16/1.04  --inst_eager_unprocessed_to_passive     true
% 2.16/1.04  --inst_prop_sim_given                   true
% 2.16/1.04  --inst_prop_sim_new                     false
% 2.16/1.04  --inst_subs_new                         false
% 2.16/1.04  --inst_eq_res_simp                      false
% 2.16/1.04  --inst_subs_given                       false
% 2.16/1.04  --inst_orphan_elimination               true
% 2.16/1.04  --inst_learning_loop_flag               true
% 2.16/1.04  --inst_learning_start                   3000
% 2.16/1.04  --inst_learning_factor                  2
% 2.16/1.04  --inst_start_prop_sim_after_learn       3
% 2.16/1.04  --inst_sel_renew                        solver
% 2.16/1.04  --inst_lit_activity_flag                true
% 2.16/1.04  --inst_restr_to_given                   false
% 2.16/1.04  --inst_activity_threshold               500
% 2.16/1.04  --inst_out_proof                        true
% 2.16/1.04  
% 2.16/1.04  ------ Resolution Options
% 2.16/1.04  
% 2.16/1.04  --resolution_flag                       false
% 2.16/1.04  --res_lit_sel                           adaptive
% 2.16/1.04  --res_lit_sel_side                      none
% 2.16/1.04  --res_ordering                          kbo
% 2.16/1.04  --res_to_prop_solver                    active
% 2.16/1.04  --res_prop_simpl_new                    false
% 2.16/1.04  --res_prop_simpl_given                  true
% 2.16/1.04  --res_passive_queue_type                priority_queues
% 2.16/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.16/1.04  --res_passive_queues_freq               [15;5]
% 2.16/1.04  --res_forward_subs                      full
% 2.16/1.04  --res_backward_subs                     full
% 2.16/1.04  --res_forward_subs_resolution           true
% 2.16/1.04  --res_backward_subs_resolution          true
% 2.16/1.04  --res_orphan_elimination                true
% 2.16/1.04  --res_time_limit                        2.
% 2.16/1.04  --res_out_proof                         true
% 2.16/1.04  
% 2.16/1.04  ------ Superposition Options
% 2.16/1.04  
% 2.16/1.04  --superposition_flag                    true
% 2.16/1.04  --sup_passive_queue_type                priority_queues
% 2.16/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.16/1.04  --sup_passive_queues_freq               [8;1;4]
% 2.16/1.04  --demod_completeness_check              fast
% 2.16/1.04  --demod_use_ground                      true
% 2.16/1.04  --sup_to_prop_solver                    passive
% 2.16/1.04  --sup_prop_simpl_new                    true
% 2.16/1.04  --sup_prop_simpl_given                  true
% 2.16/1.04  --sup_fun_splitting                     false
% 2.16/1.04  --sup_smt_interval                      50000
% 2.16/1.04  
% 2.16/1.04  ------ Superposition Simplification Setup
% 2.16/1.04  
% 2.16/1.04  --sup_indices_passive                   []
% 2.16/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 2.16/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/1.04  --sup_full_bw                           [BwDemod]
% 2.16/1.04  --sup_immed_triv                        [TrivRules]
% 2.16/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.16/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/1.04  --sup_immed_bw_main                     []
% 2.16/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.16/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 2.16/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.16/1.04  
% 2.16/1.04  ------ Combination Options
% 2.16/1.04  
% 2.16/1.04  --comb_res_mult                         3
% 2.16/1.04  --comb_sup_mult                         2
% 2.16/1.04  --comb_inst_mult                        10
% 2.16/1.04  
% 2.16/1.04  ------ Debug Options
% 2.16/1.04  
% 2.16/1.04  --dbg_backtrace                         false
% 2.16/1.04  --dbg_dump_prop_clauses                 false
% 2.16/1.04  --dbg_dump_prop_clauses_file            -
% 2.16/1.04  --dbg_out_stat                          false
% 2.16/1.04  
% 2.16/1.04  
% 2.16/1.04  
% 2.16/1.04  
% 2.16/1.04  ------ Proving...
% 2.16/1.04  
% 2.16/1.04  
% 2.16/1.04  % SZS status Theorem for theBenchmark.p
% 2.16/1.04  
% 2.16/1.04  % SZS output start CNFRefutation for theBenchmark.p
% 2.16/1.04  
% 2.16/1.04  fof(f5,axiom,(
% 2.16/1.04    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0))))),
% 2.16/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.16/1.04  
% 2.16/1.04  fof(f15,plain,(
% 2.16/1.04    ! [X0,X1] : (! [X2] : ((k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.16/1.04    inference(ennf_transformation,[],[f5])).
% 2.16/1.04  
% 2.16/1.04  fof(f16,plain,(
% 2.16/1.04    ! [X0,X1] : (! [X2] : (k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.16/1.04    inference(flattening,[],[f15])).
% 2.16/1.04  
% 2.16/1.04  fof(f39,plain,(
% 2.16/1.04    ( ! [X2,X0,X1] : (k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.16/1.04    inference(cnf_transformation,[],[f16])).
% 2.16/1.04  
% 2.16/1.04  fof(f21,plain,(
% 2.16/1.04    ! [X2,X3,X0,X1] : (sP0(X2,X3,X0,X1) <=> ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))))),
% 2.16/1.04    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.16/1.04  
% 2.16/1.04  fof(f23,plain,(
% 2.16/1.04    ! [X2,X3,X0,X1] : ((sP0(X2,X3,X0,X1) | ((k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0)))) & (((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))) | ~sP0(X2,X3,X0,X1)))),
% 2.16/1.04    inference(nnf_transformation,[],[f21])).
% 2.16/1.04  
% 2.16/1.04  fof(f24,plain,(
% 2.16/1.04    ! [X2,X3,X0,X1] : ((sP0(X2,X3,X0,X1) | ((k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0)))) & ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0)) | ~sP0(X2,X3,X0,X1)))),
% 2.16/1.04    inference(flattening,[],[f23])).
% 2.16/1.04  
% 2.16/1.04  fof(f25,plain,(
% 2.16/1.04    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ((k1_funct_1(X2,X1) != X0 | ~r2_hidden(X1,k1_relat_1(X2))) & k1_funct_1(X3,X0) = X1 & r2_hidden(X0,k2_relat_1(X2)))) & ((k1_funct_1(X2,X1) = X0 & r2_hidden(X1,k1_relat_1(X2))) | k1_funct_1(X3,X0) != X1 | ~r2_hidden(X0,k2_relat_1(X2)) | ~sP0(X0,X1,X2,X3)))),
% 2.16/1.04    inference(rectify,[],[f24])).
% 2.16/1.04  
% 2.16/1.04  fof(f41,plain,(
% 2.16/1.04    ( ! [X2,X0,X3,X1] : (k1_funct_1(X2,X1) = X0 | k1_funct_1(X3,X0) != X1 | ~r2_hidden(X0,k2_relat_1(X2)) | ~sP0(X0,X1,X2,X3)) )),
% 2.16/1.04    inference(cnf_transformation,[],[f25])).
% 2.16/1.04  
% 2.16/1.04  fof(f58,plain,(
% 2.16/1.04    ( ! [X2,X0,X3] : (k1_funct_1(X2,k1_funct_1(X3,X0)) = X0 | ~r2_hidden(X0,k2_relat_1(X2)) | ~sP0(X0,k1_funct_1(X3,X0),X2,X3)) )),
% 2.16/1.04    inference(equality_resolution,[],[f41])).
% 2.16/1.04  
% 2.16/1.04  fof(f6,axiom,(
% 2.16/1.04    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) => (k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0)))) & ((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) => (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) & k2_relat_1(X0) = k1_relat_1(X1))))))),
% 2.16/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.16/1.04  
% 2.16/1.04  fof(f17,plain,(
% 2.16/1.04    ! [X0] : ((! [X1] : ((k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | (k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))))) & k2_relat_1(X0) = k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.16/1.04    inference(ennf_transformation,[],[f6])).
% 2.16/1.04  
% 2.16/1.04  fof(f18,plain,(
% 2.16/1.04    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0)))) & k2_relat_1(X0) = k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.16/1.04    inference(flattening,[],[f17])).
% 2.16/1.04  
% 2.16/1.04  fof(f22,plain,(
% 2.16/1.04    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & sP0(X2,X3,X0,X1)) & k2_relat_1(X0) = k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.16/1.04    inference(definition_folding,[],[f18,f21])).
% 2.16/1.04  
% 2.16/1.04  fof(f26,plain,(
% 2.16/1.04    ! [X0] : (! [X1] : (((k2_funct_1(X0) = X1 | (? [X2,X3] : (((k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))) & k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X2,X3,X0,X1)) | k2_relat_1(X0) != k1_relat_1(X1))) & ((! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & sP0(X2,X3,X0,X1)) & k2_relat_1(X0) = k1_relat_1(X1)) | k2_funct_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.16/1.04    inference(nnf_transformation,[],[f22])).
% 2.16/1.04  
% 2.16/1.04  fof(f27,plain,(
% 2.16/1.04    ! [X0] : (! [X1] : (((k2_funct_1(X0) = X1 | ? [X2,X3] : (((k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))) & k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X2,X3,X0,X1)) | k2_relat_1(X0) != k1_relat_1(X1)) & ((! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & sP0(X2,X3,X0,X1)) & k2_relat_1(X0) = k1_relat_1(X1)) | k2_funct_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.16/1.04    inference(flattening,[],[f26])).
% 2.16/1.04  
% 2.16/1.04  fof(f28,plain,(
% 2.16/1.04    ! [X0] : (! [X1] : (((k2_funct_1(X0) = X1 | ? [X2,X3] : (((k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))) & k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X2,X3,X0,X1)) | k2_relat_1(X0) != k1_relat_1(X1)) & ((! [X4,X5] : (((k1_funct_1(X1,X4) = X5 & r2_hidden(X4,k2_relat_1(X0))) | k1_funct_1(X0,X5) != X4 | ~r2_hidden(X5,k1_relat_1(X0))) & sP0(X4,X5,X0,X1)) & k2_relat_1(X0) = k1_relat_1(X1)) | k2_funct_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.16/1.04    inference(rectify,[],[f27])).
% 2.16/1.04  
% 2.16/1.04  fof(f29,plain,(
% 2.16/1.04    ! [X1,X0] : (? [X2,X3] : (((k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))) & k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X2,X3,X0,X1)) => (((k1_funct_1(X1,sK1(X0,X1)) != sK2(X0,X1) | ~r2_hidden(sK1(X0,X1),k2_relat_1(X0))) & k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))) | ~sP0(sK1(X0,X1),sK2(X0,X1),X0,X1)))),
% 2.16/1.04    introduced(choice_axiom,[])).
% 2.16/1.04  
% 2.16/1.04  fof(f30,plain,(
% 2.16/1.04    ! [X0] : (! [X1] : (((k2_funct_1(X0) = X1 | (((k1_funct_1(X1,sK1(X0,X1)) != sK2(X0,X1) | ~r2_hidden(sK1(X0,X1),k2_relat_1(X0))) & k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))) | ~sP0(sK1(X0,X1),sK2(X0,X1),X0,X1)) | k2_relat_1(X0) != k1_relat_1(X1)) & ((! [X4,X5] : (((k1_funct_1(X1,X4) = X5 & r2_hidden(X4,k2_relat_1(X0))) | k1_funct_1(X0,X5) != X4 | ~r2_hidden(X5,k1_relat_1(X0))) & sP0(X4,X5,X0,X1)) & k2_relat_1(X0) = k1_relat_1(X1)) | k2_funct_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.16/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f28,f29])).
% 2.16/1.04  
% 2.16/1.04  fof(f46,plain,(
% 2.16/1.04    ( ! [X4,X0,X5,X1] : (sP0(X4,X5,X0,X1) | k2_funct_1(X0) != X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.16/1.04    inference(cnf_transformation,[],[f30])).
% 2.16/1.04  
% 2.16/1.04  fof(f64,plain,(
% 2.16/1.04    ( ! [X4,X0,X5] : (sP0(X4,X5,X0,k2_funct_1(X0)) | ~v1_funct_1(k2_funct_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.16/1.04    inference(equality_resolution,[],[f46])).
% 2.16/1.04  
% 2.16/1.04  fof(f7,conjecture,(
% 2.16/1.04    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0 & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0)))),
% 2.16/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.16/1.04  
% 2.16/1.04  fof(f8,negated_conjecture,(
% 2.16/1.04    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0 & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0)))),
% 2.16/1.04    inference(negated_conjecture,[],[f7])).
% 2.16/1.04  
% 2.16/1.04  fof(f19,plain,(
% 2.16/1.04    ? [X0,X1] : (((k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0 | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0) & (r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 2.16/1.04    inference(ennf_transformation,[],[f8])).
% 2.16/1.04  
% 2.16/1.04  fof(f20,plain,(
% 2.16/1.04    ? [X0,X1] : ((k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0 | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0) & r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 2.16/1.04    inference(flattening,[],[f19])).
% 2.16/1.04  
% 2.16/1.04  fof(f31,plain,(
% 2.16/1.04    ? [X0,X1] : ((k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0 | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0) & r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => ((k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) != sK3 | k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),sK3)) != sK3) & r2_hidden(sK3,k2_relat_1(sK4)) & v2_funct_1(sK4) & v1_funct_1(sK4) & v1_relat_1(sK4))),
% 2.16/1.04    introduced(choice_axiom,[])).
% 2.16/1.04  
% 2.16/1.04  fof(f32,plain,(
% 2.16/1.04    (k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) != sK3 | k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),sK3)) != sK3) & r2_hidden(sK3,k2_relat_1(sK4)) & v2_funct_1(sK4) & v1_funct_1(sK4) & v1_relat_1(sK4)),
% 2.16/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f20,f31])).
% 2.16/1.04  
% 2.16/1.04  fof(f54,plain,(
% 2.16/1.04    v2_funct_1(sK4)),
% 2.16/1.04    inference(cnf_transformation,[],[f32])).
% 2.16/1.04  
% 2.16/1.04  fof(f52,plain,(
% 2.16/1.04    v1_relat_1(sK4)),
% 2.16/1.04    inference(cnf_transformation,[],[f32])).
% 2.16/1.04  
% 2.16/1.04  fof(f53,plain,(
% 2.16/1.04    v1_funct_1(sK4)),
% 2.16/1.04    inference(cnf_transformation,[],[f32])).
% 2.16/1.04  
% 2.16/1.04  fof(f3,axiom,(
% 2.16/1.04    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 2.16/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.16/1.04  
% 2.16/1.04  fof(f11,plain,(
% 2.16/1.04    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.16/1.04    inference(ennf_transformation,[],[f3])).
% 2.16/1.04  
% 2.16/1.04  fof(f12,plain,(
% 2.16/1.04    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.16/1.04    inference(flattening,[],[f11])).
% 2.16/1.04  
% 2.16/1.04  fof(f36,plain,(
% 2.16/1.04    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.16/1.04    inference(cnf_transformation,[],[f12])).
% 2.16/1.04  
% 2.16/1.04  fof(f4,axiom,(
% 2.16/1.04    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k4_relat_1(X0)) & v1_relat_1(k4_relat_1(X0))))),
% 2.16/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.16/1.04  
% 2.16/1.04  fof(f13,plain,(
% 2.16/1.04    ! [X0] : ((v1_funct_1(k4_relat_1(X0)) & v1_relat_1(k4_relat_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.16/1.04    inference(ennf_transformation,[],[f4])).
% 2.16/1.04  
% 2.16/1.04  fof(f14,plain,(
% 2.16/1.04    ! [X0] : ((v1_funct_1(k4_relat_1(X0)) & v1_relat_1(k4_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.16/1.04    inference(flattening,[],[f13])).
% 2.16/1.04  
% 2.16/1.04  fof(f38,plain,(
% 2.16/1.04    ( ! [X0] : (v1_funct_1(k4_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.16/1.04    inference(cnf_transformation,[],[f14])).
% 2.16/1.04  
% 2.16/1.04  fof(f45,plain,(
% 2.16/1.04    ( ! [X0,X1] : (k2_relat_1(X0) = k1_relat_1(X1) | k2_funct_1(X0) != X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.16/1.04    inference(cnf_transformation,[],[f30])).
% 2.16/1.04  
% 2.16/1.04  fof(f65,plain,(
% 2.16/1.04    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(k2_funct_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.16/1.04    inference(equality_resolution,[],[f45])).
% 2.16/1.04  
% 2.16/1.04  fof(f56,plain,(
% 2.16/1.04    k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) != sK3 | k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),sK3)) != sK3),
% 2.16/1.04    inference(cnf_transformation,[],[f32])).
% 2.16/1.04  
% 2.16/1.04  fof(f37,plain,(
% 2.16/1.04    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.16/1.04    inference(cnf_transformation,[],[f14])).
% 2.16/1.04  
% 2.16/1.04  fof(f55,plain,(
% 2.16/1.04    r2_hidden(sK3,k2_relat_1(sK4))),
% 2.16/1.04    inference(cnf_transformation,[],[f32])).
% 2.16/1.04  
% 2.16/1.04  cnf(c_6,plain,
% 2.16/1.04      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.16/1.04      | ~ v1_funct_1(X2)
% 2.16/1.04      | ~ v1_funct_1(X1)
% 2.16/1.04      | ~ v1_relat_1(X2)
% 2.16/1.04      | ~ v1_relat_1(X1)
% 2.16/1.04      | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ),
% 2.16/1.04      inference(cnf_transformation,[],[f39]) ).
% 2.16/1.04  
% 2.16/1.04  cnf(c_1177,plain,
% 2.16/1.04      ( ~ r2_hidden(X0_43,k1_relat_1(X0_44))
% 2.16/1.04      | ~ v1_funct_1(X0_44)
% 2.16/1.04      | ~ v1_funct_1(X1_44)
% 2.16/1.04      | ~ v1_relat_1(X0_44)
% 2.16/1.04      | ~ v1_relat_1(X1_44)
% 2.16/1.04      | k1_funct_1(k5_relat_1(X0_44,X1_44),X0_43) = k1_funct_1(X1_44,k1_funct_1(X0_44,X0_43)) ),
% 2.16/1.04      inference(subtyping,[status(esa)],[c_6]) ).
% 2.16/1.04  
% 2.16/1.04  cnf(c_3379,plain,
% 2.16/1.04      ( ~ r2_hidden(X0_43,k1_relat_1(k2_funct_1(sK4)))
% 2.16/1.04      | ~ v1_funct_1(X0_44)
% 2.16/1.04      | ~ v1_funct_1(k2_funct_1(sK4))
% 2.16/1.04      | ~ v1_relat_1(X0_44)
% 2.16/1.04      | ~ v1_relat_1(k2_funct_1(sK4))
% 2.16/1.04      | k1_funct_1(k5_relat_1(k2_funct_1(sK4),X0_44),X0_43) = k1_funct_1(X0_44,k1_funct_1(k2_funct_1(sK4),X0_43)) ),
% 2.16/1.04      inference(instantiation,[status(thm)],[c_1177]) ).
% 2.16/1.04  
% 2.16/1.04  cnf(c_3386,plain,
% 2.16/1.04      ( ~ r2_hidden(sK3,k1_relat_1(k2_funct_1(sK4)))
% 2.16/1.04      | ~ v1_funct_1(k2_funct_1(sK4))
% 2.16/1.04      | ~ v1_funct_1(sK4)
% 2.16/1.04      | ~ v1_relat_1(k2_funct_1(sK4))
% 2.16/1.04      | ~ v1_relat_1(sK4)
% 2.16/1.04      | k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) = k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),sK3)) ),
% 2.16/1.04      inference(instantiation,[status(thm)],[c_3379]) ).
% 2.16/1.04  
% 2.16/1.04  cnf(c_1191,plain,
% 2.16/1.04      ( X0_43 != X1_43 | X2_43 != X1_43 | X2_43 = X0_43 ),
% 2.16/1.04      theory(equality) ).
% 2.16/1.04  
% 2.16/1.04  cnf(c_1889,plain,
% 2.16/1.04      ( k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) != X0_43
% 2.16/1.04      | k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) = sK3
% 2.16/1.04      | sK3 != X0_43 ),
% 2.16/1.04      inference(instantiation,[status(thm)],[c_1191]) ).
% 2.16/1.04  
% 2.16/1.04  cnf(c_1947,plain,
% 2.16/1.04      ( k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) != k1_funct_1(X0_44,X0_43)
% 2.16/1.04      | k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) = sK3
% 2.16/1.04      | sK3 != k1_funct_1(X0_44,X0_43) ),
% 2.16/1.04      inference(instantiation,[status(thm)],[c_1889]) ).
% 2.16/1.04  
% 2.16/1.04  cnf(c_2990,plain,
% 2.16/1.04      ( k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) != k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),X0_43))
% 2.16/1.04      | k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) = sK3
% 2.16/1.04      | sK3 != k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),X0_43)) ),
% 2.16/1.04      inference(instantiation,[status(thm)],[c_1947]) ).
% 2.16/1.04  
% 2.16/1.04  cnf(c_2991,plain,
% 2.16/1.04      ( k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) != k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),sK3))
% 2.16/1.04      | k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) = sK3
% 2.16/1.04      | sK3 != k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),sK3)) ),
% 2.16/1.04      inference(instantiation,[status(thm)],[c_2990]) ).
% 2.16/1.04  
% 2.16/1.04  cnf(c_1202,plain,
% 2.16/1.04      ( ~ r2_hidden(X0_43,X0_45)
% 2.16/1.04      | r2_hidden(X1_43,X1_45)
% 2.16/1.04      | X1_45 != X0_45
% 2.16/1.04      | X1_43 != X0_43 ),
% 2.16/1.04      theory(equality) ).
% 2.16/1.04  
% 2.16/1.04  cnf(c_1896,plain,
% 2.16/1.04      ( r2_hidden(X0_43,X0_45)
% 2.16/1.04      | ~ r2_hidden(sK3,k2_relat_1(sK4))
% 2.16/1.04      | X0_45 != k2_relat_1(sK4)
% 2.16/1.04      | X0_43 != sK3 ),
% 2.16/1.04      inference(instantiation,[status(thm)],[c_1202]) ).
% 2.16/1.04  
% 2.16/1.04  cnf(c_2584,plain,
% 2.16/1.04      ( r2_hidden(X0_43,k1_relat_1(k2_funct_1(sK4)))
% 2.16/1.04      | ~ r2_hidden(sK3,k2_relat_1(sK4))
% 2.16/1.04      | k1_relat_1(k2_funct_1(sK4)) != k2_relat_1(sK4)
% 2.16/1.04      | X0_43 != sK3 ),
% 2.16/1.04      inference(instantiation,[status(thm)],[c_1896]) ).
% 2.16/1.04  
% 2.16/1.04  cnf(c_2586,plain,
% 2.16/1.04      ( r2_hidden(sK3,k1_relat_1(k2_funct_1(sK4)))
% 2.16/1.04      | ~ r2_hidden(sK3,k2_relat_1(sK4))
% 2.16/1.04      | k1_relat_1(k2_funct_1(sK4)) != k2_relat_1(sK4)
% 2.16/1.04      | sK3 != sK3 ),
% 2.16/1.04      inference(instantiation,[status(thm)],[c_2584]) ).
% 2.16/1.04  
% 2.16/1.04  cnf(c_2118,plain,
% 2.16/1.04      ( k1_funct_1(X0_44,X0_43) != X1_43
% 2.16/1.04      | sK3 != X1_43
% 2.16/1.04      | sK3 = k1_funct_1(X0_44,X0_43) ),
% 2.16/1.04      inference(instantiation,[status(thm)],[c_1191]) ).
% 2.16/1.04  
% 2.16/1.04  cnf(c_2431,plain,
% 2.16/1.04      ( k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),X0_43)) != X0_43
% 2.16/1.04      | sK3 != X0_43
% 2.16/1.04      | sK3 = k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),X0_43)) ),
% 2.16/1.04      inference(instantiation,[status(thm)],[c_2118]) ).
% 2.16/1.04  
% 2.16/1.04  cnf(c_2432,plain,
% 2.16/1.04      ( k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),sK3)) != sK3
% 2.16/1.04      | sK3 = k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),sK3))
% 2.16/1.04      | sK3 != sK3 ),
% 2.16/1.04      inference(instantiation,[status(thm)],[c_2431]) ).
% 2.16/1.04  
% 2.16/1.04  cnf(c_1195,plain,
% 2.16/1.04      ( ~ v1_relat_1(X0_44) | v1_relat_1(X1_44) | X1_44 != X0_44 ),
% 2.16/1.04      theory(equality) ).
% 2.16/1.04  
% 2.16/1.04  cnf(c_2084,plain,
% 2.16/1.04      ( ~ v1_relat_1(X0_44)
% 2.16/1.04      | v1_relat_1(k2_funct_1(sK4))
% 2.16/1.04      | k2_funct_1(sK4) != X0_44 ),
% 2.16/1.04      inference(instantiation,[status(thm)],[c_1195]) ).
% 2.16/1.04  
% 2.16/1.04  cnf(c_2296,plain,
% 2.16/1.04      ( v1_relat_1(k2_funct_1(sK4))
% 2.16/1.04      | ~ v1_relat_1(k4_relat_1(sK4))
% 2.16/1.04      | k2_funct_1(sK4) != k4_relat_1(sK4) ),
% 2.16/1.04      inference(instantiation,[status(thm)],[c_2084]) ).
% 2.16/1.04  
% 2.16/1.04  cnf(c_10,plain,
% 2.16/1.04      ( ~ sP0(X0,k1_funct_1(X1,X0),X2,X1)
% 2.16/1.04      | ~ r2_hidden(X0,k2_relat_1(X2))
% 2.16/1.04      | k1_funct_1(X2,k1_funct_1(X1,X0)) = X0 ),
% 2.16/1.04      inference(cnf_transformation,[],[f58]) ).
% 2.16/1.04  
% 2.16/1.04  cnf(c_1173,plain,
% 2.16/1.04      ( ~ sP0(X0_43,k1_funct_1(X0_44,X0_43),X1_44,X0_44)
% 2.16/1.04      | ~ r2_hidden(X0_43,k2_relat_1(X1_44))
% 2.16/1.04      | k1_funct_1(X1_44,k1_funct_1(X0_44,X0_43)) = X0_43 ),
% 2.16/1.04      inference(subtyping,[status(esa)],[c_10]) ).
% 2.16/1.04  
% 2.16/1.04  cnf(c_1978,plain,
% 2.16/1.04      ( ~ sP0(X0_43,k1_funct_1(k2_funct_1(sK4),X0_43),sK4,k2_funct_1(sK4))
% 2.16/1.04      | ~ r2_hidden(X0_43,k2_relat_1(sK4))
% 2.16/1.04      | k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),X0_43)) = X0_43 ),
% 2.16/1.04      inference(instantiation,[status(thm)],[c_1173]) ).
% 2.16/1.04  
% 2.16/1.04  cnf(c_1981,plain,
% 2.16/1.04      ( ~ sP0(sK3,k1_funct_1(k2_funct_1(sK4),sK3),sK4,k2_funct_1(sK4))
% 2.16/1.04      | ~ r2_hidden(sK3,k2_relat_1(sK4))
% 2.16/1.04      | k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),sK3)) = sK3 ),
% 2.16/1.04      inference(instantiation,[status(thm)],[c_1978]) ).
% 2.16/1.04  
% 2.16/1.04  cnf(c_1199,plain,
% 2.16/1.04      ( ~ v1_funct_1(X0_44) | v1_funct_1(X1_44) | X1_44 != X0_44 ),
% 2.16/1.04      theory(equality) ).
% 2.16/1.04  
% 2.16/1.04  cnf(c_1879,plain,
% 2.16/1.04      ( ~ v1_funct_1(X0_44)
% 2.16/1.04      | v1_funct_1(k2_funct_1(sK4))
% 2.16/1.04      | k2_funct_1(sK4) != X0_44 ),
% 2.16/1.04      inference(instantiation,[status(thm)],[c_1199]) ).
% 2.16/1.04  
% 2.16/1.04  cnf(c_1969,plain,
% 2.16/1.04      ( v1_funct_1(k2_funct_1(sK4))
% 2.16/1.04      | ~ v1_funct_1(k4_relat_1(sK4))
% 2.16/1.04      | k2_funct_1(sK4) != k4_relat_1(sK4) ),
% 2.16/1.04      inference(instantiation,[status(thm)],[c_1879]) ).
% 2.16/1.04  
% 2.16/1.04  cnf(c_17,plain,
% 2.16/1.04      ( sP0(X0,X1,X2,k2_funct_1(X2))
% 2.16/1.04      | ~ v1_funct_1(X2)
% 2.16/1.04      | ~ v1_funct_1(k2_funct_1(X2))
% 2.16/1.04      | ~ v2_funct_1(X2)
% 2.16/1.04      | ~ v1_relat_1(X2)
% 2.16/1.04      | ~ v1_relat_1(k2_funct_1(X2)) ),
% 2.16/1.04      inference(cnf_transformation,[],[f64]) ).
% 2.16/1.04  
% 2.16/1.04  cnf(c_21,negated_conjecture,
% 2.16/1.04      ( v2_funct_1(sK4) ),
% 2.16/1.04      inference(cnf_transformation,[],[f54]) ).
% 2.16/1.04  
% 2.16/1.04  cnf(c_436,plain,
% 2.16/1.04      ( sP0(X0,X1,X2,k2_funct_1(X2))
% 2.16/1.04      | ~ v1_funct_1(X2)
% 2.16/1.04      | ~ v1_funct_1(k2_funct_1(X2))
% 2.16/1.04      | ~ v1_relat_1(X2)
% 2.16/1.04      | ~ v1_relat_1(k2_funct_1(X2))
% 2.16/1.04      | sK4 != X2 ),
% 2.16/1.04      inference(resolution_lifted,[status(thm)],[c_17,c_21]) ).
% 2.16/1.04  
% 2.16/1.04  cnf(c_437,plain,
% 2.16/1.04      ( sP0(X0,X1,sK4,k2_funct_1(sK4))
% 2.16/1.04      | ~ v1_funct_1(k2_funct_1(sK4))
% 2.16/1.04      | ~ v1_funct_1(sK4)
% 2.16/1.04      | ~ v1_relat_1(k2_funct_1(sK4))
% 2.16/1.04      | ~ v1_relat_1(sK4) ),
% 2.16/1.04      inference(unflattening,[status(thm)],[c_436]) ).
% 2.16/1.04  
% 2.16/1.04  cnf(c_23,negated_conjecture,
% 2.16/1.04      ( v1_relat_1(sK4) ),
% 2.16/1.04      inference(cnf_transformation,[],[f52]) ).
% 2.16/1.04  
% 2.16/1.04  cnf(c_22,negated_conjecture,
% 2.16/1.04      ( v1_funct_1(sK4) ),
% 2.16/1.04      inference(cnf_transformation,[],[f53]) ).
% 2.16/1.04  
% 2.16/1.04  cnf(c_441,plain,
% 2.16/1.04      ( ~ v1_relat_1(k2_funct_1(sK4))
% 2.16/1.04      | sP0(X0,X1,sK4,k2_funct_1(sK4))
% 2.16/1.04      | ~ v1_funct_1(k2_funct_1(sK4)) ),
% 2.16/1.04      inference(global_propositional_subsumption,
% 2.16/1.04                [status(thm)],
% 2.16/1.04                [c_437,c_23,c_22]) ).
% 2.16/1.04  
% 2.16/1.04  cnf(c_442,plain,
% 2.16/1.04      ( sP0(X0,X1,sK4,k2_funct_1(sK4))
% 2.16/1.04      | ~ v1_funct_1(k2_funct_1(sK4))
% 2.16/1.04      | ~ v1_relat_1(k2_funct_1(sK4)) ),
% 2.16/1.04      inference(renaming,[status(thm)],[c_441]) ).
% 2.16/1.04  
% 2.16/1.04  cnf(c_1159,plain,
% 2.16/1.04      ( sP0(X0_43,X1_43,sK4,k2_funct_1(sK4))
% 2.16/1.04      | ~ v1_funct_1(k2_funct_1(sK4))
% 2.16/1.04      | ~ v1_relat_1(k2_funct_1(sK4)) ),
% 2.16/1.04      inference(subtyping,[status(esa)],[c_442]) ).
% 2.16/1.04  
% 2.16/1.04  cnf(c_1185,plain,
% 2.16/1.04      ( sP0(X0_43,X1_43,sK4,k2_funct_1(sK4)) | ~ sP2_iProver_split ),
% 2.16/1.04      inference(splitting,
% 2.16/1.04                [splitting(split),new_symbols(definition,[sP2_iProver_split])],
% 2.16/1.04                [c_1159]) ).
% 2.16/1.04  
% 2.16/1.04  cnf(c_1905,plain,
% 2.16/1.04      ( sP0(X0_43,k1_funct_1(k2_funct_1(sK4),X0_43),sK4,k2_funct_1(sK4))
% 2.16/1.04      | ~ sP2_iProver_split ),
% 2.16/1.04      inference(instantiation,[status(thm)],[c_1185]) ).
% 2.16/1.04  
% 2.16/1.04  cnf(c_1911,plain,
% 2.16/1.04      ( sP0(sK3,k1_funct_1(k2_funct_1(sK4),sK3),sK4,k2_funct_1(sK4))
% 2.16/1.04      | ~ sP2_iProver_split ),
% 2.16/1.04      inference(instantiation,[status(thm)],[c_1905]) ).
% 2.16/1.04  
% 2.16/1.04  cnf(c_1186,plain,
% 2.16/1.04      ( ~ v1_funct_1(k2_funct_1(sK4))
% 2.16/1.04      | ~ v1_relat_1(k2_funct_1(sK4))
% 2.16/1.04      | sP2_iProver_split ),
% 2.16/1.04      inference(splitting,
% 2.16/1.04                [splitting(split),new_symbols(definition,[])],
% 2.16/1.04                [c_1159]) ).
% 2.16/1.04  
% 2.16/1.04  cnf(c_1657,plain,
% 2.16/1.04      ( v1_funct_1(k2_funct_1(sK4)) != iProver_top
% 2.16/1.04      | v1_relat_1(k2_funct_1(sK4)) != iProver_top
% 2.16/1.04      | sP2_iProver_split = iProver_top ),
% 2.16/1.04      inference(predicate_to_equality,[status(thm)],[c_1186]) ).
% 2.16/1.04  
% 2.16/1.04  cnf(c_3,plain,
% 2.16/1.04      ( ~ v1_funct_1(X0)
% 2.16/1.04      | ~ v2_funct_1(X0)
% 2.16/1.04      | ~ v1_relat_1(X0)
% 2.16/1.04      | k2_funct_1(X0) = k4_relat_1(X0) ),
% 2.16/1.04      inference(cnf_transformation,[],[f36]) ).
% 2.16/1.04  
% 2.16/1.04  cnf(c_380,plain,
% 2.16/1.04      ( ~ v1_funct_1(X0)
% 2.16/1.04      | ~ v1_relat_1(X0)
% 2.16/1.04      | k2_funct_1(X0) = k4_relat_1(X0)
% 2.16/1.04      | sK4 != X0 ),
% 2.16/1.04      inference(resolution_lifted,[status(thm)],[c_3,c_21]) ).
% 2.16/1.04  
% 2.16/1.04  cnf(c_381,plain,
% 2.16/1.04      ( ~ v1_funct_1(sK4)
% 2.16/1.04      | ~ v1_relat_1(sK4)
% 2.16/1.04      | k2_funct_1(sK4) = k4_relat_1(sK4) ),
% 2.16/1.04      inference(unflattening,[status(thm)],[c_380]) ).
% 2.16/1.04  
% 2.16/1.04  cnf(c_74,plain,
% 2.16/1.04      ( ~ v1_funct_1(sK4)
% 2.16/1.04      | ~ v2_funct_1(sK4)
% 2.16/1.04      | ~ v1_relat_1(sK4)
% 2.16/1.04      | k2_funct_1(sK4) = k4_relat_1(sK4) ),
% 2.16/1.04      inference(instantiation,[status(thm)],[c_3]) ).
% 2.16/1.04  
% 2.16/1.04  cnf(c_383,plain,
% 2.16/1.04      ( k2_funct_1(sK4) = k4_relat_1(sK4) ),
% 2.16/1.04      inference(global_propositional_subsumption,
% 2.16/1.04                [status(thm)],
% 2.16/1.04                [c_381,c_23,c_22,c_21,c_74]) ).
% 2.16/1.04  
% 2.16/1.04  cnf(c_1162,plain,
% 2.16/1.04      ( k2_funct_1(sK4) = k4_relat_1(sK4) ),
% 2.16/1.04      inference(subtyping,[status(esa)],[c_383]) ).
% 2.16/1.04  
% 2.16/1.04  cnf(c_1712,plain,
% 2.16/1.04      ( v1_funct_1(k4_relat_1(sK4)) != iProver_top
% 2.16/1.04      | v1_relat_1(k4_relat_1(sK4)) != iProver_top
% 2.16/1.04      | sP2_iProver_split = iProver_top ),
% 2.16/1.04      inference(light_normalisation,[status(thm)],[c_1657,c_1162]) ).
% 2.16/1.04  
% 2.16/1.04  cnf(c_4,plain,
% 2.16/1.04      ( ~ v1_funct_1(X0)
% 2.16/1.04      | v1_funct_1(k4_relat_1(X0))
% 2.16/1.04      | ~ v2_funct_1(X0)
% 2.16/1.04      | ~ v1_relat_1(X0) ),
% 2.16/1.04      inference(cnf_transformation,[],[f38]) ).
% 2.16/1.04  
% 2.16/1.04  cnf(c_369,plain,
% 2.16/1.04      ( ~ v1_funct_1(X0)
% 2.16/1.04      | v1_funct_1(k4_relat_1(X0))
% 2.16/1.04      | ~ v1_relat_1(X0)
% 2.16/1.04      | sK4 != X0 ),
% 2.16/1.04      inference(resolution_lifted,[status(thm)],[c_4,c_21]) ).
% 2.16/1.04  
% 2.16/1.04  cnf(c_370,plain,
% 2.16/1.04      ( v1_funct_1(k4_relat_1(sK4))
% 2.16/1.04      | ~ v1_funct_1(sK4)
% 2.16/1.04      | ~ v1_relat_1(sK4) ),
% 2.16/1.04      inference(unflattening,[status(thm)],[c_369]) ).
% 2.16/1.04  
% 2.16/1.04  cnf(c_71,plain,
% 2.16/1.04      ( v1_funct_1(k4_relat_1(sK4))
% 2.16/1.04      | ~ v1_funct_1(sK4)
% 2.16/1.04      | ~ v2_funct_1(sK4)
% 2.16/1.04      | ~ v1_relat_1(sK4) ),
% 2.16/1.04      inference(instantiation,[status(thm)],[c_4]) ).
% 2.16/1.04  
% 2.16/1.04  cnf(c_372,plain,
% 2.16/1.04      ( v1_funct_1(k4_relat_1(sK4)) ),
% 2.16/1.04      inference(global_propositional_subsumption,
% 2.16/1.04                [status(thm)],
% 2.16/1.04                [c_370,c_23,c_22,c_21,c_71]) ).
% 2.16/1.04  
% 2.16/1.04  cnf(c_1163,plain,
% 2.16/1.04      ( v1_funct_1(k4_relat_1(sK4)) ),
% 2.16/1.04      inference(subtyping,[status(esa)],[c_372]) ).
% 2.16/1.04  
% 2.16/1.04  cnf(c_1652,plain,
% 2.16/1.04      ( v1_funct_1(k4_relat_1(sK4)) = iProver_top ),
% 2.16/1.04      inference(predicate_to_equality,[status(thm)],[c_1163]) ).
% 2.16/1.04  
% 2.16/1.04  cnf(c_1716,plain,
% 2.16/1.04      ( v1_relat_1(k4_relat_1(sK4)) != iProver_top
% 2.16/1.04      | sP2_iProver_split = iProver_top ),
% 2.16/1.04      inference(forward_subsumption_resolution,
% 2.16/1.04                [status(thm)],
% 2.16/1.04                [c_1712,c_1652]) ).
% 2.16/1.04  
% 2.16/1.04  cnf(c_1831,plain,
% 2.16/1.04      ( ~ v1_relat_1(k4_relat_1(sK4)) | sP2_iProver_split ),
% 2.16/1.04      inference(predicate_to_equality_rev,[status(thm)],[c_1716]) ).
% 2.16/1.04  
% 2.16/1.04  cnf(c_18,plain,
% 2.16/1.04      ( ~ v1_funct_1(X0)
% 2.16/1.04      | ~ v1_funct_1(k2_funct_1(X0))
% 2.16/1.04      | ~ v2_funct_1(X0)
% 2.16/1.04      | ~ v1_relat_1(X0)
% 2.16/1.04      | ~ v1_relat_1(k2_funct_1(X0))
% 2.16/1.04      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 2.16/1.04      inference(cnf_transformation,[],[f65]) ).
% 2.16/1.04  
% 2.16/1.04  cnf(c_265,plain,
% 2.16/1.04      ( ~ v1_funct_1(X0)
% 2.16/1.04      | ~ v1_funct_1(k2_funct_1(X0))
% 2.16/1.04      | ~ v1_relat_1(X0)
% 2.16/1.04      | ~ v1_relat_1(k2_funct_1(X0))
% 2.16/1.04      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 2.16/1.04      | sK4 != X0 ),
% 2.16/1.04      inference(resolution_lifted,[status(thm)],[c_18,c_21]) ).
% 2.16/1.04  
% 2.16/1.04  cnf(c_266,plain,
% 2.16/1.04      ( ~ v1_funct_1(k2_funct_1(sK4))
% 2.16/1.04      | ~ v1_funct_1(sK4)
% 2.16/1.04      | ~ v1_relat_1(k2_funct_1(sK4))
% 2.16/1.04      | ~ v1_relat_1(sK4)
% 2.16/1.04      | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
% 2.16/1.04      inference(unflattening,[status(thm)],[c_265]) ).
% 2.16/1.04  
% 2.16/1.04  cnf(c_268,plain,
% 2.16/1.04      ( ~ v1_relat_1(k2_funct_1(sK4))
% 2.16/1.04      | ~ v1_funct_1(k2_funct_1(sK4))
% 2.16/1.04      | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
% 2.16/1.04      inference(global_propositional_subsumption,
% 2.16/1.04                [status(thm)],
% 2.16/1.04                [c_266,c_23,c_22]) ).
% 2.16/1.04  
% 2.16/1.04  cnf(c_269,plain,
% 2.16/1.04      ( ~ v1_funct_1(k2_funct_1(sK4))
% 2.16/1.04      | ~ v1_relat_1(k2_funct_1(sK4))
% 2.16/1.04      | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
% 2.16/1.04      inference(renaming,[status(thm)],[c_268]) ).
% 2.16/1.04  
% 2.16/1.04  cnf(c_1167,plain,
% 2.16/1.04      ( ~ v1_funct_1(k2_funct_1(sK4))
% 2.16/1.04      | ~ v1_relat_1(k2_funct_1(sK4))
% 2.16/1.04      | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
% 2.16/1.04      inference(subtyping,[status(esa)],[c_269]) ).
% 2.16/1.04  
% 2.16/1.04  cnf(c_19,negated_conjecture,
% 2.16/1.04      ( k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) != sK3
% 2.16/1.04      | k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),sK3)) != sK3 ),
% 2.16/1.04      inference(cnf_transformation,[],[f56]) ).
% 2.16/1.04  
% 2.16/1.04  cnf(c_1171,negated_conjecture,
% 2.16/1.04      ( k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) != sK3
% 2.16/1.04      | k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),sK3)) != sK3 ),
% 2.16/1.04      inference(subtyping,[status(esa)],[c_19]) ).
% 2.16/1.04  
% 2.16/1.04  cnf(c_1188,plain,( X0_43 = X0_43 ),theory(equality) ).
% 2.16/1.04  
% 2.16/1.04  cnf(c_1219,plain,
% 2.16/1.04      ( sK3 = sK3 ),
% 2.16/1.04      inference(instantiation,[status(thm)],[c_1188]) ).
% 2.16/1.04  
% 2.16/1.04  cnf(c_5,plain,
% 2.16/1.04      ( ~ v1_funct_1(X0)
% 2.16/1.04      | ~ v2_funct_1(X0)
% 2.16/1.04      | ~ v1_relat_1(X0)
% 2.16/1.04      | v1_relat_1(k4_relat_1(X0)) ),
% 2.16/1.04      inference(cnf_transformation,[],[f37]) ).
% 2.16/1.04  
% 2.16/1.04  cnf(c_68,plain,
% 2.16/1.04      ( ~ v1_funct_1(sK4)
% 2.16/1.04      | ~ v2_funct_1(sK4)
% 2.16/1.04      | v1_relat_1(k4_relat_1(sK4))
% 2.16/1.04      | ~ v1_relat_1(sK4) ),
% 2.16/1.04      inference(instantiation,[status(thm)],[c_5]) ).
% 2.16/1.04  
% 2.16/1.04  cnf(c_20,negated_conjecture,
% 2.16/1.04      ( r2_hidden(sK3,k2_relat_1(sK4)) ),
% 2.16/1.04      inference(cnf_transformation,[],[f55]) ).
% 2.16/1.04  
% 2.16/1.04  cnf(contradiction,plain,
% 2.16/1.04      ( $false ),
% 2.16/1.04      inference(minisat,
% 2.16/1.04                [status(thm)],
% 2.16/1.04                [c_3386,c_2991,c_2586,c_2432,c_2296,c_1981,c_1969,c_1911,
% 2.16/1.04                 c_1831,c_1162,c_1167,c_1171,c_1219,c_71,c_68,c_20,c_21,
% 2.16/1.04                 c_22,c_23]) ).
% 2.16/1.04  
% 2.16/1.04  
% 2.16/1.04  % SZS output end CNFRefutation for theBenchmark.p
% 2.16/1.04  
% 2.16/1.04  ------                               Statistics
% 2.16/1.04  
% 2.16/1.04  ------ General
% 2.16/1.04  
% 2.16/1.04  abstr_ref_over_cycles:                  0
% 2.16/1.04  abstr_ref_under_cycles:                 0
% 2.16/1.04  gc_basic_clause_elim:                   0
% 2.16/1.04  forced_gc_time:                         0
% 2.16/1.04  parsing_time:                           0.006
% 2.16/1.04  unif_index_cands_time:                  0.
% 2.16/1.04  unif_index_add_time:                    0.
% 2.16/1.04  orderings_time:                         0.
% 2.16/1.04  out_proof_time:                         0.009
% 2.16/1.04  total_time:                             0.111
% 2.16/1.04  num_of_symbols:                         52
% 2.16/1.04  num_of_terms:                           3130
% 2.16/1.04  
% 2.16/1.04  ------ Preprocessing
% 2.16/1.04  
% 2.16/1.04  num_of_splits:                          3
% 2.16/1.04  num_of_split_atoms:                     3
% 2.16/1.04  num_of_reused_defs:                     0
% 2.16/1.04  num_eq_ax_congr_red:                    10
% 2.16/1.04  num_of_sem_filtered_clauses:            1
% 2.16/1.04  num_of_subtypes:                        3
% 2.16/1.04  monotx_restored_types:                  1
% 2.16/1.04  sat_num_of_epr_types:                   0
% 2.16/1.04  sat_num_of_non_cyclic_types:            0
% 2.16/1.04  sat_guarded_non_collapsed_types:        1
% 2.16/1.04  num_pure_diseq_elim:                    0
% 2.16/1.04  simp_replaced_by:                       0
% 2.16/1.04  res_preprocessed:                       132
% 2.16/1.04  prep_upred:                             0
% 2.16/1.04  prep_unflattend:                        153
% 2.16/1.04  smt_new_axioms:                         0
% 2.16/1.04  pred_elim_cands:                        4
% 2.16/1.04  pred_elim:                              1
% 2.16/1.04  pred_elim_cl:                           1
% 2.16/1.04  pred_elim_cycles:                       3
% 2.16/1.04  merged_defs:                            0
% 2.16/1.04  merged_defs_ncl:                        0
% 2.16/1.04  bin_hyper_res:                          0
% 2.16/1.04  prep_cycles:                            4
% 2.16/1.04  pred_elim_time:                         0.011
% 2.16/1.04  splitting_time:                         0.
% 2.16/1.04  sem_filter_time:                        0.
% 2.16/1.04  monotx_time:                            0.
% 2.16/1.04  subtype_inf_time:                       0.001
% 2.16/1.04  
% 2.16/1.04  ------ Problem properties
% 2.16/1.04  
% 2.16/1.04  clauses:                                25
% 2.16/1.04  conjectures:                            4
% 2.16/1.04  epr:                                    2
% 2.16/1.04  horn:                                   21
% 2.16/1.04  ground:                                 10
% 2.16/1.04  unary:                                  5
% 2.16/1.04  binary:                                 8
% 2.16/1.04  lits:                                   70
% 2.16/1.04  lits_eq:                                18
% 2.16/1.04  fd_pure:                                0
% 2.16/1.04  fd_pseudo:                              0
% 2.16/1.04  fd_cond:                                3
% 2.16/1.04  fd_pseudo_cond:                         1
% 2.16/1.04  ac_symbols:                             0
% 2.16/1.04  
% 2.16/1.04  ------ Propositional Solver
% 2.16/1.04  
% 2.16/1.04  prop_solver_calls:                      26
% 2.16/1.04  prop_fast_solver_calls:                 1058
% 2.16/1.04  smt_solver_calls:                       0
% 2.16/1.04  smt_fast_solver_calls:                  0
% 2.16/1.04  prop_num_of_clauses:                    949
% 2.16/1.04  prop_preprocess_simplified:             4371
% 2.16/1.04  prop_fo_subsumed:                       26
% 2.16/1.04  prop_solver_time:                       0.
% 2.16/1.04  smt_solver_time:                        0.
% 2.16/1.04  smt_fast_solver_time:                   0.
% 2.16/1.04  prop_fast_solver_time:                  0.
% 2.16/1.04  prop_unsat_core_time:                   0.
% 2.16/1.04  
% 2.16/1.04  ------ QBF
% 2.16/1.04  
% 2.16/1.04  qbf_q_res:                              0
% 2.16/1.04  qbf_num_tautologies:                    0
% 2.16/1.04  qbf_prep_cycles:                        0
% 2.16/1.04  
% 2.16/1.04  ------ BMC1
% 2.16/1.04  
% 2.16/1.04  bmc1_current_bound:                     -1
% 2.16/1.04  bmc1_last_solved_bound:                 -1
% 2.16/1.04  bmc1_unsat_core_size:                   -1
% 2.16/1.04  bmc1_unsat_core_parents_size:           -1
% 2.16/1.04  bmc1_merge_next_fun:                    0
% 2.16/1.04  bmc1_unsat_core_clauses_time:           0.
% 2.16/1.04  
% 2.16/1.04  ------ Instantiation
% 2.16/1.04  
% 2.16/1.04  inst_num_of_clauses:                    312
% 2.16/1.04  inst_num_in_passive:                    125
% 2.16/1.04  inst_num_in_active:                     180
% 2.16/1.04  inst_num_in_unprocessed:                6
% 2.16/1.04  inst_num_of_loops:                      188
% 2.16/1.04  inst_num_of_learning_restarts:          0
% 2.16/1.04  inst_num_moves_active_passive:          3
% 2.16/1.04  inst_lit_activity:                      0
% 2.16/1.04  inst_lit_activity_moves:                0
% 2.16/1.04  inst_num_tautologies:                   0
% 2.16/1.04  inst_num_prop_implied:                  0
% 2.16/1.04  inst_num_existing_simplified:           0
% 2.16/1.04  inst_num_eq_res_simplified:             0
% 2.16/1.04  inst_num_child_elim:                    0
% 2.16/1.04  inst_num_of_dismatching_blockings:      114
% 2.16/1.04  inst_num_of_non_proper_insts:           302
% 2.16/1.04  inst_num_of_duplicates:                 0
% 2.16/1.04  inst_inst_num_from_inst_to_res:         0
% 2.16/1.04  inst_dismatching_checking_time:         0.
% 2.16/1.04  
% 2.16/1.04  ------ Resolution
% 2.16/1.04  
% 2.16/1.04  res_num_of_clauses:                     0
% 2.16/1.04  res_num_in_passive:                     0
% 2.16/1.04  res_num_in_active:                      0
% 2.16/1.04  res_num_of_loops:                       136
% 2.16/1.04  res_forward_subset_subsumed:            59
% 2.16/1.04  res_backward_subset_subsumed:           0
% 2.16/1.04  res_forward_subsumed:                   0
% 2.16/1.04  res_backward_subsumed:                  0
% 2.16/1.04  res_forward_subsumption_resolution:     0
% 2.16/1.04  res_backward_subsumption_resolution:    0
% 2.16/1.04  res_clause_to_clause_subsumption:       106
% 2.16/1.04  res_orphan_elimination:                 0
% 2.16/1.04  res_tautology_del:                      73
% 2.16/1.04  res_num_eq_res_simplified:              0
% 2.16/1.04  res_num_sel_changes:                    0
% 2.16/1.04  res_moves_from_active_to_pass:          0
% 2.16/1.04  
% 2.16/1.04  ------ Superposition
% 2.16/1.04  
% 2.16/1.04  sup_time_total:                         0.
% 2.16/1.04  sup_time_generating:                    0.
% 2.16/1.04  sup_time_sim_full:                      0.
% 2.16/1.04  sup_time_sim_immed:                     0.
% 2.16/1.04  
% 2.16/1.04  sup_num_of_clauses:                     47
% 2.16/1.04  sup_num_in_active:                      35
% 2.16/1.04  sup_num_in_passive:                     12
% 2.16/1.04  sup_num_of_loops:                       36
% 2.16/1.04  sup_fw_superposition:                   22
% 2.16/1.04  sup_bw_superposition:                   6
% 2.16/1.04  sup_immediate_simplified:               5
% 2.16/1.04  sup_given_eliminated:                   0
% 2.16/1.04  comparisons_done:                       0
% 2.16/1.04  comparisons_avoided:                    0
% 2.16/1.04  
% 2.16/1.04  ------ Simplifications
% 2.16/1.04  
% 2.16/1.04  
% 2.16/1.04  sim_fw_subset_subsumed:                 1
% 2.16/1.04  sim_bw_subset_subsumed:                 1
% 2.16/1.04  sim_fw_subsumed:                        0
% 2.16/1.04  sim_bw_subsumed:                        0
% 2.16/1.04  sim_fw_subsumption_res:                 4
% 2.16/1.04  sim_bw_subsumption_res:                 0
% 2.16/1.04  sim_tautology_del:                      2
% 2.16/1.04  sim_eq_tautology_del:                   2
% 2.16/1.04  sim_eq_res_simp:                        1
% 2.16/1.04  sim_fw_demodulated:                     3
% 2.16/1.04  sim_bw_demodulated:                     1
% 2.16/1.04  sim_light_normalised:                   11
% 2.16/1.04  sim_joinable_taut:                      0
% 2.16/1.04  sim_joinable_simp:                      0
% 2.16/1.04  sim_ac_normalised:                      0
% 2.16/1.04  sim_smt_subsumption:                    0
% 2.16/1.04  
%------------------------------------------------------------------------------
