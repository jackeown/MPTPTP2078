%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:50:42 EST 2020

% Result     : Theorem 2.51s
% Output     : CNFRefutation 2.51s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 641 expanded)
%              Number of clauses        :   96 ( 218 expanded)
%              Number of leaves         :   14 ( 122 expanded)
%              Depth                    :   19
%              Number of atoms          :  634 (2987 expanded)
%              Number of equality atoms :  274 ( 724 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   19 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => v2_funct_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => v2_funct_1(k2_funct_1(X0)) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f15,plain,(
    ? [X0] :
      ( ~ v2_funct_1(k2_funct_1(X0))
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
    ? [X0] :
      ( ~ v2_funct_1(k2_funct_1(X0))
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f31,plain,
    ( ? [X0] :
        ( ~ v2_funct_1(k2_funct_1(X0))
        & v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ~ v2_funct_1(k2_funct_1(sK5))
      & v2_funct_1(sK5)
      & v1_funct_1(sK5)
      & v1_relat_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ~ v2_funct_1(k2_funct_1(sK5))
    & v2_funct_1(sK5)
    & v1_funct_1(sK5)
    & v1_relat_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f16,f31])).

fof(f54,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f32])).

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

fof(f52,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f55,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f32])).

fof(f56,plain,(
    v2_funct_1(sK5) ),
    inference(cnf_transformation,[],[f32])).

fof(f1,axiom,(
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
    inference(ennf_transformation,[],[f1])).

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

fof(f19,plain,(
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

fof(f20,plain,(
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
    inference(rectify,[],[f19])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
          & r2_hidden(X2,k1_relat_1(X0))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( sK1(X0) != sK2(X0)
        & k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK2(X0))
        & r2_hidden(sK2(X0),k1_relat_1(X0))
        & r2_hidden(sK1(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ( sK1(X0) != sK2(X0)
            & k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK2(X0))
            & r2_hidden(sK2(X0),k1_relat_1(X0))
            & r2_hidden(sK1(X0),k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f20,f21])).

fof(f34,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | r2_hidden(sK1(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f57,plain,(
    ~ v2_funct_1(k2_funct_1(sK5)) ),
    inference(cnf_transformation,[],[f32])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f10,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f38,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f39,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

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
    inference(definition_folding,[],[f12,f17])).

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
    inference(nnf_transformation,[],[f18])).

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
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ( k1_funct_1(X1,X2) != X3
              | ~ r2_hidden(X2,k2_relat_1(X0)) )
            & k1_funct_1(X0,X3) = X2
            & r2_hidden(X3,k1_relat_1(X0)) )
          | ~ sP0(X2,X3,X0,X1) )
     => ( ( ( k1_funct_1(X1,sK3(X0,X1)) != sK4(X0,X1)
            | ~ r2_hidden(sK3(X0,X1),k2_relat_1(X0)) )
          & k1_funct_1(X0,sK4(X0,X1)) = sK3(X0,X1)
          & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) )
        | ~ sP0(sK3(X0,X1),sK4(X0,X1),X0,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k2_funct_1(X0) = X1
              | ( ( k1_funct_1(X1,sK3(X0,X1)) != sK4(X0,X1)
                  | ~ r2_hidden(sK3(X0,X1),k2_relat_1(X0)) )
                & k1_funct_1(X0,sK4(X0,X1)) = sK3(X0,X1)
                & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) )
              | ~ sP0(sK3(X0,X1),sK4(X0,X1),X0,X1)
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f28,f29])).

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

fof(f65,plain,(
    ! [X4,X0,X5] :
      ( sP0(X4,X5,X0,k2_funct_1(X0))
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f46])).

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
    inference(nnf_transformation,[],[f17])).

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

fof(f59,plain,(
    ! [X2,X0,X3] :
      ( k1_funct_1(X2,k1_funct_1(X3,X0)) = X0
      | ~ r2_hidden(X0,k2_relat_1(X2))
      | ~ sP0(X0,k1_funct_1(X3,X0),X2,X3) ) ),
    inference(equality_resolution,[],[f41])).

fof(f35,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | r2_hidden(sK2(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f36,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK2(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f37,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | sK1(X0) != sK2(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_24,negated_conjecture,
    ( v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_3935,negated_conjecture,
    ( v1_relat_1(sK5) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_4462,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3935])).

cnf(c_20,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_3939,plain,
    ( ~ v1_relat_1(X0_42)
    | ~ v1_funct_1(X0_42)
    | ~ v2_funct_1(X0_42)
    | k1_relat_1(k2_funct_1(X0_42)) = k2_relat_1(X0_42) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_4458,plain,
    ( k1_relat_1(k2_funct_1(X0_42)) = k2_relat_1(X0_42)
    | v1_relat_1(X0_42) != iProver_top
    | v1_funct_1(X0_42) != iProver_top
    | v2_funct_1(X0_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3939])).

cnf(c_5069,plain,
    ( k1_relat_1(k2_funct_1(sK5)) = k2_relat_1(sK5)
    | v1_funct_1(sK5) != iProver_top
    | v2_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4462,c_4458])).

cnf(c_23,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_22,negated_conjecture,
    ( v2_funct_1(sK5) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_4032,plain,
    ( ~ v1_relat_1(sK5)
    | ~ v1_funct_1(sK5)
    | ~ v2_funct_1(sK5)
    | k1_relat_1(k2_funct_1(sK5)) = k2_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_3939])).

cnf(c_5172,plain,
    ( k1_relat_1(k2_funct_1(sK5)) = k2_relat_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5069,c_24,c_23,c_22,c_4032])).

cnf(c_3,plain,
    ( r2_hidden(sK1(X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_3955,plain,
    ( r2_hidden(sK1(X0_42),k1_relat_1(X0_42))
    | ~ v1_relat_1(X0_42)
    | ~ v1_funct_1(X0_42)
    | v2_funct_1(X0_42) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_4442,plain,
    ( r2_hidden(sK1(X0_42),k1_relat_1(X0_42)) = iProver_top
    | v1_relat_1(X0_42) != iProver_top
    | v1_funct_1(X0_42) != iProver_top
    | v2_funct_1(X0_42) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3955])).

cnf(c_5175,plain,
    ( r2_hidden(sK1(k2_funct_1(sK5)),k2_relat_1(sK5)) = iProver_top
    | v1_relat_1(k2_funct_1(sK5)) != iProver_top
    | v1_funct_1(k2_funct_1(sK5)) != iProver_top
    | v2_funct_1(k2_funct_1(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5172,c_4442])).

cnf(c_25,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_26,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_21,negated_conjecture,
    ( ~ v2_funct_1(k2_funct_1(sK5)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_28,plain,
    ( v2_funct_1(k2_funct_1(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_69,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_71,plain,
    ( v1_relat_1(k2_funct_1(sK5)) = iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_69])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_72,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_74,plain,
    ( v1_relat_1(sK5) != iProver_top
    | v1_funct_1(k2_funct_1(sK5)) = iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_72])).

cnf(c_5196,plain,
    ( r2_hidden(sK1(k2_funct_1(sK5)),k2_relat_1(sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5175,c_25,c_26,c_28,c_71,c_74])).

cnf(c_17,plain,
    ( sP0(X0,X1,X2,k2_funct_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(k2_funct_1(X2))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(k2_funct_1(X2))
    | ~ v2_funct_1(X2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_3941,plain,
    ( sP0(X0_44,X1_44,X0_42,k2_funct_1(X0_42))
    | ~ v1_relat_1(X0_42)
    | ~ v1_relat_1(k2_funct_1(X0_42))
    | ~ v1_funct_1(X0_42)
    | ~ v1_funct_1(k2_funct_1(X0_42))
    | ~ v2_funct_1(X0_42) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_4456,plain,
    ( sP0(X0_44,X1_44,X0_42,k2_funct_1(X0_42)) = iProver_top
    | v1_relat_1(X0_42) != iProver_top
    | v1_relat_1(k2_funct_1(X0_42)) != iProver_top
    | v1_funct_1(X0_42) != iProver_top
    | v1_funct_1(k2_funct_1(X0_42)) != iProver_top
    | v2_funct_1(X0_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3941])).

cnf(c_3953,plain,
    ( ~ v1_relat_1(X0_42)
    | ~ v1_funct_1(X0_42)
    | v1_funct_1(k2_funct_1(X0_42)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_4444,plain,
    ( v1_relat_1(X0_42) != iProver_top
    | v1_funct_1(X0_42) != iProver_top
    | v1_funct_1(k2_funct_1(X0_42)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3953])).

cnf(c_3952,plain,
    ( ~ v1_relat_1(X0_42)
    | v1_relat_1(k2_funct_1(X0_42))
    | ~ v1_funct_1(X0_42) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_4445,plain,
    ( v1_relat_1(X0_42) != iProver_top
    | v1_relat_1(k2_funct_1(X0_42)) = iProver_top
    | v1_funct_1(X0_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3952])).

cnf(c_4561,plain,
    ( sP0(X0_44,X1_44,X0_42,k2_funct_1(X0_42)) = iProver_top
    | v1_relat_1(X0_42) != iProver_top
    | v1_funct_1(X0_42) != iProver_top
    | v2_funct_1(X0_42) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4456,c_4444,c_4445])).

cnf(c_10,plain,
    ( ~ sP0(X0,k1_funct_1(X1,X0),X2,X1)
    | ~ r2_hidden(X0,k2_relat_1(X2))
    | k1_funct_1(X2,k1_funct_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_3948,plain,
    ( ~ sP0(X0_44,k1_funct_1(X0_42,X0_44),X1_42,X0_42)
    | ~ r2_hidden(X0_44,k2_relat_1(X1_42))
    | k1_funct_1(X1_42,k1_funct_1(X0_42,X0_44)) = X0_44 ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_4449,plain,
    ( k1_funct_1(X0_42,k1_funct_1(X1_42,X0_44)) = X0_44
    | sP0(X0_44,k1_funct_1(X1_42,X0_44),X0_42,X1_42) != iProver_top
    | r2_hidden(X0_44,k2_relat_1(X0_42)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3948])).

cnf(c_5395,plain,
    ( k1_funct_1(X0_42,k1_funct_1(k2_funct_1(X0_42),X0_44)) = X0_44
    | r2_hidden(X0_44,k2_relat_1(X0_42)) != iProver_top
    | v1_relat_1(X0_42) != iProver_top
    | v1_funct_1(X0_42) != iProver_top
    | v2_funct_1(X0_42) != iProver_top ),
    inference(superposition,[status(thm)],[c_4561,c_4449])).

cnf(c_6001,plain,
    ( k1_funct_1(sK5,k1_funct_1(k2_funct_1(sK5),sK1(k2_funct_1(sK5)))) = sK1(k2_funct_1(sK5))
    | v1_relat_1(sK5) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v2_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5196,c_5395])).

cnf(c_27,plain,
    ( v2_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_6766,plain,
    ( k1_funct_1(sK5,k1_funct_1(k2_funct_1(sK5),sK1(k2_funct_1(sK5)))) = sK1(k2_funct_1(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6001,c_25,c_26,c_27])).

cnf(c_2,plain,
    ( r2_hidden(sK2(X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_3956,plain,
    ( r2_hidden(sK2(X0_42),k1_relat_1(X0_42))
    | ~ v1_relat_1(X0_42)
    | ~ v1_funct_1(X0_42)
    | v2_funct_1(X0_42) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_4441,plain,
    ( r2_hidden(sK2(X0_42),k1_relat_1(X0_42)) = iProver_top
    | v1_relat_1(X0_42) != iProver_top
    | v1_funct_1(X0_42) != iProver_top
    | v2_funct_1(X0_42) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3956])).

cnf(c_5176,plain,
    ( r2_hidden(sK2(k2_funct_1(sK5)),k2_relat_1(sK5)) = iProver_top
    | v1_relat_1(k2_funct_1(sK5)) != iProver_top
    | v1_funct_1(k2_funct_1(sK5)) != iProver_top
    | v2_funct_1(k2_funct_1(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5172,c_4441])).

cnf(c_1630,plain,
    ( r2_hidden(sK2(X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_funct_1(sK5) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_21])).

cnf(c_1631,plain,
    ( r2_hidden(sK2(k2_funct_1(sK5)),k1_relat_1(k2_funct_1(sK5)))
    | ~ v1_relat_1(k2_funct_1(sK5))
    | ~ v1_funct_1(k2_funct_1(sK5)) ),
    inference(unflattening,[status(thm)],[c_1630])).

cnf(c_1632,plain,
    ( r2_hidden(sK2(k2_funct_1(sK5)),k1_relat_1(k2_funct_1(sK5))) = iProver_top
    | v1_relat_1(k2_funct_1(sK5)) != iProver_top
    | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1631])).

cnf(c_3974,plain,
    ( k2_relat_1(X0_42) = k2_relat_1(X1_42)
    | X0_42 != X1_42 ),
    theory(equality)).

cnf(c_3983,plain,
    ( k2_relat_1(sK5) = k2_relat_1(sK5)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_3974])).

cnf(c_3960,plain,
    ( X0_42 = X0_42 ),
    theory(equality)).

cnf(c_3985,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_3960])).

cnf(c_3962,plain,
    ( X0_44 = X0_44 ),
    theory(equality)).

cnf(c_4865,plain,
    ( sK2(k2_funct_1(sK5)) = sK2(k2_funct_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_3962])).

cnf(c_3964,plain,
    ( X0_43 != X1_43
    | X2_43 != X1_43
    | X2_43 = X0_43 ),
    theory(equality)).

cnf(c_4757,plain,
    ( k2_relat_1(X0_42) != X0_43
    | k2_relat_1(X0_42) = k1_relat_1(X1_42)
    | k1_relat_1(X1_42) != X0_43 ),
    inference(instantiation,[status(thm)],[c_3964])).

cnf(c_4830,plain,
    ( k2_relat_1(X0_42) != k2_relat_1(X0_42)
    | k2_relat_1(X0_42) = k1_relat_1(X1_42)
    | k1_relat_1(X1_42) != k2_relat_1(X0_42) ),
    inference(instantiation,[status(thm)],[c_4757])).

cnf(c_5056,plain,
    ( k2_relat_1(X0_42) != k2_relat_1(X0_42)
    | k2_relat_1(X0_42) = k1_relat_1(k2_funct_1(X0_42))
    | k1_relat_1(k2_funct_1(X0_42)) != k2_relat_1(X0_42) ),
    inference(instantiation,[status(thm)],[c_4830])).

cnf(c_5057,plain,
    ( k2_relat_1(sK5) != k2_relat_1(sK5)
    | k2_relat_1(sK5) = k1_relat_1(k2_funct_1(sK5))
    | k1_relat_1(k2_funct_1(sK5)) != k2_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_5056])).

cnf(c_3971,plain,
    ( ~ r2_hidden(X0_44,X0_43)
    | r2_hidden(X1_44,X1_43)
    | X1_44 != X0_44
    | X1_43 != X0_43 ),
    theory(equality)).

cnf(c_4786,plain,
    ( r2_hidden(X0_44,X0_43)
    | ~ r2_hidden(sK2(k2_funct_1(sK5)),k1_relat_1(k2_funct_1(sK5)))
    | X0_44 != sK2(k2_funct_1(sK5))
    | X0_43 != k1_relat_1(k2_funct_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_3971])).

cnf(c_4918,plain,
    ( r2_hidden(sK2(k2_funct_1(sK5)),X0_43)
    | ~ r2_hidden(sK2(k2_funct_1(sK5)),k1_relat_1(k2_funct_1(sK5)))
    | sK2(k2_funct_1(sK5)) != sK2(k2_funct_1(sK5))
    | X0_43 != k1_relat_1(k2_funct_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_4786])).

cnf(c_5125,plain,
    ( r2_hidden(sK2(k2_funct_1(sK5)),k2_relat_1(X0_42))
    | ~ r2_hidden(sK2(k2_funct_1(sK5)),k1_relat_1(k2_funct_1(sK5)))
    | sK2(k2_funct_1(sK5)) != sK2(k2_funct_1(sK5))
    | k2_relat_1(X0_42) != k1_relat_1(k2_funct_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_4918])).

cnf(c_5128,plain,
    ( sK2(k2_funct_1(sK5)) != sK2(k2_funct_1(sK5))
    | k2_relat_1(X0_42) != k1_relat_1(k2_funct_1(sK5))
    | r2_hidden(sK2(k2_funct_1(sK5)),k2_relat_1(X0_42)) = iProver_top
    | r2_hidden(sK2(k2_funct_1(sK5)),k1_relat_1(k2_funct_1(sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5125])).

cnf(c_5130,plain,
    ( sK2(k2_funct_1(sK5)) != sK2(k2_funct_1(sK5))
    | k2_relat_1(sK5) != k1_relat_1(k2_funct_1(sK5))
    | r2_hidden(sK2(k2_funct_1(sK5)),k2_relat_1(sK5)) = iProver_top
    | r2_hidden(sK2(k2_funct_1(sK5)),k1_relat_1(k2_funct_1(sK5))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5128])).

cnf(c_5261,plain,
    ( r2_hidden(sK2(k2_funct_1(sK5)),k2_relat_1(sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5176,c_24,c_25,c_23,c_26,c_22,c_71,c_74,c_1632,c_3983,c_3985,c_4032,c_4865,c_5057,c_5130])).

cnf(c_6000,plain,
    ( k1_funct_1(sK5,k1_funct_1(k2_funct_1(sK5),sK2(k2_funct_1(sK5)))) = sK2(k2_funct_1(sK5))
    | v1_relat_1(sK5) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v2_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5261,c_5395])).

cnf(c_70,plain,
    ( v1_relat_1(k2_funct_1(sK5))
    | ~ v1_relat_1(sK5)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_73,plain,
    ( ~ v1_relat_1(sK5)
    | v1_funct_1(k2_funct_1(sK5))
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_5129,plain,
    ( r2_hidden(sK2(k2_funct_1(sK5)),k2_relat_1(sK5))
    | ~ r2_hidden(sK2(k2_funct_1(sK5)),k1_relat_1(k2_funct_1(sK5)))
    | sK2(k2_funct_1(sK5)) != sK2(k2_funct_1(sK5))
    | k2_relat_1(sK5) != k1_relat_1(k2_funct_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_5125])).

cnf(c_5126,plain,
    ( ~ sP0(sK2(k2_funct_1(sK5)),k1_funct_1(X0_42,sK2(k2_funct_1(sK5))),X1_42,X0_42)
    | ~ r2_hidden(sK2(k2_funct_1(sK5)),k2_relat_1(X1_42))
    | k1_funct_1(X1_42,k1_funct_1(X0_42,sK2(k2_funct_1(sK5)))) = sK2(k2_funct_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_3948])).

cnf(c_5514,plain,
    ( ~ sP0(sK2(k2_funct_1(sK5)),k1_funct_1(k2_funct_1(X0_42),sK2(k2_funct_1(sK5))),X0_42,k2_funct_1(X0_42))
    | ~ r2_hidden(sK2(k2_funct_1(sK5)),k2_relat_1(X0_42))
    | k1_funct_1(X0_42,k1_funct_1(k2_funct_1(X0_42),sK2(k2_funct_1(sK5)))) = sK2(k2_funct_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_5126])).

cnf(c_5517,plain,
    ( ~ sP0(sK2(k2_funct_1(sK5)),k1_funct_1(k2_funct_1(sK5),sK2(k2_funct_1(sK5))),sK5,k2_funct_1(sK5))
    | ~ r2_hidden(sK2(k2_funct_1(sK5)),k2_relat_1(sK5))
    | k1_funct_1(sK5,k1_funct_1(k2_funct_1(sK5),sK2(k2_funct_1(sK5)))) = sK2(k2_funct_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_5514])).

cnf(c_4102,plain,
    ( ~ v1_funct_1(X0_42)
    | sP0(X0_44,X1_44,X0_42,k2_funct_1(X0_42))
    | ~ v1_relat_1(X0_42)
    | ~ v2_funct_1(X0_42) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3941,c_3953,c_3952])).

cnf(c_4103,plain,
    ( sP0(X0_44,X1_44,X0_42,k2_funct_1(X0_42))
    | ~ v1_relat_1(X0_42)
    | ~ v1_funct_1(X0_42)
    | ~ v2_funct_1(X0_42) ),
    inference(renaming,[status(thm)],[c_4102])).

cnf(c_5515,plain,
    ( sP0(sK2(k2_funct_1(sK5)),k1_funct_1(k2_funct_1(X0_42),sK2(k2_funct_1(sK5))),X0_42,k2_funct_1(X0_42))
    | ~ v1_relat_1(X0_42)
    | ~ v1_funct_1(X0_42)
    | ~ v2_funct_1(X0_42) ),
    inference(instantiation,[status(thm)],[c_4103])).

cnf(c_5521,plain,
    ( sP0(sK2(k2_funct_1(sK5)),k1_funct_1(k2_funct_1(sK5),sK2(k2_funct_1(sK5))),sK5,k2_funct_1(sK5))
    | ~ v1_relat_1(sK5)
    | ~ v1_funct_1(sK5)
    | ~ v2_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_5515])).

cnf(c_6418,plain,
    ( k1_funct_1(sK5,k1_funct_1(k2_funct_1(sK5),sK2(k2_funct_1(sK5)))) = sK2(k2_funct_1(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6000,c_24,c_23,c_22,c_70,c_73,c_1631,c_3983,c_3985,c_4032,c_4865,c_5057,c_5129,c_5517,c_5521])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | k1_funct_1(X0,sK2(X0)) = k1_funct_1(X0,sK1(X0)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_3957,plain,
    ( ~ v1_relat_1(X0_42)
    | ~ v1_funct_1(X0_42)
    | v2_funct_1(X0_42)
    | k1_funct_1(X0_42,sK2(X0_42)) = k1_funct_1(X0_42,sK1(X0_42)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_4440,plain,
    ( k1_funct_1(X0_42,sK2(X0_42)) = k1_funct_1(X0_42,sK1(X0_42))
    | v1_relat_1(X0_42) != iProver_top
    | v1_funct_1(X0_42) != iProver_top
    | v2_funct_1(X0_42) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3957])).

cnf(c_4842,plain,
    ( k1_funct_1(k2_funct_1(X0_42),sK1(k2_funct_1(X0_42))) = k1_funct_1(k2_funct_1(X0_42),sK2(k2_funct_1(X0_42)))
    | v1_relat_1(X0_42) != iProver_top
    | v1_funct_1(X0_42) != iProver_top
    | v1_funct_1(k2_funct_1(X0_42)) != iProver_top
    | v2_funct_1(k2_funct_1(X0_42)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4445,c_4440])).

cnf(c_3993,plain,
    ( v1_relat_1(X0_42) != iProver_top
    | v1_funct_1(X0_42) != iProver_top
    | v1_funct_1(k2_funct_1(X0_42)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3953])).

cnf(c_6035,plain,
    ( v1_funct_1(X0_42) != iProver_top
    | v1_relat_1(X0_42) != iProver_top
    | k1_funct_1(k2_funct_1(X0_42),sK1(k2_funct_1(X0_42))) = k1_funct_1(k2_funct_1(X0_42),sK2(k2_funct_1(X0_42)))
    | v2_funct_1(k2_funct_1(X0_42)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4842,c_3993])).

cnf(c_6036,plain,
    ( k1_funct_1(k2_funct_1(X0_42),sK1(k2_funct_1(X0_42))) = k1_funct_1(k2_funct_1(X0_42),sK2(k2_funct_1(X0_42)))
    | v1_relat_1(X0_42) != iProver_top
    | v1_funct_1(X0_42) != iProver_top
    | v2_funct_1(k2_funct_1(X0_42)) = iProver_top ),
    inference(renaming,[status(thm)],[c_6035])).

cnf(c_3938,negated_conjecture,
    ( ~ v2_funct_1(k2_funct_1(sK5)) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_4459,plain,
    ( v2_funct_1(k2_funct_1(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3938])).

cnf(c_6045,plain,
    ( k1_funct_1(k2_funct_1(sK5),sK1(k2_funct_1(sK5))) = k1_funct_1(k2_funct_1(sK5),sK2(k2_funct_1(sK5)))
    | v1_relat_1(sK5) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_6036,c_4459])).

cnf(c_4854,plain,
    ( k1_funct_1(k2_funct_1(sK5),sK1(k2_funct_1(sK5))) = k1_funct_1(k2_funct_1(sK5),sK2(k2_funct_1(sK5)))
    | v1_relat_1(sK5) != iProver_top
    | v1_funct_1(k2_funct_1(sK5)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v2_funct_1(k2_funct_1(sK5)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4842])).

cnf(c_6215,plain,
    ( k1_funct_1(k2_funct_1(sK5),sK1(k2_funct_1(sK5))) = k1_funct_1(k2_funct_1(sK5),sK2(k2_funct_1(sK5))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6045,c_25,c_26,c_28,c_74,c_4854])).

cnf(c_6420,plain,
    ( k1_funct_1(sK5,k1_funct_1(k2_funct_1(sK5),sK1(k2_funct_1(sK5)))) = sK2(k2_funct_1(sK5)) ),
    inference(light_normalisation,[status(thm)],[c_6418,c_6215])).

cnf(c_6769,plain,
    ( sK2(k2_funct_1(sK5)) = sK1(k2_funct_1(sK5)) ),
    inference(demodulation,[status(thm)],[c_6766,c_6420])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | sK2(X0) != sK1(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_3958,plain,
    ( ~ v1_relat_1(X0_42)
    | ~ v1_funct_1(X0_42)
    | v2_funct_1(X0_42)
    | sK2(X0_42) != sK1(X0_42) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_4730,plain,
    ( ~ v1_relat_1(k2_funct_1(sK5))
    | ~ v1_funct_1(k2_funct_1(sK5))
    | v2_funct_1(k2_funct_1(sK5))
    | sK2(k2_funct_1(sK5)) != sK1(k2_funct_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_3958])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6769,c_4730,c_73,c_70,c_21,c_23,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:48:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.34  % Running in FOF mode
% 2.51/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.00  
% 2.51/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.51/1.00  
% 2.51/1.00  ------  iProver source info
% 2.51/1.00  
% 2.51/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.51/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.51/1.00  git: non_committed_changes: false
% 2.51/1.00  git: last_make_outside_of_git: false
% 2.51/1.00  
% 2.51/1.00  ------ 
% 2.51/1.00  
% 2.51/1.00  ------ Input Options
% 2.51/1.00  
% 2.51/1.00  --out_options                           all
% 2.51/1.00  --tptp_safe_out                         true
% 2.51/1.00  --problem_path                          ""
% 2.51/1.00  --include_path                          ""
% 2.51/1.00  --clausifier                            res/vclausify_rel
% 2.51/1.00  --clausifier_options                    --mode clausify
% 2.51/1.00  --stdin                                 false
% 2.51/1.00  --stats_out                             all
% 2.51/1.00  
% 2.51/1.00  ------ General Options
% 2.51/1.00  
% 2.51/1.00  --fof                                   false
% 2.51/1.00  --time_out_real                         305.
% 2.51/1.00  --time_out_virtual                      -1.
% 2.51/1.00  --symbol_type_check                     false
% 2.51/1.00  --clausify_out                          false
% 2.51/1.00  --sig_cnt_out                           false
% 2.51/1.00  --trig_cnt_out                          false
% 2.51/1.00  --trig_cnt_out_tolerance                1.
% 2.51/1.00  --trig_cnt_out_sk_spl                   false
% 2.51/1.00  --abstr_cl_out                          false
% 2.51/1.00  
% 2.51/1.00  ------ Global Options
% 2.51/1.00  
% 2.51/1.00  --schedule                              default
% 2.51/1.00  --add_important_lit                     false
% 2.51/1.00  --prop_solver_per_cl                    1000
% 2.51/1.00  --min_unsat_core                        false
% 2.51/1.00  --soft_assumptions                      false
% 2.51/1.00  --soft_lemma_size                       3
% 2.51/1.00  --prop_impl_unit_size                   0
% 2.51/1.00  --prop_impl_unit                        []
% 2.51/1.00  --share_sel_clauses                     true
% 2.51/1.00  --reset_solvers                         false
% 2.51/1.00  --bc_imp_inh                            [conj_cone]
% 2.51/1.00  --conj_cone_tolerance                   3.
% 2.51/1.00  --extra_neg_conj                        none
% 2.51/1.00  --large_theory_mode                     true
% 2.51/1.00  --prolific_symb_bound                   200
% 2.51/1.00  --lt_threshold                          2000
% 2.51/1.00  --clause_weak_htbl                      true
% 2.51/1.00  --gc_record_bc_elim                     false
% 2.51/1.00  
% 2.51/1.00  ------ Preprocessing Options
% 2.51/1.00  
% 2.51/1.00  --preprocessing_flag                    true
% 2.51/1.00  --time_out_prep_mult                    0.1
% 2.51/1.00  --splitting_mode                        input
% 2.51/1.00  --splitting_grd                         true
% 2.51/1.00  --splitting_cvd                         false
% 2.51/1.00  --splitting_cvd_svl                     false
% 2.51/1.00  --splitting_nvd                         32
% 2.51/1.00  --sub_typing                            true
% 2.51/1.00  --prep_gs_sim                           true
% 2.51/1.00  --prep_unflatten                        true
% 2.51/1.00  --prep_res_sim                          true
% 2.51/1.00  --prep_upred                            true
% 2.51/1.00  --prep_sem_filter                       exhaustive
% 2.51/1.00  --prep_sem_filter_out                   false
% 2.51/1.00  --pred_elim                             true
% 2.51/1.00  --res_sim_input                         true
% 2.51/1.00  --eq_ax_congr_red                       true
% 2.51/1.00  --pure_diseq_elim                       true
% 2.51/1.00  --brand_transform                       false
% 2.51/1.00  --non_eq_to_eq                          false
% 2.51/1.00  --prep_def_merge                        true
% 2.51/1.00  --prep_def_merge_prop_impl              false
% 2.51/1.00  --prep_def_merge_mbd                    true
% 2.51/1.00  --prep_def_merge_tr_red                 false
% 2.51/1.00  --prep_def_merge_tr_cl                  false
% 2.51/1.00  --smt_preprocessing                     true
% 2.51/1.00  --smt_ac_axioms                         fast
% 2.51/1.00  --preprocessed_out                      false
% 2.51/1.00  --preprocessed_stats                    false
% 2.51/1.00  
% 2.51/1.00  ------ Abstraction refinement Options
% 2.51/1.00  
% 2.51/1.00  --abstr_ref                             []
% 2.51/1.00  --abstr_ref_prep                        false
% 2.51/1.00  --abstr_ref_until_sat                   false
% 2.51/1.00  --abstr_ref_sig_restrict                funpre
% 2.51/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.51/1.00  --abstr_ref_under                       []
% 2.51/1.00  
% 2.51/1.00  ------ SAT Options
% 2.51/1.00  
% 2.51/1.00  --sat_mode                              false
% 2.51/1.00  --sat_fm_restart_options                ""
% 2.51/1.00  --sat_gr_def                            false
% 2.51/1.00  --sat_epr_types                         true
% 2.51/1.00  --sat_non_cyclic_types                  false
% 2.51/1.00  --sat_finite_models                     false
% 2.51/1.00  --sat_fm_lemmas                         false
% 2.51/1.00  --sat_fm_prep                           false
% 2.51/1.00  --sat_fm_uc_incr                        true
% 2.51/1.00  --sat_out_model                         small
% 2.51/1.00  --sat_out_clauses                       false
% 2.51/1.00  
% 2.51/1.00  ------ QBF Options
% 2.51/1.00  
% 2.51/1.00  --qbf_mode                              false
% 2.51/1.00  --qbf_elim_univ                         false
% 2.51/1.00  --qbf_dom_inst                          none
% 2.51/1.00  --qbf_dom_pre_inst                      false
% 2.51/1.00  --qbf_sk_in                             false
% 2.51/1.00  --qbf_pred_elim                         true
% 2.51/1.00  --qbf_split                             512
% 2.51/1.00  
% 2.51/1.00  ------ BMC1 Options
% 2.51/1.00  
% 2.51/1.00  --bmc1_incremental                      false
% 2.51/1.00  --bmc1_axioms                           reachable_all
% 2.51/1.00  --bmc1_min_bound                        0
% 2.51/1.00  --bmc1_max_bound                        -1
% 2.51/1.00  --bmc1_max_bound_default                -1
% 2.51/1.00  --bmc1_symbol_reachability              true
% 2.51/1.00  --bmc1_property_lemmas                  false
% 2.51/1.00  --bmc1_k_induction                      false
% 2.51/1.00  --bmc1_non_equiv_states                 false
% 2.51/1.00  --bmc1_deadlock                         false
% 2.51/1.00  --bmc1_ucm                              false
% 2.51/1.00  --bmc1_add_unsat_core                   none
% 2.51/1.00  --bmc1_unsat_core_children              false
% 2.51/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.51/1.00  --bmc1_out_stat                         full
% 2.51/1.00  --bmc1_ground_init                      false
% 2.51/1.00  --bmc1_pre_inst_next_state              false
% 2.51/1.00  --bmc1_pre_inst_state                   false
% 2.51/1.00  --bmc1_pre_inst_reach_state             false
% 2.51/1.00  --bmc1_out_unsat_core                   false
% 2.51/1.00  --bmc1_aig_witness_out                  false
% 2.51/1.00  --bmc1_verbose                          false
% 2.51/1.00  --bmc1_dump_clauses_tptp                false
% 2.51/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.51/1.00  --bmc1_dump_file                        -
% 2.51/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.51/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.51/1.00  --bmc1_ucm_extend_mode                  1
% 2.51/1.00  --bmc1_ucm_init_mode                    2
% 2.51/1.00  --bmc1_ucm_cone_mode                    none
% 2.51/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.51/1.00  --bmc1_ucm_relax_model                  4
% 2.51/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.51/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.51/1.00  --bmc1_ucm_layered_model                none
% 2.51/1.00  --bmc1_ucm_max_lemma_size               10
% 2.51/1.00  
% 2.51/1.00  ------ AIG Options
% 2.51/1.00  
% 2.51/1.00  --aig_mode                              false
% 2.51/1.00  
% 2.51/1.00  ------ Instantiation Options
% 2.51/1.00  
% 2.51/1.00  --instantiation_flag                    true
% 2.51/1.00  --inst_sos_flag                         false
% 2.51/1.00  --inst_sos_phase                        true
% 2.51/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.51/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.51/1.00  --inst_lit_sel_side                     num_symb
% 2.51/1.00  --inst_solver_per_active                1400
% 2.51/1.00  --inst_solver_calls_frac                1.
% 2.51/1.00  --inst_passive_queue_type               priority_queues
% 2.51/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.51/1.00  --inst_passive_queues_freq              [25;2]
% 2.51/1.00  --inst_dismatching                      true
% 2.51/1.00  --inst_eager_unprocessed_to_passive     true
% 2.51/1.00  --inst_prop_sim_given                   true
% 2.51/1.00  --inst_prop_sim_new                     false
% 2.51/1.00  --inst_subs_new                         false
% 2.51/1.00  --inst_eq_res_simp                      false
% 2.51/1.00  --inst_subs_given                       false
% 2.51/1.00  --inst_orphan_elimination               true
% 2.51/1.00  --inst_learning_loop_flag               true
% 2.51/1.00  --inst_learning_start                   3000
% 2.51/1.00  --inst_learning_factor                  2
% 2.51/1.00  --inst_start_prop_sim_after_learn       3
% 2.51/1.00  --inst_sel_renew                        solver
% 2.51/1.00  --inst_lit_activity_flag                true
% 2.51/1.00  --inst_restr_to_given                   false
% 2.51/1.00  --inst_activity_threshold               500
% 2.51/1.00  --inst_out_proof                        true
% 2.51/1.00  
% 2.51/1.00  ------ Resolution Options
% 2.51/1.00  
% 2.51/1.00  --resolution_flag                       true
% 2.51/1.00  --res_lit_sel                           adaptive
% 2.51/1.00  --res_lit_sel_side                      none
% 2.51/1.00  --res_ordering                          kbo
% 2.51/1.00  --res_to_prop_solver                    active
% 2.51/1.00  --res_prop_simpl_new                    false
% 2.51/1.00  --res_prop_simpl_given                  true
% 2.51/1.00  --res_passive_queue_type                priority_queues
% 2.51/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.51/1.00  --res_passive_queues_freq               [15;5]
% 2.51/1.00  --res_forward_subs                      full
% 2.51/1.00  --res_backward_subs                     full
% 2.51/1.00  --res_forward_subs_resolution           true
% 2.51/1.00  --res_backward_subs_resolution          true
% 2.51/1.00  --res_orphan_elimination                true
% 2.51/1.00  --res_time_limit                        2.
% 2.51/1.00  --res_out_proof                         true
% 2.51/1.00  
% 2.51/1.00  ------ Superposition Options
% 2.51/1.00  
% 2.51/1.00  --superposition_flag                    true
% 2.51/1.00  --sup_passive_queue_type                priority_queues
% 2.51/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.51/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.51/1.00  --demod_completeness_check              fast
% 2.51/1.00  --demod_use_ground                      true
% 2.51/1.00  --sup_to_prop_solver                    passive
% 2.51/1.00  --sup_prop_simpl_new                    true
% 2.51/1.00  --sup_prop_simpl_given                  true
% 2.51/1.00  --sup_fun_splitting                     false
% 2.51/1.00  --sup_smt_interval                      50000
% 2.51/1.00  
% 2.51/1.00  ------ Superposition Simplification Setup
% 2.51/1.00  
% 2.51/1.00  --sup_indices_passive                   []
% 2.51/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.51/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.51/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.51/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.51/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.51/1.00  --sup_full_bw                           [BwDemod]
% 2.51/1.00  --sup_immed_triv                        [TrivRules]
% 2.51/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.51/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.51/1.00  --sup_immed_bw_main                     []
% 2.51/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.51/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.51/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.51/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.51/1.00  
% 2.51/1.00  ------ Combination Options
% 2.51/1.00  
% 2.51/1.00  --comb_res_mult                         3
% 2.51/1.00  --comb_sup_mult                         2
% 2.51/1.00  --comb_inst_mult                        10
% 2.51/1.00  
% 2.51/1.00  ------ Debug Options
% 2.51/1.00  
% 2.51/1.00  --dbg_backtrace                         false
% 2.51/1.00  --dbg_dump_prop_clauses                 false
% 2.51/1.00  --dbg_dump_prop_clauses_file            -
% 2.51/1.00  --dbg_out_stat                          false
% 2.51/1.00  ------ Parsing...
% 2.51/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.51/1.00  
% 2.51/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.51/1.00  
% 2.51/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.51/1.00  
% 2.51/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.51/1.00  ------ Proving...
% 2.51/1.00  ------ Problem Properties 
% 2.51/1.00  
% 2.51/1.00  
% 2.51/1.00  clauses                                 24
% 2.51/1.00  conjectures                             4
% 2.51/1.00  EPR                                     3
% 2.51/1.00  Horn                                    17
% 2.51/1.00  unary                                   4
% 2.51/1.00  binary                                  3
% 2.51/1.00  lits                                    101
% 2.51/1.00  lits eq                                 17
% 2.51/1.00  fd_pure                                 0
% 2.51/1.00  fd_pseudo                               0
% 2.51/1.00  fd_cond                                 0
% 2.51/1.00  fd_pseudo_cond                          5
% 2.51/1.00  AC symbols                              0
% 2.51/1.00  
% 2.51/1.00  ------ Schedule dynamic 5 is on 
% 2.51/1.00  
% 2.51/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.51/1.00  
% 2.51/1.00  
% 2.51/1.00  ------ 
% 2.51/1.00  Current options:
% 2.51/1.00  ------ 
% 2.51/1.00  
% 2.51/1.00  ------ Input Options
% 2.51/1.00  
% 2.51/1.00  --out_options                           all
% 2.51/1.00  --tptp_safe_out                         true
% 2.51/1.00  --problem_path                          ""
% 2.51/1.00  --include_path                          ""
% 2.51/1.00  --clausifier                            res/vclausify_rel
% 2.51/1.00  --clausifier_options                    --mode clausify
% 2.51/1.00  --stdin                                 false
% 2.51/1.00  --stats_out                             all
% 2.51/1.00  
% 2.51/1.00  ------ General Options
% 2.51/1.00  
% 2.51/1.00  --fof                                   false
% 2.51/1.00  --time_out_real                         305.
% 2.51/1.00  --time_out_virtual                      -1.
% 2.51/1.00  --symbol_type_check                     false
% 2.51/1.00  --clausify_out                          false
% 2.51/1.00  --sig_cnt_out                           false
% 2.51/1.00  --trig_cnt_out                          false
% 2.51/1.00  --trig_cnt_out_tolerance                1.
% 2.51/1.00  --trig_cnt_out_sk_spl                   false
% 2.51/1.00  --abstr_cl_out                          false
% 2.51/1.00  
% 2.51/1.00  ------ Global Options
% 2.51/1.00  
% 2.51/1.00  --schedule                              default
% 2.51/1.00  --add_important_lit                     false
% 2.51/1.00  --prop_solver_per_cl                    1000
% 2.51/1.00  --min_unsat_core                        false
% 2.51/1.00  --soft_assumptions                      false
% 2.51/1.00  --soft_lemma_size                       3
% 2.51/1.00  --prop_impl_unit_size                   0
% 2.51/1.00  --prop_impl_unit                        []
% 2.51/1.00  --share_sel_clauses                     true
% 2.51/1.00  --reset_solvers                         false
% 2.51/1.00  --bc_imp_inh                            [conj_cone]
% 2.51/1.00  --conj_cone_tolerance                   3.
% 2.51/1.00  --extra_neg_conj                        none
% 2.51/1.00  --large_theory_mode                     true
% 2.51/1.00  --prolific_symb_bound                   200
% 2.51/1.00  --lt_threshold                          2000
% 2.51/1.00  --clause_weak_htbl                      true
% 2.51/1.00  --gc_record_bc_elim                     false
% 2.51/1.00  
% 2.51/1.00  ------ Preprocessing Options
% 2.51/1.00  
% 2.51/1.00  --preprocessing_flag                    true
% 2.51/1.00  --time_out_prep_mult                    0.1
% 2.51/1.00  --splitting_mode                        input
% 2.51/1.00  --splitting_grd                         true
% 2.51/1.00  --splitting_cvd                         false
% 2.51/1.00  --splitting_cvd_svl                     false
% 2.51/1.00  --splitting_nvd                         32
% 2.51/1.00  --sub_typing                            true
% 2.51/1.00  --prep_gs_sim                           true
% 2.51/1.00  --prep_unflatten                        true
% 2.51/1.00  --prep_res_sim                          true
% 2.51/1.00  --prep_upred                            true
% 2.51/1.00  --prep_sem_filter                       exhaustive
% 2.51/1.00  --prep_sem_filter_out                   false
% 2.51/1.00  --pred_elim                             true
% 2.51/1.00  --res_sim_input                         true
% 2.51/1.00  --eq_ax_congr_red                       true
% 2.51/1.00  --pure_diseq_elim                       true
% 2.51/1.00  --brand_transform                       false
% 2.51/1.00  --non_eq_to_eq                          false
% 2.51/1.00  --prep_def_merge                        true
% 2.51/1.00  --prep_def_merge_prop_impl              false
% 2.51/1.00  --prep_def_merge_mbd                    true
% 2.51/1.00  --prep_def_merge_tr_red                 false
% 2.51/1.00  --prep_def_merge_tr_cl                  false
% 2.51/1.00  --smt_preprocessing                     true
% 2.51/1.00  --smt_ac_axioms                         fast
% 2.51/1.00  --preprocessed_out                      false
% 2.51/1.00  --preprocessed_stats                    false
% 2.51/1.00  
% 2.51/1.00  ------ Abstraction refinement Options
% 2.51/1.00  
% 2.51/1.00  --abstr_ref                             []
% 2.51/1.00  --abstr_ref_prep                        false
% 2.51/1.00  --abstr_ref_until_sat                   false
% 2.51/1.00  --abstr_ref_sig_restrict                funpre
% 2.51/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.51/1.00  --abstr_ref_under                       []
% 2.51/1.00  
% 2.51/1.00  ------ SAT Options
% 2.51/1.00  
% 2.51/1.00  --sat_mode                              false
% 2.51/1.00  --sat_fm_restart_options                ""
% 2.51/1.00  --sat_gr_def                            false
% 2.51/1.00  --sat_epr_types                         true
% 2.51/1.00  --sat_non_cyclic_types                  false
% 2.51/1.00  --sat_finite_models                     false
% 2.51/1.00  --sat_fm_lemmas                         false
% 2.51/1.00  --sat_fm_prep                           false
% 2.51/1.00  --sat_fm_uc_incr                        true
% 2.51/1.00  --sat_out_model                         small
% 2.51/1.00  --sat_out_clauses                       false
% 2.51/1.00  
% 2.51/1.00  ------ QBF Options
% 2.51/1.00  
% 2.51/1.00  --qbf_mode                              false
% 2.51/1.00  --qbf_elim_univ                         false
% 2.51/1.00  --qbf_dom_inst                          none
% 2.51/1.00  --qbf_dom_pre_inst                      false
% 2.51/1.00  --qbf_sk_in                             false
% 2.51/1.00  --qbf_pred_elim                         true
% 2.51/1.00  --qbf_split                             512
% 2.51/1.00  
% 2.51/1.00  ------ BMC1 Options
% 2.51/1.00  
% 2.51/1.00  --bmc1_incremental                      false
% 2.51/1.00  --bmc1_axioms                           reachable_all
% 2.51/1.00  --bmc1_min_bound                        0
% 2.51/1.00  --bmc1_max_bound                        -1
% 2.51/1.00  --bmc1_max_bound_default                -1
% 2.51/1.00  --bmc1_symbol_reachability              true
% 2.51/1.00  --bmc1_property_lemmas                  false
% 2.51/1.00  --bmc1_k_induction                      false
% 2.51/1.00  --bmc1_non_equiv_states                 false
% 2.51/1.00  --bmc1_deadlock                         false
% 2.51/1.00  --bmc1_ucm                              false
% 2.51/1.00  --bmc1_add_unsat_core                   none
% 2.51/1.00  --bmc1_unsat_core_children              false
% 2.51/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.51/1.00  --bmc1_out_stat                         full
% 2.51/1.00  --bmc1_ground_init                      false
% 2.51/1.00  --bmc1_pre_inst_next_state              false
% 2.51/1.00  --bmc1_pre_inst_state                   false
% 2.51/1.00  --bmc1_pre_inst_reach_state             false
% 2.51/1.00  --bmc1_out_unsat_core                   false
% 2.51/1.00  --bmc1_aig_witness_out                  false
% 2.51/1.00  --bmc1_verbose                          false
% 2.51/1.00  --bmc1_dump_clauses_tptp                false
% 2.51/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.51/1.00  --bmc1_dump_file                        -
% 2.51/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.51/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.51/1.00  --bmc1_ucm_extend_mode                  1
% 2.51/1.00  --bmc1_ucm_init_mode                    2
% 2.51/1.00  --bmc1_ucm_cone_mode                    none
% 2.51/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.51/1.00  --bmc1_ucm_relax_model                  4
% 2.51/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.51/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.51/1.00  --bmc1_ucm_layered_model                none
% 2.51/1.00  --bmc1_ucm_max_lemma_size               10
% 2.51/1.00  
% 2.51/1.00  ------ AIG Options
% 2.51/1.00  
% 2.51/1.00  --aig_mode                              false
% 2.51/1.00  
% 2.51/1.00  ------ Instantiation Options
% 2.51/1.00  
% 2.51/1.00  --instantiation_flag                    true
% 2.51/1.00  --inst_sos_flag                         false
% 2.51/1.00  --inst_sos_phase                        true
% 2.51/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.51/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.51/1.00  --inst_lit_sel_side                     none
% 2.51/1.00  --inst_solver_per_active                1400
% 2.51/1.00  --inst_solver_calls_frac                1.
% 2.51/1.00  --inst_passive_queue_type               priority_queues
% 2.51/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.51/1.00  --inst_passive_queues_freq              [25;2]
% 2.51/1.00  --inst_dismatching                      true
% 2.51/1.00  --inst_eager_unprocessed_to_passive     true
% 2.51/1.00  --inst_prop_sim_given                   true
% 2.51/1.00  --inst_prop_sim_new                     false
% 2.51/1.00  --inst_subs_new                         false
% 2.51/1.00  --inst_eq_res_simp                      false
% 2.51/1.00  --inst_subs_given                       false
% 2.51/1.00  --inst_orphan_elimination               true
% 2.51/1.00  --inst_learning_loop_flag               true
% 2.51/1.00  --inst_learning_start                   3000
% 2.51/1.00  --inst_learning_factor                  2
% 2.51/1.00  --inst_start_prop_sim_after_learn       3
% 2.51/1.00  --inst_sel_renew                        solver
% 2.51/1.00  --inst_lit_activity_flag                true
% 2.51/1.00  --inst_restr_to_given                   false
% 2.51/1.00  --inst_activity_threshold               500
% 2.51/1.00  --inst_out_proof                        true
% 2.51/1.00  
% 2.51/1.00  ------ Resolution Options
% 2.51/1.00  
% 2.51/1.00  --resolution_flag                       false
% 2.51/1.00  --res_lit_sel                           adaptive
% 2.51/1.00  --res_lit_sel_side                      none
% 2.51/1.00  --res_ordering                          kbo
% 2.51/1.00  --res_to_prop_solver                    active
% 2.51/1.00  --res_prop_simpl_new                    false
% 2.51/1.00  --res_prop_simpl_given                  true
% 2.51/1.00  --res_passive_queue_type                priority_queues
% 2.51/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.51/1.00  --res_passive_queues_freq               [15;5]
% 2.51/1.00  --res_forward_subs                      full
% 2.51/1.00  --res_backward_subs                     full
% 2.51/1.00  --res_forward_subs_resolution           true
% 2.51/1.00  --res_backward_subs_resolution          true
% 2.51/1.00  --res_orphan_elimination                true
% 2.51/1.00  --res_time_limit                        2.
% 2.51/1.00  --res_out_proof                         true
% 2.51/1.00  
% 2.51/1.00  ------ Superposition Options
% 2.51/1.00  
% 2.51/1.00  --superposition_flag                    true
% 2.51/1.00  --sup_passive_queue_type                priority_queues
% 2.51/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.51/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.51/1.00  --demod_completeness_check              fast
% 2.51/1.00  --demod_use_ground                      true
% 2.51/1.00  --sup_to_prop_solver                    passive
% 2.51/1.00  --sup_prop_simpl_new                    true
% 2.51/1.00  --sup_prop_simpl_given                  true
% 2.51/1.00  --sup_fun_splitting                     false
% 2.51/1.00  --sup_smt_interval                      50000
% 2.51/1.00  
% 2.51/1.00  ------ Superposition Simplification Setup
% 2.51/1.00  
% 2.51/1.00  --sup_indices_passive                   []
% 2.51/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.51/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.51/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.51/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.51/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.51/1.00  --sup_full_bw                           [BwDemod]
% 2.51/1.00  --sup_immed_triv                        [TrivRules]
% 2.51/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.51/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.51/1.00  --sup_immed_bw_main                     []
% 2.51/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.51/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.51/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.51/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.51/1.00  
% 2.51/1.00  ------ Combination Options
% 2.51/1.00  
% 2.51/1.00  --comb_res_mult                         3
% 2.51/1.00  --comb_sup_mult                         2
% 2.51/1.00  --comb_inst_mult                        10
% 2.51/1.00  
% 2.51/1.00  ------ Debug Options
% 2.51/1.00  
% 2.51/1.00  --dbg_backtrace                         false
% 2.51/1.00  --dbg_dump_prop_clauses                 false
% 2.51/1.00  --dbg_dump_prop_clauses_file            -
% 2.51/1.00  --dbg_out_stat                          false
% 2.51/1.00  
% 2.51/1.00  
% 2.51/1.00  
% 2.51/1.00  
% 2.51/1.00  ------ Proving...
% 2.51/1.00  
% 2.51/1.00  
% 2.51/1.00  % SZS status Theorem for theBenchmark.p
% 2.51/1.00  
% 2.51/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.51/1.00  
% 2.51/1.00  fof(f5,conjecture,(
% 2.51/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => v2_funct_1(k2_funct_1(X0))))),
% 2.51/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.51/1.00  
% 2.51/1.00  fof(f6,negated_conjecture,(
% 2.51/1.00    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => v2_funct_1(k2_funct_1(X0))))),
% 2.51/1.00    inference(negated_conjecture,[],[f5])).
% 2.51/1.00  
% 2.51/1.00  fof(f15,plain,(
% 2.51/1.00    ? [X0] : ((~v2_funct_1(k2_funct_1(X0)) & v2_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 2.51/1.00    inference(ennf_transformation,[],[f6])).
% 2.51/1.00  
% 2.51/1.00  fof(f16,plain,(
% 2.51/1.00    ? [X0] : (~v2_funct_1(k2_funct_1(X0)) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 2.51/1.00    inference(flattening,[],[f15])).
% 2.51/1.00  
% 2.51/1.00  fof(f31,plain,(
% 2.51/1.00    ? [X0] : (~v2_funct_1(k2_funct_1(X0)) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (~v2_funct_1(k2_funct_1(sK5)) & v2_funct_1(sK5) & v1_funct_1(sK5) & v1_relat_1(sK5))),
% 2.51/1.00    introduced(choice_axiom,[])).
% 2.51/1.00  
% 2.51/1.00  fof(f32,plain,(
% 2.51/1.00    ~v2_funct_1(k2_funct_1(sK5)) & v2_funct_1(sK5) & v1_funct_1(sK5) & v1_relat_1(sK5)),
% 2.51/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f16,f31])).
% 2.51/1.00  
% 2.51/1.00  fof(f54,plain,(
% 2.51/1.00    v1_relat_1(sK5)),
% 2.51/1.00    inference(cnf_transformation,[],[f32])).
% 2.51/1.00  
% 2.51/1.00  fof(f4,axiom,(
% 2.51/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 2.51/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.51/1.00  
% 2.51/1.00  fof(f13,plain,(
% 2.51/1.00    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.51/1.00    inference(ennf_transformation,[],[f4])).
% 2.51/1.00  
% 2.51/1.00  fof(f14,plain,(
% 2.51/1.00    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.51/1.00    inference(flattening,[],[f13])).
% 2.51/1.00  
% 2.51/1.00  fof(f52,plain,(
% 2.51/1.00    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.51/1.00    inference(cnf_transformation,[],[f14])).
% 2.51/1.00  
% 2.51/1.00  fof(f55,plain,(
% 2.51/1.00    v1_funct_1(sK5)),
% 2.51/1.00    inference(cnf_transformation,[],[f32])).
% 2.51/1.00  
% 2.51/1.00  fof(f56,plain,(
% 2.51/1.00    v2_funct_1(sK5)),
% 2.51/1.00    inference(cnf_transformation,[],[f32])).
% 2.51/1.00  
% 2.51/1.00  fof(f1,axiom,(
% 2.51/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 2.51/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.51/1.00  
% 2.51/1.00  fof(f7,plain,(
% 2.51/1.00    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.51/1.00    inference(ennf_transformation,[],[f1])).
% 2.51/1.00  
% 2.51/1.00  fof(f8,plain,(
% 2.51/1.00    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.51/1.00    inference(flattening,[],[f7])).
% 2.51/1.00  
% 2.51/1.00  fof(f19,plain,(
% 2.51/1.00    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.51/1.00    inference(nnf_transformation,[],[f8])).
% 2.51/1.00  
% 2.51/1.00  fof(f20,plain,(
% 2.51/1.00    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.51/1.00    inference(rectify,[],[f19])).
% 2.51/1.00  
% 2.51/1.00  fof(f21,plain,(
% 2.51/1.00    ! [X0] : (? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => (sK1(X0) != sK2(X0) & k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK2(X0)) & r2_hidden(sK2(X0),k1_relat_1(X0)) & r2_hidden(sK1(X0),k1_relat_1(X0))))),
% 2.51/1.00    introduced(choice_axiom,[])).
% 2.51/1.00  
% 2.51/1.00  fof(f22,plain,(
% 2.51/1.00    ! [X0] : (((v2_funct_1(X0) | (sK1(X0) != sK2(X0) & k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK2(X0)) & r2_hidden(sK2(X0),k1_relat_1(X0)) & r2_hidden(sK1(X0),k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.51/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f20,f21])).
% 2.51/1.00  
% 2.51/1.00  fof(f34,plain,(
% 2.51/1.00    ( ! [X0] : (v2_funct_1(X0) | r2_hidden(sK1(X0),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.51/1.00    inference(cnf_transformation,[],[f22])).
% 2.51/1.00  
% 2.51/1.00  fof(f57,plain,(
% 2.51/1.00    ~v2_funct_1(k2_funct_1(sK5))),
% 2.51/1.00    inference(cnf_transformation,[],[f32])).
% 2.51/1.00  
% 2.51/1.00  fof(f2,axiom,(
% 2.51/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.51/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.51/1.00  
% 2.51/1.00  fof(f9,plain,(
% 2.51/1.00    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.51/1.00    inference(ennf_transformation,[],[f2])).
% 2.51/1.00  
% 2.51/1.00  fof(f10,plain,(
% 2.51/1.00    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.51/1.00    inference(flattening,[],[f9])).
% 2.51/1.00  
% 2.51/1.00  fof(f38,plain,(
% 2.51/1.00    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.51/1.00    inference(cnf_transformation,[],[f10])).
% 2.51/1.00  
% 2.51/1.00  fof(f39,plain,(
% 2.51/1.00    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.51/1.00    inference(cnf_transformation,[],[f10])).
% 2.51/1.00  
% 2.51/1.00  fof(f3,axiom,(
% 2.51/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) => (k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0)))) & ((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) => (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) & k1_relat_1(X1) = k2_relat_1(X0))))))),
% 2.51/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.51/1.00  
% 2.51/1.00  fof(f11,plain,(
% 2.51/1.00    ! [X0] : ((! [X1] : ((k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | (k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))))) & k1_relat_1(X1) = k2_relat_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.51/1.00    inference(ennf_transformation,[],[f3])).
% 2.51/1.00  
% 2.51/1.00  fof(f12,plain,(
% 2.51/1.00    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0)))) & k1_relat_1(X1) = k2_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.51/1.00    inference(flattening,[],[f11])).
% 2.51/1.00  
% 2.51/1.00  fof(f17,plain,(
% 2.51/1.00    ! [X2,X3,X0,X1] : (sP0(X2,X3,X0,X1) <=> ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))))),
% 2.51/1.00    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.51/1.00  
% 2.51/1.00  fof(f18,plain,(
% 2.51/1.00    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & sP0(X2,X3,X0,X1)) & k1_relat_1(X1) = k2_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.51/1.00    inference(definition_folding,[],[f12,f17])).
% 2.51/1.00  
% 2.51/1.00  fof(f26,plain,(
% 2.51/1.00    ! [X0] : (! [X1] : (((k2_funct_1(X0) = X1 | (? [X2,X3] : (((k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))) & k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X2,X3,X0,X1)) | k1_relat_1(X1) != k2_relat_1(X0))) & ((! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & sP0(X2,X3,X0,X1)) & k1_relat_1(X1) = k2_relat_1(X0)) | k2_funct_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.51/1.00    inference(nnf_transformation,[],[f18])).
% 2.51/1.00  
% 2.51/1.00  fof(f27,plain,(
% 2.51/1.00    ! [X0] : (! [X1] : (((k2_funct_1(X0) = X1 | ? [X2,X3] : (((k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))) & k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X2,X3,X0,X1)) | k1_relat_1(X1) != k2_relat_1(X0)) & ((! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & sP0(X2,X3,X0,X1)) & k1_relat_1(X1) = k2_relat_1(X0)) | k2_funct_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.51/1.00    inference(flattening,[],[f26])).
% 2.51/1.00  
% 2.51/1.00  fof(f28,plain,(
% 2.51/1.00    ! [X0] : (! [X1] : (((k2_funct_1(X0) = X1 | ? [X2,X3] : (((k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))) & k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X2,X3,X0,X1)) | k1_relat_1(X1) != k2_relat_1(X0)) & ((! [X4,X5] : (((k1_funct_1(X1,X4) = X5 & r2_hidden(X4,k2_relat_1(X0))) | k1_funct_1(X0,X5) != X4 | ~r2_hidden(X5,k1_relat_1(X0))) & sP0(X4,X5,X0,X1)) & k1_relat_1(X1) = k2_relat_1(X0)) | k2_funct_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.51/1.00    inference(rectify,[],[f27])).
% 2.51/1.00  
% 2.51/1.00  fof(f29,plain,(
% 2.51/1.00    ! [X1,X0] : (? [X2,X3] : (((k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))) & k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X2,X3,X0,X1)) => (((k1_funct_1(X1,sK3(X0,X1)) != sK4(X0,X1) | ~r2_hidden(sK3(X0,X1),k2_relat_1(X0))) & k1_funct_1(X0,sK4(X0,X1)) = sK3(X0,X1) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))) | ~sP0(sK3(X0,X1),sK4(X0,X1),X0,X1)))),
% 2.51/1.00    introduced(choice_axiom,[])).
% 2.51/1.00  
% 2.51/1.00  fof(f30,plain,(
% 2.51/1.00    ! [X0] : (! [X1] : (((k2_funct_1(X0) = X1 | (((k1_funct_1(X1,sK3(X0,X1)) != sK4(X0,X1) | ~r2_hidden(sK3(X0,X1),k2_relat_1(X0))) & k1_funct_1(X0,sK4(X0,X1)) = sK3(X0,X1) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))) | ~sP0(sK3(X0,X1),sK4(X0,X1),X0,X1)) | k1_relat_1(X1) != k2_relat_1(X0)) & ((! [X4,X5] : (((k1_funct_1(X1,X4) = X5 & r2_hidden(X4,k2_relat_1(X0))) | k1_funct_1(X0,X5) != X4 | ~r2_hidden(X5,k1_relat_1(X0))) & sP0(X4,X5,X0,X1)) & k1_relat_1(X1) = k2_relat_1(X0)) | k2_funct_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.51/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f28,f29])).
% 2.51/1.00  
% 2.51/1.00  fof(f46,plain,(
% 2.51/1.00    ( ! [X4,X0,X5,X1] : (sP0(X4,X5,X0,X1) | k2_funct_1(X0) != X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.51/1.00    inference(cnf_transformation,[],[f30])).
% 2.51/1.00  
% 2.51/1.00  fof(f65,plain,(
% 2.51/1.00    ( ! [X4,X0,X5] : (sP0(X4,X5,X0,k2_funct_1(X0)) | ~v1_funct_1(k2_funct_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.51/1.00    inference(equality_resolution,[],[f46])).
% 2.51/1.00  
% 2.51/1.00  fof(f23,plain,(
% 2.51/1.00    ! [X2,X3,X0,X1] : ((sP0(X2,X3,X0,X1) | ((k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0)))) & (((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))) | ~sP0(X2,X3,X0,X1)))),
% 2.51/1.00    inference(nnf_transformation,[],[f17])).
% 2.51/1.00  
% 2.51/1.00  fof(f24,plain,(
% 2.51/1.00    ! [X2,X3,X0,X1] : ((sP0(X2,X3,X0,X1) | ((k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0)))) & ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0)) | ~sP0(X2,X3,X0,X1)))),
% 2.51/1.00    inference(flattening,[],[f23])).
% 2.51/1.00  
% 2.51/1.00  fof(f25,plain,(
% 2.51/1.00    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ((k1_funct_1(X2,X1) != X0 | ~r2_hidden(X1,k1_relat_1(X2))) & k1_funct_1(X3,X0) = X1 & r2_hidden(X0,k2_relat_1(X2)))) & ((k1_funct_1(X2,X1) = X0 & r2_hidden(X1,k1_relat_1(X2))) | k1_funct_1(X3,X0) != X1 | ~r2_hidden(X0,k2_relat_1(X2)) | ~sP0(X0,X1,X2,X3)))),
% 2.51/1.00    inference(rectify,[],[f24])).
% 2.51/1.00  
% 2.51/1.00  fof(f41,plain,(
% 2.51/1.00    ( ! [X2,X0,X3,X1] : (k1_funct_1(X2,X1) = X0 | k1_funct_1(X3,X0) != X1 | ~r2_hidden(X0,k2_relat_1(X2)) | ~sP0(X0,X1,X2,X3)) )),
% 2.51/1.00    inference(cnf_transformation,[],[f25])).
% 2.51/1.00  
% 2.51/1.00  fof(f59,plain,(
% 2.51/1.00    ( ! [X2,X0,X3] : (k1_funct_1(X2,k1_funct_1(X3,X0)) = X0 | ~r2_hidden(X0,k2_relat_1(X2)) | ~sP0(X0,k1_funct_1(X3,X0),X2,X3)) )),
% 2.51/1.00    inference(equality_resolution,[],[f41])).
% 2.51/1.00  
% 2.51/1.00  fof(f35,plain,(
% 2.51/1.00    ( ! [X0] : (v2_funct_1(X0) | r2_hidden(sK2(X0),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.51/1.00    inference(cnf_transformation,[],[f22])).
% 2.51/1.00  
% 2.51/1.00  fof(f36,plain,(
% 2.51/1.00    ( ! [X0] : (v2_funct_1(X0) | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK2(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.51/1.00    inference(cnf_transformation,[],[f22])).
% 2.51/1.00  
% 2.51/1.00  fof(f37,plain,(
% 2.51/1.00    ( ! [X0] : (v2_funct_1(X0) | sK1(X0) != sK2(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.51/1.00    inference(cnf_transformation,[],[f22])).
% 2.51/1.00  
% 2.51/1.00  cnf(c_24,negated_conjecture,
% 2.51/1.00      ( v1_relat_1(sK5) ),
% 2.51/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_3935,negated_conjecture,
% 2.51/1.00      ( v1_relat_1(sK5) ),
% 2.51/1.00      inference(subtyping,[status(esa)],[c_24]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_4462,plain,
% 2.51/1.00      ( v1_relat_1(sK5) = iProver_top ),
% 2.51/1.00      inference(predicate_to_equality,[status(thm)],[c_3935]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_20,plain,
% 2.51/1.00      ( ~ v1_relat_1(X0)
% 2.51/1.00      | ~ v1_funct_1(X0)
% 2.51/1.00      | ~ v2_funct_1(X0)
% 2.51/1.00      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 2.51/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_3939,plain,
% 2.51/1.00      ( ~ v1_relat_1(X0_42)
% 2.51/1.00      | ~ v1_funct_1(X0_42)
% 2.51/1.00      | ~ v2_funct_1(X0_42)
% 2.51/1.00      | k1_relat_1(k2_funct_1(X0_42)) = k2_relat_1(X0_42) ),
% 2.51/1.00      inference(subtyping,[status(esa)],[c_20]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_4458,plain,
% 2.51/1.00      ( k1_relat_1(k2_funct_1(X0_42)) = k2_relat_1(X0_42)
% 2.51/1.00      | v1_relat_1(X0_42) != iProver_top
% 2.51/1.00      | v1_funct_1(X0_42) != iProver_top
% 2.51/1.00      | v2_funct_1(X0_42) != iProver_top ),
% 2.51/1.00      inference(predicate_to_equality,[status(thm)],[c_3939]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_5069,plain,
% 2.51/1.00      ( k1_relat_1(k2_funct_1(sK5)) = k2_relat_1(sK5)
% 2.51/1.00      | v1_funct_1(sK5) != iProver_top
% 2.51/1.00      | v2_funct_1(sK5) != iProver_top ),
% 2.51/1.00      inference(superposition,[status(thm)],[c_4462,c_4458]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_23,negated_conjecture,
% 2.51/1.00      ( v1_funct_1(sK5) ),
% 2.51/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_22,negated_conjecture,
% 2.51/1.00      ( v2_funct_1(sK5) ),
% 2.51/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_4032,plain,
% 2.51/1.00      ( ~ v1_relat_1(sK5)
% 2.51/1.00      | ~ v1_funct_1(sK5)
% 2.51/1.00      | ~ v2_funct_1(sK5)
% 2.51/1.00      | k1_relat_1(k2_funct_1(sK5)) = k2_relat_1(sK5) ),
% 2.51/1.00      inference(instantiation,[status(thm)],[c_3939]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_5172,plain,
% 2.51/1.00      ( k1_relat_1(k2_funct_1(sK5)) = k2_relat_1(sK5) ),
% 2.51/1.00      inference(global_propositional_subsumption,
% 2.51/1.00                [status(thm)],
% 2.51/1.00                [c_5069,c_24,c_23,c_22,c_4032]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_3,plain,
% 2.51/1.00      ( r2_hidden(sK1(X0),k1_relat_1(X0))
% 2.51/1.00      | ~ v1_relat_1(X0)
% 2.51/1.00      | ~ v1_funct_1(X0)
% 2.51/1.00      | v2_funct_1(X0) ),
% 2.51/1.00      inference(cnf_transformation,[],[f34]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_3955,plain,
% 2.51/1.00      ( r2_hidden(sK1(X0_42),k1_relat_1(X0_42))
% 2.51/1.00      | ~ v1_relat_1(X0_42)
% 2.51/1.00      | ~ v1_funct_1(X0_42)
% 2.51/1.00      | v2_funct_1(X0_42) ),
% 2.51/1.00      inference(subtyping,[status(esa)],[c_3]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_4442,plain,
% 2.51/1.00      ( r2_hidden(sK1(X0_42),k1_relat_1(X0_42)) = iProver_top
% 2.51/1.00      | v1_relat_1(X0_42) != iProver_top
% 2.51/1.00      | v1_funct_1(X0_42) != iProver_top
% 2.51/1.00      | v2_funct_1(X0_42) = iProver_top ),
% 2.51/1.00      inference(predicate_to_equality,[status(thm)],[c_3955]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_5175,plain,
% 2.51/1.00      ( r2_hidden(sK1(k2_funct_1(sK5)),k2_relat_1(sK5)) = iProver_top
% 2.51/1.00      | v1_relat_1(k2_funct_1(sK5)) != iProver_top
% 2.51/1.00      | v1_funct_1(k2_funct_1(sK5)) != iProver_top
% 2.51/1.00      | v2_funct_1(k2_funct_1(sK5)) = iProver_top ),
% 2.51/1.00      inference(superposition,[status(thm)],[c_5172,c_4442]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_25,plain,
% 2.51/1.00      ( v1_relat_1(sK5) = iProver_top ),
% 2.51/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_26,plain,
% 2.51/1.00      ( v1_funct_1(sK5) = iProver_top ),
% 2.51/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_21,negated_conjecture,
% 2.51/1.00      ( ~ v2_funct_1(k2_funct_1(sK5)) ),
% 2.51/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_28,plain,
% 2.51/1.00      ( v2_funct_1(k2_funct_1(sK5)) != iProver_top ),
% 2.51/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_6,plain,
% 2.51/1.00      ( ~ v1_relat_1(X0)
% 2.51/1.00      | v1_relat_1(k2_funct_1(X0))
% 2.51/1.00      | ~ v1_funct_1(X0) ),
% 2.51/1.00      inference(cnf_transformation,[],[f38]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_69,plain,
% 2.51/1.00      ( v1_relat_1(X0) != iProver_top
% 2.51/1.00      | v1_relat_1(k2_funct_1(X0)) = iProver_top
% 2.51/1.00      | v1_funct_1(X0) != iProver_top ),
% 2.51/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_71,plain,
% 2.51/1.00      ( v1_relat_1(k2_funct_1(sK5)) = iProver_top
% 2.51/1.00      | v1_relat_1(sK5) != iProver_top
% 2.51/1.00      | v1_funct_1(sK5) != iProver_top ),
% 2.51/1.00      inference(instantiation,[status(thm)],[c_69]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_5,plain,
% 2.51/1.00      ( ~ v1_relat_1(X0)
% 2.51/1.00      | ~ v1_funct_1(X0)
% 2.51/1.00      | v1_funct_1(k2_funct_1(X0)) ),
% 2.51/1.00      inference(cnf_transformation,[],[f39]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_72,plain,
% 2.51/1.00      ( v1_relat_1(X0) != iProver_top
% 2.51/1.00      | v1_funct_1(X0) != iProver_top
% 2.51/1.00      | v1_funct_1(k2_funct_1(X0)) = iProver_top ),
% 2.51/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_74,plain,
% 2.51/1.00      ( v1_relat_1(sK5) != iProver_top
% 2.51/1.00      | v1_funct_1(k2_funct_1(sK5)) = iProver_top
% 2.51/1.00      | v1_funct_1(sK5) != iProver_top ),
% 2.51/1.00      inference(instantiation,[status(thm)],[c_72]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_5196,plain,
% 2.51/1.00      ( r2_hidden(sK1(k2_funct_1(sK5)),k2_relat_1(sK5)) = iProver_top ),
% 2.51/1.00      inference(global_propositional_subsumption,
% 2.51/1.00                [status(thm)],
% 2.51/1.00                [c_5175,c_25,c_26,c_28,c_71,c_74]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_17,plain,
% 2.51/1.00      ( sP0(X0,X1,X2,k2_funct_1(X2))
% 2.51/1.00      | ~ v1_relat_1(X2)
% 2.51/1.00      | ~ v1_relat_1(k2_funct_1(X2))
% 2.51/1.00      | ~ v1_funct_1(X2)
% 2.51/1.00      | ~ v1_funct_1(k2_funct_1(X2))
% 2.51/1.00      | ~ v2_funct_1(X2) ),
% 2.51/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_3941,plain,
% 2.51/1.00      ( sP0(X0_44,X1_44,X0_42,k2_funct_1(X0_42))
% 2.51/1.00      | ~ v1_relat_1(X0_42)
% 2.51/1.00      | ~ v1_relat_1(k2_funct_1(X0_42))
% 2.51/1.00      | ~ v1_funct_1(X0_42)
% 2.51/1.00      | ~ v1_funct_1(k2_funct_1(X0_42))
% 2.51/1.00      | ~ v2_funct_1(X0_42) ),
% 2.51/1.00      inference(subtyping,[status(esa)],[c_17]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_4456,plain,
% 2.51/1.00      ( sP0(X0_44,X1_44,X0_42,k2_funct_1(X0_42)) = iProver_top
% 2.51/1.00      | v1_relat_1(X0_42) != iProver_top
% 2.51/1.00      | v1_relat_1(k2_funct_1(X0_42)) != iProver_top
% 2.51/1.00      | v1_funct_1(X0_42) != iProver_top
% 2.51/1.00      | v1_funct_1(k2_funct_1(X0_42)) != iProver_top
% 2.51/1.00      | v2_funct_1(X0_42) != iProver_top ),
% 2.51/1.00      inference(predicate_to_equality,[status(thm)],[c_3941]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_3953,plain,
% 2.51/1.00      ( ~ v1_relat_1(X0_42)
% 2.51/1.00      | ~ v1_funct_1(X0_42)
% 2.51/1.00      | v1_funct_1(k2_funct_1(X0_42)) ),
% 2.51/1.00      inference(subtyping,[status(esa)],[c_5]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_4444,plain,
% 2.51/1.00      ( v1_relat_1(X0_42) != iProver_top
% 2.51/1.00      | v1_funct_1(X0_42) != iProver_top
% 2.51/1.00      | v1_funct_1(k2_funct_1(X0_42)) = iProver_top ),
% 2.51/1.00      inference(predicate_to_equality,[status(thm)],[c_3953]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_3952,plain,
% 2.51/1.00      ( ~ v1_relat_1(X0_42)
% 2.51/1.00      | v1_relat_1(k2_funct_1(X0_42))
% 2.51/1.00      | ~ v1_funct_1(X0_42) ),
% 2.51/1.00      inference(subtyping,[status(esa)],[c_6]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_4445,plain,
% 2.51/1.00      ( v1_relat_1(X0_42) != iProver_top
% 2.51/1.00      | v1_relat_1(k2_funct_1(X0_42)) = iProver_top
% 2.51/1.00      | v1_funct_1(X0_42) != iProver_top ),
% 2.51/1.00      inference(predicate_to_equality,[status(thm)],[c_3952]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_4561,plain,
% 2.51/1.00      ( sP0(X0_44,X1_44,X0_42,k2_funct_1(X0_42)) = iProver_top
% 2.51/1.00      | v1_relat_1(X0_42) != iProver_top
% 2.51/1.00      | v1_funct_1(X0_42) != iProver_top
% 2.51/1.00      | v2_funct_1(X0_42) != iProver_top ),
% 2.51/1.00      inference(forward_subsumption_resolution,
% 2.51/1.00                [status(thm)],
% 2.51/1.00                [c_4456,c_4444,c_4445]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_10,plain,
% 2.51/1.00      ( ~ sP0(X0,k1_funct_1(X1,X0),X2,X1)
% 2.51/1.00      | ~ r2_hidden(X0,k2_relat_1(X2))
% 2.51/1.00      | k1_funct_1(X2,k1_funct_1(X1,X0)) = X0 ),
% 2.51/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_3948,plain,
% 2.51/1.00      ( ~ sP0(X0_44,k1_funct_1(X0_42,X0_44),X1_42,X0_42)
% 2.51/1.00      | ~ r2_hidden(X0_44,k2_relat_1(X1_42))
% 2.51/1.00      | k1_funct_1(X1_42,k1_funct_1(X0_42,X0_44)) = X0_44 ),
% 2.51/1.00      inference(subtyping,[status(esa)],[c_10]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_4449,plain,
% 2.51/1.00      ( k1_funct_1(X0_42,k1_funct_1(X1_42,X0_44)) = X0_44
% 2.51/1.00      | sP0(X0_44,k1_funct_1(X1_42,X0_44),X0_42,X1_42) != iProver_top
% 2.51/1.00      | r2_hidden(X0_44,k2_relat_1(X0_42)) != iProver_top ),
% 2.51/1.00      inference(predicate_to_equality,[status(thm)],[c_3948]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_5395,plain,
% 2.51/1.00      ( k1_funct_1(X0_42,k1_funct_1(k2_funct_1(X0_42),X0_44)) = X0_44
% 2.51/1.00      | r2_hidden(X0_44,k2_relat_1(X0_42)) != iProver_top
% 2.51/1.00      | v1_relat_1(X0_42) != iProver_top
% 2.51/1.00      | v1_funct_1(X0_42) != iProver_top
% 2.51/1.00      | v2_funct_1(X0_42) != iProver_top ),
% 2.51/1.00      inference(superposition,[status(thm)],[c_4561,c_4449]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_6001,plain,
% 2.51/1.00      ( k1_funct_1(sK5,k1_funct_1(k2_funct_1(sK5),sK1(k2_funct_1(sK5)))) = sK1(k2_funct_1(sK5))
% 2.51/1.00      | v1_relat_1(sK5) != iProver_top
% 2.51/1.00      | v1_funct_1(sK5) != iProver_top
% 2.51/1.00      | v2_funct_1(sK5) != iProver_top ),
% 2.51/1.00      inference(superposition,[status(thm)],[c_5196,c_5395]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_27,plain,
% 2.51/1.00      ( v2_funct_1(sK5) = iProver_top ),
% 2.51/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_6766,plain,
% 2.51/1.00      ( k1_funct_1(sK5,k1_funct_1(k2_funct_1(sK5),sK1(k2_funct_1(sK5)))) = sK1(k2_funct_1(sK5)) ),
% 2.51/1.00      inference(global_propositional_subsumption,
% 2.51/1.00                [status(thm)],
% 2.51/1.00                [c_6001,c_25,c_26,c_27]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_2,plain,
% 2.51/1.00      ( r2_hidden(sK2(X0),k1_relat_1(X0))
% 2.51/1.00      | ~ v1_relat_1(X0)
% 2.51/1.00      | ~ v1_funct_1(X0)
% 2.51/1.00      | v2_funct_1(X0) ),
% 2.51/1.00      inference(cnf_transformation,[],[f35]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_3956,plain,
% 2.51/1.00      ( r2_hidden(sK2(X0_42),k1_relat_1(X0_42))
% 2.51/1.00      | ~ v1_relat_1(X0_42)
% 2.51/1.00      | ~ v1_funct_1(X0_42)
% 2.51/1.00      | v2_funct_1(X0_42) ),
% 2.51/1.00      inference(subtyping,[status(esa)],[c_2]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_4441,plain,
% 2.51/1.00      ( r2_hidden(sK2(X0_42),k1_relat_1(X0_42)) = iProver_top
% 2.51/1.00      | v1_relat_1(X0_42) != iProver_top
% 2.51/1.00      | v1_funct_1(X0_42) != iProver_top
% 2.51/1.00      | v2_funct_1(X0_42) = iProver_top ),
% 2.51/1.00      inference(predicate_to_equality,[status(thm)],[c_3956]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_5176,plain,
% 2.51/1.00      ( r2_hidden(sK2(k2_funct_1(sK5)),k2_relat_1(sK5)) = iProver_top
% 2.51/1.00      | v1_relat_1(k2_funct_1(sK5)) != iProver_top
% 2.51/1.00      | v1_funct_1(k2_funct_1(sK5)) != iProver_top
% 2.51/1.00      | v2_funct_1(k2_funct_1(sK5)) = iProver_top ),
% 2.51/1.00      inference(superposition,[status(thm)],[c_5172,c_4441]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_1630,plain,
% 2.51/1.00      ( r2_hidden(sK2(X0),k1_relat_1(X0))
% 2.51/1.00      | ~ v1_relat_1(X0)
% 2.51/1.00      | ~ v1_funct_1(X0)
% 2.51/1.00      | k2_funct_1(sK5) != X0 ),
% 2.51/1.00      inference(resolution_lifted,[status(thm)],[c_2,c_21]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_1631,plain,
% 2.51/1.00      ( r2_hidden(sK2(k2_funct_1(sK5)),k1_relat_1(k2_funct_1(sK5)))
% 2.51/1.00      | ~ v1_relat_1(k2_funct_1(sK5))
% 2.51/1.00      | ~ v1_funct_1(k2_funct_1(sK5)) ),
% 2.51/1.00      inference(unflattening,[status(thm)],[c_1630]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_1632,plain,
% 2.51/1.00      ( r2_hidden(sK2(k2_funct_1(sK5)),k1_relat_1(k2_funct_1(sK5))) = iProver_top
% 2.51/1.00      | v1_relat_1(k2_funct_1(sK5)) != iProver_top
% 2.51/1.00      | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
% 2.51/1.00      inference(predicate_to_equality,[status(thm)],[c_1631]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_3974,plain,
% 2.51/1.00      ( k2_relat_1(X0_42) = k2_relat_1(X1_42) | X0_42 != X1_42 ),
% 2.51/1.00      theory(equality) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_3983,plain,
% 2.51/1.00      ( k2_relat_1(sK5) = k2_relat_1(sK5) | sK5 != sK5 ),
% 2.51/1.00      inference(instantiation,[status(thm)],[c_3974]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_3960,plain,( X0_42 = X0_42 ),theory(equality) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_3985,plain,
% 2.51/1.00      ( sK5 = sK5 ),
% 2.51/1.00      inference(instantiation,[status(thm)],[c_3960]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_3962,plain,( X0_44 = X0_44 ),theory(equality) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_4865,plain,
% 2.51/1.00      ( sK2(k2_funct_1(sK5)) = sK2(k2_funct_1(sK5)) ),
% 2.51/1.00      inference(instantiation,[status(thm)],[c_3962]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_3964,plain,
% 2.51/1.00      ( X0_43 != X1_43 | X2_43 != X1_43 | X2_43 = X0_43 ),
% 2.51/1.00      theory(equality) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_4757,plain,
% 2.51/1.00      ( k2_relat_1(X0_42) != X0_43
% 2.51/1.00      | k2_relat_1(X0_42) = k1_relat_1(X1_42)
% 2.51/1.00      | k1_relat_1(X1_42) != X0_43 ),
% 2.51/1.00      inference(instantiation,[status(thm)],[c_3964]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_4830,plain,
% 2.51/1.00      ( k2_relat_1(X0_42) != k2_relat_1(X0_42)
% 2.51/1.00      | k2_relat_1(X0_42) = k1_relat_1(X1_42)
% 2.51/1.00      | k1_relat_1(X1_42) != k2_relat_1(X0_42) ),
% 2.51/1.00      inference(instantiation,[status(thm)],[c_4757]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_5056,plain,
% 2.51/1.00      ( k2_relat_1(X0_42) != k2_relat_1(X0_42)
% 2.51/1.00      | k2_relat_1(X0_42) = k1_relat_1(k2_funct_1(X0_42))
% 2.51/1.00      | k1_relat_1(k2_funct_1(X0_42)) != k2_relat_1(X0_42) ),
% 2.51/1.00      inference(instantiation,[status(thm)],[c_4830]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_5057,plain,
% 2.51/1.00      ( k2_relat_1(sK5) != k2_relat_1(sK5)
% 2.51/1.00      | k2_relat_1(sK5) = k1_relat_1(k2_funct_1(sK5))
% 2.51/1.00      | k1_relat_1(k2_funct_1(sK5)) != k2_relat_1(sK5) ),
% 2.51/1.00      inference(instantiation,[status(thm)],[c_5056]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_3971,plain,
% 2.51/1.00      ( ~ r2_hidden(X0_44,X0_43)
% 2.51/1.00      | r2_hidden(X1_44,X1_43)
% 2.51/1.00      | X1_44 != X0_44
% 2.51/1.00      | X1_43 != X0_43 ),
% 2.51/1.00      theory(equality) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_4786,plain,
% 2.51/1.00      ( r2_hidden(X0_44,X0_43)
% 2.51/1.00      | ~ r2_hidden(sK2(k2_funct_1(sK5)),k1_relat_1(k2_funct_1(sK5)))
% 2.51/1.00      | X0_44 != sK2(k2_funct_1(sK5))
% 2.51/1.00      | X0_43 != k1_relat_1(k2_funct_1(sK5)) ),
% 2.51/1.00      inference(instantiation,[status(thm)],[c_3971]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_4918,plain,
% 2.51/1.00      ( r2_hidden(sK2(k2_funct_1(sK5)),X0_43)
% 2.51/1.00      | ~ r2_hidden(sK2(k2_funct_1(sK5)),k1_relat_1(k2_funct_1(sK5)))
% 2.51/1.00      | sK2(k2_funct_1(sK5)) != sK2(k2_funct_1(sK5))
% 2.51/1.00      | X0_43 != k1_relat_1(k2_funct_1(sK5)) ),
% 2.51/1.00      inference(instantiation,[status(thm)],[c_4786]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_5125,plain,
% 2.51/1.00      ( r2_hidden(sK2(k2_funct_1(sK5)),k2_relat_1(X0_42))
% 2.51/1.00      | ~ r2_hidden(sK2(k2_funct_1(sK5)),k1_relat_1(k2_funct_1(sK5)))
% 2.51/1.00      | sK2(k2_funct_1(sK5)) != sK2(k2_funct_1(sK5))
% 2.51/1.00      | k2_relat_1(X0_42) != k1_relat_1(k2_funct_1(sK5)) ),
% 2.51/1.00      inference(instantiation,[status(thm)],[c_4918]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_5128,plain,
% 2.51/1.00      ( sK2(k2_funct_1(sK5)) != sK2(k2_funct_1(sK5))
% 2.51/1.00      | k2_relat_1(X0_42) != k1_relat_1(k2_funct_1(sK5))
% 2.51/1.00      | r2_hidden(sK2(k2_funct_1(sK5)),k2_relat_1(X0_42)) = iProver_top
% 2.51/1.00      | r2_hidden(sK2(k2_funct_1(sK5)),k1_relat_1(k2_funct_1(sK5))) != iProver_top ),
% 2.51/1.00      inference(predicate_to_equality,[status(thm)],[c_5125]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_5130,plain,
% 2.51/1.00      ( sK2(k2_funct_1(sK5)) != sK2(k2_funct_1(sK5))
% 2.51/1.00      | k2_relat_1(sK5) != k1_relat_1(k2_funct_1(sK5))
% 2.51/1.00      | r2_hidden(sK2(k2_funct_1(sK5)),k2_relat_1(sK5)) = iProver_top
% 2.51/1.00      | r2_hidden(sK2(k2_funct_1(sK5)),k1_relat_1(k2_funct_1(sK5))) != iProver_top ),
% 2.51/1.00      inference(instantiation,[status(thm)],[c_5128]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_5261,plain,
% 2.51/1.00      ( r2_hidden(sK2(k2_funct_1(sK5)),k2_relat_1(sK5)) = iProver_top ),
% 2.51/1.00      inference(global_propositional_subsumption,
% 2.51/1.00                [status(thm)],
% 2.51/1.00                [c_5176,c_24,c_25,c_23,c_26,c_22,c_71,c_74,c_1632,c_3983,
% 2.51/1.00                 c_3985,c_4032,c_4865,c_5057,c_5130]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_6000,plain,
% 2.51/1.00      ( k1_funct_1(sK5,k1_funct_1(k2_funct_1(sK5),sK2(k2_funct_1(sK5)))) = sK2(k2_funct_1(sK5))
% 2.51/1.00      | v1_relat_1(sK5) != iProver_top
% 2.51/1.00      | v1_funct_1(sK5) != iProver_top
% 2.51/1.00      | v2_funct_1(sK5) != iProver_top ),
% 2.51/1.00      inference(superposition,[status(thm)],[c_5261,c_5395]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_70,plain,
% 2.51/1.00      ( v1_relat_1(k2_funct_1(sK5))
% 2.51/1.00      | ~ v1_relat_1(sK5)
% 2.51/1.00      | ~ v1_funct_1(sK5) ),
% 2.51/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_73,plain,
% 2.51/1.00      ( ~ v1_relat_1(sK5)
% 2.51/1.00      | v1_funct_1(k2_funct_1(sK5))
% 2.51/1.00      | ~ v1_funct_1(sK5) ),
% 2.51/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_5129,plain,
% 2.51/1.00      ( r2_hidden(sK2(k2_funct_1(sK5)),k2_relat_1(sK5))
% 2.51/1.00      | ~ r2_hidden(sK2(k2_funct_1(sK5)),k1_relat_1(k2_funct_1(sK5)))
% 2.51/1.00      | sK2(k2_funct_1(sK5)) != sK2(k2_funct_1(sK5))
% 2.51/1.00      | k2_relat_1(sK5) != k1_relat_1(k2_funct_1(sK5)) ),
% 2.51/1.00      inference(instantiation,[status(thm)],[c_5125]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_5126,plain,
% 2.51/1.00      ( ~ sP0(sK2(k2_funct_1(sK5)),k1_funct_1(X0_42,sK2(k2_funct_1(sK5))),X1_42,X0_42)
% 2.51/1.00      | ~ r2_hidden(sK2(k2_funct_1(sK5)),k2_relat_1(X1_42))
% 2.51/1.00      | k1_funct_1(X1_42,k1_funct_1(X0_42,sK2(k2_funct_1(sK5)))) = sK2(k2_funct_1(sK5)) ),
% 2.51/1.00      inference(instantiation,[status(thm)],[c_3948]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_5514,plain,
% 2.51/1.00      ( ~ sP0(sK2(k2_funct_1(sK5)),k1_funct_1(k2_funct_1(X0_42),sK2(k2_funct_1(sK5))),X0_42,k2_funct_1(X0_42))
% 2.51/1.00      | ~ r2_hidden(sK2(k2_funct_1(sK5)),k2_relat_1(X0_42))
% 2.51/1.00      | k1_funct_1(X0_42,k1_funct_1(k2_funct_1(X0_42),sK2(k2_funct_1(sK5)))) = sK2(k2_funct_1(sK5)) ),
% 2.51/1.00      inference(instantiation,[status(thm)],[c_5126]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_5517,plain,
% 2.51/1.00      ( ~ sP0(sK2(k2_funct_1(sK5)),k1_funct_1(k2_funct_1(sK5),sK2(k2_funct_1(sK5))),sK5,k2_funct_1(sK5))
% 2.51/1.00      | ~ r2_hidden(sK2(k2_funct_1(sK5)),k2_relat_1(sK5))
% 2.51/1.00      | k1_funct_1(sK5,k1_funct_1(k2_funct_1(sK5),sK2(k2_funct_1(sK5)))) = sK2(k2_funct_1(sK5)) ),
% 2.51/1.00      inference(instantiation,[status(thm)],[c_5514]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_4102,plain,
% 2.51/1.00      ( ~ v1_funct_1(X0_42)
% 2.51/1.00      | sP0(X0_44,X1_44,X0_42,k2_funct_1(X0_42))
% 2.51/1.00      | ~ v1_relat_1(X0_42)
% 2.51/1.00      | ~ v2_funct_1(X0_42) ),
% 2.51/1.00      inference(global_propositional_subsumption,
% 2.51/1.00                [status(thm)],
% 2.51/1.00                [c_3941,c_3953,c_3952]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_4103,plain,
% 2.51/1.00      ( sP0(X0_44,X1_44,X0_42,k2_funct_1(X0_42))
% 2.51/1.00      | ~ v1_relat_1(X0_42)
% 2.51/1.00      | ~ v1_funct_1(X0_42)
% 2.51/1.00      | ~ v2_funct_1(X0_42) ),
% 2.51/1.00      inference(renaming,[status(thm)],[c_4102]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_5515,plain,
% 2.51/1.00      ( sP0(sK2(k2_funct_1(sK5)),k1_funct_1(k2_funct_1(X0_42),sK2(k2_funct_1(sK5))),X0_42,k2_funct_1(X0_42))
% 2.51/1.00      | ~ v1_relat_1(X0_42)
% 2.51/1.00      | ~ v1_funct_1(X0_42)
% 2.51/1.00      | ~ v2_funct_1(X0_42) ),
% 2.51/1.00      inference(instantiation,[status(thm)],[c_4103]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_5521,plain,
% 2.51/1.00      ( sP0(sK2(k2_funct_1(sK5)),k1_funct_1(k2_funct_1(sK5),sK2(k2_funct_1(sK5))),sK5,k2_funct_1(sK5))
% 2.51/1.00      | ~ v1_relat_1(sK5)
% 2.51/1.00      | ~ v1_funct_1(sK5)
% 2.51/1.00      | ~ v2_funct_1(sK5) ),
% 2.51/1.00      inference(instantiation,[status(thm)],[c_5515]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_6418,plain,
% 2.51/1.00      ( k1_funct_1(sK5,k1_funct_1(k2_funct_1(sK5),sK2(k2_funct_1(sK5)))) = sK2(k2_funct_1(sK5)) ),
% 2.51/1.00      inference(global_propositional_subsumption,
% 2.51/1.00                [status(thm)],
% 2.51/1.00                [c_6000,c_24,c_23,c_22,c_70,c_73,c_1631,c_3983,c_3985,
% 2.51/1.00                 c_4032,c_4865,c_5057,c_5129,c_5517,c_5521]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_1,plain,
% 2.51/1.00      ( ~ v1_relat_1(X0)
% 2.51/1.00      | ~ v1_funct_1(X0)
% 2.51/1.00      | v2_funct_1(X0)
% 2.51/1.00      | k1_funct_1(X0,sK2(X0)) = k1_funct_1(X0,sK1(X0)) ),
% 2.51/1.00      inference(cnf_transformation,[],[f36]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_3957,plain,
% 2.51/1.00      ( ~ v1_relat_1(X0_42)
% 2.51/1.00      | ~ v1_funct_1(X0_42)
% 2.51/1.00      | v2_funct_1(X0_42)
% 2.51/1.00      | k1_funct_1(X0_42,sK2(X0_42)) = k1_funct_1(X0_42,sK1(X0_42)) ),
% 2.51/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_4440,plain,
% 2.51/1.00      ( k1_funct_1(X0_42,sK2(X0_42)) = k1_funct_1(X0_42,sK1(X0_42))
% 2.51/1.00      | v1_relat_1(X0_42) != iProver_top
% 2.51/1.00      | v1_funct_1(X0_42) != iProver_top
% 2.51/1.00      | v2_funct_1(X0_42) = iProver_top ),
% 2.51/1.00      inference(predicate_to_equality,[status(thm)],[c_3957]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_4842,plain,
% 2.51/1.00      ( k1_funct_1(k2_funct_1(X0_42),sK1(k2_funct_1(X0_42))) = k1_funct_1(k2_funct_1(X0_42),sK2(k2_funct_1(X0_42)))
% 2.51/1.00      | v1_relat_1(X0_42) != iProver_top
% 2.51/1.00      | v1_funct_1(X0_42) != iProver_top
% 2.51/1.00      | v1_funct_1(k2_funct_1(X0_42)) != iProver_top
% 2.51/1.00      | v2_funct_1(k2_funct_1(X0_42)) = iProver_top ),
% 2.51/1.00      inference(superposition,[status(thm)],[c_4445,c_4440]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_3993,plain,
% 2.51/1.00      ( v1_relat_1(X0_42) != iProver_top
% 2.51/1.00      | v1_funct_1(X0_42) != iProver_top
% 2.51/1.00      | v1_funct_1(k2_funct_1(X0_42)) = iProver_top ),
% 2.51/1.00      inference(predicate_to_equality,[status(thm)],[c_3953]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_6035,plain,
% 2.51/1.00      ( v1_funct_1(X0_42) != iProver_top
% 2.51/1.00      | v1_relat_1(X0_42) != iProver_top
% 2.51/1.00      | k1_funct_1(k2_funct_1(X0_42),sK1(k2_funct_1(X0_42))) = k1_funct_1(k2_funct_1(X0_42),sK2(k2_funct_1(X0_42)))
% 2.51/1.00      | v2_funct_1(k2_funct_1(X0_42)) = iProver_top ),
% 2.51/1.00      inference(global_propositional_subsumption,
% 2.51/1.00                [status(thm)],
% 2.51/1.00                [c_4842,c_3993]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_6036,plain,
% 2.51/1.00      ( k1_funct_1(k2_funct_1(X0_42),sK1(k2_funct_1(X0_42))) = k1_funct_1(k2_funct_1(X0_42),sK2(k2_funct_1(X0_42)))
% 2.51/1.00      | v1_relat_1(X0_42) != iProver_top
% 2.51/1.00      | v1_funct_1(X0_42) != iProver_top
% 2.51/1.00      | v2_funct_1(k2_funct_1(X0_42)) = iProver_top ),
% 2.51/1.00      inference(renaming,[status(thm)],[c_6035]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_3938,negated_conjecture,
% 2.51/1.00      ( ~ v2_funct_1(k2_funct_1(sK5)) ),
% 2.51/1.00      inference(subtyping,[status(esa)],[c_21]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_4459,plain,
% 2.51/1.00      ( v2_funct_1(k2_funct_1(sK5)) != iProver_top ),
% 2.51/1.00      inference(predicate_to_equality,[status(thm)],[c_3938]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_6045,plain,
% 2.51/1.00      ( k1_funct_1(k2_funct_1(sK5),sK1(k2_funct_1(sK5))) = k1_funct_1(k2_funct_1(sK5),sK2(k2_funct_1(sK5)))
% 2.51/1.00      | v1_relat_1(sK5) != iProver_top
% 2.51/1.00      | v1_funct_1(sK5) != iProver_top ),
% 2.51/1.00      inference(superposition,[status(thm)],[c_6036,c_4459]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_4854,plain,
% 2.51/1.00      ( k1_funct_1(k2_funct_1(sK5),sK1(k2_funct_1(sK5))) = k1_funct_1(k2_funct_1(sK5),sK2(k2_funct_1(sK5)))
% 2.51/1.00      | v1_relat_1(sK5) != iProver_top
% 2.51/1.00      | v1_funct_1(k2_funct_1(sK5)) != iProver_top
% 2.51/1.00      | v1_funct_1(sK5) != iProver_top
% 2.51/1.00      | v2_funct_1(k2_funct_1(sK5)) = iProver_top ),
% 2.51/1.00      inference(instantiation,[status(thm)],[c_4842]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_6215,plain,
% 2.51/1.00      ( k1_funct_1(k2_funct_1(sK5),sK1(k2_funct_1(sK5))) = k1_funct_1(k2_funct_1(sK5),sK2(k2_funct_1(sK5))) ),
% 2.51/1.00      inference(global_propositional_subsumption,
% 2.51/1.00                [status(thm)],
% 2.51/1.00                [c_6045,c_25,c_26,c_28,c_74,c_4854]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_6420,plain,
% 2.51/1.00      ( k1_funct_1(sK5,k1_funct_1(k2_funct_1(sK5),sK1(k2_funct_1(sK5)))) = sK2(k2_funct_1(sK5)) ),
% 2.51/1.00      inference(light_normalisation,[status(thm)],[c_6418,c_6215]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_6769,plain,
% 2.51/1.00      ( sK2(k2_funct_1(sK5)) = sK1(k2_funct_1(sK5)) ),
% 2.51/1.00      inference(demodulation,[status(thm)],[c_6766,c_6420]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_0,plain,
% 2.51/1.00      ( ~ v1_relat_1(X0)
% 2.51/1.00      | ~ v1_funct_1(X0)
% 2.51/1.00      | v2_funct_1(X0)
% 2.51/1.00      | sK2(X0) != sK1(X0) ),
% 2.51/1.00      inference(cnf_transformation,[],[f37]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_3958,plain,
% 2.51/1.00      ( ~ v1_relat_1(X0_42)
% 2.51/1.00      | ~ v1_funct_1(X0_42)
% 2.51/1.00      | v2_funct_1(X0_42)
% 2.51/1.00      | sK2(X0_42) != sK1(X0_42) ),
% 2.51/1.00      inference(subtyping,[status(esa)],[c_0]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_4730,plain,
% 2.51/1.00      ( ~ v1_relat_1(k2_funct_1(sK5))
% 2.51/1.00      | ~ v1_funct_1(k2_funct_1(sK5))
% 2.51/1.00      | v2_funct_1(k2_funct_1(sK5))
% 2.51/1.00      | sK2(k2_funct_1(sK5)) != sK1(k2_funct_1(sK5)) ),
% 2.51/1.00      inference(instantiation,[status(thm)],[c_3958]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(contradiction,plain,
% 2.51/1.00      ( $false ),
% 2.51/1.00      inference(minisat,
% 2.51/1.00                [status(thm)],
% 2.51/1.00                [c_6769,c_4730,c_73,c_70,c_21,c_23,c_24]) ).
% 2.51/1.00  
% 2.51/1.00  
% 2.51/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.51/1.00  
% 2.51/1.00  ------                               Statistics
% 2.51/1.00  
% 2.51/1.00  ------ General
% 2.51/1.00  
% 2.51/1.00  abstr_ref_over_cycles:                  0
% 2.51/1.00  abstr_ref_under_cycles:                 0
% 2.51/1.00  gc_basic_clause_elim:                   0
% 2.51/1.00  forced_gc_time:                         0
% 2.51/1.00  parsing_time:                           0.009
% 2.51/1.00  unif_index_cands_time:                  0.
% 2.51/1.00  unif_index_add_time:                    0.
% 2.51/1.00  orderings_time:                         0.
% 2.51/1.00  out_proof_time:                         0.012
% 2.51/1.00  total_time:                             0.187
% 2.51/1.00  num_of_symbols:                         45
% 2.51/1.00  num_of_terms:                           3141
% 2.51/1.00  
% 2.51/1.00  ------ Preprocessing
% 2.51/1.00  
% 2.51/1.00  num_of_splits:                          0
% 2.51/1.00  num_of_split_atoms:                     0
% 2.51/1.00  num_of_reused_defs:                     0
% 2.51/1.00  num_eq_ax_congr_red:                    21
% 2.51/1.00  num_of_sem_filtered_clauses:            1
% 2.51/1.00  num_of_subtypes:                        3
% 2.51/1.00  monotx_restored_types:                  1
% 2.51/1.00  sat_num_of_epr_types:                   0
% 2.51/1.00  sat_num_of_non_cyclic_types:            0
% 2.51/1.00  sat_guarded_non_collapsed_types:        1
% 2.51/1.00  num_pure_diseq_elim:                    0
% 2.51/1.00  simp_replaced_by:                       0
% 2.51/1.00  res_preprocessed:                       127
% 2.51/1.00  prep_upred:                             0
% 2.51/1.00  prep_unflattend:                        208
% 2.51/1.00  smt_new_axioms:                         0
% 2.51/1.00  pred_elim_cands:                        5
% 2.51/1.00  pred_elim:                              0
% 2.51/1.00  pred_elim_cl:                           0
% 2.51/1.00  pred_elim_cycles:                       4
% 2.51/1.00  merged_defs:                            0
% 2.51/1.00  merged_defs_ncl:                        0
% 2.51/1.00  bin_hyper_res:                          0
% 2.51/1.00  prep_cycles:                            4
% 2.51/1.00  pred_elim_time:                         0.067
% 2.51/1.00  splitting_time:                         0.
% 2.51/1.00  sem_filter_time:                        0.
% 2.51/1.00  monotx_time:                            0.001
% 2.51/1.00  subtype_inf_time:                       0.001
% 2.51/1.00  
% 2.51/1.00  ------ Problem properties
% 2.51/1.00  
% 2.51/1.00  clauses:                                24
% 2.51/1.00  conjectures:                            4
% 2.51/1.00  epr:                                    3
% 2.51/1.00  horn:                                   17
% 2.51/1.00  ground:                                 4
% 2.51/1.00  unary:                                  4
% 2.51/1.00  binary:                                 3
% 2.51/1.00  lits:                                   101
% 2.51/1.00  lits_eq:                                17
% 2.51/1.00  fd_pure:                                0
% 2.51/1.00  fd_pseudo:                              0
% 2.51/1.00  fd_cond:                                0
% 2.51/1.00  fd_pseudo_cond:                         5
% 2.51/1.00  ac_symbols:                             0
% 2.51/1.00  
% 2.51/1.00  ------ Propositional Solver
% 2.51/1.00  
% 2.51/1.00  prop_solver_calls:                      27
% 2.51/1.00  prop_fast_solver_calls:                 2117
% 2.51/1.00  smt_solver_calls:                       0
% 2.51/1.00  smt_fast_solver_calls:                  0
% 2.51/1.00  prop_num_of_clauses:                    1144
% 2.51/1.00  prop_preprocess_simplified:             5379
% 2.51/1.00  prop_fo_subsumed:                       131
% 2.51/1.00  prop_solver_time:                       0.
% 2.51/1.00  smt_solver_time:                        0.
% 2.51/1.00  smt_fast_solver_time:                   0.
% 2.51/1.00  prop_fast_solver_time:                  0.
% 2.51/1.00  prop_unsat_core_time:                   0.
% 2.51/1.00  
% 2.51/1.00  ------ QBF
% 2.51/1.00  
% 2.51/1.00  qbf_q_res:                              0
% 2.51/1.00  qbf_num_tautologies:                    0
% 2.51/1.00  qbf_prep_cycles:                        0
% 2.51/1.00  
% 2.51/1.00  ------ BMC1
% 2.51/1.00  
% 2.51/1.00  bmc1_current_bound:                     -1
% 2.51/1.00  bmc1_last_solved_bound:                 -1
% 2.51/1.00  bmc1_unsat_core_size:                   -1
% 2.51/1.00  bmc1_unsat_core_parents_size:           -1
% 2.51/1.00  bmc1_merge_next_fun:                    0
% 2.51/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.51/1.00  
% 2.51/1.00  ------ Instantiation
% 2.51/1.00  
% 2.51/1.00  inst_num_of_clauses:                    320
% 2.51/1.00  inst_num_in_passive:                    10
% 2.51/1.00  inst_num_in_active:                     214
% 2.51/1.00  inst_num_in_unprocessed:                96
% 2.51/1.00  inst_num_of_loops:                      220
% 2.51/1.00  inst_num_of_learning_restarts:          0
% 2.51/1.00  inst_num_moves_active_passive:          1
% 2.51/1.00  inst_lit_activity:                      0
% 2.51/1.00  inst_lit_activity_moves:                0
% 2.51/1.00  inst_num_tautologies:                   0
% 2.51/1.00  inst_num_prop_implied:                  0
% 2.51/1.00  inst_num_existing_simplified:           0
% 2.51/1.00  inst_num_eq_res_simplified:             0
% 2.51/1.00  inst_num_child_elim:                    0
% 2.51/1.00  inst_num_of_dismatching_blockings:      133
% 2.51/1.00  inst_num_of_non_proper_insts:           460
% 2.51/1.00  inst_num_of_duplicates:                 0
% 2.51/1.00  inst_inst_num_from_inst_to_res:         0
% 2.51/1.00  inst_dismatching_checking_time:         0.
% 2.51/1.00  
% 2.51/1.00  ------ Resolution
% 2.51/1.00  
% 2.51/1.00  res_num_of_clauses:                     0
% 2.51/1.00  res_num_in_passive:                     0
% 2.51/1.00  res_num_in_active:                      0
% 2.51/1.00  res_num_of_loops:                       131
% 2.51/1.00  res_forward_subset_subsumed:            61
% 2.51/1.00  res_backward_subset_subsumed:           2
% 2.51/1.00  res_forward_subsumed:                   0
% 2.51/1.00  res_backward_subsumed:                  0
% 2.51/1.00  res_forward_subsumption_resolution:     28
% 2.51/1.00  res_backward_subsumption_resolution:    0
% 2.51/1.00  res_clause_to_clause_subsumption:       356
% 2.51/1.00  res_orphan_elimination:                 0
% 2.51/1.00  res_tautology_del:                      128
% 2.51/1.00  res_num_eq_res_simplified:              0
% 2.51/1.00  res_num_sel_changes:                    0
% 2.51/1.00  res_moves_from_active_to_pass:          0
% 2.51/1.00  
% 2.51/1.00  ------ Superposition
% 2.51/1.00  
% 2.51/1.00  sup_time_total:                         0.
% 2.51/1.00  sup_time_generating:                    0.
% 2.51/1.00  sup_time_sim_full:                      0.
% 2.51/1.00  sup_time_sim_immed:                     0.
% 2.51/1.00  
% 2.51/1.00  sup_num_of_clauses:                     51
% 2.51/1.00  sup_num_in_active:                      41
% 2.51/1.00  sup_num_in_passive:                     10
% 2.51/1.00  sup_num_of_loops:                       42
% 2.51/1.00  sup_fw_superposition:                   33
% 2.51/1.00  sup_bw_superposition:                   22
% 2.51/1.00  sup_immediate_simplified:               23
% 2.51/1.00  sup_given_eliminated:                   0
% 2.51/1.00  comparisons_done:                       0
% 2.51/1.00  comparisons_avoided:                    0
% 2.51/1.00  
% 2.51/1.00  ------ Simplifications
% 2.51/1.00  
% 2.51/1.00  
% 2.51/1.00  sim_fw_subset_subsumed:                 17
% 2.51/1.00  sim_bw_subset_subsumed:                 0
% 2.51/1.00  sim_fw_subsumed:                        0
% 2.51/1.00  sim_bw_subsumed:                        0
% 2.51/1.00  sim_fw_subsumption_res:                 6
% 2.51/1.00  sim_bw_subsumption_res:                 0
% 2.51/1.00  sim_tautology_del:                      6
% 2.51/1.00  sim_eq_tautology_del:                   6
% 2.51/1.00  sim_eq_res_simp:                        0
% 2.51/1.00  sim_fw_demodulated:                     0
% 2.51/1.00  sim_bw_demodulated:                     1
% 2.51/1.00  sim_light_normalised:                   7
% 2.51/1.00  sim_joinable_taut:                      0
% 2.51/1.00  sim_joinable_simp:                      0
% 2.51/1.00  sim_ac_normalised:                      0
% 2.51/1.00  sim_smt_subsumption:                    0
% 2.51/1.00  
%------------------------------------------------------------------------------
