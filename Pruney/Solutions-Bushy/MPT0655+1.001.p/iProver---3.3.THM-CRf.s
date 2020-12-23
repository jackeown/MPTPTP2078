%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0655+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:49 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 758 expanded)
%              Number of clauses        :   67 ( 211 expanded)
%              Number of leaves         :    9 ( 146 expanded)
%              Depth                    :   23
%              Number of atoms          :  518 (4000 expanded)
%              Number of equality atoms :  200 ( 918 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   19 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f36,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK2(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f39,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => v2_funct_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f57,plain,(
    ~ v2_funct_1(k2_funct_1(sK5)) ),
    inference(cnf_transformation,[],[f32])).

fof(f54,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f32])).

fof(f55,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f32])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = k2_relat_1(X0)
      | k2_funct_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f66,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f56,plain,(
    v2_funct_1(sK5) ),
    inference(cnf_transformation,[],[f32])).

fof(f35,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | r2_hidden(sK2(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k2_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
          & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
        & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 )
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
        & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 )
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f34,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | r2_hidden(sK1(X0),k1_relat_1(X0))
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

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_2257,plain,
    ( ~ v1_relat_1(X0_43)
    | v1_relat_1(k2_funct_1(X0_43))
    | ~ v1_funct_1(X0_43) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_2766,plain,
    ( v1_relat_1(X0_43) != iProver_top
    | v1_relat_1(k2_funct_1(X0_43)) = iProver_top
    | v1_funct_1(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2257])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | k1_funct_1(X0,sK2(X0)) = k1_funct_1(X0,sK1(X0)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_2262,plain,
    ( ~ v1_relat_1(X0_43)
    | ~ v1_funct_1(X0_43)
    | v2_funct_1(X0_43)
    | k1_funct_1(X0_43,sK2(X0_43)) = k1_funct_1(X0_43,sK1(X0_43)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_2761,plain,
    ( k1_funct_1(X0_43,sK2(X0_43)) = k1_funct_1(X0_43,sK1(X0_43))
    | v1_relat_1(X0_43) != iProver_top
    | v1_funct_1(X0_43) != iProver_top
    | v2_funct_1(X0_43) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2262])).

cnf(c_3142,plain,
    ( k1_funct_1(k2_funct_1(X0_43),sK1(k2_funct_1(X0_43))) = k1_funct_1(k2_funct_1(X0_43),sK2(k2_funct_1(X0_43)))
    | v1_relat_1(X0_43) != iProver_top
    | v1_funct_1(X0_43) != iProver_top
    | v1_funct_1(k2_funct_1(X0_43)) != iProver_top
    | v2_funct_1(k2_funct_1(X0_43)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2766,c_2761])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_2258,plain,
    ( ~ v1_relat_1(X0_43)
    | ~ v1_funct_1(X0_43)
    | v1_funct_1(k2_funct_1(X0_43)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_2298,plain,
    ( v1_relat_1(X0_43) != iProver_top
    | v1_funct_1(X0_43) != iProver_top
    | v1_funct_1(k2_funct_1(X0_43)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2258])).

cnf(c_5697,plain,
    ( v1_funct_1(X0_43) != iProver_top
    | v1_relat_1(X0_43) != iProver_top
    | k1_funct_1(k2_funct_1(X0_43),sK1(k2_funct_1(X0_43))) = k1_funct_1(k2_funct_1(X0_43),sK2(k2_funct_1(X0_43)))
    | v2_funct_1(k2_funct_1(X0_43)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3142,c_2298])).

cnf(c_5698,plain,
    ( k1_funct_1(k2_funct_1(X0_43),sK1(k2_funct_1(X0_43))) = k1_funct_1(k2_funct_1(X0_43),sK2(k2_funct_1(X0_43)))
    | v1_relat_1(X0_43) != iProver_top
    | v1_funct_1(X0_43) != iProver_top
    | v2_funct_1(k2_funct_1(X0_43)) = iProver_top ),
    inference(renaming,[status(thm)],[c_5697])).

cnf(c_21,negated_conjecture,
    ( ~ v2_funct_1(k2_funct_1(sK5)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2243,negated_conjecture,
    ( ~ v2_funct_1(k2_funct_1(sK5)) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_2780,plain,
    ( v2_funct_1(k2_funct_1(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2243])).

cnf(c_5707,plain,
    ( k1_funct_1(k2_funct_1(sK5),sK1(k2_funct_1(sK5))) = k1_funct_1(k2_funct_1(sK5),sK2(k2_funct_1(sK5)))
    | v1_relat_1(sK5) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5698,c_2780])).

cnf(c_24,negated_conjecture,
    ( v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_25,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_26,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_28,plain,
    ( v2_funct_1(k2_funct_1(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_74,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_76,plain,
    ( v1_relat_1(sK5) != iProver_top
    | v1_funct_1(k2_funct_1(sK5)) = iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_74])).

cnf(c_3154,plain,
    ( k1_funct_1(k2_funct_1(sK5),sK1(k2_funct_1(sK5))) = k1_funct_1(k2_funct_1(sK5),sK2(k2_funct_1(sK5)))
    | v1_relat_1(sK5) != iProver_top
    | v1_funct_1(k2_funct_1(sK5)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v2_funct_1(k2_funct_1(sK5)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3142])).

cnf(c_5726,plain,
    ( k1_funct_1(k2_funct_1(sK5),sK1(k2_funct_1(sK5))) = k1_funct_1(k2_funct_1(sK5),sK2(k2_funct_1(sK5))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5707,c_25,c_26,c_28,c_76,c_3154])).

cnf(c_2240,negated_conjecture,
    ( v1_relat_1(sK5) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_2783,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2240])).

cnf(c_18,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_141,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v2_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18,c_6,c_5])).

cnf(c_142,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(renaming,[status(thm)],[c_141])).

cnf(c_2239,plain,
    ( ~ v1_relat_1(X0_43)
    | ~ v1_funct_1(X0_43)
    | ~ v2_funct_1(X0_43)
    | k1_relat_1(k2_funct_1(X0_43)) = k2_relat_1(X0_43) ),
    inference(subtyping,[status(esa)],[c_142])).

cnf(c_2784,plain,
    ( k1_relat_1(k2_funct_1(X0_43)) = k2_relat_1(X0_43)
    | v1_relat_1(X0_43) != iProver_top
    | v1_funct_1(X0_43) != iProver_top
    | v2_funct_1(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2239])).

cnf(c_3288,plain,
    ( k1_relat_1(k2_funct_1(sK5)) = k2_relat_1(sK5)
    | v1_funct_1(sK5) != iProver_top
    | v2_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2783,c_2784])).

cnf(c_22,negated_conjecture,
    ( v2_funct_1(sK5) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2344,plain,
    ( ~ v1_relat_1(sK5)
    | ~ v1_funct_1(sK5)
    | ~ v2_funct_1(sK5)
    | k1_relat_1(k2_funct_1(sK5)) = k2_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_2239])).

cnf(c_3361,plain,
    ( k1_relat_1(k2_funct_1(sK5)) = k2_relat_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3288,c_24,c_23,c_22,c_2344])).

cnf(c_2,plain,
    ( r2_hidden(sK2(X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_2261,plain,
    ( r2_hidden(sK2(X0_43),k1_relat_1(X0_43))
    | ~ v1_relat_1(X0_43)
    | ~ v1_funct_1(X0_43)
    | v2_funct_1(X0_43) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_2762,plain,
    ( r2_hidden(sK2(X0_43),k1_relat_1(X0_43)) = iProver_top
    | v1_relat_1(X0_43) != iProver_top
    | v1_funct_1(X0_43) != iProver_top
    | v2_funct_1(X0_43) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2261])).

cnf(c_3365,plain,
    ( r2_hidden(sK2(k2_funct_1(sK5)),k2_relat_1(sK5)) = iProver_top
    | v1_relat_1(k2_funct_1(sK5)) != iProver_top
    | v1_funct_1(k2_funct_1(sK5)) != iProver_top
    | v2_funct_1(k2_funct_1(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3361,c_2762])).

cnf(c_71,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_73,plain,
    ( v1_relat_1(k2_funct_1(sK5)) = iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_71])).

cnf(c_3475,plain,
    ( r2_hidden(sK2(k2_funct_1(sK5)),k2_relat_1(sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3365,c_25,c_26,c_28,c_73,c_76])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2244,plain,
    ( ~ r2_hidden(X0_45,k2_relat_1(X0_43))
    | ~ v1_relat_1(X0_43)
    | ~ v1_funct_1(X0_43)
    | ~ v2_funct_1(X0_43)
    | k1_funct_1(X0_43,k1_funct_1(k2_funct_1(X0_43),X0_45)) = X0_45 ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_2779,plain,
    ( k1_funct_1(X0_43,k1_funct_1(k2_funct_1(X0_43),X0_45)) = X0_45
    | r2_hidden(X0_45,k2_relat_1(X0_43)) != iProver_top
    | v1_relat_1(X0_43) != iProver_top
    | v1_funct_1(X0_43) != iProver_top
    | v2_funct_1(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2244])).

cnf(c_3764,plain,
    ( k1_funct_1(sK5,k1_funct_1(k2_funct_1(sK5),sK2(k2_funct_1(sK5)))) = sK2(k2_funct_1(sK5))
    | v1_relat_1(sK5) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v2_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3475,c_2779])).

cnf(c_72,plain,
    ( v1_relat_1(k2_funct_1(sK5))
    | ~ v1_relat_1(sK5)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_75,plain,
    ( ~ v1_relat_1(sK5)
    | v1_funct_1(k2_funct_1(sK5))
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3383,plain,
    ( r2_hidden(sK2(k2_funct_1(sK5)),k2_relat_1(sK5))
    | ~ v1_relat_1(k2_funct_1(sK5))
    | ~ v1_funct_1(k2_funct_1(sK5))
    | v2_funct_1(k2_funct_1(sK5)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3365])).

cnf(c_3464,plain,
    ( ~ r2_hidden(sK2(k2_funct_1(sK5)),k2_relat_1(sK5))
    | ~ v1_relat_1(sK5)
    | ~ v1_funct_1(sK5)
    | ~ v2_funct_1(sK5)
    | k1_funct_1(sK5,k1_funct_1(k2_funct_1(sK5),sK2(k2_funct_1(sK5)))) = sK2(k2_funct_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_2244])).

cnf(c_4368,plain,
    ( k1_funct_1(sK5,k1_funct_1(k2_funct_1(sK5),sK2(k2_funct_1(sK5)))) = sK2(k2_funct_1(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3764,c_24,c_23,c_22,c_21,c_72,c_75,c_3383,c_3464])).

cnf(c_5732,plain,
    ( k1_funct_1(sK5,k1_funct_1(k2_funct_1(sK5),sK1(k2_funct_1(sK5)))) = sK2(k2_funct_1(sK5)) ),
    inference(demodulation,[status(thm)],[c_5726,c_4368])).

cnf(c_3,plain,
    ( r2_hidden(sK1(X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_2260,plain,
    ( r2_hidden(sK1(X0_43),k1_relat_1(X0_43))
    | ~ v1_relat_1(X0_43)
    | ~ v1_funct_1(X0_43)
    | v2_funct_1(X0_43) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_2763,plain,
    ( r2_hidden(sK1(X0_43),k1_relat_1(X0_43)) = iProver_top
    | v1_relat_1(X0_43) != iProver_top
    | v1_funct_1(X0_43) != iProver_top
    | v2_funct_1(X0_43) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2260])).

cnf(c_3364,plain,
    ( r2_hidden(sK1(k2_funct_1(sK5)),k2_relat_1(sK5)) = iProver_top
    | v1_relat_1(k2_funct_1(sK5)) != iProver_top
    | v1_funct_1(k2_funct_1(sK5)) != iProver_top
    | v2_funct_1(k2_funct_1(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3361,c_2763])).

cnf(c_3385,plain,
    ( r2_hidden(sK1(k2_funct_1(sK5)),k2_relat_1(sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3364,c_25,c_26,c_28,c_73,c_76])).

cnf(c_3763,plain,
    ( k1_funct_1(sK5,k1_funct_1(k2_funct_1(sK5),sK1(k2_funct_1(sK5)))) = sK1(k2_funct_1(sK5))
    | v1_relat_1(sK5) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v2_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3385,c_2779])).

cnf(c_3382,plain,
    ( r2_hidden(sK1(k2_funct_1(sK5)),k2_relat_1(sK5))
    | ~ v1_relat_1(k2_funct_1(sK5))
    | ~ v1_funct_1(k2_funct_1(sK5))
    | v2_funct_1(k2_funct_1(sK5)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3364])).

cnf(c_3497,plain,
    ( ~ r2_hidden(sK1(k2_funct_1(sK5)),k2_relat_1(sK5))
    | ~ v1_relat_1(sK5)
    | ~ v1_funct_1(sK5)
    | ~ v2_funct_1(sK5)
    | k1_funct_1(sK5,k1_funct_1(k2_funct_1(sK5),sK1(k2_funct_1(sK5)))) = sK1(k2_funct_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_2244])).

cnf(c_4315,plain,
    ( k1_funct_1(sK5,k1_funct_1(k2_funct_1(sK5),sK1(k2_funct_1(sK5)))) = sK1(k2_funct_1(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3763,c_24,c_23,c_22,c_21,c_72,c_75,c_3382,c_3497])).

cnf(c_5734,plain,
    ( sK2(k2_funct_1(sK5)) = sK1(k2_funct_1(sK5)) ),
    inference(light_normalisation,[status(thm)],[c_5732,c_4315])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | sK2(X0) != sK1(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_2263,plain,
    ( ~ v1_relat_1(X0_43)
    | ~ v1_funct_1(X0_43)
    | v2_funct_1(X0_43)
    | sK2(X0_43) != sK1(X0_43) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_3066,plain,
    ( ~ v1_relat_1(k2_funct_1(sK5))
    | ~ v1_funct_1(k2_funct_1(sK5))
    | v2_funct_1(k2_funct_1(sK5))
    | sK2(k2_funct_1(sK5)) != sK1(k2_funct_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_2263])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5734,c_3066,c_75,c_72,c_21,c_23,c_24])).


%------------------------------------------------------------------------------
