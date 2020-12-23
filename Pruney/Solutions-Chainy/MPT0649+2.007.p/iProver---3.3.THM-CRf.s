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
% DateTime   : Thu Dec  3 11:50:21 EST 2020

% Result     : Theorem 2.05s
% Output     : CNFRefutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 437 expanded)
%              Number of clauses        :   67 ( 135 expanded)
%              Number of leaves         :   12 (  85 expanded)
%              Depth                    :   24
%              Number of atoms          :  497 (2450 expanded)
%              Number of equality atoms :  211 ( 826 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   19 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k1_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
          & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( r2_hidden(X0,k1_relat_1(X1))
            & v2_funct_1(X1) )
         => ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
            & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) != X0
        | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) != X0 )
      & r2_hidden(X0,k1_relat_1(X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) != X0
        | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) != X0 )
      & r2_hidden(X0,k1_relat_1(X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f31,plain,
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

fof(f32,plain,
    ( ( k1_funct_1(k5_relat_1(sK4,k2_funct_1(sK4)),sK3) != sK3
      | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK3)) != sK3 )
    & r2_hidden(sK3,k1_relat_1(sK4))
    & v2_funct_1(sK4)
    & v1_funct_1(sK4)
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f20,f31])).

fof(f51,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f32])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

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

fof(f21,plain,(
    ! [X2,X3,X0,X1] :
      ( sP0(X2,X3,X0,X1)
    <=> ( ( k1_funct_1(X0,X3) = X2
          & r2_hidden(X3,k1_relat_1(X0)) )
        | k1_funct_1(X1,X2) != X3
        | ~ r2_hidden(X2,k2_relat_1(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

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

fof(f44,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k1_relat_1(X1)
      | k2_funct_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f64,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f36,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f37,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f53,plain,(
    v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f32])).

fof(f52,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f32])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
           => k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0)
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0)
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f47,plain,(
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
    inference(cnf_transformation,[],[f30])).

fof(f59,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X1,k1_funct_1(X0,X5)) = X5
      | ~ r2_hidden(X5,k1_relat_1(X0))
      | k2_funct_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f60,plain,(
    ! [X0,X5] :
      ( k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X5)) = X5
      | ~ r2_hidden(X5,k1_relat_1(X0))
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f59])).

fof(f55,plain,
    ( k1_funct_1(k5_relat_1(sK4,k2_funct_1(sK4)),sK3) != sK3
    | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK3)) != sK3 ),
    inference(cnf_transformation,[],[f32])).

fof(f54,plain,(
    r2_hidden(sK3,k1_relat_1(sK4)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_22,negated_conjecture,
    ( v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1130,negated_conjecture,
    ( v1_relat_1(sK4) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1586,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1130])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1143,plain,
    ( ~ v1_relat_1(X0_45)
    | k7_relat_1(X0_45,k1_relat_1(X0_45)) = X0_45 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1574,plain,
    ( k7_relat_1(X0_45,k1_relat_1(X0_45)) = X0_45
    | v1_relat_1(X0_45) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1143])).

cnf(c_1904,plain,
    ( k7_relat_1(sK4,k1_relat_1(sK4)) = sK4 ),
    inference(superposition,[status(thm)],[c_1586,c_1574])).

cnf(c_2,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(X0,X1)),k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1142,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(X0_45,X0_46)),k2_relat_1(X0_45))
    | ~ v1_relat_1(X0_45) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1575,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(X0_45,X0_46)),k2_relat_1(X0_45)) = iProver_top
    | v1_relat_1(X0_45) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1142])).

cnf(c_2010,plain,
    ( r1_tarski(k2_relat_1(sK4),k2_relat_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1904,c_1575])).

cnf(c_23,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2593,plain,
    ( r1_tarski(k2_relat_1(sK4),k2_relat_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2010,c_23])).

cnf(c_17,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(k2_funct_1(X0))
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_4,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_3,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_130,plain,
    ( ~ v1_relat_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17,c_4,c_3])).

cnf(c_131,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(renaming,[status(thm)],[c_130])).

cnf(c_20,negated_conjecture,
    ( v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_290,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_131,c_20])).

cnf(c_291,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_290])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_28,plain,
    ( ~ v2_funct_1(sK4)
    | ~ v1_funct_1(k2_funct_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(k2_funct_1(sK4))
    | ~ v1_relat_1(sK4)
    | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_67,plain,
    ( ~ v1_funct_1(sK4)
    | v1_relat_1(k2_funct_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_70,plain,
    ( v1_funct_1(k2_funct_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_293,plain,
    ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_291,c_22,c_21,c_20,c_28,c_67,c_70])).

cnf(c_1129,plain,
    ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
    inference(subtyping,[status(esa)],[c_293])).

cnf(c_0,plain,
    ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1144,plain,
    ( ~ r1_tarski(k2_relat_1(X0_45),k1_relat_1(X1_45))
    | ~ v1_relat_1(X0_45)
    | ~ v1_relat_1(X1_45)
    | k1_relat_1(k5_relat_1(X0_45,X1_45)) = k1_relat_1(X0_45) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1573,plain,
    ( k1_relat_1(k5_relat_1(X0_45,X1_45)) = k1_relat_1(X0_45)
    | r1_tarski(k2_relat_1(X0_45),k1_relat_1(X1_45)) != iProver_top
    | v1_relat_1(X0_45) != iProver_top
    | v1_relat_1(X1_45) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1144])).

cnf(c_1897,plain,
    ( k1_relat_1(k5_relat_1(X0_45,k2_funct_1(sK4))) = k1_relat_1(X0_45)
    | r1_tarski(k2_relat_1(X0_45),k2_relat_1(sK4)) != iProver_top
    | v1_relat_1(X0_45) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1129,c_1573])).

cnf(c_24,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_66,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_68,plain,
    ( v1_funct_1(sK4) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_66])).

cnf(c_2070,plain,
    ( v1_relat_1(X0_45) != iProver_top
    | r1_tarski(k2_relat_1(X0_45),k2_relat_1(sK4)) != iProver_top
    | k1_relat_1(k5_relat_1(X0_45,k2_funct_1(sK4))) = k1_relat_1(X0_45) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1897,c_23,c_24,c_68])).

cnf(c_2071,plain,
    ( k1_relat_1(k5_relat_1(X0_45,k2_funct_1(sK4))) = k1_relat_1(X0_45)
    | r1_tarski(k2_relat_1(X0_45),k2_relat_1(sK4)) != iProver_top
    | v1_relat_1(X0_45) != iProver_top ),
    inference(renaming,[status(thm)],[c_2070])).

cnf(c_2598,plain,
    ( k1_relat_1(k5_relat_1(sK4,k2_funct_1(sK4))) = k1_relat_1(sK4)
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2593,c_2071])).

cnf(c_1899,plain,
    ( k1_relat_1(k5_relat_1(sK4,k2_funct_1(sK4))) = k1_relat_1(sK4)
    | r1_tarski(k2_relat_1(sK4),k2_relat_1(sK4)) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1897])).

cnf(c_2601,plain,
    ( k1_relat_1(k5_relat_1(sK4,k2_funct_1(sK4))) = k1_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2598,c_23,c_24,c_68,c_1899,c_2010])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X1,X2)))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1139,plain,
    ( ~ r2_hidden(X0_44,k1_relat_1(k5_relat_1(X0_45,X1_45)))
    | ~ v1_funct_1(X0_45)
    | ~ v1_funct_1(X1_45)
    | ~ v1_relat_1(X0_45)
    | ~ v1_relat_1(X1_45)
    | k1_funct_1(k5_relat_1(X0_45,X1_45),X0_44) = k1_funct_1(X1_45,k1_funct_1(X0_45,X0_44)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1578,plain,
    ( k1_funct_1(k5_relat_1(X0_45,X1_45),X0_44) = k1_funct_1(X1_45,k1_funct_1(X0_45,X0_44))
    | r2_hidden(X0_44,k1_relat_1(k5_relat_1(X0_45,X1_45))) != iProver_top
    | v1_funct_1(X0_45) != iProver_top
    | v1_funct_1(X1_45) != iProver_top
    | v1_relat_1(X0_45) != iProver_top
    | v1_relat_1(X1_45) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1139])).

cnf(c_2929,plain,
    ( k1_funct_1(k5_relat_1(sK4,k2_funct_1(sK4)),X0_44) = k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0_44))
    | r2_hidden(X0_44,k1_relat_1(sK4)) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2601,c_1578])).

cnf(c_2931,plain,
    ( k1_funct_1(k5_relat_1(sK4,k2_funct_1(sK4)),sK3) = k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK3))
    | r2_hidden(sK3,k1_relat_1(sK4)) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2929])).

cnf(c_1149,plain,
    ( X0_44 != X1_44
    | X2_44 != X1_44
    | X2_44 = X0_44 ),
    theory(equality)).

cnf(c_1770,plain,
    ( k1_funct_1(k5_relat_1(sK4,k2_funct_1(sK4)),sK3) != X0_44
    | k1_funct_1(k5_relat_1(sK4,k2_funct_1(sK4)),sK3) = sK3
    | sK3 != X0_44 ),
    inference(instantiation,[status(thm)],[c_1149])).

cnf(c_1812,plain,
    ( k1_funct_1(k5_relat_1(sK4,k2_funct_1(sK4)),sK3) != k1_funct_1(X0_45,X0_44)
    | k1_funct_1(k5_relat_1(sK4,k2_funct_1(sK4)),sK3) = sK3
    | sK3 != k1_funct_1(X0_45,X0_44) ),
    inference(instantiation,[status(thm)],[c_1770])).

cnf(c_2198,plain,
    ( k1_funct_1(k5_relat_1(sK4,k2_funct_1(sK4)),sK3) != k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0_44))
    | k1_funct_1(k5_relat_1(sK4,k2_funct_1(sK4)),sK3) = sK3
    | sK3 != k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0_44)) ),
    inference(instantiation,[status(thm)],[c_1812])).

cnf(c_2199,plain,
    ( k1_funct_1(k5_relat_1(sK4,k2_funct_1(sK4)),sK3) != k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK3))
    | k1_funct_1(k5_relat_1(sK4,k2_funct_1(sK4)),sK3) = sK3
    | sK3 != k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK3)) ),
    inference(instantiation,[status(thm)],[c_2198])).

cnf(c_1927,plain,
    ( k1_funct_1(X0_45,X0_44) != X1_44
    | sK3 != X1_44
    | sK3 = k1_funct_1(X0_45,X0_44) ),
    inference(instantiation,[status(thm)],[c_1149])).

cnf(c_2123,plain,
    ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0_44)) != X0_44
    | sK3 != X0_44
    | sK3 = k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0_44)) ),
    inference(instantiation,[status(thm)],[c_1927])).

cnf(c_2124,plain,
    ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK3)) != sK3
    | sK3 = k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK3))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2123])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_403,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_20])).

cnf(c_404,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | ~ v1_funct_1(k2_funct_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(k2_funct_1(sK4))
    | ~ v1_relat_1(sK4)
    | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_403])).

cnf(c_408,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_404,c_22,c_21,c_67,c_70])).

cnf(c_1124,plain,
    ( ~ r2_hidden(X0_44,k1_relat_1(sK4))
    | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0_44)) = X0_44 ),
    inference(subtyping,[status(esa)],[c_408])).

cnf(c_1227,plain,
    ( ~ r2_hidden(sK3,k1_relat_1(sK4))
    | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK3)) = sK3 ),
    inference(instantiation,[status(thm)],[c_1124])).

cnf(c_18,negated_conjecture,
    ( k1_funct_1(k5_relat_1(sK4,k2_funct_1(sK4)),sK3) != sK3
    | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK3)) != sK3 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1133,negated_conjecture,
    ( k1_funct_1(k5_relat_1(sK4,k2_funct_1(sK4)),sK3) != sK3
    | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK3)) != sK3 ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1146,plain,
    ( X0_44 = X0_44 ),
    theory(equality)).

cnf(c_1179,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1146])).

cnf(c_69,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_71,plain,
    ( v1_funct_1(k2_funct_1(sK4)) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_69])).

cnf(c_19,negated_conjecture,
    ( r2_hidden(sK3,k1_relat_1(sK4)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_26,plain,
    ( r2_hidden(sK3,k1_relat_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2931,c_2199,c_2124,c_1227,c_1133,c_1179,c_71,c_68,c_26,c_19,c_24,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:14:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.05/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/0.98  
% 2.05/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.05/0.98  
% 2.05/0.98  ------  iProver source info
% 2.05/0.98  
% 2.05/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.05/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.05/0.98  git: non_committed_changes: false
% 2.05/0.98  git: last_make_outside_of_git: false
% 2.05/0.98  
% 2.05/0.98  ------ 
% 2.05/0.98  
% 2.05/0.98  ------ Input Options
% 2.05/0.98  
% 2.05/0.98  --out_options                           all
% 2.05/0.98  --tptp_safe_out                         true
% 2.05/0.98  --problem_path                          ""
% 2.05/0.98  --include_path                          ""
% 2.05/0.98  --clausifier                            res/vclausify_rel
% 2.05/0.98  --clausifier_options                    --mode clausify
% 2.05/0.98  --stdin                                 false
% 2.05/0.98  --stats_out                             all
% 2.05/0.98  
% 2.05/0.98  ------ General Options
% 2.05/0.98  
% 2.05/0.98  --fof                                   false
% 2.05/0.98  --time_out_real                         305.
% 2.05/0.98  --time_out_virtual                      -1.
% 2.05/0.98  --symbol_type_check                     false
% 2.05/0.98  --clausify_out                          false
% 2.05/0.98  --sig_cnt_out                           false
% 2.05/0.98  --trig_cnt_out                          false
% 2.05/0.98  --trig_cnt_out_tolerance                1.
% 2.05/0.98  --trig_cnt_out_sk_spl                   false
% 2.05/0.98  --abstr_cl_out                          false
% 2.05/0.98  
% 2.05/0.98  ------ Global Options
% 2.05/0.98  
% 2.05/0.98  --schedule                              default
% 2.05/0.98  --add_important_lit                     false
% 2.05/0.98  --prop_solver_per_cl                    1000
% 2.05/0.98  --min_unsat_core                        false
% 2.05/0.98  --soft_assumptions                      false
% 2.05/0.98  --soft_lemma_size                       3
% 2.05/0.98  --prop_impl_unit_size                   0
% 2.05/0.98  --prop_impl_unit                        []
% 2.05/0.98  --share_sel_clauses                     true
% 2.05/0.98  --reset_solvers                         false
% 2.05/0.98  --bc_imp_inh                            [conj_cone]
% 2.05/0.98  --conj_cone_tolerance                   3.
% 2.05/0.98  --extra_neg_conj                        none
% 2.05/0.98  --large_theory_mode                     true
% 2.05/0.98  --prolific_symb_bound                   200
% 2.05/0.98  --lt_threshold                          2000
% 2.05/0.98  --clause_weak_htbl                      true
% 2.05/0.98  --gc_record_bc_elim                     false
% 2.05/0.98  
% 2.05/0.98  ------ Preprocessing Options
% 2.05/0.98  
% 2.05/0.98  --preprocessing_flag                    true
% 2.05/0.98  --time_out_prep_mult                    0.1
% 2.05/0.98  --splitting_mode                        input
% 2.05/0.98  --splitting_grd                         true
% 2.05/0.98  --splitting_cvd                         false
% 2.05/0.98  --splitting_cvd_svl                     false
% 2.05/0.98  --splitting_nvd                         32
% 2.05/0.98  --sub_typing                            true
% 2.05/0.98  --prep_gs_sim                           true
% 2.05/0.98  --prep_unflatten                        true
% 2.05/0.98  --prep_res_sim                          true
% 2.05/0.98  --prep_upred                            true
% 2.05/0.98  --prep_sem_filter                       exhaustive
% 2.05/0.98  --prep_sem_filter_out                   false
% 2.05/0.98  --pred_elim                             true
% 2.05/0.98  --res_sim_input                         true
% 2.05/0.98  --eq_ax_congr_red                       true
% 2.05/0.98  --pure_diseq_elim                       true
% 2.05/0.98  --brand_transform                       false
% 2.05/0.98  --non_eq_to_eq                          false
% 2.05/0.98  --prep_def_merge                        true
% 2.05/0.98  --prep_def_merge_prop_impl              false
% 2.05/0.98  --prep_def_merge_mbd                    true
% 2.05/0.98  --prep_def_merge_tr_red                 false
% 2.05/0.98  --prep_def_merge_tr_cl                  false
% 2.05/0.98  --smt_preprocessing                     true
% 2.05/0.98  --smt_ac_axioms                         fast
% 2.05/0.98  --preprocessed_out                      false
% 2.05/0.98  --preprocessed_stats                    false
% 2.05/0.98  
% 2.05/0.98  ------ Abstraction refinement Options
% 2.05/0.98  
% 2.05/0.98  --abstr_ref                             []
% 2.05/0.98  --abstr_ref_prep                        false
% 2.05/0.98  --abstr_ref_until_sat                   false
% 2.05/0.98  --abstr_ref_sig_restrict                funpre
% 2.05/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.05/0.98  --abstr_ref_under                       []
% 2.05/0.98  
% 2.05/0.98  ------ SAT Options
% 2.05/0.98  
% 2.05/0.98  --sat_mode                              false
% 2.05/0.98  --sat_fm_restart_options                ""
% 2.05/0.98  --sat_gr_def                            false
% 2.05/0.98  --sat_epr_types                         true
% 2.05/0.98  --sat_non_cyclic_types                  false
% 2.05/0.98  --sat_finite_models                     false
% 2.05/0.98  --sat_fm_lemmas                         false
% 2.05/0.98  --sat_fm_prep                           false
% 2.05/0.98  --sat_fm_uc_incr                        true
% 2.05/0.98  --sat_out_model                         small
% 2.05/0.98  --sat_out_clauses                       false
% 2.05/0.98  
% 2.05/0.98  ------ QBF Options
% 2.05/0.98  
% 2.05/0.98  --qbf_mode                              false
% 2.05/0.98  --qbf_elim_univ                         false
% 2.05/0.98  --qbf_dom_inst                          none
% 2.05/0.98  --qbf_dom_pre_inst                      false
% 2.05/0.98  --qbf_sk_in                             false
% 2.05/0.98  --qbf_pred_elim                         true
% 2.05/0.98  --qbf_split                             512
% 2.05/0.98  
% 2.05/0.98  ------ BMC1 Options
% 2.05/0.98  
% 2.05/0.98  --bmc1_incremental                      false
% 2.05/0.98  --bmc1_axioms                           reachable_all
% 2.05/0.98  --bmc1_min_bound                        0
% 2.05/0.98  --bmc1_max_bound                        -1
% 2.05/0.98  --bmc1_max_bound_default                -1
% 2.05/0.98  --bmc1_symbol_reachability              true
% 2.05/0.98  --bmc1_property_lemmas                  false
% 2.05/0.98  --bmc1_k_induction                      false
% 2.05/0.98  --bmc1_non_equiv_states                 false
% 2.05/0.98  --bmc1_deadlock                         false
% 2.05/0.98  --bmc1_ucm                              false
% 2.05/0.98  --bmc1_add_unsat_core                   none
% 2.05/0.98  --bmc1_unsat_core_children              false
% 2.05/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.05/0.98  --bmc1_out_stat                         full
% 2.05/0.98  --bmc1_ground_init                      false
% 2.05/0.98  --bmc1_pre_inst_next_state              false
% 2.05/0.98  --bmc1_pre_inst_state                   false
% 2.05/0.98  --bmc1_pre_inst_reach_state             false
% 2.05/0.98  --bmc1_out_unsat_core                   false
% 2.05/0.98  --bmc1_aig_witness_out                  false
% 2.05/0.98  --bmc1_verbose                          false
% 2.05/0.98  --bmc1_dump_clauses_tptp                false
% 2.05/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.05/0.98  --bmc1_dump_file                        -
% 2.05/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.05/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.05/0.98  --bmc1_ucm_extend_mode                  1
% 2.05/0.98  --bmc1_ucm_init_mode                    2
% 2.05/0.98  --bmc1_ucm_cone_mode                    none
% 2.05/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.05/0.98  --bmc1_ucm_relax_model                  4
% 2.05/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.05/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.05/0.98  --bmc1_ucm_layered_model                none
% 2.05/0.98  --bmc1_ucm_max_lemma_size               10
% 2.05/0.98  
% 2.05/0.98  ------ AIG Options
% 2.05/0.98  
% 2.05/0.98  --aig_mode                              false
% 2.05/0.98  
% 2.05/0.98  ------ Instantiation Options
% 2.05/0.98  
% 2.05/0.98  --instantiation_flag                    true
% 2.05/0.98  --inst_sos_flag                         false
% 2.05/0.98  --inst_sos_phase                        true
% 2.05/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.05/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.05/0.98  --inst_lit_sel_side                     num_symb
% 2.05/0.98  --inst_solver_per_active                1400
% 2.05/0.98  --inst_solver_calls_frac                1.
% 2.05/0.98  --inst_passive_queue_type               priority_queues
% 2.05/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.05/0.98  --inst_passive_queues_freq              [25;2]
% 2.05/0.98  --inst_dismatching                      true
% 2.05/0.98  --inst_eager_unprocessed_to_passive     true
% 2.05/0.98  --inst_prop_sim_given                   true
% 2.05/0.98  --inst_prop_sim_new                     false
% 2.05/0.98  --inst_subs_new                         false
% 2.05/0.98  --inst_eq_res_simp                      false
% 2.05/0.98  --inst_subs_given                       false
% 2.05/0.98  --inst_orphan_elimination               true
% 2.05/0.98  --inst_learning_loop_flag               true
% 2.05/0.98  --inst_learning_start                   3000
% 2.05/0.98  --inst_learning_factor                  2
% 2.05/0.98  --inst_start_prop_sim_after_learn       3
% 2.05/0.98  --inst_sel_renew                        solver
% 2.05/0.98  --inst_lit_activity_flag                true
% 2.05/0.98  --inst_restr_to_given                   false
% 2.05/0.98  --inst_activity_threshold               500
% 2.05/0.98  --inst_out_proof                        true
% 2.05/0.98  
% 2.05/0.98  ------ Resolution Options
% 2.05/0.98  
% 2.05/0.98  --resolution_flag                       true
% 2.05/0.98  --res_lit_sel                           adaptive
% 2.05/0.98  --res_lit_sel_side                      none
% 2.05/0.98  --res_ordering                          kbo
% 2.05/0.98  --res_to_prop_solver                    active
% 2.05/0.98  --res_prop_simpl_new                    false
% 2.05/0.98  --res_prop_simpl_given                  true
% 2.05/0.98  --res_passive_queue_type                priority_queues
% 2.05/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.05/0.98  --res_passive_queues_freq               [15;5]
% 2.05/0.98  --res_forward_subs                      full
% 2.05/0.98  --res_backward_subs                     full
% 2.05/0.98  --res_forward_subs_resolution           true
% 2.05/0.98  --res_backward_subs_resolution          true
% 2.05/0.98  --res_orphan_elimination                true
% 2.05/0.98  --res_time_limit                        2.
% 2.05/0.98  --res_out_proof                         true
% 2.05/0.98  
% 2.05/0.98  ------ Superposition Options
% 2.05/0.98  
% 2.05/0.98  --superposition_flag                    true
% 2.05/0.98  --sup_passive_queue_type                priority_queues
% 2.05/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.05/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.05/0.98  --demod_completeness_check              fast
% 2.05/0.98  --demod_use_ground                      true
% 2.05/0.98  --sup_to_prop_solver                    passive
% 2.05/0.98  --sup_prop_simpl_new                    true
% 2.05/0.98  --sup_prop_simpl_given                  true
% 2.05/0.98  --sup_fun_splitting                     false
% 2.05/0.98  --sup_smt_interval                      50000
% 2.05/0.98  
% 2.05/0.98  ------ Superposition Simplification Setup
% 2.05/0.98  
% 2.05/0.98  --sup_indices_passive                   []
% 2.05/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.05/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.05/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.05/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.05/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.05/0.98  --sup_full_bw                           [BwDemod]
% 2.05/0.98  --sup_immed_triv                        [TrivRules]
% 2.05/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.05/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.05/0.98  --sup_immed_bw_main                     []
% 2.05/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.05/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.05/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.05/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.05/0.98  
% 2.05/0.98  ------ Combination Options
% 2.05/0.98  
% 2.05/0.98  --comb_res_mult                         3
% 2.05/0.98  --comb_sup_mult                         2
% 2.05/0.98  --comb_inst_mult                        10
% 2.05/0.98  
% 2.05/0.98  ------ Debug Options
% 2.05/0.98  
% 2.05/0.98  --dbg_backtrace                         false
% 2.05/0.98  --dbg_dump_prop_clauses                 false
% 2.05/0.98  --dbg_dump_prop_clauses_file            -
% 2.05/0.98  --dbg_out_stat                          false
% 2.05/0.98  ------ Parsing...
% 2.05/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.05/0.98  
% 2.05/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.05/0.98  
% 2.05/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.05/0.98  
% 2.05/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.05/0.98  ------ Proving...
% 2.05/0.98  ------ Problem Properties 
% 2.05/0.98  
% 2.05/0.98  
% 2.05/0.98  clauses                                 22
% 2.05/0.98  conjectures                             4
% 2.05/0.98  EPR                                     2
% 2.05/0.98  Horn                                    18
% 2.05/0.98  unary                                   5
% 2.05/0.98  binary                                  8
% 2.05/0.98  lits                                    62
% 2.05/0.98  lits eq                                 17
% 2.05/0.98  fd_pure                                 0
% 2.05/0.98  fd_pseudo                               0
% 2.05/0.98  fd_cond                                 3
% 2.05/0.98  fd_pseudo_cond                          1
% 2.05/0.98  AC symbols                              0
% 2.05/0.98  
% 2.05/0.98  ------ Schedule dynamic 5 is on 
% 2.05/0.98  
% 2.05/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.05/0.98  
% 2.05/0.98  
% 2.05/0.98  ------ 
% 2.05/0.98  Current options:
% 2.05/0.98  ------ 
% 2.05/0.98  
% 2.05/0.98  ------ Input Options
% 2.05/0.98  
% 2.05/0.98  --out_options                           all
% 2.05/0.98  --tptp_safe_out                         true
% 2.05/0.98  --problem_path                          ""
% 2.05/0.98  --include_path                          ""
% 2.05/0.98  --clausifier                            res/vclausify_rel
% 2.05/0.98  --clausifier_options                    --mode clausify
% 2.05/0.98  --stdin                                 false
% 2.05/0.98  --stats_out                             all
% 2.05/0.98  
% 2.05/0.98  ------ General Options
% 2.05/0.98  
% 2.05/0.98  --fof                                   false
% 2.05/0.98  --time_out_real                         305.
% 2.05/0.98  --time_out_virtual                      -1.
% 2.05/0.98  --symbol_type_check                     false
% 2.05/0.98  --clausify_out                          false
% 2.05/0.98  --sig_cnt_out                           false
% 2.05/0.98  --trig_cnt_out                          false
% 2.05/0.98  --trig_cnt_out_tolerance                1.
% 2.05/0.98  --trig_cnt_out_sk_spl                   false
% 2.05/0.98  --abstr_cl_out                          false
% 2.05/0.98  
% 2.05/0.98  ------ Global Options
% 2.05/0.98  
% 2.05/0.98  --schedule                              default
% 2.05/0.98  --add_important_lit                     false
% 2.05/0.98  --prop_solver_per_cl                    1000
% 2.05/0.98  --min_unsat_core                        false
% 2.05/0.98  --soft_assumptions                      false
% 2.05/0.98  --soft_lemma_size                       3
% 2.05/0.98  --prop_impl_unit_size                   0
% 2.05/0.98  --prop_impl_unit                        []
% 2.05/0.98  --share_sel_clauses                     true
% 2.05/0.98  --reset_solvers                         false
% 2.05/0.98  --bc_imp_inh                            [conj_cone]
% 2.05/0.98  --conj_cone_tolerance                   3.
% 2.05/0.98  --extra_neg_conj                        none
% 2.05/0.98  --large_theory_mode                     true
% 2.05/0.98  --prolific_symb_bound                   200
% 2.05/0.98  --lt_threshold                          2000
% 2.05/0.98  --clause_weak_htbl                      true
% 2.05/0.98  --gc_record_bc_elim                     false
% 2.05/0.98  
% 2.05/0.98  ------ Preprocessing Options
% 2.05/0.98  
% 2.05/0.98  --preprocessing_flag                    true
% 2.05/0.98  --time_out_prep_mult                    0.1
% 2.05/0.98  --splitting_mode                        input
% 2.05/0.98  --splitting_grd                         true
% 2.05/0.98  --splitting_cvd                         false
% 2.05/0.98  --splitting_cvd_svl                     false
% 2.05/0.98  --splitting_nvd                         32
% 2.05/0.98  --sub_typing                            true
% 2.05/0.98  --prep_gs_sim                           true
% 2.05/0.98  --prep_unflatten                        true
% 2.05/0.98  --prep_res_sim                          true
% 2.05/0.98  --prep_upred                            true
% 2.05/0.98  --prep_sem_filter                       exhaustive
% 2.05/0.98  --prep_sem_filter_out                   false
% 2.05/0.98  --pred_elim                             true
% 2.05/0.98  --res_sim_input                         true
% 2.05/0.98  --eq_ax_congr_red                       true
% 2.05/0.98  --pure_diseq_elim                       true
% 2.05/0.98  --brand_transform                       false
% 2.05/0.98  --non_eq_to_eq                          false
% 2.05/0.98  --prep_def_merge                        true
% 2.05/0.98  --prep_def_merge_prop_impl              false
% 2.05/0.98  --prep_def_merge_mbd                    true
% 2.05/0.98  --prep_def_merge_tr_red                 false
% 2.05/0.98  --prep_def_merge_tr_cl                  false
% 2.05/0.98  --smt_preprocessing                     true
% 2.05/0.98  --smt_ac_axioms                         fast
% 2.05/0.98  --preprocessed_out                      false
% 2.05/0.98  --preprocessed_stats                    false
% 2.05/0.98  
% 2.05/0.98  ------ Abstraction refinement Options
% 2.05/0.98  
% 2.05/0.98  --abstr_ref                             []
% 2.05/0.98  --abstr_ref_prep                        false
% 2.05/0.98  --abstr_ref_until_sat                   false
% 2.05/0.98  --abstr_ref_sig_restrict                funpre
% 2.05/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.05/0.98  --abstr_ref_under                       []
% 2.05/0.98  
% 2.05/0.98  ------ SAT Options
% 2.05/0.98  
% 2.05/0.98  --sat_mode                              false
% 2.05/0.98  --sat_fm_restart_options                ""
% 2.05/0.98  --sat_gr_def                            false
% 2.05/0.98  --sat_epr_types                         true
% 2.05/0.98  --sat_non_cyclic_types                  false
% 2.05/0.98  --sat_finite_models                     false
% 2.05/0.98  --sat_fm_lemmas                         false
% 2.05/0.98  --sat_fm_prep                           false
% 2.05/0.98  --sat_fm_uc_incr                        true
% 2.05/0.98  --sat_out_model                         small
% 2.05/0.98  --sat_out_clauses                       false
% 2.05/0.98  
% 2.05/0.98  ------ QBF Options
% 2.05/0.98  
% 2.05/0.98  --qbf_mode                              false
% 2.05/0.98  --qbf_elim_univ                         false
% 2.05/0.98  --qbf_dom_inst                          none
% 2.05/0.98  --qbf_dom_pre_inst                      false
% 2.05/0.98  --qbf_sk_in                             false
% 2.05/0.98  --qbf_pred_elim                         true
% 2.05/0.98  --qbf_split                             512
% 2.05/0.98  
% 2.05/0.98  ------ BMC1 Options
% 2.05/0.98  
% 2.05/0.98  --bmc1_incremental                      false
% 2.05/0.98  --bmc1_axioms                           reachable_all
% 2.05/0.98  --bmc1_min_bound                        0
% 2.05/0.98  --bmc1_max_bound                        -1
% 2.05/0.98  --bmc1_max_bound_default                -1
% 2.05/0.98  --bmc1_symbol_reachability              true
% 2.05/0.98  --bmc1_property_lemmas                  false
% 2.05/0.98  --bmc1_k_induction                      false
% 2.05/0.98  --bmc1_non_equiv_states                 false
% 2.05/0.98  --bmc1_deadlock                         false
% 2.05/0.98  --bmc1_ucm                              false
% 2.05/0.98  --bmc1_add_unsat_core                   none
% 2.05/0.98  --bmc1_unsat_core_children              false
% 2.05/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.05/0.98  --bmc1_out_stat                         full
% 2.05/0.98  --bmc1_ground_init                      false
% 2.05/0.98  --bmc1_pre_inst_next_state              false
% 2.05/0.98  --bmc1_pre_inst_state                   false
% 2.05/0.98  --bmc1_pre_inst_reach_state             false
% 2.05/0.98  --bmc1_out_unsat_core                   false
% 2.05/0.98  --bmc1_aig_witness_out                  false
% 2.05/0.98  --bmc1_verbose                          false
% 2.05/0.98  --bmc1_dump_clauses_tptp                false
% 2.05/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.05/0.98  --bmc1_dump_file                        -
% 2.05/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.05/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.05/0.98  --bmc1_ucm_extend_mode                  1
% 2.05/0.98  --bmc1_ucm_init_mode                    2
% 2.05/0.98  --bmc1_ucm_cone_mode                    none
% 2.05/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.05/0.98  --bmc1_ucm_relax_model                  4
% 2.05/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.05/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.05/0.98  --bmc1_ucm_layered_model                none
% 2.05/0.98  --bmc1_ucm_max_lemma_size               10
% 2.05/0.98  
% 2.05/0.98  ------ AIG Options
% 2.05/0.98  
% 2.05/0.98  --aig_mode                              false
% 2.05/0.98  
% 2.05/0.98  ------ Instantiation Options
% 2.05/0.98  
% 2.05/0.98  --instantiation_flag                    true
% 2.05/0.98  --inst_sos_flag                         false
% 2.05/0.98  --inst_sos_phase                        true
% 2.05/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.05/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.05/0.98  --inst_lit_sel_side                     none
% 2.05/0.98  --inst_solver_per_active                1400
% 2.05/0.98  --inst_solver_calls_frac                1.
% 2.05/0.98  --inst_passive_queue_type               priority_queues
% 2.05/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.05/0.98  --inst_passive_queues_freq              [25;2]
% 2.05/0.98  --inst_dismatching                      true
% 2.05/0.98  --inst_eager_unprocessed_to_passive     true
% 2.05/0.98  --inst_prop_sim_given                   true
% 2.05/0.98  --inst_prop_sim_new                     false
% 2.05/0.98  --inst_subs_new                         false
% 2.05/0.98  --inst_eq_res_simp                      false
% 2.05/0.98  --inst_subs_given                       false
% 2.05/0.98  --inst_orphan_elimination               true
% 2.05/0.98  --inst_learning_loop_flag               true
% 2.05/0.98  --inst_learning_start                   3000
% 2.05/0.98  --inst_learning_factor                  2
% 2.05/0.98  --inst_start_prop_sim_after_learn       3
% 2.05/0.98  --inst_sel_renew                        solver
% 2.05/0.98  --inst_lit_activity_flag                true
% 2.05/0.98  --inst_restr_to_given                   false
% 2.05/0.98  --inst_activity_threshold               500
% 2.05/0.98  --inst_out_proof                        true
% 2.05/0.98  
% 2.05/0.98  ------ Resolution Options
% 2.05/0.98  
% 2.05/0.98  --resolution_flag                       false
% 2.05/0.98  --res_lit_sel                           adaptive
% 2.05/0.98  --res_lit_sel_side                      none
% 2.05/0.98  --res_ordering                          kbo
% 2.05/0.98  --res_to_prop_solver                    active
% 2.05/0.98  --res_prop_simpl_new                    false
% 2.05/0.98  --res_prop_simpl_given                  true
% 2.05/0.98  --res_passive_queue_type                priority_queues
% 2.05/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.05/0.98  --res_passive_queues_freq               [15;5]
% 2.05/0.98  --res_forward_subs                      full
% 2.05/0.98  --res_backward_subs                     full
% 2.05/0.98  --res_forward_subs_resolution           true
% 2.05/0.98  --res_backward_subs_resolution          true
% 2.05/0.98  --res_orphan_elimination                true
% 2.05/0.98  --res_time_limit                        2.
% 2.05/0.98  --res_out_proof                         true
% 2.05/0.98  
% 2.05/0.98  ------ Superposition Options
% 2.05/0.98  
% 2.05/0.98  --superposition_flag                    true
% 2.05/0.98  --sup_passive_queue_type                priority_queues
% 2.05/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.05/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.05/0.98  --demod_completeness_check              fast
% 2.05/0.98  --demod_use_ground                      true
% 2.05/0.98  --sup_to_prop_solver                    passive
% 2.05/0.98  --sup_prop_simpl_new                    true
% 2.05/0.98  --sup_prop_simpl_given                  true
% 2.05/0.98  --sup_fun_splitting                     false
% 2.05/0.98  --sup_smt_interval                      50000
% 2.05/0.98  
% 2.05/0.98  ------ Superposition Simplification Setup
% 2.05/0.98  
% 2.05/0.98  --sup_indices_passive                   []
% 2.05/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.05/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.05/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.05/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.05/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.05/0.98  --sup_full_bw                           [BwDemod]
% 2.05/0.98  --sup_immed_triv                        [TrivRules]
% 2.05/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.05/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.05/0.98  --sup_immed_bw_main                     []
% 2.05/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.05/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.05/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.05/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.05/0.98  
% 2.05/0.98  ------ Combination Options
% 2.05/0.98  
% 2.05/0.98  --comb_res_mult                         3
% 2.05/0.98  --comb_sup_mult                         2
% 2.05/0.98  --comb_inst_mult                        10
% 2.05/0.98  
% 2.05/0.98  ------ Debug Options
% 2.05/0.98  
% 2.05/0.98  --dbg_backtrace                         false
% 2.05/0.98  --dbg_dump_prop_clauses                 false
% 2.05/0.98  --dbg_dump_prop_clauses_file            -
% 2.05/0.98  --dbg_out_stat                          false
% 2.05/0.98  
% 2.05/0.98  
% 2.05/0.98  
% 2.05/0.98  
% 2.05/0.98  ------ Proving...
% 2.05/0.98  
% 2.05/0.98  
% 2.05/0.98  % SZS status Theorem for theBenchmark.p
% 2.05/0.98  
% 2.05/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.05/0.98  
% 2.05/0.98  fof(f7,conjecture,(
% 2.05/0.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0)))),
% 2.05/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.05/0.98  
% 2.05/0.98  fof(f8,negated_conjecture,(
% 2.05/0.98    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0)))),
% 2.05/0.98    inference(negated_conjecture,[],[f7])).
% 2.05/0.98  
% 2.05/0.98  fof(f19,plain,(
% 2.05/0.98    ? [X0,X1] : (((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) != X0 | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) != X0) & (r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 2.05/0.98    inference(ennf_transformation,[],[f8])).
% 2.05/0.98  
% 2.05/0.98  fof(f20,plain,(
% 2.05/0.98    ? [X0,X1] : ((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) != X0 | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) != X0) & r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 2.05/0.98    inference(flattening,[],[f19])).
% 2.05/0.98  
% 2.05/0.98  fof(f31,plain,(
% 2.05/0.98    ? [X0,X1] : ((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) != X0 | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) != X0) & r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => ((k1_funct_1(k5_relat_1(sK4,k2_funct_1(sK4)),sK3) != sK3 | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK3)) != sK3) & r2_hidden(sK3,k1_relat_1(sK4)) & v2_funct_1(sK4) & v1_funct_1(sK4) & v1_relat_1(sK4))),
% 2.05/0.98    introduced(choice_axiom,[])).
% 2.05/0.98  
% 2.05/0.98  fof(f32,plain,(
% 2.05/0.98    (k1_funct_1(k5_relat_1(sK4,k2_funct_1(sK4)),sK3) != sK3 | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK3)) != sK3) & r2_hidden(sK3,k1_relat_1(sK4)) & v2_funct_1(sK4) & v1_funct_1(sK4) & v1_relat_1(sK4)),
% 2.05/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f20,f31])).
% 2.05/0.98  
% 2.05/0.98  fof(f51,plain,(
% 2.05/0.98    v1_relat_1(sK4)),
% 2.05/0.98    inference(cnf_transformation,[],[f32])).
% 2.05/0.98  
% 2.05/0.98  fof(f2,axiom,(
% 2.05/0.98    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 2.05/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.05/0.98  
% 2.05/0.98  fof(f11,plain,(
% 2.05/0.98    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 2.05/0.98    inference(ennf_transformation,[],[f2])).
% 2.05/0.98  
% 2.05/0.98  fof(f34,plain,(
% 2.05/0.98    ( ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 2.05/0.98    inference(cnf_transformation,[],[f11])).
% 2.05/0.98  
% 2.05/0.98  fof(f3,axiom,(
% 2.05/0.98    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)))),
% 2.05/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.05/0.98  
% 2.05/0.98  fof(f12,plain,(
% 2.05/0.98    ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.05/0.98    inference(ennf_transformation,[],[f3])).
% 2.05/0.98  
% 2.05/0.98  fof(f35,plain,(
% 2.05/0.98    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.05/0.98    inference(cnf_transformation,[],[f12])).
% 2.05/0.98  
% 2.05/0.98  fof(f6,axiom,(
% 2.05/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) => (k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0)))) & ((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) => (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) & k2_relat_1(X0) = k1_relat_1(X1))))))),
% 2.05/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.05/0.98  
% 2.05/0.98  fof(f17,plain,(
% 2.05/0.98    ! [X0] : ((! [X1] : ((k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | (k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))))) & k2_relat_1(X0) = k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.05/0.98    inference(ennf_transformation,[],[f6])).
% 2.05/0.98  
% 2.05/0.98  fof(f18,plain,(
% 2.05/0.98    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0)))) & k2_relat_1(X0) = k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.05/0.98    inference(flattening,[],[f17])).
% 2.05/0.98  
% 2.05/0.98  fof(f21,plain,(
% 2.05/0.98    ! [X2,X3,X0,X1] : (sP0(X2,X3,X0,X1) <=> ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))))),
% 2.05/0.98    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.05/0.98  
% 2.05/0.98  fof(f22,plain,(
% 2.05/0.98    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & sP0(X2,X3,X0,X1)) & k2_relat_1(X0) = k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.05/0.98    inference(definition_folding,[],[f18,f21])).
% 2.05/0.98  
% 2.05/0.98  fof(f26,plain,(
% 2.05/0.98    ! [X0] : (! [X1] : (((k2_funct_1(X0) = X1 | (? [X2,X3] : (((k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))) & k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X2,X3,X0,X1)) | k2_relat_1(X0) != k1_relat_1(X1))) & ((! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & sP0(X2,X3,X0,X1)) & k2_relat_1(X0) = k1_relat_1(X1)) | k2_funct_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.05/0.98    inference(nnf_transformation,[],[f22])).
% 2.05/0.98  
% 2.05/0.98  fof(f27,plain,(
% 2.05/0.98    ! [X0] : (! [X1] : (((k2_funct_1(X0) = X1 | ? [X2,X3] : (((k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))) & k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X2,X3,X0,X1)) | k2_relat_1(X0) != k1_relat_1(X1)) & ((! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & sP0(X2,X3,X0,X1)) & k2_relat_1(X0) = k1_relat_1(X1)) | k2_funct_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.05/0.98    inference(flattening,[],[f26])).
% 2.05/0.98  
% 2.05/0.98  fof(f28,plain,(
% 2.05/0.98    ! [X0] : (! [X1] : (((k2_funct_1(X0) = X1 | ? [X2,X3] : (((k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))) & k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X2,X3,X0,X1)) | k2_relat_1(X0) != k1_relat_1(X1)) & ((! [X4,X5] : (((k1_funct_1(X1,X4) = X5 & r2_hidden(X4,k2_relat_1(X0))) | k1_funct_1(X0,X5) != X4 | ~r2_hidden(X5,k1_relat_1(X0))) & sP0(X4,X5,X0,X1)) & k2_relat_1(X0) = k1_relat_1(X1)) | k2_funct_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.05/0.98    inference(rectify,[],[f27])).
% 2.05/0.98  
% 2.05/0.98  fof(f29,plain,(
% 2.05/0.98    ! [X1,X0] : (? [X2,X3] : (((k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))) & k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X2,X3,X0,X1)) => (((k1_funct_1(X1,sK1(X0,X1)) != sK2(X0,X1) | ~r2_hidden(sK1(X0,X1),k2_relat_1(X0))) & k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))) | ~sP0(sK1(X0,X1),sK2(X0,X1),X0,X1)))),
% 2.05/0.98    introduced(choice_axiom,[])).
% 2.05/0.98  
% 2.05/0.98  fof(f30,plain,(
% 2.05/0.98    ! [X0] : (! [X1] : (((k2_funct_1(X0) = X1 | (((k1_funct_1(X1,sK1(X0,X1)) != sK2(X0,X1) | ~r2_hidden(sK1(X0,X1),k2_relat_1(X0))) & k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))) | ~sP0(sK1(X0,X1),sK2(X0,X1),X0,X1)) | k2_relat_1(X0) != k1_relat_1(X1)) & ((! [X4,X5] : (((k1_funct_1(X1,X4) = X5 & r2_hidden(X4,k2_relat_1(X0))) | k1_funct_1(X0,X5) != X4 | ~r2_hidden(X5,k1_relat_1(X0))) & sP0(X4,X5,X0,X1)) & k2_relat_1(X0) = k1_relat_1(X1)) | k2_funct_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.05/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f28,f29])).
% 2.05/0.98  
% 2.05/0.98  fof(f44,plain,(
% 2.05/0.98    ( ! [X0,X1] : (k2_relat_1(X0) = k1_relat_1(X1) | k2_funct_1(X0) != X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.05/0.98    inference(cnf_transformation,[],[f30])).
% 2.05/0.98  
% 2.05/0.98  fof(f64,plain,(
% 2.05/0.98    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(k2_funct_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.05/0.98    inference(equality_resolution,[],[f44])).
% 2.05/0.98  
% 2.05/0.98  fof(f4,axiom,(
% 2.05/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.05/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.05/0.98  
% 2.05/0.98  fof(f13,plain,(
% 2.05/0.98    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.05/0.98    inference(ennf_transformation,[],[f4])).
% 2.05/0.98  
% 2.05/0.98  fof(f14,plain,(
% 2.05/0.98    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.05/0.98    inference(flattening,[],[f13])).
% 2.05/0.98  
% 2.05/0.98  fof(f36,plain,(
% 2.05/0.98    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.05/0.98    inference(cnf_transformation,[],[f14])).
% 2.05/0.98  
% 2.05/0.98  fof(f37,plain,(
% 2.05/0.98    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.05/0.98    inference(cnf_transformation,[],[f14])).
% 2.05/0.98  
% 2.05/0.98  fof(f53,plain,(
% 2.05/0.98    v2_funct_1(sK4)),
% 2.05/0.98    inference(cnf_transformation,[],[f32])).
% 2.05/0.98  
% 2.05/0.98  fof(f52,plain,(
% 2.05/0.98    v1_funct_1(sK4)),
% 2.05/0.98    inference(cnf_transformation,[],[f32])).
% 2.05/0.98  
% 2.05/0.98  fof(f1,axiom,(
% 2.05/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 2.05/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.05/0.98  
% 2.05/0.98  fof(f9,plain,(
% 2.05/0.98    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.05/0.98    inference(ennf_transformation,[],[f1])).
% 2.05/0.98  
% 2.05/0.98  fof(f10,plain,(
% 2.05/0.98    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.05/0.98    inference(flattening,[],[f9])).
% 2.05/0.98  
% 2.05/0.98  fof(f33,plain,(
% 2.05/0.98    ( ! [X0,X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.05/0.98    inference(cnf_transformation,[],[f10])).
% 2.05/0.98  
% 2.05/0.98  fof(f5,axiom,(
% 2.05/0.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) => k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0))))),
% 2.05/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.05/0.98  
% 2.05/0.98  fof(f15,plain,(
% 2.05/0.98    ! [X0,X1] : (! [X2] : ((k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.05/0.98    inference(ennf_transformation,[],[f5])).
% 2.05/0.98  
% 2.05/0.98  fof(f16,plain,(
% 2.05/0.98    ! [X0,X1] : (! [X2] : (k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.05/0.98    inference(flattening,[],[f15])).
% 2.05/0.98  
% 2.05/0.98  fof(f38,plain,(
% 2.05/0.98    ( ! [X2,X0,X1] : (k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.05/0.98    inference(cnf_transformation,[],[f16])).
% 2.05/0.98  
% 2.05/0.98  fof(f47,plain,(
% 2.05/0.98    ( ! [X4,X0,X5,X1] : (k1_funct_1(X1,X4) = X5 | k1_funct_1(X0,X5) != X4 | ~r2_hidden(X5,k1_relat_1(X0)) | k2_funct_1(X0) != X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.05/0.98    inference(cnf_transformation,[],[f30])).
% 2.05/0.98  
% 2.05/0.98  fof(f59,plain,(
% 2.05/0.98    ( ! [X0,X5,X1] : (k1_funct_1(X1,k1_funct_1(X0,X5)) = X5 | ~r2_hidden(X5,k1_relat_1(X0)) | k2_funct_1(X0) != X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.05/0.98    inference(equality_resolution,[],[f47])).
% 2.05/0.98  
% 2.05/0.98  fof(f60,plain,(
% 2.05/0.98    ( ! [X0,X5] : (k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X5)) = X5 | ~r2_hidden(X5,k1_relat_1(X0)) | ~v1_funct_1(k2_funct_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.05/0.98    inference(equality_resolution,[],[f59])).
% 2.05/0.98  
% 2.05/0.98  fof(f55,plain,(
% 2.05/0.98    k1_funct_1(k5_relat_1(sK4,k2_funct_1(sK4)),sK3) != sK3 | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK3)) != sK3),
% 2.05/0.98    inference(cnf_transformation,[],[f32])).
% 2.05/0.98  
% 2.05/0.98  fof(f54,plain,(
% 2.05/0.98    r2_hidden(sK3,k1_relat_1(sK4))),
% 2.05/0.98    inference(cnf_transformation,[],[f32])).
% 2.05/0.98  
% 2.05/0.98  cnf(c_22,negated_conjecture,
% 2.05/0.98      ( v1_relat_1(sK4) ),
% 2.05/0.98      inference(cnf_transformation,[],[f51]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_1130,negated_conjecture,
% 2.05/0.98      ( v1_relat_1(sK4) ),
% 2.05/0.98      inference(subtyping,[status(esa)],[c_22]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_1586,plain,
% 2.05/0.98      ( v1_relat_1(sK4) = iProver_top ),
% 2.05/0.98      inference(predicate_to_equality,[status(thm)],[c_1130]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_1,plain,
% 2.05/0.98      ( ~ v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0 ),
% 2.05/0.98      inference(cnf_transformation,[],[f34]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_1143,plain,
% 2.05/0.98      ( ~ v1_relat_1(X0_45)
% 2.05/0.98      | k7_relat_1(X0_45,k1_relat_1(X0_45)) = X0_45 ),
% 2.05/0.98      inference(subtyping,[status(esa)],[c_1]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_1574,plain,
% 2.05/0.98      ( k7_relat_1(X0_45,k1_relat_1(X0_45)) = X0_45
% 2.05/0.98      | v1_relat_1(X0_45) != iProver_top ),
% 2.05/0.98      inference(predicate_to_equality,[status(thm)],[c_1143]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_1904,plain,
% 2.05/0.98      ( k7_relat_1(sK4,k1_relat_1(sK4)) = sK4 ),
% 2.05/0.98      inference(superposition,[status(thm)],[c_1586,c_1574]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_2,plain,
% 2.05/0.98      ( r1_tarski(k2_relat_1(k7_relat_1(X0,X1)),k2_relat_1(X0))
% 2.05/0.98      | ~ v1_relat_1(X0) ),
% 2.05/0.98      inference(cnf_transformation,[],[f35]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_1142,plain,
% 2.05/0.98      ( r1_tarski(k2_relat_1(k7_relat_1(X0_45,X0_46)),k2_relat_1(X0_45))
% 2.05/0.98      | ~ v1_relat_1(X0_45) ),
% 2.05/0.98      inference(subtyping,[status(esa)],[c_2]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_1575,plain,
% 2.05/0.98      ( r1_tarski(k2_relat_1(k7_relat_1(X0_45,X0_46)),k2_relat_1(X0_45)) = iProver_top
% 2.05/0.98      | v1_relat_1(X0_45) != iProver_top ),
% 2.05/0.98      inference(predicate_to_equality,[status(thm)],[c_1142]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_2010,plain,
% 2.05/0.98      ( r1_tarski(k2_relat_1(sK4),k2_relat_1(sK4)) = iProver_top
% 2.05/0.98      | v1_relat_1(sK4) != iProver_top ),
% 2.05/0.98      inference(superposition,[status(thm)],[c_1904,c_1575]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_23,plain,
% 2.05/0.98      ( v1_relat_1(sK4) = iProver_top ),
% 2.05/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_2593,plain,
% 2.05/0.98      ( r1_tarski(k2_relat_1(sK4),k2_relat_1(sK4)) = iProver_top ),
% 2.05/0.98      inference(global_propositional_subsumption,
% 2.05/0.98                [status(thm)],
% 2.05/0.98                [c_2010,c_23]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_17,plain,
% 2.05/0.98      ( ~ v2_funct_1(X0)
% 2.05/0.98      | ~ v1_funct_1(X0)
% 2.05/0.98      | ~ v1_funct_1(k2_funct_1(X0))
% 2.05/0.98      | ~ v1_relat_1(X0)
% 2.05/0.98      | ~ v1_relat_1(k2_funct_1(X0))
% 2.05/0.98      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 2.05/0.98      inference(cnf_transformation,[],[f64]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_4,plain,
% 2.05/0.98      ( ~ v1_funct_1(X0)
% 2.05/0.98      | ~ v1_relat_1(X0)
% 2.05/0.98      | v1_relat_1(k2_funct_1(X0)) ),
% 2.05/0.98      inference(cnf_transformation,[],[f36]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_3,plain,
% 2.05/0.98      ( ~ v1_funct_1(X0)
% 2.05/0.98      | v1_funct_1(k2_funct_1(X0))
% 2.05/0.98      | ~ v1_relat_1(X0) ),
% 2.05/0.98      inference(cnf_transformation,[],[f37]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_130,plain,
% 2.05/0.98      ( ~ v1_relat_1(X0)
% 2.05/0.98      | ~ v2_funct_1(X0)
% 2.05/0.98      | ~ v1_funct_1(X0)
% 2.05/0.98      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 2.05/0.98      inference(global_propositional_subsumption,
% 2.05/0.98                [status(thm)],
% 2.05/0.98                [c_17,c_4,c_3]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_131,plain,
% 2.05/0.98      ( ~ v2_funct_1(X0)
% 2.05/0.98      | ~ v1_funct_1(X0)
% 2.05/0.98      | ~ v1_relat_1(X0)
% 2.05/0.98      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 2.05/0.98      inference(renaming,[status(thm)],[c_130]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_20,negated_conjecture,
% 2.05/0.98      ( v2_funct_1(sK4) ),
% 2.05/0.98      inference(cnf_transformation,[],[f53]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_290,plain,
% 2.05/0.98      ( ~ v1_funct_1(X0)
% 2.05/0.98      | ~ v1_relat_1(X0)
% 2.05/0.98      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 2.05/0.98      | sK4 != X0 ),
% 2.05/0.98      inference(resolution_lifted,[status(thm)],[c_131,c_20]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_291,plain,
% 2.05/0.98      ( ~ v1_funct_1(sK4)
% 2.05/0.98      | ~ v1_relat_1(sK4)
% 2.05/0.98      | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
% 2.05/0.98      inference(unflattening,[status(thm)],[c_290]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_21,negated_conjecture,
% 2.05/0.98      ( v1_funct_1(sK4) ),
% 2.05/0.98      inference(cnf_transformation,[],[f52]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_28,plain,
% 2.05/0.98      ( ~ v2_funct_1(sK4)
% 2.05/0.98      | ~ v1_funct_1(k2_funct_1(sK4))
% 2.05/0.98      | ~ v1_funct_1(sK4)
% 2.05/0.98      | ~ v1_relat_1(k2_funct_1(sK4))
% 2.05/0.98      | ~ v1_relat_1(sK4)
% 2.05/0.98      | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
% 2.05/0.98      inference(instantiation,[status(thm)],[c_17]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_67,plain,
% 2.05/0.98      ( ~ v1_funct_1(sK4)
% 2.05/0.98      | v1_relat_1(k2_funct_1(sK4))
% 2.05/0.98      | ~ v1_relat_1(sK4) ),
% 2.05/0.98      inference(instantiation,[status(thm)],[c_4]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_70,plain,
% 2.05/0.98      ( v1_funct_1(k2_funct_1(sK4))
% 2.05/0.98      | ~ v1_funct_1(sK4)
% 2.05/0.98      | ~ v1_relat_1(sK4) ),
% 2.05/0.98      inference(instantiation,[status(thm)],[c_3]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_293,plain,
% 2.05/0.98      ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
% 2.05/0.98      inference(global_propositional_subsumption,
% 2.05/0.98                [status(thm)],
% 2.05/0.98                [c_291,c_22,c_21,c_20,c_28,c_67,c_70]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_1129,plain,
% 2.05/0.98      ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
% 2.05/0.98      inference(subtyping,[status(esa)],[c_293]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_0,plain,
% 2.05/0.98      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
% 2.05/0.98      | ~ v1_relat_1(X1)
% 2.05/0.98      | ~ v1_relat_1(X0)
% 2.05/0.98      | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ),
% 2.05/0.98      inference(cnf_transformation,[],[f33]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_1144,plain,
% 2.05/0.98      ( ~ r1_tarski(k2_relat_1(X0_45),k1_relat_1(X1_45))
% 2.05/0.98      | ~ v1_relat_1(X0_45)
% 2.05/0.98      | ~ v1_relat_1(X1_45)
% 2.05/0.98      | k1_relat_1(k5_relat_1(X0_45,X1_45)) = k1_relat_1(X0_45) ),
% 2.05/0.98      inference(subtyping,[status(esa)],[c_0]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_1573,plain,
% 2.05/0.98      ( k1_relat_1(k5_relat_1(X0_45,X1_45)) = k1_relat_1(X0_45)
% 2.05/0.98      | r1_tarski(k2_relat_1(X0_45),k1_relat_1(X1_45)) != iProver_top
% 2.05/0.98      | v1_relat_1(X0_45) != iProver_top
% 2.05/0.98      | v1_relat_1(X1_45) != iProver_top ),
% 2.05/0.98      inference(predicate_to_equality,[status(thm)],[c_1144]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_1897,plain,
% 2.05/0.98      ( k1_relat_1(k5_relat_1(X0_45,k2_funct_1(sK4))) = k1_relat_1(X0_45)
% 2.05/0.98      | r1_tarski(k2_relat_1(X0_45),k2_relat_1(sK4)) != iProver_top
% 2.05/0.98      | v1_relat_1(X0_45) != iProver_top
% 2.05/0.98      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 2.05/0.98      inference(superposition,[status(thm)],[c_1129,c_1573]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_24,plain,
% 2.05/0.98      ( v1_funct_1(sK4) = iProver_top ),
% 2.05/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_66,plain,
% 2.05/0.98      ( v1_funct_1(X0) != iProver_top
% 2.05/0.98      | v1_relat_1(X0) != iProver_top
% 2.05/0.98      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 2.05/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_68,plain,
% 2.05/0.98      ( v1_funct_1(sK4) != iProver_top
% 2.05/0.98      | v1_relat_1(k2_funct_1(sK4)) = iProver_top
% 2.05/0.98      | v1_relat_1(sK4) != iProver_top ),
% 2.05/0.98      inference(instantiation,[status(thm)],[c_66]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_2070,plain,
% 2.05/0.98      ( v1_relat_1(X0_45) != iProver_top
% 2.05/0.98      | r1_tarski(k2_relat_1(X0_45),k2_relat_1(sK4)) != iProver_top
% 2.05/0.98      | k1_relat_1(k5_relat_1(X0_45,k2_funct_1(sK4))) = k1_relat_1(X0_45) ),
% 2.05/0.98      inference(global_propositional_subsumption,
% 2.05/0.98                [status(thm)],
% 2.05/0.98                [c_1897,c_23,c_24,c_68]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_2071,plain,
% 2.05/0.98      ( k1_relat_1(k5_relat_1(X0_45,k2_funct_1(sK4))) = k1_relat_1(X0_45)
% 2.05/0.98      | r1_tarski(k2_relat_1(X0_45),k2_relat_1(sK4)) != iProver_top
% 2.05/0.98      | v1_relat_1(X0_45) != iProver_top ),
% 2.05/0.98      inference(renaming,[status(thm)],[c_2070]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_2598,plain,
% 2.05/0.98      ( k1_relat_1(k5_relat_1(sK4,k2_funct_1(sK4))) = k1_relat_1(sK4)
% 2.05/0.98      | v1_relat_1(sK4) != iProver_top ),
% 2.05/0.98      inference(superposition,[status(thm)],[c_2593,c_2071]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_1899,plain,
% 2.05/0.98      ( k1_relat_1(k5_relat_1(sK4,k2_funct_1(sK4))) = k1_relat_1(sK4)
% 2.05/0.98      | r1_tarski(k2_relat_1(sK4),k2_relat_1(sK4)) != iProver_top
% 2.05/0.98      | v1_relat_1(k2_funct_1(sK4)) != iProver_top
% 2.05/0.98      | v1_relat_1(sK4) != iProver_top ),
% 2.05/0.98      inference(instantiation,[status(thm)],[c_1897]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_2601,plain,
% 2.05/0.98      ( k1_relat_1(k5_relat_1(sK4,k2_funct_1(sK4))) = k1_relat_1(sK4) ),
% 2.05/0.98      inference(global_propositional_subsumption,
% 2.05/0.98                [status(thm)],
% 2.05/0.98                [c_2598,c_23,c_24,c_68,c_1899,c_2010]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_5,plain,
% 2.05/0.98      ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X1,X2)))
% 2.05/0.98      | ~ v1_funct_1(X1)
% 2.05/0.98      | ~ v1_funct_1(X2)
% 2.05/0.98      | ~ v1_relat_1(X2)
% 2.05/0.98      | ~ v1_relat_1(X1)
% 2.05/0.98      | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ),
% 2.05/0.98      inference(cnf_transformation,[],[f38]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_1139,plain,
% 2.05/0.98      ( ~ r2_hidden(X0_44,k1_relat_1(k5_relat_1(X0_45,X1_45)))
% 2.05/0.98      | ~ v1_funct_1(X0_45)
% 2.05/0.98      | ~ v1_funct_1(X1_45)
% 2.05/0.98      | ~ v1_relat_1(X0_45)
% 2.05/0.98      | ~ v1_relat_1(X1_45)
% 2.05/0.98      | k1_funct_1(k5_relat_1(X0_45,X1_45),X0_44) = k1_funct_1(X1_45,k1_funct_1(X0_45,X0_44)) ),
% 2.05/0.98      inference(subtyping,[status(esa)],[c_5]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_1578,plain,
% 2.05/0.98      ( k1_funct_1(k5_relat_1(X0_45,X1_45),X0_44) = k1_funct_1(X1_45,k1_funct_1(X0_45,X0_44))
% 2.05/0.98      | r2_hidden(X0_44,k1_relat_1(k5_relat_1(X0_45,X1_45))) != iProver_top
% 2.05/0.98      | v1_funct_1(X0_45) != iProver_top
% 2.05/0.98      | v1_funct_1(X1_45) != iProver_top
% 2.05/0.98      | v1_relat_1(X0_45) != iProver_top
% 2.05/0.98      | v1_relat_1(X1_45) != iProver_top ),
% 2.05/0.98      inference(predicate_to_equality,[status(thm)],[c_1139]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_2929,plain,
% 2.05/0.98      ( k1_funct_1(k5_relat_1(sK4,k2_funct_1(sK4)),X0_44) = k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0_44))
% 2.05/0.98      | r2_hidden(X0_44,k1_relat_1(sK4)) != iProver_top
% 2.05/0.98      | v1_funct_1(k2_funct_1(sK4)) != iProver_top
% 2.05/0.98      | v1_funct_1(sK4) != iProver_top
% 2.05/0.98      | v1_relat_1(k2_funct_1(sK4)) != iProver_top
% 2.05/0.98      | v1_relat_1(sK4) != iProver_top ),
% 2.05/0.98      inference(superposition,[status(thm)],[c_2601,c_1578]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_2931,plain,
% 2.05/0.98      ( k1_funct_1(k5_relat_1(sK4,k2_funct_1(sK4)),sK3) = k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK3))
% 2.05/0.98      | r2_hidden(sK3,k1_relat_1(sK4)) != iProver_top
% 2.05/0.98      | v1_funct_1(k2_funct_1(sK4)) != iProver_top
% 2.05/0.98      | v1_funct_1(sK4) != iProver_top
% 2.05/0.98      | v1_relat_1(k2_funct_1(sK4)) != iProver_top
% 2.05/0.98      | v1_relat_1(sK4) != iProver_top ),
% 2.05/0.98      inference(instantiation,[status(thm)],[c_2929]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_1149,plain,
% 2.05/0.98      ( X0_44 != X1_44 | X2_44 != X1_44 | X2_44 = X0_44 ),
% 2.05/0.98      theory(equality) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_1770,plain,
% 2.05/0.98      ( k1_funct_1(k5_relat_1(sK4,k2_funct_1(sK4)),sK3) != X0_44
% 2.05/0.98      | k1_funct_1(k5_relat_1(sK4,k2_funct_1(sK4)),sK3) = sK3
% 2.05/0.98      | sK3 != X0_44 ),
% 2.05/0.98      inference(instantiation,[status(thm)],[c_1149]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_1812,plain,
% 2.05/0.98      ( k1_funct_1(k5_relat_1(sK4,k2_funct_1(sK4)),sK3) != k1_funct_1(X0_45,X0_44)
% 2.05/0.98      | k1_funct_1(k5_relat_1(sK4,k2_funct_1(sK4)),sK3) = sK3
% 2.05/0.98      | sK3 != k1_funct_1(X0_45,X0_44) ),
% 2.05/0.98      inference(instantiation,[status(thm)],[c_1770]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_2198,plain,
% 2.05/0.98      ( k1_funct_1(k5_relat_1(sK4,k2_funct_1(sK4)),sK3) != k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0_44))
% 2.05/0.98      | k1_funct_1(k5_relat_1(sK4,k2_funct_1(sK4)),sK3) = sK3
% 2.05/0.98      | sK3 != k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0_44)) ),
% 2.05/0.98      inference(instantiation,[status(thm)],[c_1812]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_2199,plain,
% 2.05/0.98      ( k1_funct_1(k5_relat_1(sK4,k2_funct_1(sK4)),sK3) != k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK3))
% 2.05/0.98      | k1_funct_1(k5_relat_1(sK4,k2_funct_1(sK4)),sK3) = sK3
% 2.05/0.98      | sK3 != k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK3)) ),
% 2.05/0.98      inference(instantiation,[status(thm)],[c_2198]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_1927,plain,
% 2.05/0.98      ( k1_funct_1(X0_45,X0_44) != X1_44
% 2.05/0.98      | sK3 != X1_44
% 2.05/0.98      | sK3 = k1_funct_1(X0_45,X0_44) ),
% 2.05/0.98      inference(instantiation,[status(thm)],[c_1149]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_2123,plain,
% 2.05/0.98      ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0_44)) != X0_44
% 2.05/0.98      | sK3 != X0_44
% 2.05/0.98      | sK3 = k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0_44)) ),
% 2.05/0.98      inference(instantiation,[status(thm)],[c_1927]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_2124,plain,
% 2.05/0.98      ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK3)) != sK3
% 2.05/0.98      | sK3 = k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK3))
% 2.05/0.98      | sK3 != sK3 ),
% 2.05/0.98      inference(instantiation,[status(thm)],[c_2123]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_14,plain,
% 2.05/0.98      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.05/0.98      | ~ v2_funct_1(X1)
% 2.05/0.98      | ~ v1_funct_1(X1)
% 2.05/0.98      | ~ v1_funct_1(k2_funct_1(X1))
% 2.05/0.98      | ~ v1_relat_1(X1)
% 2.05/0.98      | ~ v1_relat_1(k2_funct_1(X1))
% 2.05/0.98      | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ),
% 2.05/0.98      inference(cnf_transformation,[],[f60]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_403,plain,
% 2.05/0.98      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.05/0.98      | ~ v1_funct_1(X1)
% 2.05/0.98      | ~ v1_funct_1(k2_funct_1(X1))
% 2.05/0.98      | ~ v1_relat_1(X1)
% 2.05/0.98      | ~ v1_relat_1(k2_funct_1(X1))
% 2.05/0.98      | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0
% 2.05/0.98      | sK4 != X1 ),
% 2.05/0.98      inference(resolution_lifted,[status(thm)],[c_14,c_20]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_404,plain,
% 2.05/0.98      ( ~ r2_hidden(X0,k1_relat_1(sK4))
% 2.05/0.98      | ~ v1_funct_1(k2_funct_1(sK4))
% 2.05/0.98      | ~ v1_funct_1(sK4)
% 2.05/0.98      | ~ v1_relat_1(k2_funct_1(sK4))
% 2.05/0.98      | ~ v1_relat_1(sK4)
% 2.05/0.98      | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0)) = X0 ),
% 2.05/0.98      inference(unflattening,[status(thm)],[c_403]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_408,plain,
% 2.05/0.98      ( ~ r2_hidden(X0,k1_relat_1(sK4))
% 2.05/0.98      | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0)) = X0 ),
% 2.05/0.98      inference(global_propositional_subsumption,
% 2.05/0.98                [status(thm)],
% 2.05/0.98                [c_404,c_22,c_21,c_67,c_70]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_1124,plain,
% 2.05/0.98      ( ~ r2_hidden(X0_44,k1_relat_1(sK4))
% 2.05/0.98      | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0_44)) = X0_44 ),
% 2.05/0.98      inference(subtyping,[status(esa)],[c_408]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_1227,plain,
% 2.05/0.98      ( ~ r2_hidden(sK3,k1_relat_1(sK4))
% 2.05/0.98      | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK3)) = sK3 ),
% 2.05/0.98      inference(instantiation,[status(thm)],[c_1124]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_18,negated_conjecture,
% 2.05/0.98      ( k1_funct_1(k5_relat_1(sK4,k2_funct_1(sK4)),sK3) != sK3
% 2.05/0.98      | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK3)) != sK3 ),
% 2.05/0.98      inference(cnf_transformation,[],[f55]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_1133,negated_conjecture,
% 2.05/0.98      ( k1_funct_1(k5_relat_1(sK4,k2_funct_1(sK4)),sK3) != sK3
% 2.05/0.98      | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK3)) != sK3 ),
% 2.05/0.98      inference(subtyping,[status(esa)],[c_18]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_1146,plain,( X0_44 = X0_44 ),theory(equality) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_1179,plain,
% 2.05/0.98      ( sK3 = sK3 ),
% 2.05/0.98      inference(instantiation,[status(thm)],[c_1146]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_69,plain,
% 2.05/0.98      ( v1_funct_1(X0) != iProver_top
% 2.05/0.98      | v1_funct_1(k2_funct_1(X0)) = iProver_top
% 2.05/0.98      | v1_relat_1(X0) != iProver_top ),
% 2.05/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_71,plain,
% 2.05/0.98      ( v1_funct_1(k2_funct_1(sK4)) = iProver_top
% 2.05/0.98      | v1_funct_1(sK4) != iProver_top
% 2.05/0.98      | v1_relat_1(sK4) != iProver_top ),
% 2.05/0.98      inference(instantiation,[status(thm)],[c_69]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_19,negated_conjecture,
% 2.05/0.98      ( r2_hidden(sK3,k1_relat_1(sK4)) ),
% 2.05/0.98      inference(cnf_transformation,[],[f54]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_26,plain,
% 2.05/0.98      ( r2_hidden(sK3,k1_relat_1(sK4)) = iProver_top ),
% 2.05/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(contradiction,plain,
% 2.05/0.98      ( $false ),
% 2.05/0.98      inference(minisat,
% 2.05/0.98                [status(thm)],
% 2.05/0.98                [c_2931,c_2199,c_2124,c_1227,c_1133,c_1179,c_71,c_68,
% 2.05/0.98                 c_26,c_19,c_24,c_23]) ).
% 2.05/0.98  
% 2.05/0.98  
% 2.05/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.05/0.98  
% 2.05/0.98  ------                               Statistics
% 2.05/0.98  
% 2.05/0.98  ------ General
% 2.05/0.98  
% 2.05/0.98  abstr_ref_over_cycles:                  0
% 2.05/0.98  abstr_ref_under_cycles:                 0
% 2.05/0.98  gc_basic_clause_elim:                   0
% 2.05/0.98  forced_gc_time:                         0
% 2.05/0.98  parsing_time:                           0.006
% 2.05/0.98  unif_index_cands_time:                  0.
% 2.05/0.98  unif_index_add_time:                    0.
% 2.05/0.98  orderings_time:                         0.
% 2.05/0.98  out_proof_time:                         0.011
% 2.05/0.98  total_time:                             0.145
% 2.05/0.98  num_of_symbols:                         50
% 2.05/0.98  num_of_terms:                           2709
% 2.05/0.98  
% 2.05/0.98  ------ Preprocessing
% 2.05/0.98  
% 2.05/0.98  num_of_splits:                          0
% 2.05/0.98  num_of_split_atoms:                     0
% 2.05/0.98  num_of_reused_defs:                     0
% 2.05/0.98  num_eq_ax_congr_red:                    12
% 2.05/0.98  num_of_sem_filtered_clauses:            1
% 2.05/0.98  num_of_subtypes:                        3
% 2.05/0.98  monotx_restored_types:                  1
% 2.05/0.98  sat_num_of_epr_types:                   0
% 2.05/0.98  sat_num_of_non_cyclic_types:            0
% 2.05/0.98  sat_guarded_non_collapsed_types:        1
% 2.05/0.98  num_pure_diseq_elim:                    0
% 2.05/0.98  simp_replaced_by:                       0
% 2.05/0.98  res_preprocessed:                       128
% 2.05/0.98  prep_upred:                             0
% 2.05/0.98  prep_unflattend:                        151
% 2.05/0.98  smt_new_axioms:                         0
% 2.05/0.98  pred_elim_cands:                        5
% 2.05/0.98  pred_elim:                              1
% 2.05/0.98  pred_elim_cl:                           1
% 2.05/0.98  pred_elim_cycles:                       5
% 2.05/0.98  merged_defs:                            0
% 2.05/0.98  merged_defs_ncl:                        0
% 2.05/0.98  bin_hyper_res:                          0
% 2.05/0.98  prep_cycles:                            4
% 2.05/0.98  pred_elim_time:                         0.03
% 2.05/0.98  splitting_time:                         0.
% 2.05/0.98  sem_filter_time:                        0.
% 2.05/0.98  monotx_time:                            0.001
% 2.05/0.98  subtype_inf_time:                       0.001
% 2.05/0.98  
% 2.05/0.98  ------ Problem properties
% 2.05/0.98  
% 2.05/0.98  clauses:                                22
% 2.05/0.98  conjectures:                            4
% 2.05/0.98  epr:                                    2
% 2.05/0.98  horn:                                   18
% 2.05/0.98  ground:                                 5
% 2.05/0.98  unary:                                  5
% 2.05/0.98  binary:                                 8
% 2.05/0.98  lits:                                   62
% 2.05/0.98  lits_eq:                                17
% 2.05/0.98  fd_pure:                                0
% 2.05/0.98  fd_pseudo:                              0
% 2.05/0.98  fd_cond:                                3
% 2.05/0.98  fd_pseudo_cond:                         1
% 2.05/0.98  ac_symbols:                             0
% 2.05/0.98  
% 2.05/0.98  ------ Propositional Solver
% 2.05/0.98  
% 2.05/0.98  prop_solver_calls:                      26
% 2.05/0.98  prop_fast_solver_calls:                 1020
% 2.05/0.98  smt_solver_calls:                       0
% 2.05/0.98  smt_fast_solver_calls:                  0
% 2.05/0.98  prop_num_of_clauses:                    735
% 2.05/0.98  prop_preprocess_simplified:             4134
% 2.05/0.98  prop_fo_subsumed:                       29
% 2.05/0.98  prop_solver_time:                       0.
% 2.05/0.98  smt_solver_time:                        0.
% 2.05/0.98  smt_fast_solver_time:                   0.
% 2.05/0.98  prop_fast_solver_time:                  0.
% 2.05/0.98  prop_unsat_core_time:                   0.
% 2.05/0.98  
% 2.05/0.98  ------ QBF
% 2.05/0.98  
% 2.05/0.98  qbf_q_res:                              0
% 2.05/0.98  qbf_num_tautologies:                    0
% 2.05/0.98  qbf_prep_cycles:                        0
% 2.05/0.98  
% 2.05/0.98  ------ BMC1
% 2.05/0.98  
% 2.05/0.98  bmc1_current_bound:                     -1
% 2.05/0.98  bmc1_last_solved_bound:                 -1
% 2.05/0.98  bmc1_unsat_core_size:                   -1
% 2.05/0.98  bmc1_unsat_core_parents_size:           -1
% 2.05/0.98  bmc1_merge_next_fun:                    0
% 2.05/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.05/0.98  
% 2.05/0.98  ------ Instantiation
% 2.05/0.98  
% 2.05/0.98  inst_num_of_clauses:                    242
% 2.05/0.98  inst_num_in_passive:                    19
% 2.05/0.98  inst_num_in_active:                     158
% 2.05/0.98  inst_num_in_unprocessed:                66
% 2.05/0.98  inst_num_of_loops:                      170
% 2.05/0.98  inst_num_of_learning_restarts:          0
% 2.05/0.98  inst_num_moves_active_passive:          9
% 2.05/0.98  inst_lit_activity:                      0
% 2.05/0.98  inst_lit_activity_moves:                0
% 2.05/0.98  inst_num_tautologies:                   0
% 2.05/0.98  inst_num_prop_implied:                  0
% 2.05/0.98  inst_num_existing_simplified:           0
% 2.05/0.98  inst_num_eq_res_simplified:             0
% 2.05/0.98  inst_num_child_elim:                    0
% 2.05/0.98  inst_num_of_dismatching_blockings:      109
% 2.05/0.98  inst_num_of_non_proper_insts:           244
% 2.05/0.98  inst_num_of_duplicates:                 0
% 2.05/0.98  inst_inst_num_from_inst_to_res:         0
% 2.05/0.98  inst_dismatching_checking_time:         0.
% 2.05/0.98  
% 2.05/0.98  ------ Resolution
% 2.05/0.98  
% 2.05/0.98  res_num_of_clauses:                     0
% 2.05/0.98  res_num_in_passive:                     0
% 2.05/0.98  res_num_in_active:                      0
% 2.05/0.98  res_num_of_loops:                       132
% 2.05/0.98  res_forward_subset_subsumed:            51
% 2.05/0.98  res_backward_subset_subsumed:           2
% 2.05/0.98  res_forward_subsumed:                   0
% 2.05/0.99  res_backward_subsumed:                  0
% 2.05/0.99  res_forward_subsumption_resolution:     0
% 2.05/0.99  res_backward_subsumption_resolution:    0
% 2.05/0.99  res_clause_to_clause_subsumption:       60
% 2.05/0.99  res_orphan_elimination:                 0
% 2.05/0.99  res_tautology_del:                      66
% 2.05/0.99  res_num_eq_res_simplified:              0
% 2.05/0.99  res_num_sel_changes:                    0
% 2.05/0.99  res_moves_from_active_to_pass:          0
% 2.05/0.99  
% 2.05/0.99  ------ Superposition
% 2.05/0.99  
% 2.05/0.99  sup_time_total:                         0.
% 2.05/0.99  sup_time_generating:                    0.
% 2.05/0.99  sup_time_sim_full:                      0.
% 2.05/0.99  sup_time_sim_immed:                     0.
% 2.05/0.99  
% 2.05/0.99  sup_num_of_clauses:                     45
% 2.05/0.99  sup_num_in_active:                      33
% 2.05/0.99  sup_num_in_passive:                     12
% 2.05/0.99  sup_num_of_loops:                       32
% 2.05/0.99  sup_fw_superposition:                   23
% 2.05/0.99  sup_bw_superposition:                   9
% 2.05/0.99  sup_immediate_simplified:               8
% 2.05/0.99  sup_given_eliminated:                   0
% 2.05/0.99  comparisons_done:                       0
% 2.05/0.99  comparisons_avoided:                    0
% 2.05/0.99  
% 2.05/0.99  ------ Simplifications
% 2.05/0.99  
% 2.05/0.99  
% 2.05/0.99  sim_fw_subset_subsumed:                 2
% 2.05/0.99  sim_bw_subset_subsumed:                 0
% 2.05/0.99  sim_fw_subsumed:                        0
% 2.05/0.99  sim_bw_subsumed:                        0
% 2.05/0.99  sim_fw_subsumption_res:                 0
% 2.05/0.99  sim_bw_subsumption_res:                 0
% 2.05/0.99  sim_tautology_del:                      2
% 2.05/0.99  sim_eq_tautology_del:                   6
% 2.05/0.99  sim_eq_res_simp:                        0
% 2.05/0.99  sim_fw_demodulated:                     0
% 2.05/0.99  sim_bw_demodulated:                     0
% 2.05/0.99  sim_light_normalised:                   6
% 2.05/0.99  sim_joinable_taut:                      0
% 2.05/0.99  sim_joinable_simp:                      0
% 2.05/0.99  sim_ac_normalised:                      0
% 2.05/0.99  sim_smt_subsumption:                    0
% 2.05/0.99  
%------------------------------------------------------------------------------
