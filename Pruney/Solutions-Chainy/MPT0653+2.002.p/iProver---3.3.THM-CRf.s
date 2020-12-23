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
% DateTime   : Thu Dec  3 11:50:40 EST 2020

% Result     : Theorem 7.32s
% Output     : CNFRefutation 7.32s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 226 expanded)
%              Number of clauses        :   86 (  96 expanded)
%              Number of leaves         :   18 (  54 expanded)
%              Depth                    :   11
%              Number of atoms          :  640 (1775 expanded)
%              Number of equality atoms :  258 ( 790 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   28 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k2_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
          & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
        & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 )
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
        & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 )
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f7,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
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
    inference(negated_conjecture,[],[f7])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f31,plain,(
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

fof(f30,plain,
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

fof(f32,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f29,f31,f30])).

fof(f55,plain,(
    ! [X2,X3] :
      ( k1_funct_1(sK3,X2) = X3
      | k1_funct_1(sK4,X3) != X2
      | ~ r2_hidden(X3,k1_relat_1(sK4))
      | ~ r2_hidden(X2,k1_relat_1(sK3)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f57,plain,(
    ! [X3] :
      ( k1_funct_1(sK3,k1_funct_1(sK4,X3)) = X3
      | ~ r2_hidden(X3,k1_relat_1(sK4))
      | ~ r2_hidden(k1_funct_1(sK4,X3),k1_relat_1(sK3)) ) ),
    inference(equality_resolution,[],[f55])).

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

fof(f9,plain,(
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

fof(f10,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
          & r2_hidden(X2,k1_relat_1(X0))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( sK0(X0) != sK1(X0)
        & k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0))
        & r2_hidden(sK1(X0),k1_relat_1(X0))
        & r2_hidden(sK0(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ( sK0(X0) != sK1(X0)
            & k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0))
            & r2_hidden(sK1(X0),k1_relat_1(X0))
            & r2_hidden(sK0(X0),k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f25])).

fof(f33,plain,(
    ! [X4,X0,X3] :
      ( X3 = X4
      | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1))
        & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ( k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1))
            & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f27])).

fof(f46,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f45,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK2(X0,X1),k1_relat_1(X0))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f52,plain,(
    k1_relat_1(sK3) = k2_relat_1(sK4) ),
    inference(cnf_transformation,[],[f32])).

fof(f53,plain,(
    k1_relat_1(sK4) = k2_relat_1(sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f56,plain,(
    k2_funct_1(sK3) != sK4 ),
    inference(cnf_transformation,[],[f32])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f41,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f42,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f12,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f39,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f38,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f51,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f50,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f32])).

fof(f49,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f32])).

fof(f48,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f47,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_856,plain,
    ( X0_44 != X1_44
    | X2_44 != X1_44
    | X2_44 = X0_44 ),
    theory(equality)).

cnf(c_12157,plain,
    ( X0_44 != X1_44
    | X0_44 = k1_funct_1(X0_42,X2_44)
    | k1_funct_1(X0_42,X2_44) != X1_44 ),
    inference(instantiation,[status(thm)],[c_856])).

cnf(c_27399,plain,
    ( X0_44 != sK2(sK4,k2_funct_1(sK3))
    | X0_44 = k1_funct_1(sK3,k1_funct_1(sK4,sK2(sK4,k2_funct_1(sK3))))
    | k1_funct_1(sK3,k1_funct_1(sK4,sK2(sK4,k2_funct_1(sK3)))) != sK2(sK4,k2_funct_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_12157])).

cnf(c_35193,plain,
    ( k1_funct_1(X0_42,k1_funct_1(k2_funct_1(X0_42),sK2(sK4,k2_funct_1(sK3)))) != sK2(sK4,k2_funct_1(sK3))
    | k1_funct_1(X0_42,k1_funct_1(k2_funct_1(X0_42),sK2(sK4,k2_funct_1(sK3)))) = k1_funct_1(sK3,k1_funct_1(sK4,sK2(sK4,k2_funct_1(sK3))))
    | k1_funct_1(sK3,k1_funct_1(sK4,sK2(sK4,k2_funct_1(sK3)))) != sK2(sK4,k2_funct_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_27399])).

cnf(c_35194,plain,
    ( k1_funct_1(sK3,k1_funct_1(k2_funct_1(sK3),sK2(sK4,k2_funct_1(sK3)))) != sK2(sK4,k2_funct_1(sK3))
    | k1_funct_1(sK3,k1_funct_1(k2_funct_1(sK3),sK2(sK4,k2_funct_1(sK3)))) = k1_funct_1(sK3,k1_funct_1(sK4,sK2(sK4,k2_funct_1(sK3))))
    | k1_funct_1(sK3,k1_funct_1(sK4,sK2(sK4,k2_funct_1(sK3)))) != sK2(sK4,k2_funct_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_35193])).

cnf(c_853,plain,
    ( X0_44 = X0_44 ),
    theory(equality)).

cnf(c_12200,plain,
    ( k1_funct_1(k2_funct_1(sK3),sK2(sK4,k2_funct_1(sK3))) = k1_funct_1(k2_funct_1(sK3),sK2(sK4,k2_funct_1(sK3))) ),
    inference(instantiation,[status(thm)],[c_853])).

cnf(c_862,plain,
    ( ~ r2_hidden(X0_44,X0_43)
    | r2_hidden(X1_44,X1_43)
    | X1_44 != X0_44
    | X1_43 != X0_43 ),
    theory(equality)).

cnf(c_1370,plain,
    ( ~ r2_hidden(X0_44,X0_43)
    | r2_hidden(X1_44,k1_relat_1(X0_42))
    | X1_44 != X0_44
    | k1_relat_1(X0_42) != X0_43 ),
    inference(instantiation,[status(thm)],[c_862])).

cnf(c_1517,plain,
    ( r2_hidden(X0_44,k1_relat_1(X0_42))
    | ~ r2_hidden(k1_funct_1(X1_42,X1_44),k2_relat_1(X1_42))
    | X0_44 != k1_funct_1(X1_42,X1_44)
    | k1_relat_1(X0_42) != k2_relat_1(X1_42) ),
    inference(instantiation,[status(thm)],[c_1370])).

cnf(c_1916,plain,
    ( r2_hidden(X0_44,k1_relat_1(sK3))
    | ~ r2_hidden(k1_funct_1(k2_funct_1(X0_42),X1_44),k2_relat_1(k2_funct_1(X0_42)))
    | X0_44 != k1_funct_1(k2_funct_1(X0_42),X1_44)
    | k1_relat_1(sK3) != k2_relat_1(k2_funct_1(X0_42)) ),
    inference(instantiation,[status(thm)],[c_1517])).

cnf(c_3069,plain,
    ( ~ r2_hidden(k1_funct_1(k2_funct_1(X0_42),X0_44),k2_relat_1(k2_funct_1(X0_42)))
    | r2_hidden(k1_funct_1(k2_funct_1(X0_42),X0_44),k1_relat_1(sK3))
    | k1_funct_1(k2_funct_1(X0_42),X0_44) != k1_funct_1(k2_funct_1(X0_42),X0_44)
    | k1_relat_1(sK3) != k2_relat_1(k2_funct_1(X0_42)) ),
    inference(instantiation,[status(thm)],[c_1916])).

cnf(c_6101,plain,
    ( ~ r2_hidden(k1_funct_1(k2_funct_1(sK3),sK2(sK4,k2_funct_1(sK3))),k2_relat_1(k2_funct_1(sK3)))
    | r2_hidden(k1_funct_1(k2_funct_1(sK3),sK2(sK4,k2_funct_1(sK3))),k1_relat_1(sK3))
    | k1_funct_1(k2_funct_1(sK3),sK2(sK4,k2_funct_1(sK3))) != k1_funct_1(k2_funct_1(sK3),sK2(sK4,k2_funct_1(sK3)))
    | k1_relat_1(sK3) != k2_relat_1(k2_funct_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_3069])).

cnf(c_1748,plain,
    ( r2_hidden(X0_44,X0_43)
    | ~ r2_hidden(sK2(sK4,k2_funct_1(sK3)),k1_relat_1(sK4))
    | X0_44 != sK2(sK4,k2_funct_1(sK3))
    | X0_43 != k1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_862])).

cnf(c_2207,plain,
    ( r2_hidden(X0_44,k2_relat_1(sK3))
    | ~ r2_hidden(sK2(sK4,k2_funct_1(sK3)),k1_relat_1(sK4))
    | X0_44 != sK2(sK4,k2_funct_1(sK3))
    | k2_relat_1(sK3) != k1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1748])).

cnf(c_3438,plain,
    ( r2_hidden(sK2(sK4,k2_funct_1(sK3)),k2_relat_1(sK3))
    | ~ r2_hidden(sK2(sK4,k2_funct_1(sK3)),k1_relat_1(sK4))
    | sK2(sK4,k2_funct_1(sK3)) != sK2(sK4,k2_funct_1(sK3))
    | k2_relat_1(sK3) != k1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2207])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_842,plain,
    ( ~ r2_hidden(X0_44,k1_relat_1(X0_42))
    | r2_hidden(k1_funct_1(X0_42,X0_44),k2_relat_1(X0_42))
    | ~ v1_relat_1(X0_42)
    | ~ v1_funct_1(X0_42) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1804,plain,
    ( ~ r2_hidden(X0_44,k1_relat_1(k2_funct_1(sK3)))
    | r2_hidden(k1_funct_1(k2_funct_1(sK3),X0_44),k2_relat_1(k2_funct_1(sK3)))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_842])).

cnf(c_2735,plain,
    ( ~ r2_hidden(sK2(sK4,k2_funct_1(sK3)),k1_relat_1(k2_funct_1(sK3)))
    | r2_hidden(k1_funct_1(k2_funct_1(sK3),sK2(sK4,k2_funct_1(sK3))),k2_relat_1(k2_funct_1(sK3)))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_1804])).

cnf(c_2724,plain,
    ( k1_funct_1(sK4,sK2(sK4,k2_funct_1(sK3))) = k1_funct_1(sK4,sK2(sK4,k2_funct_1(sK3))) ),
    inference(instantiation,[status(thm)],[c_853])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_838,plain,
    ( ~ r2_hidden(X0_44,k2_relat_1(X0_42))
    | ~ v1_relat_1(X0_42)
    | ~ v1_funct_1(X0_42)
    | ~ v2_funct_1(X0_42)
    | k1_funct_1(X0_42,k1_funct_1(k2_funct_1(X0_42),X0_44)) = X0_44 ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_2388,plain,
    ( ~ r2_hidden(sK2(sK4,k2_funct_1(sK3)),k2_relat_1(X0_42))
    | ~ v1_relat_1(X0_42)
    | ~ v1_funct_1(X0_42)
    | ~ v2_funct_1(X0_42)
    | k1_funct_1(X0_42,k1_funct_1(k2_funct_1(X0_42),sK2(sK4,k2_funct_1(sK3)))) = sK2(sK4,k2_funct_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_838])).

cnf(c_2390,plain,
    ( ~ r2_hidden(sK2(sK4,k2_funct_1(sK3)),k2_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | k1_funct_1(sK3,k1_funct_1(k2_funct_1(sK3),sK2(sK4,k2_funct_1(sK3)))) = sK2(sK4,k2_funct_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_2388])).

cnf(c_1278,plain,
    ( ~ r2_hidden(X0_44,X0_43)
    | r2_hidden(X1_44,k1_relat_1(sK3))
    | X1_44 != X0_44
    | k1_relat_1(sK3) != X0_43 ),
    inference(instantiation,[status(thm)],[c_862])).

cnf(c_1305,plain,
    ( ~ r2_hidden(X0_44,k2_relat_1(sK4))
    | r2_hidden(X1_44,k1_relat_1(sK3))
    | X1_44 != X0_44
    | k1_relat_1(sK3) != k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1278])).

cnf(c_1322,plain,
    ( r2_hidden(X0_44,k1_relat_1(sK3))
    | ~ r2_hidden(k1_funct_1(sK4,X1_44),k2_relat_1(sK4))
    | X0_44 != k1_funct_1(sK4,X1_44)
    | k1_relat_1(sK3) != k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1305])).

cnf(c_1994,plain,
    ( r2_hidden(X0_44,k1_relat_1(sK3))
    | ~ r2_hidden(k1_funct_1(sK4,sK2(sK4,k2_funct_1(sK3))),k2_relat_1(sK4))
    | X0_44 != k1_funct_1(sK4,sK2(sK4,k2_funct_1(sK3)))
    | k1_relat_1(sK3) != k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1322])).

cnf(c_2333,plain,
    ( ~ r2_hidden(k1_funct_1(sK4,sK2(sK4,k2_funct_1(sK3))),k2_relat_1(sK4))
    | r2_hidden(k1_funct_1(sK4,sK2(sK4,k2_funct_1(sK3))),k1_relat_1(sK3))
    | k1_funct_1(sK4,sK2(sK4,k2_funct_1(sK3))) != k1_funct_1(sK4,sK2(sK4,k2_funct_1(sK3)))
    | k1_relat_1(sK3) != k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1994])).

cnf(c_2074,plain,
    ( sK2(sK4,k2_funct_1(sK3)) = sK2(sK4,k2_funct_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_853])).

cnf(c_855,plain,
    ( X0_43 != X1_43
    | X2_43 != X1_43
    | X2_43 = X0_43 ),
    theory(equality)).

cnf(c_1512,plain,
    ( X0_43 != X1_43
    | X0_43 = k1_relat_1(X0_42)
    | k1_relat_1(X0_42) != X1_43 ),
    inference(instantiation,[status(thm)],[c_855])).

cnf(c_1886,plain,
    ( X0_43 != k2_relat_1(sK3)
    | X0_43 = k1_relat_1(sK4)
    | k1_relat_1(sK4) != k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1512])).

cnf(c_1973,plain,
    ( k2_relat_1(sK3) != k2_relat_1(sK3)
    | k2_relat_1(sK3) = k1_relat_1(sK4)
    | k1_relat_1(sK4) != k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1886])).

cnf(c_1448,plain,
    ( ~ r2_hidden(X0_44,k1_relat_1(sK4))
    | r2_hidden(k1_funct_1(sK4,X0_44),k2_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_842])).

cnf(c_1704,plain,
    ( ~ r2_hidden(sK2(sK4,k2_funct_1(sK3)),k1_relat_1(sK4))
    | r2_hidden(k1_funct_1(sK4,sK2(sK4,k2_funct_1(sK3))),k2_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1448])).

cnf(c_1514,plain,
    ( r2_hidden(X0_44,k1_relat_1(X0_42))
    | ~ r2_hidden(sK2(sK4,k2_funct_1(sK3)),k1_relat_1(sK4))
    | X0_44 != sK2(sK4,k2_funct_1(sK3))
    | k1_relat_1(X0_42) != k1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1370])).

cnf(c_1569,plain,
    ( r2_hidden(X0_44,k1_relat_1(k2_funct_1(sK3)))
    | ~ r2_hidden(sK2(sK4,k2_funct_1(sK3)),k1_relat_1(sK4))
    | X0_44 != sK2(sK4,k2_funct_1(sK3))
    | k1_relat_1(k2_funct_1(sK3)) != k1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1514])).

cnf(c_1696,plain,
    ( r2_hidden(sK2(sK4,k2_funct_1(sK3)),k1_relat_1(k2_funct_1(sK3)))
    | ~ r2_hidden(sK2(sK4,k2_funct_1(sK3)),k1_relat_1(sK4))
    | sK2(sK4,k2_funct_1(sK3)) != sK2(sK4,k2_funct_1(sK3))
    | k1_relat_1(k2_funct_1(sK3)) != k1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1569])).

cnf(c_15,negated_conjecture,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | ~ r2_hidden(k1_funct_1(sK4,X0),k1_relat_1(sK3))
    | k1_funct_1(sK3,k1_funct_1(sK4,X0)) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_834,negated_conjecture,
    ( ~ r2_hidden(X0_44,k1_relat_1(sK4))
    | ~ r2_hidden(k1_funct_1(sK4,X0_44),k1_relat_1(sK3))
    | k1_funct_1(sK3,k1_funct_1(sK4,X0_44)) = X0_44 ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1395,plain,
    ( ~ r2_hidden(sK2(sK4,k2_funct_1(sK3)),k1_relat_1(sK4))
    | ~ r2_hidden(k1_funct_1(sK4,sK2(sK4,k2_funct_1(sK3))),k1_relat_1(sK3))
    | k1_funct_1(sK3,k1_funct_1(sK4,sK2(sK4,k2_funct_1(sK3)))) = sK2(sK4,k2_funct_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_834])).

cnf(c_1313,plain,
    ( X0_43 != X1_43
    | k1_relat_1(sK3) != X1_43
    | k1_relat_1(sK3) = X0_43 ),
    inference(instantiation,[status(thm)],[c_855])).

cnf(c_1360,plain,
    ( X0_43 != k1_relat_1(sK3)
    | k1_relat_1(sK3) = X0_43
    | k1_relat_1(sK3) != k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1313])).

cnf(c_1390,plain,
    ( k2_relat_1(k2_funct_1(sK3)) != k1_relat_1(sK3)
    | k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3))
    | k1_relat_1(sK3) != k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1360])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | X0 = X2
    | k1_funct_1(X1,X0) != k1_funct_1(X1,X2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_845,plain,
    ( ~ r2_hidden(X0_44,k1_relat_1(X0_42))
    | ~ r2_hidden(X1_44,k1_relat_1(X0_42))
    | ~ v1_relat_1(X0_42)
    | ~ v1_funct_1(X0_42)
    | ~ v2_funct_1(X0_42)
    | X0_44 = X1_44
    | k1_funct_1(X0_42,X0_44) != k1_funct_1(X0_42,X1_44) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1378,plain,
    ( ~ r2_hidden(k1_funct_1(k2_funct_1(sK3),sK2(sK4,k2_funct_1(sK3))),k1_relat_1(X0_42))
    | ~ r2_hidden(k1_funct_1(sK4,sK2(sK4,k2_funct_1(sK3))),k1_relat_1(X0_42))
    | ~ v1_relat_1(X0_42)
    | ~ v1_funct_1(X0_42)
    | ~ v2_funct_1(X0_42)
    | k1_funct_1(X0_42,k1_funct_1(k2_funct_1(sK3),sK2(sK4,k2_funct_1(sK3)))) != k1_funct_1(X0_42,k1_funct_1(sK4,sK2(sK4,k2_funct_1(sK3))))
    | k1_funct_1(k2_funct_1(sK3),sK2(sK4,k2_funct_1(sK3))) = k1_funct_1(sK4,sK2(sK4,k2_funct_1(sK3))) ),
    inference(instantiation,[status(thm)],[c_845])).

cnf(c_1380,plain,
    ( ~ r2_hidden(k1_funct_1(k2_funct_1(sK3),sK2(sK4,k2_funct_1(sK3))),k1_relat_1(sK3))
    | ~ r2_hidden(k1_funct_1(sK4,sK2(sK4,k2_funct_1(sK3))),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | k1_funct_1(k2_funct_1(sK3),sK2(sK4,k2_funct_1(sK3))) = k1_funct_1(sK4,sK2(sK4,k2_funct_1(sK3)))
    | k1_funct_1(sK3,k1_funct_1(k2_funct_1(sK3),sK2(sK4,k2_funct_1(sK3)))) != k1_funct_1(sK3,k1_funct_1(sK4,sK2(sK4,k2_funct_1(sK3)))) ),
    inference(instantiation,[status(thm)],[c_1378])).

cnf(c_1288,plain,
    ( k1_relat_1(k2_funct_1(sK3)) != X0_43
    | k1_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK4)
    | k1_relat_1(sK4) != X0_43 ),
    inference(instantiation,[status(thm)],[c_855])).

cnf(c_1346,plain,
    ( k1_relat_1(k2_funct_1(sK3)) != k2_relat_1(sK3)
    | k1_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK4)
    | k1_relat_1(sK4) != k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1288])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | X1 = X0
    | k1_funct_1(X1,sK2(X0,X1)) != k1_funct_1(X0,sK2(X0,X1))
    | k1_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_837,plain,
    ( ~ v1_relat_1(X0_42)
    | ~ v1_relat_1(X1_42)
    | ~ v1_funct_1(X0_42)
    | ~ v1_funct_1(X1_42)
    | k1_funct_1(X1_42,sK2(X0_42,X1_42)) != k1_funct_1(X0_42,sK2(X0_42,X1_42))
    | k1_relat_1(X1_42) != k1_relat_1(X0_42)
    | X1_42 = X0_42 ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1270,plain,
    ( ~ v1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK4)
    | k1_funct_1(k2_funct_1(sK3),sK2(sK4,k2_funct_1(sK3))) != k1_funct_1(sK4,sK2(sK4,k2_funct_1(sK3)))
    | k1_relat_1(k2_funct_1(sK3)) != k1_relat_1(sK4)
    | k2_funct_1(sK3) = sK4 ),
    inference(instantiation,[status(thm)],[c_837])).

cnf(c_13,plain,
    ( r2_hidden(sK2(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | X1 = X0
    | k1_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_836,plain,
    ( r2_hidden(sK2(X0_42,X1_42),k1_relat_1(X0_42))
    | ~ v1_relat_1(X0_42)
    | ~ v1_relat_1(X1_42)
    | ~ v1_funct_1(X0_42)
    | ~ v1_funct_1(X1_42)
    | k1_relat_1(X1_42) != k1_relat_1(X0_42)
    | X1_42 = X0_42 ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1271,plain,
    ( r2_hidden(sK2(sK4,k2_funct_1(sK3)),k1_relat_1(sK4))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK4)
    | k1_relat_1(k2_funct_1(sK3)) != k1_relat_1(sK4)
    | k2_funct_1(sK3) = sK4 ),
    inference(instantiation,[status(thm)],[c_836])).

cnf(c_18,negated_conjecture,
    ( k1_relat_1(sK3) = k2_relat_1(sK4) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_831,negated_conjecture,
    ( k1_relat_1(sK3) = k2_relat_1(sK4) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_17,negated_conjecture,
    ( k1_relat_1(sK4) = k2_relat_1(sK3) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_832,negated_conjecture,
    ( k1_relat_1(sK4) = k2_relat_1(sK3) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_14,negated_conjecture,
    ( k2_funct_1(sK3) != sK4 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_835,negated_conjecture,
    ( k2_funct_1(sK3) != sK4 ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_840,plain,
    ( ~ v1_relat_1(X0_42)
    | ~ v1_funct_1(X0_42)
    | ~ v2_funct_1(X0_42)
    | k1_relat_1(k2_funct_1(X0_42)) = k2_relat_1(X0_42) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_893,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_840])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_841,plain,
    ( ~ v1_relat_1(X0_42)
    | ~ v1_funct_1(X0_42)
    | ~ v2_funct_1(X0_42)
    | k2_relat_1(k2_funct_1(X0_42)) = k1_relat_1(X0_42) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_890,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_841])).

cnf(c_851,plain,
    ( X0_42 = X0_42 ),
    theory(equality)).

cnf(c_876,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_851])).

cnf(c_864,plain,
    ( k2_relat_1(X0_42) = k2_relat_1(X1_42)
    | X0_42 != X1_42 ),
    theory(equality)).

cnf(c_873,plain,
    ( k2_relat_1(sK3) = k2_relat_1(sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_864])).

cnf(c_861,plain,
    ( k1_relat_1(X0_42) = k1_relat_1(X1_42)
    | X0_42 != X1_42 ),
    theory(equality)).

cnf(c_870,plain,
    ( k1_relat_1(sK3) = k1_relat_1(sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_861])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_60,plain,
    ( ~ v1_relat_1(sK3)
    | v1_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_57,plain,
    ( v1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_19,negated_conjecture,
    ( v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_21,negated_conjecture,
    ( v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_23,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f47])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_35194,c_12200,c_6101,c_3438,c_2735,c_2724,c_2390,c_2333,c_2074,c_1973,c_1704,c_1696,c_1395,c_1390,c_1380,c_1346,c_1270,c_1271,c_831,c_832,c_835,c_893,c_890,c_876,c_873,c_870,c_60,c_57,c_19,c_20,c_21,c_22,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:42:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.32/1.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.32/1.50  
% 7.32/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.32/1.50  
% 7.32/1.50  ------  iProver source info
% 7.32/1.50  
% 7.32/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.32/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.32/1.50  git: non_committed_changes: false
% 7.32/1.50  git: last_make_outside_of_git: false
% 7.32/1.50  
% 7.32/1.50  ------ 
% 7.32/1.50  
% 7.32/1.50  ------ Input Options
% 7.32/1.50  
% 7.32/1.50  --out_options                           all
% 7.32/1.50  --tptp_safe_out                         true
% 7.32/1.50  --problem_path                          ""
% 7.32/1.50  --include_path                          ""
% 7.32/1.50  --clausifier                            res/vclausify_rel
% 7.32/1.50  --clausifier_options                    ""
% 7.32/1.50  --stdin                                 false
% 7.32/1.50  --stats_out                             all
% 7.32/1.50  
% 7.32/1.50  ------ General Options
% 7.32/1.50  
% 7.32/1.50  --fof                                   false
% 7.32/1.50  --time_out_real                         305.
% 7.32/1.50  --time_out_virtual                      -1.
% 7.32/1.50  --symbol_type_check                     false
% 7.32/1.50  --clausify_out                          false
% 7.32/1.50  --sig_cnt_out                           false
% 7.32/1.50  --trig_cnt_out                          false
% 7.32/1.50  --trig_cnt_out_tolerance                1.
% 7.32/1.50  --trig_cnt_out_sk_spl                   false
% 7.32/1.50  --abstr_cl_out                          false
% 7.32/1.50  
% 7.32/1.50  ------ Global Options
% 7.32/1.50  
% 7.32/1.50  --schedule                              default
% 7.32/1.50  --add_important_lit                     false
% 7.32/1.50  --prop_solver_per_cl                    1000
% 7.32/1.50  --min_unsat_core                        false
% 7.32/1.50  --soft_assumptions                      false
% 7.32/1.50  --soft_lemma_size                       3
% 7.32/1.50  --prop_impl_unit_size                   0
% 7.32/1.50  --prop_impl_unit                        []
% 7.32/1.50  --share_sel_clauses                     true
% 7.32/1.50  --reset_solvers                         false
% 7.32/1.50  --bc_imp_inh                            [conj_cone]
% 7.32/1.50  --conj_cone_tolerance                   3.
% 7.32/1.50  --extra_neg_conj                        none
% 7.32/1.50  --large_theory_mode                     true
% 7.32/1.50  --prolific_symb_bound                   200
% 7.32/1.50  --lt_threshold                          2000
% 7.32/1.50  --clause_weak_htbl                      true
% 7.32/1.50  --gc_record_bc_elim                     false
% 7.32/1.50  
% 7.32/1.50  ------ Preprocessing Options
% 7.32/1.50  
% 7.32/1.50  --preprocessing_flag                    true
% 7.32/1.50  --time_out_prep_mult                    0.1
% 7.32/1.50  --splitting_mode                        input
% 7.32/1.50  --splitting_grd                         true
% 7.32/1.50  --splitting_cvd                         false
% 7.32/1.50  --splitting_cvd_svl                     false
% 7.32/1.50  --splitting_nvd                         32
% 7.32/1.50  --sub_typing                            true
% 7.32/1.50  --prep_gs_sim                           true
% 7.32/1.50  --prep_unflatten                        true
% 7.32/1.50  --prep_res_sim                          true
% 7.32/1.50  --prep_upred                            true
% 7.32/1.50  --prep_sem_filter                       exhaustive
% 7.32/1.50  --prep_sem_filter_out                   false
% 7.32/1.50  --pred_elim                             true
% 7.32/1.50  --res_sim_input                         true
% 7.32/1.50  --eq_ax_congr_red                       true
% 7.32/1.50  --pure_diseq_elim                       true
% 7.32/1.50  --brand_transform                       false
% 7.32/1.50  --non_eq_to_eq                          false
% 7.32/1.50  --prep_def_merge                        true
% 7.32/1.50  --prep_def_merge_prop_impl              false
% 7.32/1.50  --prep_def_merge_mbd                    true
% 7.32/1.50  --prep_def_merge_tr_red                 false
% 7.32/1.50  --prep_def_merge_tr_cl                  false
% 7.32/1.50  --smt_preprocessing                     true
% 7.32/1.50  --smt_ac_axioms                         fast
% 7.32/1.50  --preprocessed_out                      false
% 7.32/1.50  --preprocessed_stats                    false
% 7.32/1.50  
% 7.32/1.50  ------ Abstraction refinement Options
% 7.32/1.50  
% 7.32/1.50  --abstr_ref                             []
% 7.32/1.50  --abstr_ref_prep                        false
% 7.32/1.50  --abstr_ref_until_sat                   false
% 7.32/1.50  --abstr_ref_sig_restrict                funpre
% 7.32/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.32/1.50  --abstr_ref_under                       []
% 7.32/1.50  
% 7.32/1.50  ------ SAT Options
% 7.32/1.50  
% 7.32/1.50  --sat_mode                              false
% 7.32/1.50  --sat_fm_restart_options                ""
% 7.32/1.50  --sat_gr_def                            false
% 7.32/1.50  --sat_epr_types                         true
% 7.32/1.50  --sat_non_cyclic_types                  false
% 7.32/1.50  --sat_finite_models                     false
% 7.32/1.50  --sat_fm_lemmas                         false
% 7.32/1.50  --sat_fm_prep                           false
% 7.32/1.50  --sat_fm_uc_incr                        true
% 7.32/1.50  --sat_out_model                         small
% 7.32/1.50  --sat_out_clauses                       false
% 7.32/1.50  
% 7.32/1.50  ------ QBF Options
% 7.32/1.50  
% 7.32/1.50  --qbf_mode                              false
% 7.32/1.50  --qbf_elim_univ                         false
% 7.32/1.50  --qbf_dom_inst                          none
% 7.32/1.50  --qbf_dom_pre_inst                      false
% 7.32/1.50  --qbf_sk_in                             false
% 7.32/1.50  --qbf_pred_elim                         true
% 7.32/1.50  --qbf_split                             512
% 7.32/1.50  
% 7.32/1.50  ------ BMC1 Options
% 7.32/1.50  
% 7.32/1.50  --bmc1_incremental                      false
% 7.32/1.50  --bmc1_axioms                           reachable_all
% 7.32/1.50  --bmc1_min_bound                        0
% 7.32/1.50  --bmc1_max_bound                        -1
% 7.32/1.50  --bmc1_max_bound_default                -1
% 7.32/1.50  --bmc1_symbol_reachability              true
% 7.32/1.50  --bmc1_property_lemmas                  false
% 7.32/1.50  --bmc1_k_induction                      false
% 7.32/1.50  --bmc1_non_equiv_states                 false
% 7.32/1.50  --bmc1_deadlock                         false
% 7.32/1.50  --bmc1_ucm                              false
% 7.32/1.50  --bmc1_add_unsat_core                   none
% 7.32/1.50  --bmc1_unsat_core_children              false
% 7.32/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.32/1.50  --bmc1_out_stat                         full
% 7.32/1.50  --bmc1_ground_init                      false
% 7.32/1.50  --bmc1_pre_inst_next_state              false
% 7.32/1.50  --bmc1_pre_inst_state                   false
% 7.32/1.50  --bmc1_pre_inst_reach_state             false
% 7.32/1.50  --bmc1_out_unsat_core                   false
% 7.32/1.50  --bmc1_aig_witness_out                  false
% 7.32/1.50  --bmc1_verbose                          false
% 7.32/1.50  --bmc1_dump_clauses_tptp                false
% 7.32/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.32/1.50  --bmc1_dump_file                        -
% 7.32/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.32/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.32/1.50  --bmc1_ucm_extend_mode                  1
% 7.32/1.50  --bmc1_ucm_init_mode                    2
% 7.32/1.50  --bmc1_ucm_cone_mode                    none
% 7.32/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.32/1.50  --bmc1_ucm_relax_model                  4
% 7.32/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.32/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.32/1.50  --bmc1_ucm_layered_model                none
% 7.32/1.50  --bmc1_ucm_max_lemma_size               10
% 7.32/1.50  
% 7.32/1.50  ------ AIG Options
% 7.32/1.50  
% 7.32/1.50  --aig_mode                              false
% 7.32/1.50  
% 7.32/1.50  ------ Instantiation Options
% 7.32/1.50  
% 7.32/1.50  --instantiation_flag                    true
% 7.32/1.50  --inst_sos_flag                         true
% 7.32/1.50  --inst_sos_phase                        true
% 7.32/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.32/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.32/1.50  --inst_lit_sel_side                     num_symb
% 7.32/1.50  --inst_solver_per_active                1400
% 7.32/1.50  --inst_solver_calls_frac                1.
% 7.32/1.50  --inst_passive_queue_type               priority_queues
% 7.32/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.32/1.50  --inst_passive_queues_freq              [25;2]
% 7.32/1.50  --inst_dismatching                      true
% 7.32/1.50  --inst_eager_unprocessed_to_passive     true
% 7.32/1.50  --inst_prop_sim_given                   true
% 7.32/1.50  --inst_prop_sim_new                     false
% 7.32/1.50  --inst_subs_new                         false
% 7.32/1.50  --inst_eq_res_simp                      false
% 7.32/1.50  --inst_subs_given                       false
% 7.32/1.50  --inst_orphan_elimination               true
% 7.32/1.50  --inst_learning_loop_flag               true
% 7.32/1.50  --inst_learning_start                   3000
% 7.32/1.50  --inst_learning_factor                  2
% 7.32/1.50  --inst_start_prop_sim_after_learn       3
% 7.32/1.50  --inst_sel_renew                        solver
% 7.32/1.50  --inst_lit_activity_flag                true
% 7.32/1.50  --inst_restr_to_given                   false
% 7.32/1.50  --inst_activity_threshold               500
% 7.32/1.50  --inst_out_proof                        true
% 7.32/1.50  
% 7.32/1.50  ------ Resolution Options
% 7.32/1.50  
% 7.32/1.50  --resolution_flag                       true
% 7.32/1.50  --res_lit_sel                           adaptive
% 7.32/1.50  --res_lit_sel_side                      none
% 7.32/1.50  --res_ordering                          kbo
% 7.32/1.50  --res_to_prop_solver                    active
% 7.32/1.50  --res_prop_simpl_new                    false
% 7.32/1.50  --res_prop_simpl_given                  true
% 7.32/1.50  --res_passive_queue_type                priority_queues
% 7.32/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.32/1.50  --res_passive_queues_freq               [15;5]
% 7.32/1.50  --res_forward_subs                      full
% 7.32/1.50  --res_backward_subs                     full
% 7.32/1.50  --res_forward_subs_resolution           true
% 7.32/1.50  --res_backward_subs_resolution          true
% 7.32/1.50  --res_orphan_elimination                true
% 7.32/1.50  --res_time_limit                        2.
% 7.32/1.50  --res_out_proof                         true
% 7.32/1.50  
% 7.32/1.50  ------ Superposition Options
% 7.32/1.50  
% 7.32/1.50  --superposition_flag                    true
% 7.32/1.50  --sup_passive_queue_type                priority_queues
% 7.32/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.32/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.32/1.50  --demod_completeness_check              fast
% 7.32/1.50  --demod_use_ground                      true
% 7.32/1.50  --sup_to_prop_solver                    passive
% 7.32/1.50  --sup_prop_simpl_new                    true
% 7.32/1.50  --sup_prop_simpl_given                  true
% 7.32/1.50  --sup_fun_splitting                     true
% 7.32/1.50  --sup_smt_interval                      50000
% 7.32/1.50  
% 7.32/1.50  ------ Superposition Simplification Setup
% 7.32/1.50  
% 7.32/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.32/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.32/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.32/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.32/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.32/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.32/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.32/1.50  --sup_immed_triv                        [TrivRules]
% 7.32/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.32/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.32/1.50  --sup_immed_bw_main                     []
% 7.32/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.32/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.32/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.32/1.50  --sup_input_bw                          []
% 7.32/1.50  
% 7.32/1.50  ------ Combination Options
% 7.32/1.50  
% 7.32/1.50  --comb_res_mult                         3
% 7.32/1.50  --comb_sup_mult                         2
% 7.32/1.50  --comb_inst_mult                        10
% 7.32/1.50  
% 7.32/1.50  ------ Debug Options
% 7.32/1.50  
% 7.32/1.50  --dbg_backtrace                         false
% 7.32/1.50  --dbg_dump_prop_clauses                 false
% 7.32/1.50  --dbg_dump_prop_clauses_file            -
% 7.32/1.50  --dbg_out_stat                          false
% 7.32/1.50  ------ Parsing...
% 7.32/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.32/1.50  
% 7.32/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.32/1.50  
% 7.32/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.32/1.50  
% 7.32/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.32/1.50  ------ Proving...
% 7.32/1.50  ------ Problem Properties 
% 7.32/1.50  
% 7.32/1.50  
% 7.32/1.50  clauses                                 24
% 7.32/1.50  conjectures                             10
% 7.32/1.50  EPR                                     5
% 7.32/1.50  Horn                                    20
% 7.32/1.50  unary                                   8
% 7.32/1.50  binary                                  0
% 7.32/1.50  lits                                    79
% 7.32/1.50  lits eq                                 18
% 7.32/1.50  fd_pure                                 0
% 7.32/1.50  fd_pseudo                               0
% 7.32/1.50  fd_cond                                 0
% 7.32/1.50  fd_pseudo_cond                          3
% 7.32/1.50  AC symbols                              0
% 7.32/1.50  
% 7.32/1.50  ------ Schedule dynamic 5 is on 
% 7.32/1.50  
% 7.32/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.32/1.50  
% 7.32/1.50  
% 7.32/1.50  ------ 
% 7.32/1.50  Current options:
% 7.32/1.50  ------ 
% 7.32/1.50  
% 7.32/1.50  ------ Input Options
% 7.32/1.50  
% 7.32/1.50  --out_options                           all
% 7.32/1.50  --tptp_safe_out                         true
% 7.32/1.50  --problem_path                          ""
% 7.32/1.50  --include_path                          ""
% 7.32/1.50  --clausifier                            res/vclausify_rel
% 7.32/1.50  --clausifier_options                    ""
% 7.32/1.50  --stdin                                 false
% 7.32/1.50  --stats_out                             all
% 7.32/1.50  
% 7.32/1.50  ------ General Options
% 7.32/1.50  
% 7.32/1.50  --fof                                   false
% 7.32/1.50  --time_out_real                         305.
% 7.32/1.50  --time_out_virtual                      -1.
% 7.32/1.50  --symbol_type_check                     false
% 7.32/1.50  --clausify_out                          false
% 7.32/1.50  --sig_cnt_out                           false
% 7.32/1.50  --trig_cnt_out                          false
% 7.32/1.50  --trig_cnt_out_tolerance                1.
% 7.32/1.50  --trig_cnt_out_sk_spl                   false
% 7.32/1.50  --abstr_cl_out                          false
% 7.32/1.50  
% 7.32/1.50  ------ Global Options
% 7.32/1.50  
% 7.32/1.50  --schedule                              default
% 7.32/1.50  --add_important_lit                     false
% 7.32/1.50  --prop_solver_per_cl                    1000
% 7.32/1.50  --min_unsat_core                        false
% 7.32/1.50  --soft_assumptions                      false
% 7.32/1.50  --soft_lemma_size                       3
% 7.32/1.50  --prop_impl_unit_size                   0
% 7.32/1.50  --prop_impl_unit                        []
% 7.32/1.50  --share_sel_clauses                     true
% 7.32/1.50  --reset_solvers                         false
% 7.32/1.50  --bc_imp_inh                            [conj_cone]
% 7.32/1.50  --conj_cone_tolerance                   3.
% 7.32/1.50  --extra_neg_conj                        none
% 7.32/1.50  --large_theory_mode                     true
% 7.32/1.50  --prolific_symb_bound                   200
% 7.32/1.50  --lt_threshold                          2000
% 7.32/1.50  --clause_weak_htbl                      true
% 7.32/1.50  --gc_record_bc_elim                     false
% 7.32/1.50  
% 7.32/1.50  ------ Preprocessing Options
% 7.32/1.50  
% 7.32/1.50  --preprocessing_flag                    true
% 7.32/1.50  --time_out_prep_mult                    0.1
% 7.32/1.50  --splitting_mode                        input
% 7.32/1.50  --splitting_grd                         true
% 7.32/1.50  --splitting_cvd                         false
% 7.32/1.50  --splitting_cvd_svl                     false
% 7.32/1.50  --splitting_nvd                         32
% 7.32/1.50  --sub_typing                            true
% 7.32/1.50  --prep_gs_sim                           true
% 7.32/1.50  --prep_unflatten                        true
% 7.32/1.50  --prep_res_sim                          true
% 7.32/1.50  --prep_upred                            true
% 7.32/1.50  --prep_sem_filter                       exhaustive
% 7.32/1.50  --prep_sem_filter_out                   false
% 7.32/1.50  --pred_elim                             true
% 7.32/1.50  --res_sim_input                         true
% 7.32/1.50  --eq_ax_congr_red                       true
% 7.32/1.50  --pure_diseq_elim                       true
% 7.32/1.50  --brand_transform                       false
% 7.32/1.50  --non_eq_to_eq                          false
% 7.32/1.50  --prep_def_merge                        true
% 7.32/1.50  --prep_def_merge_prop_impl              false
% 7.32/1.50  --prep_def_merge_mbd                    true
% 7.32/1.50  --prep_def_merge_tr_red                 false
% 7.32/1.50  --prep_def_merge_tr_cl                  false
% 7.32/1.50  --smt_preprocessing                     true
% 7.32/1.50  --smt_ac_axioms                         fast
% 7.32/1.50  --preprocessed_out                      false
% 7.32/1.50  --preprocessed_stats                    false
% 7.32/1.50  
% 7.32/1.50  ------ Abstraction refinement Options
% 7.32/1.50  
% 7.32/1.50  --abstr_ref                             []
% 7.32/1.50  --abstr_ref_prep                        false
% 7.32/1.50  --abstr_ref_until_sat                   false
% 7.32/1.50  --abstr_ref_sig_restrict                funpre
% 7.32/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.32/1.50  --abstr_ref_under                       []
% 7.32/1.50  
% 7.32/1.50  ------ SAT Options
% 7.32/1.50  
% 7.32/1.50  --sat_mode                              false
% 7.32/1.50  --sat_fm_restart_options                ""
% 7.32/1.50  --sat_gr_def                            false
% 7.32/1.50  --sat_epr_types                         true
% 7.32/1.50  --sat_non_cyclic_types                  false
% 7.32/1.50  --sat_finite_models                     false
% 7.32/1.50  --sat_fm_lemmas                         false
% 7.32/1.50  --sat_fm_prep                           false
% 7.32/1.50  --sat_fm_uc_incr                        true
% 7.32/1.50  --sat_out_model                         small
% 7.32/1.50  --sat_out_clauses                       false
% 7.32/1.50  
% 7.32/1.50  ------ QBF Options
% 7.32/1.50  
% 7.32/1.50  --qbf_mode                              false
% 7.32/1.50  --qbf_elim_univ                         false
% 7.32/1.50  --qbf_dom_inst                          none
% 7.32/1.50  --qbf_dom_pre_inst                      false
% 7.32/1.50  --qbf_sk_in                             false
% 7.32/1.50  --qbf_pred_elim                         true
% 7.32/1.50  --qbf_split                             512
% 7.32/1.50  
% 7.32/1.50  ------ BMC1 Options
% 7.32/1.50  
% 7.32/1.50  --bmc1_incremental                      false
% 7.32/1.50  --bmc1_axioms                           reachable_all
% 7.32/1.50  --bmc1_min_bound                        0
% 7.32/1.50  --bmc1_max_bound                        -1
% 7.32/1.50  --bmc1_max_bound_default                -1
% 7.32/1.50  --bmc1_symbol_reachability              true
% 7.32/1.50  --bmc1_property_lemmas                  false
% 7.32/1.50  --bmc1_k_induction                      false
% 7.32/1.50  --bmc1_non_equiv_states                 false
% 7.32/1.50  --bmc1_deadlock                         false
% 7.32/1.50  --bmc1_ucm                              false
% 7.32/1.50  --bmc1_add_unsat_core                   none
% 7.32/1.50  --bmc1_unsat_core_children              false
% 7.32/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.32/1.50  --bmc1_out_stat                         full
% 7.32/1.50  --bmc1_ground_init                      false
% 7.32/1.50  --bmc1_pre_inst_next_state              false
% 7.32/1.50  --bmc1_pre_inst_state                   false
% 7.32/1.50  --bmc1_pre_inst_reach_state             false
% 7.32/1.50  --bmc1_out_unsat_core                   false
% 7.32/1.50  --bmc1_aig_witness_out                  false
% 7.32/1.50  --bmc1_verbose                          false
% 7.32/1.50  --bmc1_dump_clauses_tptp                false
% 7.32/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.32/1.50  --bmc1_dump_file                        -
% 7.32/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.32/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.32/1.50  --bmc1_ucm_extend_mode                  1
% 7.32/1.50  --bmc1_ucm_init_mode                    2
% 7.32/1.50  --bmc1_ucm_cone_mode                    none
% 7.32/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.32/1.50  --bmc1_ucm_relax_model                  4
% 7.32/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.32/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.32/1.50  --bmc1_ucm_layered_model                none
% 7.32/1.50  --bmc1_ucm_max_lemma_size               10
% 7.32/1.50  
% 7.32/1.50  ------ AIG Options
% 7.32/1.50  
% 7.32/1.50  --aig_mode                              false
% 7.32/1.50  
% 7.32/1.50  ------ Instantiation Options
% 7.32/1.50  
% 7.32/1.50  --instantiation_flag                    true
% 7.32/1.50  --inst_sos_flag                         true
% 7.32/1.50  --inst_sos_phase                        true
% 7.32/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.32/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.32/1.50  --inst_lit_sel_side                     none
% 7.32/1.50  --inst_solver_per_active                1400
% 7.32/1.50  --inst_solver_calls_frac                1.
% 7.32/1.50  --inst_passive_queue_type               priority_queues
% 7.32/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.32/1.50  --inst_passive_queues_freq              [25;2]
% 7.32/1.50  --inst_dismatching                      true
% 7.32/1.50  --inst_eager_unprocessed_to_passive     true
% 7.32/1.50  --inst_prop_sim_given                   true
% 7.32/1.50  --inst_prop_sim_new                     false
% 7.32/1.50  --inst_subs_new                         false
% 7.32/1.50  --inst_eq_res_simp                      false
% 7.32/1.50  --inst_subs_given                       false
% 7.32/1.50  --inst_orphan_elimination               true
% 7.32/1.50  --inst_learning_loop_flag               true
% 7.32/1.50  --inst_learning_start                   3000
% 7.32/1.50  --inst_learning_factor                  2
% 7.32/1.50  --inst_start_prop_sim_after_learn       3
% 7.32/1.50  --inst_sel_renew                        solver
% 7.32/1.50  --inst_lit_activity_flag                true
% 7.32/1.50  --inst_restr_to_given                   false
% 7.32/1.50  --inst_activity_threshold               500
% 7.32/1.50  --inst_out_proof                        true
% 7.32/1.50  
% 7.32/1.50  ------ Resolution Options
% 7.32/1.50  
% 7.32/1.50  --resolution_flag                       false
% 7.32/1.50  --res_lit_sel                           adaptive
% 7.32/1.50  --res_lit_sel_side                      none
% 7.32/1.50  --res_ordering                          kbo
% 7.32/1.50  --res_to_prop_solver                    active
% 7.32/1.50  --res_prop_simpl_new                    false
% 7.32/1.50  --res_prop_simpl_given                  true
% 7.32/1.50  --res_passive_queue_type                priority_queues
% 7.32/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.32/1.50  --res_passive_queues_freq               [15;5]
% 7.32/1.50  --res_forward_subs                      full
% 7.32/1.50  --res_backward_subs                     full
% 7.32/1.50  --res_forward_subs_resolution           true
% 7.32/1.50  --res_backward_subs_resolution          true
% 7.32/1.50  --res_orphan_elimination                true
% 7.32/1.50  --res_time_limit                        2.
% 7.32/1.50  --res_out_proof                         true
% 7.32/1.50  
% 7.32/1.50  ------ Superposition Options
% 7.32/1.50  
% 7.32/1.50  --superposition_flag                    true
% 7.32/1.50  --sup_passive_queue_type                priority_queues
% 7.32/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.32/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.32/1.50  --demod_completeness_check              fast
% 7.32/1.50  --demod_use_ground                      true
% 7.32/1.50  --sup_to_prop_solver                    passive
% 7.32/1.50  --sup_prop_simpl_new                    true
% 7.32/1.50  --sup_prop_simpl_given                  true
% 7.32/1.50  --sup_fun_splitting                     true
% 7.32/1.50  --sup_smt_interval                      50000
% 7.32/1.50  
% 7.32/1.50  ------ Superposition Simplification Setup
% 7.32/1.50  
% 7.32/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.32/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.32/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.32/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.32/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.32/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.32/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.32/1.50  --sup_immed_triv                        [TrivRules]
% 7.32/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.32/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.32/1.50  --sup_immed_bw_main                     []
% 7.32/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.32/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.32/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.32/1.50  --sup_input_bw                          []
% 7.32/1.50  
% 7.32/1.50  ------ Combination Options
% 7.32/1.50  
% 7.32/1.50  --comb_res_mult                         3
% 7.32/1.50  --comb_sup_mult                         2
% 7.32/1.50  --comb_inst_mult                        10
% 7.32/1.50  
% 7.32/1.50  ------ Debug Options
% 7.32/1.50  
% 7.32/1.50  --dbg_backtrace                         false
% 7.32/1.50  --dbg_dump_prop_clauses                 false
% 7.32/1.50  --dbg_dump_prop_clauses_file            -
% 7.32/1.50  --dbg_out_stat                          false
% 7.32/1.50  
% 7.32/1.50  
% 7.32/1.50  
% 7.32/1.50  
% 7.32/1.50  ------ Proving...
% 7.32/1.50  
% 7.32/1.50  
% 7.32/1.50  % SZS status Theorem for theBenchmark.p
% 7.32/1.50  
% 7.32/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.32/1.50  
% 7.32/1.50  fof(f3,axiom,(
% 7.32/1.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 7.32/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.50  
% 7.32/1.50  fof(f13,plain,(
% 7.32/1.50    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 7.32/1.50    inference(ennf_transformation,[],[f3])).
% 7.32/1.50  
% 7.32/1.50  fof(f14,plain,(
% 7.32/1.50    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.32/1.50    inference(flattening,[],[f13])).
% 7.32/1.50  
% 7.32/1.50  fof(f40,plain,(
% 7.32/1.50    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.32/1.50    inference(cnf_transformation,[],[f14])).
% 7.32/1.50  
% 7.32/1.50  fof(f5,axiom,(
% 7.32/1.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0 & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0)))),
% 7.32/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.50  
% 7.32/1.50  fof(f17,plain,(
% 7.32/1.50    ! [X0,X1] : (((k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0 & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0) | (~r2_hidden(X0,k2_relat_1(X1)) | ~v2_funct_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 7.32/1.50    inference(ennf_transformation,[],[f5])).
% 7.32/1.50  
% 7.32/1.50  fof(f18,plain,(
% 7.32/1.50    ! [X0,X1] : ((k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0 & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.32/1.50    inference(flattening,[],[f17])).
% 7.32/1.50  
% 7.32/1.50  fof(f43,plain,(
% 7.32/1.50    ( ! [X0,X1] : (k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 | ~r2_hidden(X0,k2_relat_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.32/1.50    inference(cnf_transformation,[],[f18])).
% 7.32/1.50  
% 7.32/1.50  fof(f7,conjecture,(
% 7.32/1.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2,X3] : ((r2_hidden(X3,k1_relat_1(X1)) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,X2) = X3 <=> k1_funct_1(X1,X3) = X2)) & k1_relat_1(X1) = k2_relat_1(X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 7.32/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.50  
% 7.32/1.50  fof(f8,negated_conjecture,(
% 7.32/1.50    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2,X3] : ((r2_hidden(X3,k1_relat_1(X1)) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,X2) = X3 <=> k1_funct_1(X1,X3) = X2)) & k1_relat_1(X1) = k2_relat_1(X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 7.32/1.50    inference(negated_conjecture,[],[f7])).
% 7.32/1.50  
% 7.32/1.50  fof(f21,plain,(
% 7.32/1.50    ? [X0] : (? [X1] : ((k2_funct_1(X0) != X1 & (! [X2,X3] : ((k1_funct_1(X0,X2) = X3 <=> k1_funct_1(X1,X3) = X2) | (~r2_hidden(X3,k1_relat_1(X1)) | ~r2_hidden(X2,k1_relat_1(X0)))) & k1_relat_1(X1) = k2_relat_1(X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 7.32/1.50    inference(ennf_transformation,[],[f8])).
% 7.32/1.50  
% 7.32/1.50  fof(f22,plain,(
% 7.32/1.50    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & ! [X2,X3] : ((k1_funct_1(X0,X2) = X3 <=> k1_funct_1(X1,X3) = X2) | ~r2_hidden(X3,k1_relat_1(X1)) | ~r2_hidden(X2,k1_relat_1(X0))) & k1_relat_1(X1) = k2_relat_1(X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 7.32/1.50    inference(flattening,[],[f21])).
% 7.32/1.50  
% 7.32/1.50  fof(f29,plain,(
% 7.32/1.50    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & ! [X2,X3] : (((k1_funct_1(X0,X2) = X3 | k1_funct_1(X1,X3) != X2) & (k1_funct_1(X1,X3) = X2 | k1_funct_1(X0,X2) != X3)) | ~r2_hidden(X3,k1_relat_1(X1)) | ~r2_hidden(X2,k1_relat_1(X0))) & k1_relat_1(X1) = k2_relat_1(X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 7.32/1.50    inference(nnf_transformation,[],[f22])).
% 7.32/1.50  
% 7.32/1.50  fof(f31,plain,(
% 7.32/1.50    ( ! [X0] : (? [X1] : (k2_funct_1(X0) != X1 & ! [X2,X3] : (((k1_funct_1(X0,X2) = X3 | k1_funct_1(X1,X3) != X2) & (k1_funct_1(X1,X3) = X2 | k1_funct_1(X0,X2) != X3)) | ~r2_hidden(X3,k1_relat_1(X1)) | ~r2_hidden(X2,k1_relat_1(X0))) & k1_relat_1(X1) = k2_relat_1(X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) => (k2_funct_1(X0) != sK4 & ! [X3,X2] : (((k1_funct_1(X0,X2) = X3 | k1_funct_1(sK4,X3) != X2) & (k1_funct_1(sK4,X3) = X2 | k1_funct_1(X0,X2) != X3)) | ~r2_hidden(X3,k1_relat_1(sK4)) | ~r2_hidden(X2,k1_relat_1(X0))) & k1_relat_1(sK4) = k2_relat_1(X0) & k1_relat_1(X0) = k2_relat_1(sK4) & v2_funct_1(X0) & v1_funct_1(sK4) & v1_relat_1(sK4))) )),
% 7.32/1.50    introduced(choice_axiom,[])).
% 7.32/1.50  
% 7.32/1.50  fof(f30,plain,(
% 7.32/1.50    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & ! [X2,X3] : (((k1_funct_1(X0,X2) = X3 | k1_funct_1(X1,X3) != X2) & (k1_funct_1(X1,X3) = X2 | k1_funct_1(X0,X2) != X3)) | ~r2_hidden(X3,k1_relat_1(X1)) | ~r2_hidden(X2,k1_relat_1(X0))) & k1_relat_1(X1) = k2_relat_1(X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k2_funct_1(sK3) != X1 & ! [X3,X2] : (((k1_funct_1(sK3,X2) = X3 | k1_funct_1(X1,X3) != X2) & (k1_funct_1(X1,X3) = X2 | k1_funct_1(sK3,X2) != X3)) | ~r2_hidden(X3,k1_relat_1(X1)) | ~r2_hidden(X2,k1_relat_1(sK3))) & k1_relat_1(X1) = k2_relat_1(sK3) & k1_relat_1(sK3) = k2_relat_1(X1) & v2_funct_1(sK3) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK3) & v1_relat_1(sK3))),
% 7.32/1.50    introduced(choice_axiom,[])).
% 7.32/1.50  
% 7.32/1.50  fof(f32,plain,(
% 7.32/1.50    (k2_funct_1(sK3) != sK4 & ! [X2,X3] : (((k1_funct_1(sK3,X2) = X3 | k1_funct_1(sK4,X3) != X2) & (k1_funct_1(sK4,X3) = X2 | k1_funct_1(sK3,X2) != X3)) | ~r2_hidden(X3,k1_relat_1(sK4)) | ~r2_hidden(X2,k1_relat_1(sK3))) & k1_relat_1(sK4) = k2_relat_1(sK3) & k1_relat_1(sK3) = k2_relat_1(sK4) & v2_funct_1(sK3) & v1_funct_1(sK4) & v1_relat_1(sK4)) & v1_funct_1(sK3) & v1_relat_1(sK3)),
% 7.32/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f29,f31,f30])).
% 7.32/1.50  
% 7.32/1.50  fof(f55,plain,(
% 7.32/1.50    ( ! [X2,X3] : (k1_funct_1(sK3,X2) = X3 | k1_funct_1(sK4,X3) != X2 | ~r2_hidden(X3,k1_relat_1(sK4)) | ~r2_hidden(X2,k1_relat_1(sK3))) )),
% 7.32/1.50    inference(cnf_transformation,[],[f32])).
% 7.32/1.50  
% 7.32/1.50  fof(f57,plain,(
% 7.32/1.50    ( ! [X3] : (k1_funct_1(sK3,k1_funct_1(sK4,X3)) = X3 | ~r2_hidden(X3,k1_relat_1(sK4)) | ~r2_hidden(k1_funct_1(sK4,X3),k1_relat_1(sK3))) )),
% 7.32/1.50    inference(equality_resolution,[],[f55])).
% 7.32/1.50  
% 7.32/1.50  fof(f1,axiom,(
% 7.32/1.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 7.32/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.50  
% 7.32/1.50  fof(f9,plain,(
% 7.32/1.50    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.32/1.50    inference(ennf_transformation,[],[f1])).
% 7.32/1.50  
% 7.32/1.50  fof(f10,plain,(
% 7.32/1.50    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.32/1.50    inference(flattening,[],[f9])).
% 7.32/1.50  
% 7.32/1.50  fof(f23,plain,(
% 7.32/1.50    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.32/1.50    inference(nnf_transformation,[],[f10])).
% 7.32/1.50  
% 7.32/1.50  fof(f24,plain,(
% 7.32/1.50    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.32/1.50    inference(rectify,[],[f23])).
% 7.32/1.50  
% 7.32/1.50  fof(f25,plain,(
% 7.32/1.50    ! [X0] : (? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => (sK0(X0) != sK1(X0) & k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0)) & r2_hidden(sK1(X0),k1_relat_1(X0)) & r2_hidden(sK0(X0),k1_relat_1(X0))))),
% 7.32/1.50    introduced(choice_axiom,[])).
% 7.32/1.50  
% 7.32/1.50  fof(f26,plain,(
% 7.32/1.50    ! [X0] : (((v2_funct_1(X0) | (sK0(X0) != sK1(X0) & k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0)) & r2_hidden(sK1(X0),k1_relat_1(X0)) & r2_hidden(sK0(X0),k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.32/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f25])).
% 7.32/1.50  
% 7.32/1.50  fof(f33,plain,(
% 7.32/1.50    ( ! [X4,X0,X3] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.32/1.50    inference(cnf_transformation,[],[f26])).
% 7.32/1.50  
% 7.32/1.50  fof(f6,axiom,(
% 7.32/1.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 7.32/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.50  
% 7.32/1.50  fof(f19,plain,(
% 7.32/1.50    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.32/1.50    inference(ennf_transformation,[],[f6])).
% 7.32/1.50  
% 7.32/1.50  fof(f20,plain,(
% 7.32/1.50    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.32/1.50    inference(flattening,[],[f19])).
% 7.32/1.50  
% 7.32/1.50  fof(f27,plain,(
% 7.32/1.50    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))))),
% 7.32/1.50    introduced(choice_axiom,[])).
% 7.32/1.50  
% 7.32/1.50  fof(f28,plain,(
% 7.32/1.50    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.32/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f27])).
% 7.32/1.50  
% 7.32/1.50  fof(f46,plain,(
% 7.32/1.50    ( ! [X0,X1] : (X0 = X1 | k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.32/1.50    inference(cnf_transformation,[],[f28])).
% 7.32/1.50  
% 7.32/1.50  fof(f45,plain,(
% 7.32/1.50    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK2(X0,X1),k1_relat_1(X0)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.32/1.50    inference(cnf_transformation,[],[f28])).
% 7.32/1.50  
% 7.32/1.50  fof(f52,plain,(
% 7.32/1.50    k1_relat_1(sK3) = k2_relat_1(sK4)),
% 7.32/1.50    inference(cnf_transformation,[],[f32])).
% 7.32/1.50  
% 7.32/1.50  fof(f53,plain,(
% 7.32/1.50    k1_relat_1(sK4) = k2_relat_1(sK3)),
% 7.32/1.50    inference(cnf_transformation,[],[f32])).
% 7.32/1.50  
% 7.32/1.50  fof(f56,plain,(
% 7.32/1.50    k2_funct_1(sK3) != sK4),
% 7.32/1.50    inference(cnf_transformation,[],[f32])).
% 7.32/1.50  
% 7.32/1.50  fof(f4,axiom,(
% 7.32/1.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 7.32/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.50  
% 7.32/1.50  fof(f15,plain,(
% 7.32/1.50    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.32/1.50    inference(ennf_transformation,[],[f4])).
% 7.32/1.50  
% 7.32/1.50  fof(f16,plain,(
% 7.32/1.50    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.32/1.50    inference(flattening,[],[f15])).
% 7.32/1.50  
% 7.32/1.50  fof(f41,plain,(
% 7.32/1.50    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.32/1.50    inference(cnf_transformation,[],[f16])).
% 7.32/1.50  
% 7.32/1.50  fof(f42,plain,(
% 7.32/1.50    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.32/1.50    inference(cnf_transformation,[],[f16])).
% 7.32/1.50  
% 7.32/1.50  fof(f2,axiom,(
% 7.32/1.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 7.32/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.50  
% 7.32/1.50  fof(f11,plain,(
% 7.32/1.50    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.32/1.50    inference(ennf_transformation,[],[f2])).
% 7.32/1.50  
% 7.32/1.50  fof(f12,plain,(
% 7.32/1.50    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.32/1.50    inference(flattening,[],[f11])).
% 7.32/1.50  
% 7.32/1.50  fof(f39,plain,(
% 7.32/1.50    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.32/1.50    inference(cnf_transformation,[],[f12])).
% 7.32/1.50  
% 7.32/1.50  fof(f38,plain,(
% 7.32/1.50    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.32/1.50    inference(cnf_transformation,[],[f12])).
% 7.32/1.50  
% 7.32/1.50  fof(f51,plain,(
% 7.32/1.50    v2_funct_1(sK3)),
% 7.32/1.50    inference(cnf_transformation,[],[f32])).
% 7.32/1.50  
% 7.32/1.50  fof(f50,plain,(
% 7.32/1.50    v1_funct_1(sK4)),
% 7.32/1.50    inference(cnf_transformation,[],[f32])).
% 7.32/1.50  
% 7.32/1.50  fof(f49,plain,(
% 7.32/1.50    v1_relat_1(sK4)),
% 7.32/1.50    inference(cnf_transformation,[],[f32])).
% 7.32/1.50  
% 7.32/1.50  fof(f48,plain,(
% 7.32/1.50    v1_funct_1(sK3)),
% 7.32/1.50    inference(cnf_transformation,[],[f32])).
% 7.32/1.50  
% 7.32/1.50  fof(f47,plain,(
% 7.32/1.50    v1_relat_1(sK3)),
% 7.32/1.50    inference(cnf_transformation,[],[f32])).
% 7.32/1.50  
% 7.32/1.50  cnf(c_856,plain,
% 7.32/1.50      ( X0_44 != X1_44 | X2_44 != X1_44 | X2_44 = X0_44 ),
% 7.32/1.50      theory(equality) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_12157,plain,
% 7.32/1.50      ( X0_44 != X1_44
% 7.32/1.50      | X0_44 = k1_funct_1(X0_42,X2_44)
% 7.32/1.50      | k1_funct_1(X0_42,X2_44) != X1_44 ),
% 7.32/1.50      inference(instantiation,[status(thm)],[c_856]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_27399,plain,
% 7.32/1.50      ( X0_44 != sK2(sK4,k2_funct_1(sK3))
% 7.32/1.50      | X0_44 = k1_funct_1(sK3,k1_funct_1(sK4,sK2(sK4,k2_funct_1(sK3))))
% 7.32/1.50      | k1_funct_1(sK3,k1_funct_1(sK4,sK2(sK4,k2_funct_1(sK3)))) != sK2(sK4,k2_funct_1(sK3)) ),
% 7.32/1.50      inference(instantiation,[status(thm)],[c_12157]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_35193,plain,
% 7.32/1.50      ( k1_funct_1(X0_42,k1_funct_1(k2_funct_1(X0_42),sK2(sK4,k2_funct_1(sK3)))) != sK2(sK4,k2_funct_1(sK3))
% 7.32/1.50      | k1_funct_1(X0_42,k1_funct_1(k2_funct_1(X0_42),sK2(sK4,k2_funct_1(sK3)))) = k1_funct_1(sK3,k1_funct_1(sK4,sK2(sK4,k2_funct_1(sK3))))
% 7.32/1.50      | k1_funct_1(sK3,k1_funct_1(sK4,sK2(sK4,k2_funct_1(sK3)))) != sK2(sK4,k2_funct_1(sK3)) ),
% 7.32/1.50      inference(instantiation,[status(thm)],[c_27399]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_35194,plain,
% 7.32/1.50      ( k1_funct_1(sK3,k1_funct_1(k2_funct_1(sK3),sK2(sK4,k2_funct_1(sK3)))) != sK2(sK4,k2_funct_1(sK3))
% 7.32/1.50      | k1_funct_1(sK3,k1_funct_1(k2_funct_1(sK3),sK2(sK4,k2_funct_1(sK3)))) = k1_funct_1(sK3,k1_funct_1(sK4,sK2(sK4,k2_funct_1(sK3))))
% 7.32/1.50      | k1_funct_1(sK3,k1_funct_1(sK4,sK2(sK4,k2_funct_1(sK3)))) != sK2(sK4,k2_funct_1(sK3)) ),
% 7.32/1.50      inference(instantiation,[status(thm)],[c_35193]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_853,plain,( X0_44 = X0_44 ),theory(equality) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_12200,plain,
% 7.32/1.50      ( k1_funct_1(k2_funct_1(sK3),sK2(sK4,k2_funct_1(sK3))) = k1_funct_1(k2_funct_1(sK3),sK2(sK4,k2_funct_1(sK3))) ),
% 7.32/1.50      inference(instantiation,[status(thm)],[c_853]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_862,plain,
% 7.32/1.50      ( ~ r2_hidden(X0_44,X0_43)
% 7.32/1.50      | r2_hidden(X1_44,X1_43)
% 7.32/1.50      | X1_44 != X0_44
% 7.32/1.50      | X1_43 != X0_43 ),
% 7.32/1.50      theory(equality) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_1370,plain,
% 7.32/1.50      ( ~ r2_hidden(X0_44,X0_43)
% 7.32/1.50      | r2_hidden(X1_44,k1_relat_1(X0_42))
% 7.32/1.50      | X1_44 != X0_44
% 7.32/1.50      | k1_relat_1(X0_42) != X0_43 ),
% 7.32/1.50      inference(instantiation,[status(thm)],[c_862]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_1517,plain,
% 7.32/1.50      ( r2_hidden(X0_44,k1_relat_1(X0_42))
% 7.32/1.50      | ~ r2_hidden(k1_funct_1(X1_42,X1_44),k2_relat_1(X1_42))
% 7.32/1.50      | X0_44 != k1_funct_1(X1_42,X1_44)
% 7.32/1.50      | k1_relat_1(X0_42) != k2_relat_1(X1_42) ),
% 7.32/1.50      inference(instantiation,[status(thm)],[c_1370]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_1916,plain,
% 7.32/1.50      ( r2_hidden(X0_44,k1_relat_1(sK3))
% 7.32/1.50      | ~ r2_hidden(k1_funct_1(k2_funct_1(X0_42),X1_44),k2_relat_1(k2_funct_1(X0_42)))
% 7.32/1.50      | X0_44 != k1_funct_1(k2_funct_1(X0_42),X1_44)
% 7.32/1.50      | k1_relat_1(sK3) != k2_relat_1(k2_funct_1(X0_42)) ),
% 7.32/1.50      inference(instantiation,[status(thm)],[c_1517]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_3069,plain,
% 7.32/1.50      ( ~ r2_hidden(k1_funct_1(k2_funct_1(X0_42),X0_44),k2_relat_1(k2_funct_1(X0_42)))
% 7.32/1.50      | r2_hidden(k1_funct_1(k2_funct_1(X0_42),X0_44),k1_relat_1(sK3))
% 7.32/1.50      | k1_funct_1(k2_funct_1(X0_42),X0_44) != k1_funct_1(k2_funct_1(X0_42),X0_44)
% 7.32/1.50      | k1_relat_1(sK3) != k2_relat_1(k2_funct_1(X0_42)) ),
% 7.32/1.50      inference(instantiation,[status(thm)],[c_1916]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_6101,plain,
% 7.32/1.50      ( ~ r2_hidden(k1_funct_1(k2_funct_1(sK3),sK2(sK4,k2_funct_1(sK3))),k2_relat_1(k2_funct_1(sK3)))
% 7.32/1.50      | r2_hidden(k1_funct_1(k2_funct_1(sK3),sK2(sK4,k2_funct_1(sK3))),k1_relat_1(sK3))
% 7.32/1.50      | k1_funct_1(k2_funct_1(sK3),sK2(sK4,k2_funct_1(sK3))) != k1_funct_1(k2_funct_1(sK3),sK2(sK4,k2_funct_1(sK3)))
% 7.32/1.50      | k1_relat_1(sK3) != k2_relat_1(k2_funct_1(sK3)) ),
% 7.32/1.50      inference(instantiation,[status(thm)],[c_3069]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_1748,plain,
% 7.32/1.50      ( r2_hidden(X0_44,X0_43)
% 7.32/1.50      | ~ r2_hidden(sK2(sK4,k2_funct_1(sK3)),k1_relat_1(sK4))
% 7.32/1.50      | X0_44 != sK2(sK4,k2_funct_1(sK3))
% 7.32/1.50      | X0_43 != k1_relat_1(sK4) ),
% 7.32/1.50      inference(instantiation,[status(thm)],[c_862]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_2207,plain,
% 7.32/1.50      ( r2_hidden(X0_44,k2_relat_1(sK3))
% 7.32/1.50      | ~ r2_hidden(sK2(sK4,k2_funct_1(sK3)),k1_relat_1(sK4))
% 7.32/1.50      | X0_44 != sK2(sK4,k2_funct_1(sK3))
% 7.32/1.50      | k2_relat_1(sK3) != k1_relat_1(sK4) ),
% 7.32/1.50      inference(instantiation,[status(thm)],[c_1748]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_3438,plain,
% 7.32/1.50      ( r2_hidden(sK2(sK4,k2_funct_1(sK3)),k2_relat_1(sK3))
% 7.32/1.50      | ~ r2_hidden(sK2(sK4,k2_funct_1(sK3)),k1_relat_1(sK4))
% 7.32/1.50      | sK2(sK4,k2_funct_1(sK3)) != sK2(sK4,k2_funct_1(sK3))
% 7.32/1.50      | k2_relat_1(sK3) != k1_relat_1(sK4) ),
% 7.32/1.50      inference(instantiation,[status(thm)],[c_2207]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_7,plain,
% 7.32/1.50      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 7.32/1.50      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 7.32/1.50      | ~ v1_relat_1(X1)
% 7.32/1.50      | ~ v1_funct_1(X1) ),
% 7.32/1.50      inference(cnf_transformation,[],[f40]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_842,plain,
% 7.32/1.50      ( ~ r2_hidden(X0_44,k1_relat_1(X0_42))
% 7.32/1.50      | r2_hidden(k1_funct_1(X0_42,X0_44),k2_relat_1(X0_42))
% 7.32/1.50      | ~ v1_relat_1(X0_42)
% 7.32/1.50      | ~ v1_funct_1(X0_42) ),
% 7.32/1.50      inference(subtyping,[status(esa)],[c_7]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_1804,plain,
% 7.32/1.50      ( ~ r2_hidden(X0_44,k1_relat_1(k2_funct_1(sK3)))
% 7.32/1.50      | r2_hidden(k1_funct_1(k2_funct_1(sK3),X0_44),k2_relat_1(k2_funct_1(sK3)))
% 7.32/1.50      | ~ v1_relat_1(k2_funct_1(sK3))
% 7.32/1.50      | ~ v1_funct_1(k2_funct_1(sK3)) ),
% 7.32/1.50      inference(instantiation,[status(thm)],[c_842]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_2735,plain,
% 7.32/1.50      ( ~ r2_hidden(sK2(sK4,k2_funct_1(sK3)),k1_relat_1(k2_funct_1(sK3)))
% 7.32/1.50      | r2_hidden(k1_funct_1(k2_funct_1(sK3),sK2(sK4,k2_funct_1(sK3))),k2_relat_1(k2_funct_1(sK3)))
% 7.32/1.50      | ~ v1_relat_1(k2_funct_1(sK3))
% 7.32/1.50      | ~ v1_funct_1(k2_funct_1(sK3)) ),
% 7.32/1.50      inference(instantiation,[status(thm)],[c_1804]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_2724,plain,
% 7.32/1.50      ( k1_funct_1(sK4,sK2(sK4,k2_funct_1(sK3))) = k1_funct_1(sK4,sK2(sK4,k2_funct_1(sK3))) ),
% 7.32/1.50      inference(instantiation,[status(thm)],[c_853]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_11,plain,
% 7.32/1.50      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 7.32/1.50      | ~ v1_relat_1(X1)
% 7.32/1.50      | ~ v1_funct_1(X1)
% 7.32/1.50      | ~ v2_funct_1(X1)
% 7.32/1.50      | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 ),
% 7.32/1.50      inference(cnf_transformation,[],[f43]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_838,plain,
% 7.32/1.50      ( ~ r2_hidden(X0_44,k2_relat_1(X0_42))
% 7.32/1.50      | ~ v1_relat_1(X0_42)
% 7.32/1.50      | ~ v1_funct_1(X0_42)
% 7.32/1.50      | ~ v2_funct_1(X0_42)
% 7.32/1.50      | k1_funct_1(X0_42,k1_funct_1(k2_funct_1(X0_42),X0_44)) = X0_44 ),
% 7.32/1.50      inference(subtyping,[status(esa)],[c_11]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_2388,plain,
% 7.32/1.50      ( ~ r2_hidden(sK2(sK4,k2_funct_1(sK3)),k2_relat_1(X0_42))
% 7.32/1.50      | ~ v1_relat_1(X0_42)
% 7.32/1.50      | ~ v1_funct_1(X0_42)
% 7.32/1.50      | ~ v2_funct_1(X0_42)
% 7.32/1.50      | k1_funct_1(X0_42,k1_funct_1(k2_funct_1(X0_42),sK2(sK4,k2_funct_1(sK3)))) = sK2(sK4,k2_funct_1(sK3)) ),
% 7.32/1.50      inference(instantiation,[status(thm)],[c_838]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_2390,plain,
% 7.32/1.50      ( ~ r2_hidden(sK2(sK4,k2_funct_1(sK3)),k2_relat_1(sK3))
% 7.32/1.50      | ~ v1_relat_1(sK3)
% 7.32/1.50      | ~ v1_funct_1(sK3)
% 7.32/1.50      | ~ v2_funct_1(sK3)
% 7.32/1.50      | k1_funct_1(sK3,k1_funct_1(k2_funct_1(sK3),sK2(sK4,k2_funct_1(sK3)))) = sK2(sK4,k2_funct_1(sK3)) ),
% 7.32/1.50      inference(instantiation,[status(thm)],[c_2388]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_1278,plain,
% 7.32/1.50      ( ~ r2_hidden(X0_44,X0_43)
% 7.32/1.50      | r2_hidden(X1_44,k1_relat_1(sK3))
% 7.32/1.50      | X1_44 != X0_44
% 7.32/1.50      | k1_relat_1(sK3) != X0_43 ),
% 7.32/1.50      inference(instantiation,[status(thm)],[c_862]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_1305,plain,
% 7.32/1.50      ( ~ r2_hidden(X0_44,k2_relat_1(sK4))
% 7.32/1.50      | r2_hidden(X1_44,k1_relat_1(sK3))
% 7.32/1.50      | X1_44 != X0_44
% 7.32/1.50      | k1_relat_1(sK3) != k2_relat_1(sK4) ),
% 7.32/1.50      inference(instantiation,[status(thm)],[c_1278]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_1322,plain,
% 7.32/1.50      ( r2_hidden(X0_44,k1_relat_1(sK3))
% 7.32/1.50      | ~ r2_hidden(k1_funct_1(sK4,X1_44),k2_relat_1(sK4))
% 7.32/1.50      | X0_44 != k1_funct_1(sK4,X1_44)
% 7.32/1.50      | k1_relat_1(sK3) != k2_relat_1(sK4) ),
% 7.32/1.50      inference(instantiation,[status(thm)],[c_1305]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_1994,plain,
% 7.32/1.50      ( r2_hidden(X0_44,k1_relat_1(sK3))
% 7.32/1.50      | ~ r2_hidden(k1_funct_1(sK4,sK2(sK4,k2_funct_1(sK3))),k2_relat_1(sK4))
% 7.32/1.50      | X0_44 != k1_funct_1(sK4,sK2(sK4,k2_funct_1(sK3)))
% 7.32/1.50      | k1_relat_1(sK3) != k2_relat_1(sK4) ),
% 7.32/1.50      inference(instantiation,[status(thm)],[c_1322]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_2333,plain,
% 7.32/1.50      ( ~ r2_hidden(k1_funct_1(sK4,sK2(sK4,k2_funct_1(sK3))),k2_relat_1(sK4))
% 7.32/1.50      | r2_hidden(k1_funct_1(sK4,sK2(sK4,k2_funct_1(sK3))),k1_relat_1(sK3))
% 7.32/1.50      | k1_funct_1(sK4,sK2(sK4,k2_funct_1(sK3))) != k1_funct_1(sK4,sK2(sK4,k2_funct_1(sK3)))
% 7.32/1.50      | k1_relat_1(sK3) != k2_relat_1(sK4) ),
% 7.32/1.50      inference(instantiation,[status(thm)],[c_1994]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_2074,plain,
% 7.32/1.50      ( sK2(sK4,k2_funct_1(sK3)) = sK2(sK4,k2_funct_1(sK3)) ),
% 7.32/1.50      inference(instantiation,[status(thm)],[c_853]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_855,plain,
% 7.32/1.50      ( X0_43 != X1_43 | X2_43 != X1_43 | X2_43 = X0_43 ),
% 7.32/1.50      theory(equality) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_1512,plain,
% 7.32/1.50      ( X0_43 != X1_43
% 7.32/1.50      | X0_43 = k1_relat_1(X0_42)
% 7.32/1.50      | k1_relat_1(X0_42) != X1_43 ),
% 7.32/1.50      inference(instantiation,[status(thm)],[c_855]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_1886,plain,
% 7.32/1.50      ( X0_43 != k2_relat_1(sK3)
% 7.32/1.50      | X0_43 = k1_relat_1(sK4)
% 7.32/1.50      | k1_relat_1(sK4) != k2_relat_1(sK3) ),
% 7.32/1.50      inference(instantiation,[status(thm)],[c_1512]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_1973,plain,
% 7.32/1.50      ( k2_relat_1(sK3) != k2_relat_1(sK3)
% 7.32/1.50      | k2_relat_1(sK3) = k1_relat_1(sK4)
% 7.32/1.50      | k1_relat_1(sK4) != k2_relat_1(sK3) ),
% 7.32/1.50      inference(instantiation,[status(thm)],[c_1886]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_1448,plain,
% 7.32/1.50      ( ~ r2_hidden(X0_44,k1_relat_1(sK4))
% 7.32/1.50      | r2_hidden(k1_funct_1(sK4,X0_44),k2_relat_1(sK4))
% 7.32/1.50      | ~ v1_relat_1(sK4)
% 7.32/1.50      | ~ v1_funct_1(sK4) ),
% 7.32/1.50      inference(instantiation,[status(thm)],[c_842]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_1704,plain,
% 7.32/1.50      ( ~ r2_hidden(sK2(sK4,k2_funct_1(sK3)),k1_relat_1(sK4))
% 7.32/1.50      | r2_hidden(k1_funct_1(sK4,sK2(sK4,k2_funct_1(sK3))),k2_relat_1(sK4))
% 7.32/1.50      | ~ v1_relat_1(sK4)
% 7.32/1.50      | ~ v1_funct_1(sK4) ),
% 7.32/1.50      inference(instantiation,[status(thm)],[c_1448]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_1514,plain,
% 7.32/1.50      ( r2_hidden(X0_44,k1_relat_1(X0_42))
% 7.32/1.50      | ~ r2_hidden(sK2(sK4,k2_funct_1(sK3)),k1_relat_1(sK4))
% 7.32/1.50      | X0_44 != sK2(sK4,k2_funct_1(sK3))
% 7.32/1.50      | k1_relat_1(X0_42) != k1_relat_1(sK4) ),
% 7.32/1.50      inference(instantiation,[status(thm)],[c_1370]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_1569,plain,
% 7.32/1.50      ( r2_hidden(X0_44,k1_relat_1(k2_funct_1(sK3)))
% 7.32/1.50      | ~ r2_hidden(sK2(sK4,k2_funct_1(sK3)),k1_relat_1(sK4))
% 7.32/1.50      | X0_44 != sK2(sK4,k2_funct_1(sK3))
% 7.32/1.50      | k1_relat_1(k2_funct_1(sK3)) != k1_relat_1(sK4) ),
% 7.32/1.50      inference(instantiation,[status(thm)],[c_1514]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_1696,plain,
% 7.32/1.50      ( r2_hidden(sK2(sK4,k2_funct_1(sK3)),k1_relat_1(k2_funct_1(sK3)))
% 7.32/1.50      | ~ r2_hidden(sK2(sK4,k2_funct_1(sK3)),k1_relat_1(sK4))
% 7.32/1.50      | sK2(sK4,k2_funct_1(sK3)) != sK2(sK4,k2_funct_1(sK3))
% 7.32/1.50      | k1_relat_1(k2_funct_1(sK3)) != k1_relat_1(sK4) ),
% 7.32/1.50      inference(instantiation,[status(thm)],[c_1569]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_15,negated_conjecture,
% 7.32/1.50      ( ~ r2_hidden(X0,k1_relat_1(sK4))
% 7.32/1.50      | ~ r2_hidden(k1_funct_1(sK4,X0),k1_relat_1(sK3))
% 7.32/1.50      | k1_funct_1(sK3,k1_funct_1(sK4,X0)) = X0 ),
% 7.32/1.50      inference(cnf_transformation,[],[f57]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_834,negated_conjecture,
% 7.32/1.50      ( ~ r2_hidden(X0_44,k1_relat_1(sK4))
% 7.32/1.50      | ~ r2_hidden(k1_funct_1(sK4,X0_44),k1_relat_1(sK3))
% 7.32/1.50      | k1_funct_1(sK3,k1_funct_1(sK4,X0_44)) = X0_44 ),
% 7.32/1.50      inference(subtyping,[status(esa)],[c_15]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_1395,plain,
% 7.32/1.50      ( ~ r2_hidden(sK2(sK4,k2_funct_1(sK3)),k1_relat_1(sK4))
% 7.32/1.50      | ~ r2_hidden(k1_funct_1(sK4,sK2(sK4,k2_funct_1(sK3))),k1_relat_1(sK3))
% 7.32/1.50      | k1_funct_1(sK3,k1_funct_1(sK4,sK2(sK4,k2_funct_1(sK3)))) = sK2(sK4,k2_funct_1(sK3)) ),
% 7.32/1.50      inference(instantiation,[status(thm)],[c_834]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_1313,plain,
% 7.32/1.50      ( X0_43 != X1_43
% 7.32/1.50      | k1_relat_1(sK3) != X1_43
% 7.32/1.50      | k1_relat_1(sK3) = X0_43 ),
% 7.32/1.50      inference(instantiation,[status(thm)],[c_855]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_1360,plain,
% 7.32/1.50      ( X0_43 != k1_relat_1(sK3)
% 7.32/1.50      | k1_relat_1(sK3) = X0_43
% 7.32/1.50      | k1_relat_1(sK3) != k1_relat_1(sK3) ),
% 7.32/1.50      inference(instantiation,[status(thm)],[c_1313]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_1390,plain,
% 7.32/1.50      ( k2_relat_1(k2_funct_1(sK3)) != k1_relat_1(sK3)
% 7.32/1.50      | k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3))
% 7.32/1.50      | k1_relat_1(sK3) != k1_relat_1(sK3) ),
% 7.32/1.50      inference(instantiation,[status(thm)],[c_1360]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_4,plain,
% 7.32/1.50      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 7.32/1.50      | ~ r2_hidden(X2,k1_relat_1(X1))
% 7.32/1.50      | ~ v1_relat_1(X1)
% 7.32/1.50      | ~ v1_funct_1(X1)
% 7.32/1.50      | ~ v2_funct_1(X1)
% 7.32/1.50      | X0 = X2
% 7.32/1.50      | k1_funct_1(X1,X0) != k1_funct_1(X1,X2) ),
% 7.32/1.50      inference(cnf_transformation,[],[f33]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_845,plain,
% 7.32/1.50      ( ~ r2_hidden(X0_44,k1_relat_1(X0_42))
% 7.32/1.50      | ~ r2_hidden(X1_44,k1_relat_1(X0_42))
% 7.32/1.50      | ~ v1_relat_1(X0_42)
% 7.32/1.50      | ~ v1_funct_1(X0_42)
% 7.32/1.50      | ~ v2_funct_1(X0_42)
% 7.32/1.50      | X0_44 = X1_44
% 7.32/1.50      | k1_funct_1(X0_42,X0_44) != k1_funct_1(X0_42,X1_44) ),
% 7.32/1.50      inference(subtyping,[status(esa)],[c_4]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_1378,plain,
% 7.32/1.50      ( ~ r2_hidden(k1_funct_1(k2_funct_1(sK3),sK2(sK4,k2_funct_1(sK3))),k1_relat_1(X0_42))
% 7.32/1.50      | ~ r2_hidden(k1_funct_1(sK4,sK2(sK4,k2_funct_1(sK3))),k1_relat_1(X0_42))
% 7.32/1.50      | ~ v1_relat_1(X0_42)
% 7.32/1.50      | ~ v1_funct_1(X0_42)
% 7.32/1.50      | ~ v2_funct_1(X0_42)
% 7.32/1.50      | k1_funct_1(X0_42,k1_funct_1(k2_funct_1(sK3),sK2(sK4,k2_funct_1(sK3)))) != k1_funct_1(X0_42,k1_funct_1(sK4,sK2(sK4,k2_funct_1(sK3))))
% 7.32/1.50      | k1_funct_1(k2_funct_1(sK3),sK2(sK4,k2_funct_1(sK3))) = k1_funct_1(sK4,sK2(sK4,k2_funct_1(sK3))) ),
% 7.32/1.50      inference(instantiation,[status(thm)],[c_845]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_1380,plain,
% 7.32/1.50      ( ~ r2_hidden(k1_funct_1(k2_funct_1(sK3),sK2(sK4,k2_funct_1(sK3))),k1_relat_1(sK3))
% 7.32/1.50      | ~ r2_hidden(k1_funct_1(sK4,sK2(sK4,k2_funct_1(sK3))),k1_relat_1(sK3))
% 7.32/1.50      | ~ v1_relat_1(sK3)
% 7.32/1.50      | ~ v1_funct_1(sK3)
% 7.32/1.50      | ~ v2_funct_1(sK3)
% 7.32/1.50      | k1_funct_1(k2_funct_1(sK3),sK2(sK4,k2_funct_1(sK3))) = k1_funct_1(sK4,sK2(sK4,k2_funct_1(sK3)))
% 7.32/1.50      | k1_funct_1(sK3,k1_funct_1(k2_funct_1(sK3),sK2(sK4,k2_funct_1(sK3)))) != k1_funct_1(sK3,k1_funct_1(sK4,sK2(sK4,k2_funct_1(sK3)))) ),
% 7.32/1.50      inference(instantiation,[status(thm)],[c_1378]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_1288,plain,
% 7.32/1.50      ( k1_relat_1(k2_funct_1(sK3)) != X0_43
% 7.32/1.50      | k1_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK4)
% 7.32/1.50      | k1_relat_1(sK4) != X0_43 ),
% 7.32/1.50      inference(instantiation,[status(thm)],[c_855]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_1346,plain,
% 7.32/1.50      ( k1_relat_1(k2_funct_1(sK3)) != k2_relat_1(sK3)
% 7.32/1.50      | k1_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK4)
% 7.32/1.50      | k1_relat_1(sK4) != k2_relat_1(sK3) ),
% 7.32/1.50      inference(instantiation,[status(thm)],[c_1288]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_12,plain,
% 7.32/1.50      ( ~ v1_relat_1(X0)
% 7.32/1.50      | ~ v1_relat_1(X1)
% 7.32/1.50      | ~ v1_funct_1(X0)
% 7.32/1.50      | ~ v1_funct_1(X1)
% 7.32/1.50      | X1 = X0
% 7.32/1.50      | k1_funct_1(X1,sK2(X0,X1)) != k1_funct_1(X0,sK2(X0,X1))
% 7.32/1.50      | k1_relat_1(X1) != k1_relat_1(X0) ),
% 7.32/1.50      inference(cnf_transformation,[],[f46]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_837,plain,
% 7.32/1.50      ( ~ v1_relat_1(X0_42)
% 7.32/1.50      | ~ v1_relat_1(X1_42)
% 7.32/1.50      | ~ v1_funct_1(X0_42)
% 7.32/1.50      | ~ v1_funct_1(X1_42)
% 7.32/1.50      | k1_funct_1(X1_42,sK2(X0_42,X1_42)) != k1_funct_1(X0_42,sK2(X0_42,X1_42))
% 7.32/1.50      | k1_relat_1(X1_42) != k1_relat_1(X0_42)
% 7.32/1.50      | X1_42 = X0_42 ),
% 7.32/1.50      inference(subtyping,[status(esa)],[c_12]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_1270,plain,
% 7.32/1.50      ( ~ v1_relat_1(k2_funct_1(sK3))
% 7.32/1.50      | ~ v1_relat_1(sK4)
% 7.32/1.50      | ~ v1_funct_1(k2_funct_1(sK3))
% 7.32/1.50      | ~ v1_funct_1(sK4)
% 7.32/1.50      | k1_funct_1(k2_funct_1(sK3),sK2(sK4,k2_funct_1(sK3))) != k1_funct_1(sK4,sK2(sK4,k2_funct_1(sK3)))
% 7.32/1.50      | k1_relat_1(k2_funct_1(sK3)) != k1_relat_1(sK4)
% 7.32/1.50      | k2_funct_1(sK3) = sK4 ),
% 7.32/1.50      inference(instantiation,[status(thm)],[c_837]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_13,plain,
% 7.32/1.50      ( r2_hidden(sK2(X0,X1),k1_relat_1(X0))
% 7.32/1.50      | ~ v1_relat_1(X0)
% 7.32/1.50      | ~ v1_relat_1(X1)
% 7.32/1.50      | ~ v1_funct_1(X0)
% 7.32/1.50      | ~ v1_funct_1(X1)
% 7.32/1.50      | X1 = X0
% 7.32/1.50      | k1_relat_1(X1) != k1_relat_1(X0) ),
% 7.32/1.50      inference(cnf_transformation,[],[f45]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_836,plain,
% 7.32/1.50      ( r2_hidden(sK2(X0_42,X1_42),k1_relat_1(X0_42))
% 7.32/1.50      | ~ v1_relat_1(X0_42)
% 7.32/1.50      | ~ v1_relat_1(X1_42)
% 7.32/1.50      | ~ v1_funct_1(X0_42)
% 7.32/1.50      | ~ v1_funct_1(X1_42)
% 7.32/1.50      | k1_relat_1(X1_42) != k1_relat_1(X0_42)
% 7.32/1.50      | X1_42 = X0_42 ),
% 7.32/1.50      inference(subtyping,[status(esa)],[c_13]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_1271,plain,
% 7.32/1.50      ( r2_hidden(sK2(sK4,k2_funct_1(sK3)),k1_relat_1(sK4))
% 7.32/1.50      | ~ v1_relat_1(k2_funct_1(sK3))
% 7.32/1.50      | ~ v1_relat_1(sK4)
% 7.32/1.50      | ~ v1_funct_1(k2_funct_1(sK3))
% 7.32/1.50      | ~ v1_funct_1(sK4)
% 7.32/1.50      | k1_relat_1(k2_funct_1(sK3)) != k1_relat_1(sK4)
% 7.32/1.50      | k2_funct_1(sK3) = sK4 ),
% 7.32/1.50      inference(instantiation,[status(thm)],[c_836]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_18,negated_conjecture,
% 7.32/1.50      ( k1_relat_1(sK3) = k2_relat_1(sK4) ),
% 7.32/1.50      inference(cnf_transformation,[],[f52]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_831,negated_conjecture,
% 7.32/1.50      ( k1_relat_1(sK3) = k2_relat_1(sK4) ),
% 7.32/1.50      inference(subtyping,[status(esa)],[c_18]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_17,negated_conjecture,
% 7.32/1.50      ( k1_relat_1(sK4) = k2_relat_1(sK3) ),
% 7.32/1.50      inference(cnf_transformation,[],[f53]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_832,negated_conjecture,
% 7.32/1.50      ( k1_relat_1(sK4) = k2_relat_1(sK3) ),
% 7.32/1.50      inference(subtyping,[status(esa)],[c_17]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_14,negated_conjecture,
% 7.32/1.50      ( k2_funct_1(sK3) != sK4 ),
% 7.32/1.50      inference(cnf_transformation,[],[f56]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_835,negated_conjecture,
% 7.32/1.50      ( k2_funct_1(sK3) != sK4 ),
% 7.32/1.50      inference(subtyping,[status(esa)],[c_14]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_9,plain,
% 7.32/1.50      ( ~ v1_relat_1(X0)
% 7.32/1.50      | ~ v1_funct_1(X0)
% 7.32/1.50      | ~ v2_funct_1(X0)
% 7.32/1.50      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 7.32/1.50      inference(cnf_transformation,[],[f41]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_840,plain,
% 7.32/1.50      ( ~ v1_relat_1(X0_42)
% 7.32/1.50      | ~ v1_funct_1(X0_42)
% 7.32/1.50      | ~ v2_funct_1(X0_42)
% 7.32/1.50      | k1_relat_1(k2_funct_1(X0_42)) = k2_relat_1(X0_42) ),
% 7.32/1.50      inference(subtyping,[status(esa)],[c_9]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_893,plain,
% 7.32/1.50      ( ~ v1_relat_1(sK3)
% 7.32/1.50      | ~ v1_funct_1(sK3)
% 7.32/1.50      | ~ v2_funct_1(sK3)
% 7.32/1.50      | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 7.32/1.50      inference(instantiation,[status(thm)],[c_840]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_8,plain,
% 7.32/1.50      ( ~ v1_relat_1(X0)
% 7.32/1.50      | ~ v1_funct_1(X0)
% 7.32/1.50      | ~ v2_funct_1(X0)
% 7.32/1.50      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 7.32/1.50      inference(cnf_transformation,[],[f42]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_841,plain,
% 7.32/1.50      ( ~ v1_relat_1(X0_42)
% 7.32/1.50      | ~ v1_funct_1(X0_42)
% 7.32/1.50      | ~ v2_funct_1(X0_42)
% 7.32/1.50      | k2_relat_1(k2_funct_1(X0_42)) = k1_relat_1(X0_42) ),
% 7.32/1.50      inference(subtyping,[status(esa)],[c_8]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_890,plain,
% 7.32/1.50      ( ~ v1_relat_1(sK3)
% 7.32/1.50      | ~ v1_funct_1(sK3)
% 7.32/1.50      | ~ v2_funct_1(sK3)
% 7.32/1.50      | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 7.32/1.50      inference(instantiation,[status(thm)],[c_841]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_851,plain,( X0_42 = X0_42 ),theory(equality) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_876,plain,
% 7.32/1.50      ( sK3 = sK3 ),
% 7.32/1.50      inference(instantiation,[status(thm)],[c_851]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_864,plain,
% 7.32/1.50      ( k2_relat_1(X0_42) = k2_relat_1(X1_42) | X0_42 != X1_42 ),
% 7.32/1.50      theory(equality) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_873,plain,
% 7.32/1.50      ( k2_relat_1(sK3) = k2_relat_1(sK3) | sK3 != sK3 ),
% 7.32/1.50      inference(instantiation,[status(thm)],[c_864]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_861,plain,
% 7.32/1.50      ( k1_relat_1(X0_42) = k1_relat_1(X1_42) | X0_42 != X1_42 ),
% 7.32/1.50      theory(equality) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_870,plain,
% 7.32/1.50      ( k1_relat_1(sK3) = k1_relat_1(sK3) | sK3 != sK3 ),
% 7.32/1.50      inference(instantiation,[status(thm)],[c_861]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_5,plain,
% 7.32/1.50      ( ~ v1_relat_1(X0)
% 7.32/1.50      | ~ v1_funct_1(X0)
% 7.32/1.50      | v1_funct_1(k2_funct_1(X0)) ),
% 7.32/1.50      inference(cnf_transformation,[],[f39]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_60,plain,
% 7.32/1.50      ( ~ v1_relat_1(sK3)
% 7.32/1.50      | v1_funct_1(k2_funct_1(sK3))
% 7.32/1.50      | ~ v1_funct_1(sK3) ),
% 7.32/1.50      inference(instantiation,[status(thm)],[c_5]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_6,plain,
% 7.32/1.50      ( ~ v1_relat_1(X0)
% 7.32/1.50      | v1_relat_1(k2_funct_1(X0))
% 7.32/1.50      | ~ v1_funct_1(X0) ),
% 7.32/1.50      inference(cnf_transformation,[],[f38]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_57,plain,
% 7.32/1.50      ( v1_relat_1(k2_funct_1(sK3))
% 7.32/1.50      | ~ v1_relat_1(sK3)
% 7.32/1.50      | ~ v1_funct_1(sK3) ),
% 7.32/1.50      inference(instantiation,[status(thm)],[c_6]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_19,negated_conjecture,
% 7.32/1.50      ( v2_funct_1(sK3) ),
% 7.32/1.50      inference(cnf_transformation,[],[f51]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_20,negated_conjecture,
% 7.32/1.50      ( v1_funct_1(sK4) ),
% 7.32/1.50      inference(cnf_transformation,[],[f50]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_21,negated_conjecture,
% 7.32/1.50      ( v1_relat_1(sK4) ),
% 7.32/1.50      inference(cnf_transformation,[],[f49]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_22,negated_conjecture,
% 7.32/1.50      ( v1_funct_1(sK3) ),
% 7.32/1.50      inference(cnf_transformation,[],[f48]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_23,negated_conjecture,
% 7.32/1.50      ( v1_relat_1(sK3) ),
% 7.32/1.50      inference(cnf_transformation,[],[f47]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(contradiction,plain,
% 7.32/1.50      ( $false ),
% 7.32/1.50      inference(minisat,
% 7.32/1.50                [status(thm)],
% 7.32/1.50                [c_35194,c_12200,c_6101,c_3438,c_2735,c_2724,c_2390,
% 7.32/1.50                 c_2333,c_2074,c_1973,c_1704,c_1696,c_1395,c_1390,c_1380,
% 7.32/1.50                 c_1346,c_1270,c_1271,c_831,c_832,c_835,c_893,c_890,
% 7.32/1.50                 c_876,c_873,c_870,c_60,c_57,c_19,c_20,c_21,c_22,c_23]) ).
% 7.32/1.50  
% 7.32/1.50  
% 7.32/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.32/1.50  
% 7.32/1.50  ------                               Statistics
% 7.32/1.50  
% 7.32/1.50  ------ General
% 7.32/1.50  
% 7.32/1.50  abstr_ref_over_cycles:                  0
% 7.32/1.50  abstr_ref_under_cycles:                 0
% 7.32/1.50  gc_basic_clause_elim:                   0
% 7.32/1.50  forced_gc_time:                         0
% 7.32/1.50  parsing_time:                           0.008
% 7.32/1.50  unif_index_cands_time:                  0.
% 7.32/1.50  unif_index_add_time:                    0.
% 7.32/1.50  orderings_time:                         0.
% 7.32/1.50  out_proof_time:                         0.009
% 7.32/1.50  total_time:                             0.994
% 7.32/1.50  num_of_symbols:                         48
% 7.32/1.50  num_of_terms:                           12257
% 7.32/1.50  
% 7.32/1.50  ------ Preprocessing
% 7.32/1.50  
% 7.32/1.50  num_of_splits:                          0
% 7.32/1.50  num_of_split_atoms:                     0
% 7.32/1.50  num_of_reused_defs:                     0
% 7.32/1.50  num_eq_ax_congr_red:                    10
% 7.32/1.50  num_of_sem_filtered_clauses:            1
% 7.32/1.50  num_of_subtypes:                        3
% 7.32/1.50  monotx_restored_types:                  0
% 7.32/1.50  sat_num_of_epr_types:                   0
% 7.32/1.50  sat_num_of_non_cyclic_types:            0
% 7.32/1.50  sat_guarded_non_collapsed_types:        2
% 7.32/1.50  num_pure_diseq_elim:                    0
% 7.32/1.50  simp_replaced_by:                       0
% 7.32/1.50  res_preprocessed:                       103
% 7.32/1.50  prep_upred:                             0
% 7.32/1.50  prep_unflattend:                        17
% 7.32/1.50  smt_new_axioms:                         0
% 7.32/1.50  pred_elim_cands:                        4
% 7.32/1.50  pred_elim:                              0
% 7.32/1.50  pred_elim_cl:                           0
% 7.32/1.50  pred_elim_cycles:                       1
% 7.32/1.50  merged_defs:                            0
% 7.32/1.50  merged_defs_ncl:                        0
% 7.32/1.50  bin_hyper_res:                          0
% 7.32/1.50  prep_cycles:                            3
% 7.32/1.50  pred_elim_time:                         0.011
% 7.32/1.50  splitting_time:                         0.
% 7.32/1.50  sem_filter_time:                        0.
% 7.32/1.50  monotx_time:                            0.
% 7.32/1.50  subtype_inf_time:                       0.
% 7.32/1.50  
% 7.32/1.50  ------ Problem properties
% 7.32/1.50  
% 7.32/1.50  clauses:                                24
% 7.32/1.50  conjectures:                            10
% 7.32/1.50  epr:                                    5
% 7.32/1.50  horn:                                   20
% 7.32/1.50  ground:                                 8
% 7.32/1.50  unary:                                  8
% 7.32/1.50  binary:                                 0
% 7.32/1.50  lits:                                   79
% 7.32/1.50  lits_eq:                                18
% 7.32/1.50  fd_pure:                                0
% 7.32/1.50  fd_pseudo:                              0
% 7.32/1.50  fd_cond:                                0
% 7.32/1.50  fd_pseudo_cond:                         3
% 7.32/1.50  ac_symbols:                             0
% 7.32/1.50  
% 7.32/1.50  ------ Propositional Solver
% 7.32/1.50  
% 7.32/1.50  prop_solver_calls:                      30
% 7.32/1.50  prop_fast_solver_calls:                 2070
% 7.32/1.50  smt_solver_calls:                       0
% 7.32/1.50  smt_fast_solver_calls:                  0
% 7.32/1.50  prop_num_of_clauses:                    9903
% 7.32/1.50  prop_preprocess_simplified:             25319
% 7.32/1.50  prop_fo_subsumed:                       228
% 7.32/1.50  prop_solver_time:                       0.
% 7.32/1.50  smt_solver_time:                        0.
% 7.32/1.50  smt_fast_solver_time:                   0.
% 7.32/1.50  prop_fast_solver_time:                  0.
% 7.32/1.50  prop_unsat_core_time:                   0.001
% 7.32/1.50  
% 7.32/1.50  ------ QBF
% 7.32/1.50  
% 7.32/1.50  qbf_q_res:                              0
% 7.32/1.50  qbf_num_tautologies:                    0
% 7.32/1.50  qbf_prep_cycles:                        0
% 7.32/1.50  
% 7.32/1.50  ------ BMC1
% 7.32/1.50  
% 7.32/1.50  bmc1_current_bound:                     -1
% 7.32/1.50  bmc1_last_solved_bound:                 -1
% 7.32/1.50  bmc1_unsat_core_size:                   -1
% 7.32/1.50  bmc1_unsat_core_parents_size:           -1
% 7.32/1.50  bmc1_merge_next_fun:                    0
% 7.32/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.32/1.50  
% 7.32/1.50  ------ Instantiation
% 7.32/1.50  
% 7.32/1.50  inst_num_of_clauses:                    3536
% 7.32/1.50  inst_num_in_passive:                    1810
% 7.32/1.50  inst_num_in_active:                     1628
% 7.32/1.50  inst_num_in_unprocessed:                97
% 7.32/1.50  inst_num_of_loops:                      1690
% 7.32/1.50  inst_num_of_learning_restarts:          0
% 7.32/1.50  inst_num_moves_active_passive:          56
% 7.32/1.50  inst_lit_activity:                      0
% 7.32/1.50  inst_lit_activity_moves:                0
% 7.32/1.50  inst_num_tautologies:                   0
% 7.32/1.50  inst_num_prop_implied:                  0
% 7.32/1.50  inst_num_existing_simplified:           0
% 7.32/1.50  inst_num_eq_res_simplified:             0
% 7.32/1.50  inst_num_child_elim:                    0
% 7.32/1.50  inst_num_of_dismatching_blockings:      4214
% 7.32/1.50  inst_num_of_non_proper_insts:           7232
% 7.32/1.50  inst_num_of_duplicates:                 0
% 7.32/1.50  inst_inst_num_from_inst_to_res:         0
% 7.32/1.50  inst_dismatching_checking_time:         0.
% 7.32/1.50  
% 7.32/1.50  ------ Resolution
% 7.32/1.50  
% 7.32/1.50  res_num_of_clauses:                     0
% 7.32/1.50  res_num_in_passive:                     0
% 7.32/1.50  res_num_in_active:                      0
% 7.32/1.50  res_num_of_loops:                       106
% 7.32/1.50  res_forward_subset_subsumed:            352
% 7.32/1.50  res_backward_subset_subsumed:           0
% 7.32/1.50  res_forward_subsumed:                   0
% 7.32/1.50  res_backward_subsumed:                  0
% 7.32/1.50  res_forward_subsumption_resolution:     0
% 7.32/1.50  res_backward_subsumption_resolution:    0
% 7.32/1.50  res_clause_to_clause_subsumption:       3588
% 7.32/1.50  res_orphan_elimination:                 0
% 7.32/1.50  res_tautology_del:                      881
% 7.32/1.50  res_num_eq_res_simplified:              0
% 7.32/1.50  res_num_sel_changes:                    0
% 7.32/1.50  res_moves_from_active_to_pass:          0
% 7.32/1.50  
% 7.32/1.50  ------ Superposition
% 7.32/1.50  
% 7.32/1.50  sup_time_total:                         0.
% 7.32/1.50  sup_time_generating:                    0.
% 7.32/1.50  sup_time_sim_full:                      0.
% 7.32/1.50  sup_time_sim_immed:                     0.
% 7.32/1.50  
% 7.32/1.50  sup_num_of_clauses:                     845
% 7.32/1.50  sup_num_in_active:                      334
% 7.32/1.50  sup_num_in_passive:                     511
% 7.32/1.50  sup_num_of_loops:                       336
% 7.32/1.50  sup_fw_superposition:                   950
% 7.32/1.50  sup_bw_superposition:                   206
% 7.32/1.50  sup_immediate_simplified:               232
% 7.32/1.50  sup_given_eliminated:                   0
% 7.32/1.50  comparisons_done:                       0
% 7.32/1.50  comparisons_avoided:                    18
% 7.32/1.50  
% 7.32/1.50  ------ Simplifications
% 7.32/1.50  
% 7.32/1.50  
% 7.32/1.50  sim_fw_subset_subsumed:                 205
% 7.32/1.50  sim_bw_subset_subsumed:                 8
% 7.32/1.50  sim_fw_subsumed:                        11
% 7.32/1.50  sim_bw_subsumed:                        0
% 7.32/1.50  sim_fw_subsumption_res:                 0
% 7.32/1.50  sim_bw_subsumption_res:                 0
% 7.32/1.50  sim_tautology_del:                      94
% 7.32/1.50  sim_eq_tautology_del:                   13
% 7.32/1.50  sim_eq_res_simp:                        0
% 7.32/1.50  sim_fw_demodulated:                     0
% 7.32/1.50  sim_bw_demodulated:                     0
% 7.32/1.50  sim_light_normalised:                   10
% 7.32/1.50  sim_joinable_taut:                      0
% 7.32/1.50  sim_joinable_simp:                      0
% 7.32/1.50  sim_ac_normalised:                      0
% 7.32/1.50  sim_smt_subsumption:                    0
% 7.32/1.50  
%------------------------------------------------------------------------------
