%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:52:06 EST 2020

% Result     : Theorem 7.38s
% Output     : CNFRefutation 7.38s
% Verified   : 
% Statistics : Number of formulae       :  129 (1082 expanded)
%              Number of clauses        :   77 ( 250 expanded)
%              Number of leaves         :   14 ( 367 expanded)
%              Depth                    :   21
%              Number of atoms          :  607 (10250 expanded)
%              Number of equality atoms :  321 (5151 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_relat_1(X3) )
             => ( ( k5_relat_1(X1,X2) = k5_relat_1(X1,X3)
                  & k1_relat_1(X3) = X0
                  & k1_relat_1(X2) = X0
                  & k2_relat_1(X1) = X0 )
               => X2 = X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ! [X3] :
                ( ( v1_funct_1(X3)
                  & v1_relat_1(X3) )
               => ( ( k5_relat_1(X1,X2) = k5_relat_1(X1,X3)
                    & k1_relat_1(X3) = X0
                    & k1_relat_1(X2) = X0
                    & k2_relat_1(X1) = X0 )
                 => X2 = X3 ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( X2 != X3
              & k5_relat_1(X1,X2) = k5_relat_1(X1,X3)
              & k1_relat_1(X3) = X0
              & k1_relat_1(X2) = X0
              & k2_relat_1(X1) = X0
              & v1_funct_1(X3)
              & v1_relat_1(X3) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( X2 != X3
              & k5_relat_1(X1,X2) = k5_relat_1(X1,X3)
              & k1_relat_1(X3) = X0
              & k1_relat_1(X2) = X0
              & k2_relat_1(X1) = X0
              & v1_funct_1(X3)
              & v1_relat_1(X3) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( X2 != X3
          & k5_relat_1(X1,X2) = k5_relat_1(X1,X3)
          & k1_relat_1(X3) = X0
          & k1_relat_1(X2) = X0
          & k2_relat_1(X1) = X0
          & v1_funct_1(X3)
          & v1_relat_1(X3) )
     => ( sK7 != X2
        & k5_relat_1(X1,sK7) = k5_relat_1(X1,X2)
        & k1_relat_1(sK7) = X0
        & k1_relat_1(X2) = X0
        & k2_relat_1(X1) = X0
        & v1_funct_1(sK7)
        & v1_relat_1(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( X2 != X3
              & k5_relat_1(X1,X2) = k5_relat_1(X1,X3)
              & k1_relat_1(X3) = X0
              & k1_relat_1(X2) = X0
              & k2_relat_1(X1) = X0
              & v1_funct_1(X3)
              & v1_relat_1(X3) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( ? [X3] :
            ( sK6 != X3
            & k5_relat_1(X1,sK6) = k5_relat_1(X1,X3)
            & k1_relat_1(X3) = X0
            & k1_relat_1(sK6) = X0
            & k2_relat_1(X1) = X0
            & v1_funct_1(X3)
            & v1_relat_1(X3) )
        & v1_funct_1(sK6)
        & v1_relat_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( X2 != X3
                & k5_relat_1(X1,X2) = k5_relat_1(X1,X3)
                & k1_relat_1(X3) = X0
                & k1_relat_1(X2) = X0
                & k2_relat_1(X1) = X0
                & v1_funct_1(X3)
                & v1_relat_1(X3) )
            & v1_funct_1(X2)
            & v1_relat_1(X2) )
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( X2 != X3
              & k5_relat_1(sK5,X2) = k5_relat_1(sK5,X3)
              & k1_relat_1(X3) = sK4
              & k1_relat_1(X2) = sK4
              & k2_relat_1(sK5) = sK4
              & v1_funct_1(X3)
              & v1_relat_1(X3) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(sK5)
      & v1_relat_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( sK6 != sK7
    & k5_relat_1(sK5,sK6) = k5_relat_1(sK5,sK7)
    & k1_relat_1(sK7) = sK4
    & k1_relat_1(sK6) = sK4
    & k2_relat_1(sK5) = sK4
    & v1_funct_1(sK7)
    & v1_relat_1(sK7)
    & v1_funct_1(sK6)
    & v1_relat_1(sK6)
    & v1_funct_1(sK5)
    & v1_relat_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f16,f29,f28,f27])).

fof(f51,plain,(
    k1_relat_1(sK7) = sK4 ),
    inference(cnf_transformation,[],[f30])).

fof(f50,plain,(
    k1_relat_1(sK6) = sK4 ),
    inference(cnf_transformation,[],[f30])).

fof(f4,axiom,(
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

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X1)) != k1_funct_1(X1,sK3(X0,X1))
        & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f14,f25])).

fof(f41,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK3(X0,X1),k1_relat_1(X0))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f45,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f30])).

fof(f46,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f30])).

fof(f47,plain,(
    v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f30])).

fof(f48,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f30])).

fof(f53,plain,(
    sK6 != sK7 ),
    inference(cnf_transformation,[],[f30])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
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

fof(f8,plain,(
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
    inference(flattening,[],[f7])).

fof(f17,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f18,plain,(
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
    inference(rectify,[],[f17])).

fof(f21,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X5)) = X5
        & r2_hidden(sK2(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK1(X0,X1)) = X2
        & r2_hidden(sK1(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
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
              ( k1_funct_1(X0,X3) != sK0(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK0(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK0(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK0(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK1(X0,X1)) = sK0(X0,X1)
                  & r2_hidden(sK1(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK0(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK2(X0,X5)) = X5
                    & r2_hidden(sK2(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f21,f20,f19])).

fof(f31,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK2(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f57,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK2(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f31])).

fof(f52,plain,(
    k5_relat_1(sK5,sK6) = k5_relat_1(sK5,sK7) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f23,plain,(
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

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f43,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f30])).

fof(f44,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f30])).

fof(f49,plain,(
    k2_relat_1(sK5) = sK4 ),
    inference(cnf_transformation,[],[f30])).

fof(f33,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f54,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f55,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
           => k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f32,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK2(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f56,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK2(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f32])).

fof(f42,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_funct_1(X0,sK3(X0,X1)) != k1_funct_1(X1,sK3(X0,X1))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_14,negated_conjecture,
    ( k1_relat_1(sK7) = sK4 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_15,negated_conjecture,
    ( k1_relat_1(sK6) = sK4 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_11,plain,
    ( r2_hidden(sK3(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | X1 = X0
    | k1_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_502,plain,
    ( X0 = X1
    | k1_relat_1(X0) != k1_relat_1(X1)
    | r2_hidden(sK3(X1,X0),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1328,plain,
    ( k1_relat_1(X0) != sK4
    | sK6 = X0
    | r2_hidden(sK3(sK6,X0),k1_relat_1(sK6)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK6) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_502])).

cnf(c_1330,plain,
    ( k1_relat_1(X0) != sK4
    | sK6 = X0
    | r2_hidden(sK3(sK6,X0),sK4) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK6) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1328,c_15])).

cnf(c_20,negated_conjecture,
    ( v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_25,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_19,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_26,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1641,plain,
    ( v1_funct_1(X0) != iProver_top
    | k1_relat_1(X0) != sK4
    | sK6 = X0
    | r2_hidden(sK3(sK6,X0),sK4) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1330,c_25,c_26])).

cnf(c_1642,plain,
    ( k1_relat_1(X0) != sK4
    | sK6 = X0
    | r2_hidden(sK3(sK6,X0),sK4) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1641])).

cnf(c_1647,plain,
    ( sK7 = sK6
    | r2_hidden(sK3(sK6,sK7),sK4) = iProver_top
    | v1_relat_1(sK7) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_14,c_1642])).

cnf(c_18,negated_conjecture,
    ( v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_27,plain,
    ( v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_17,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_28,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_12,negated_conjecture,
    ( sK6 != sK7 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_203,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_544,plain,
    ( sK7 != X0
    | sK6 != X0
    | sK6 = sK7 ),
    inference(instantiation,[status(thm)],[c_203])).

cnf(c_876,plain,
    ( sK7 != sK6
    | sK6 = sK7
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_544])).

cnf(c_202,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1040,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_202])).

cnf(c_1677,plain,
    ( r2_hidden(sK3(sK6,sK7),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1647,c_27,c_28,c_12,c_876,c_1040])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK2(X1,X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_508,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(sK2(X1,X0),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_13,negated_conjecture,
    ( k5_relat_1(sK5,sK6) = k5_relat_1(sK5,sK7) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(X0,k1_relat_1(k5_relat_1(X1,X2)))
    | ~ r2_hidden(k1_funct_1(X1,X0),k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_507,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(X0,k1_relat_1(k5_relat_1(X1,X2))) = iProver_top
    | r2_hidden(k1_funct_1(X1,X0),k1_relat_1(X2)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3809,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(X0,k1_relat_1(k5_relat_1(X1,sK7))) = iProver_top
    | r2_hidden(k1_funct_1(X1,X0),sK4) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(sK7) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_14,c_507])).

cnf(c_3836,plain,
    ( v1_funct_1(X1) != iProver_top
    | r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(X0,k1_relat_1(k5_relat_1(X1,sK7))) = iProver_top
    | r2_hidden(k1_funct_1(X1,X0),sK4) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3809,c_27,c_28])).

cnf(c_3837,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(X0,k1_relat_1(k5_relat_1(X1,sK7))) = iProver_top
    | r2_hidden(k1_funct_1(X1,X0),sK4) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_3836])).

cnf(c_3842,plain,
    ( r2_hidden(X0,k1_relat_1(k5_relat_1(sK5,sK6))) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),sK4) != iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_3837])).

cnf(c_22,negated_conjecture,
    ( v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_23,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_24,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_16,negated_conjecture,
    ( k2_relat_1(sK5) = sK4 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_510,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1185,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),sK4) = iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_16,c_510])).

cnf(c_1204,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1185,c_23,c_24])).

cnf(c_3886,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(X0,k1_relat_1(k5_relat_1(sK5,sK6))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3842,c_23,c_24,c_1185])).

cnf(c_3887,plain,
    ( r2_hidden(X0,k1_relat_1(k5_relat_1(sK5,sK6))) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3886])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X1,X2)))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_504,plain,
    ( k1_funct_1(k5_relat_1(X0,X1),X2) = k1_funct_1(X1,k1_funct_1(X0,X2))
    | r2_hidden(X2,k1_relat_1(k5_relat_1(X0,X1))) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3895,plain,
    ( k1_funct_1(k5_relat_1(sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_relat_1(sK6) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3887,c_504])).

cnf(c_17567,plain,
    ( k1_funct_1(k5_relat_1(sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3895,c_23,c_24,c_25,c_26])).

cnf(c_17577,plain,
    ( k1_funct_1(sK6,k1_funct_1(sK5,sK2(sK5,X0))) = k1_funct_1(k5_relat_1(sK5,sK6),sK2(sK5,X0))
    | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_508,c_17567])).

cnf(c_17604,plain,
    ( k1_funct_1(sK6,k1_funct_1(sK5,sK2(sK5,X0))) = k1_funct_1(k5_relat_1(sK5,sK6),sK2(sK5,X0))
    | r2_hidden(X0,sK4) != iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_17577,c_16])).

cnf(c_17635,plain,
    ( k1_funct_1(sK6,k1_funct_1(sK5,sK2(sK5,X0))) = k1_funct_1(k5_relat_1(sK5,sK6),sK2(sK5,X0))
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17604,c_23,c_24])).

cnf(c_17666,plain,
    ( k1_funct_1(sK6,k1_funct_1(sK5,sK2(sK5,sK3(sK6,sK7)))) = k1_funct_1(k5_relat_1(sK5,sK6),sK2(sK5,sK3(sK6,sK7))) ),
    inference(superposition,[status(thm)],[c_1677,c_17635])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k1_funct_1(X1,sK2(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_509,plain,
    ( k1_funct_1(X0,sK2(X0,X1)) = X1
    | r2_hidden(X1,k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_842,plain,
    ( k1_funct_1(sK5,sK2(sK5,X0)) = X0
    | r2_hidden(X0,sK4) != iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_16,c_509])).

cnf(c_911,plain,
    ( k1_funct_1(sK5,sK2(sK5,X0)) = X0
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_842,c_23,c_24])).

cnf(c_1683,plain,
    ( k1_funct_1(sK5,sK2(sK5,sK3(sK6,sK7))) = sK3(sK6,sK7) ),
    inference(superposition,[status(thm)],[c_1677,c_911])).

cnf(c_2858,plain,
    ( k1_funct_1(k5_relat_1(sK5,sK7),X0) = k1_funct_1(sK7,k1_funct_1(sK5,X0))
    | r2_hidden(X0,k1_relat_1(k5_relat_1(sK5,sK6))) != iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_relat_1(sK7) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_504])).

cnf(c_2859,plain,
    ( k1_funct_1(k5_relat_1(sK5,sK6),X0) = k1_funct_1(sK7,k1_funct_1(sK5,X0))
    | r2_hidden(X0,k1_relat_1(k5_relat_1(sK5,sK6))) != iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_relat_1(sK7) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2858,c_13])).

cnf(c_3026,plain,
    ( k1_funct_1(k5_relat_1(sK5,sK6),X0) = k1_funct_1(sK7,k1_funct_1(sK5,X0))
    | r2_hidden(X0,k1_relat_1(k5_relat_1(sK5,sK6))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2859,c_23,c_24,c_27,c_28])).

cnf(c_3896,plain,
    ( k1_funct_1(k5_relat_1(sK5,sK6),X0) = k1_funct_1(sK7,k1_funct_1(sK5,X0))
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3887,c_3026])).

cnf(c_3992,plain,
    ( k1_funct_1(sK7,k1_funct_1(sK5,sK2(sK5,X0))) = k1_funct_1(k5_relat_1(sK5,sK6),sK2(sK5,X0))
    | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_508,c_3896])).

cnf(c_3996,plain,
    ( k1_funct_1(sK7,k1_funct_1(sK5,sK2(sK5,X0))) = k1_funct_1(k5_relat_1(sK5,sK6),sK2(sK5,X0))
    | r2_hidden(X0,sK4) != iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3992,c_16])).

cnf(c_4013,plain,
    ( k1_funct_1(sK7,k1_funct_1(sK5,sK2(sK5,X0))) = k1_funct_1(k5_relat_1(sK5,sK6),sK2(sK5,X0))
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3996,c_23,c_24])).

cnf(c_4029,plain,
    ( k1_funct_1(k5_relat_1(sK5,sK6),sK2(sK5,sK3(sK6,sK7))) = k1_funct_1(sK7,k1_funct_1(sK5,sK2(sK5,sK3(sK6,sK7)))) ),
    inference(superposition,[status(thm)],[c_1677,c_4013])).

cnf(c_4032,plain,
    ( k1_funct_1(k5_relat_1(sK5,sK6),sK2(sK5,sK3(sK6,sK7))) = k1_funct_1(sK7,sK3(sK6,sK7)) ),
    inference(light_normalisation,[status(thm)],[c_4029,c_1683])).

cnf(c_17671,plain,
    ( k1_funct_1(sK6,sK3(sK6,sK7)) = k1_funct_1(sK7,sK3(sK6,sK7)) ),
    inference(light_normalisation,[status(thm)],[c_17666,c_1683,c_4032])).

cnf(c_5133,plain,
    ( k1_funct_1(sK7,sK3(sK6,sK7)) = k1_funct_1(sK7,sK3(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_202])).

cnf(c_1594,plain,
    ( k1_funct_1(sK7,sK3(sK6,sK7)) != X0
    | k1_funct_1(sK7,sK3(sK6,sK7)) = k1_funct_1(sK6,sK3(sK6,sK7))
    | k1_funct_1(sK6,sK3(sK6,sK7)) != X0 ),
    inference(instantiation,[status(thm)],[c_203])).

cnf(c_2094,plain,
    ( k1_funct_1(sK7,sK3(sK6,sK7)) != k1_funct_1(sK7,sK3(sK6,sK7))
    | k1_funct_1(sK7,sK3(sK6,sK7)) = k1_funct_1(sK6,sK3(sK6,sK7))
    | k1_funct_1(sK6,sK3(sK6,sK7)) != k1_funct_1(sK7,sK3(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_1594])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | X1 = X0
    | k1_funct_1(X1,sK3(X0,X1)) != k1_funct_1(X0,sK3(X0,X1))
    | k1_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_559,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK7)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK7)
    | k1_funct_1(sK7,sK3(X0,sK7)) != k1_funct_1(X0,sK3(X0,sK7))
    | k1_relat_1(sK7) != k1_relat_1(X0)
    | sK7 = X0 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_726,plain,
    ( ~ v1_relat_1(sK7)
    | ~ v1_relat_1(sK6)
    | ~ v1_funct_1(sK7)
    | ~ v1_funct_1(sK6)
    | k1_funct_1(sK7,sK3(sK6,sK7)) != k1_funct_1(sK6,sK3(sK6,sK7))
    | k1_relat_1(sK7) != k1_relat_1(sK6)
    | sK7 = sK6 ),
    inference(instantiation,[status(thm)],[c_559])).

cnf(c_591,plain,
    ( X0 != X1
    | k1_relat_1(sK7) != X1
    | k1_relat_1(sK7) = X0 ),
    inference(instantiation,[status(thm)],[c_203])).

cnf(c_636,plain,
    ( X0 != sK4
    | k1_relat_1(sK7) = X0
    | k1_relat_1(sK7) != sK4 ),
    inference(instantiation,[status(thm)],[c_591])).

cnf(c_653,plain,
    ( k1_relat_1(sK7) = k1_relat_1(sK6)
    | k1_relat_1(sK7) != sK4
    | k1_relat_1(sK6) != sK4 ),
    inference(instantiation,[status(thm)],[c_636])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_17671,c_5133,c_2094,c_1040,c_876,c_726,c_653,c_12,c_14,c_15,c_17,c_18,c_19,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:20:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.38/1.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.38/1.50  
% 7.38/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.38/1.50  
% 7.38/1.50  ------  iProver source info
% 7.38/1.50  
% 7.38/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.38/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.38/1.50  git: non_committed_changes: false
% 7.38/1.50  git: last_make_outside_of_git: false
% 7.38/1.50  
% 7.38/1.50  ------ 
% 7.38/1.50  
% 7.38/1.50  ------ Input Options
% 7.38/1.50  
% 7.38/1.50  --out_options                           all
% 7.38/1.50  --tptp_safe_out                         true
% 7.38/1.50  --problem_path                          ""
% 7.38/1.50  --include_path                          ""
% 7.38/1.50  --clausifier                            res/vclausify_rel
% 7.38/1.50  --clausifier_options                    ""
% 7.38/1.50  --stdin                                 false
% 7.38/1.50  --stats_out                             all
% 7.38/1.50  
% 7.38/1.50  ------ General Options
% 7.38/1.50  
% 7.38/1.50  --fof                                   false
% 7.38/1.50  --time_out_real                         305.
% 7.38/1.50  --time_out_virtual                      -1.
% 7.38/1.50  --symbol_type_check                     false
% 7.38/1.50  --clausify_out                          false
% 7.38/1.50  --sig_cnt_out                           false
% 7.38/1.50  --trig_cnt_out                          false
% 7.38/1.50  --trig_cnt_out_tolerance                1.
% 7.38/1.50  --trig_cnt_out_sk_spl                   false
% 7.38/1.50  --abstr_cl_out                          false
% 7.38/1.50  
% 7.38/1.50  ------ Global Options
% 7.38/1.50  
% 7.38/1.50  --schedule                              default
% 7.38/1.50  --add_important_lit                     false
% 7.38/1.50  --prop_solver_per_cl                    1000
% 7.38/1.50  --min_unsat_core                        false
% 7.38/1.50  --soft_assumptions                      false
% 7.38/1.50  --soft_lemma_size                       3
% 7.38/1.50  --prop_impl_unit_size                   0
% 7.38/1.50  --prop_impl_unit                        []
% 7.38/1.50  --share_sel_clauses                     true
% 7.38/1.50  --reset_solvers                         false
% 7.38/1.50  --bc_imp_inh                            [conj_cone]
% 7.38/1.50  --conj_cone_tolerance                   3.
% 7.38/1.50  --extra_neg_conj                        none
% 7.38/1.50  --large_theory_mode                     true
% 7.38/1.50  --prolific_symb_bound                   200
% 7.38/1.50  --lt_threshold                          2000
% 7.38/1.50  --clause_weak_htbl                      true
% 7.38/1.50  --gc_record_bc_elim                     false
% 7.38/1.50  
% 7.38/1.50  ------ Preprocessing Options
% 7.38/1.50  
% 7.38/1.50  --preprocessing_flag                    true
% 7.38/1.50  --time_out_prep_mult                    0.1
% 7.38/1.50  --splitting_mode                        input
% 7.38/1.50  --splitting_grd                         true
% 7.38/1.50  --splitting_cvd                         false
% 7.38/1.50  --splitting_cvd_svl                     false
% 7.38/1.50  --splitting_nvd                         32
% 7.38/1.50  --sub_typing                            true
% 7.38/1.50  --prep_gs_sim                           true
% 7.38/1.50  --prep_unflatten                        true
% 7.38/1.50  --prep_res_sim                          true
% 7.38/1.50  --prep_upred                            true
% 7.38/1.50  --prep_sem_filter                       exhaustive
% 7.38/1.50  --prep_sem_filter_out                   false
% 7.38/1.50  --pred_elim                             true
% 7.38/1.50  --res_sim_input                         true
% 7.38/1.50  --eq_ax_congr_red                       true
% 7.38/1.50  --pure_diseq_elim                       true
% 7.38/1.50  --brand_transform                       false
% 7.38/1.50  --non_eq_to_eq                          false
% 7.38/1.50  --prep_def_merge                        true
% 7.38/1.50  --prep_def_merge_prop_impl              false
% 7.38/1.50  --prep_def_merge_mbd                    true
% 7.38/1.50  --prep_def_merge_tr_red                 false
% 7.38/1.50  --prep_def_merge_tr_cl                  false
% 7.38/1.50  --smt_preprocessing                     true
% 7.38/1.50  --smt_ac_axioms                         fast
% 7.38/1.50  --preprocessed_out                      false
% 7.38/1.50  --preprocessed_stats                    false
% 7.38/1.50  
% 7.38/1.50  ------ Abstraction refinement Options
% 7.38/1.50  
% 7.38/1.50  --abstr_ref                             []
% 7.38/1.50  --abstr_ref_prep                        false
% 7.38/1.50  --abstr_ref_until_sat                   false
% 7.38/1.50  --abstr_ref_sig_restrict                funpre
% 7.38/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.38/1.50  --abstr_ref_under                       []
% 7.38/1.50  
% 7.38/1.50  ------ SAT Options
% 7.38/1.50  
% 7.38/1.50  --sat_mode                              false
% 7.38/1.50  --sat_fm_restart_options                ""
% 7.38/1.50  --sat_gr_def                            false
% 7.38/1.50  --sat_epr_types                         true
% 7.38/1.50  --sat_non_cyclic_types                  false
% 7.38/1.50  --sat_finite_models                     false
% 7.38/1.50  --sat_fm_lemmas                         false
% 7.38/1.50  --sat_fm_prep                           false
% 7.38/1.50  --sat_fm_uc_incr                        true
% 7.38/1.50  --sat_out_model                         small
% 7.38/1.50  --sat_out_clauses                       false
% 7.38/1.50  
% 7.38/1.50  ------ QBF Options
% 7.38/1.50  
% 7.38/1.50  --qbf_mode                              false
% 7.38/1.50  --qbf_elim_univ                         false
% 7.38/1.50  --qbf_dom_inst                          none
% 7.38/1.50  --qbf_dom_pre_inst                      false
% 7.38/1.50  --qbf_sk_in                             false
% 7.38/1.50  --qbf_pred_elim                         true
% 7.38/1.50  --qbf_split                             512
% 7.38/1.50  
% 7.38/1.50  ------ BMC1 Options
% 7.38/1.50  
% 7.38/1.50  --bmc1_incremental                      false
% 7.38/1.50  --bmc1_axioms                           reachable_all
% 7.38/1.50  --bmc1_min_bound                        0
% 7.38/1.50  --bmc1_max_bound                        -1
% 7.38/1.50  --bmc1_max_bound_default                -1
% 7.38/1.50  --bmc1_symbol_reachability              true
% 7.38/1.50  --bmc1_property_lemmas                  false
% 7.38/1.50  --bmc1_k_induction                      false
% 7.38/1.50  --bmc1_non_equiv_states                 false
% 7.38/1.50  --bmc1_deadlock                         false
% 7.38/1.50  --bmc1_ucm                              false
% 7.38/1.50  --bmc1_add_unsat_core                   none
% 7.38/1.50  --bmc1_unsat_core_children              false
% 7.38/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.38/1.50  --bmc1_out_stat                         full
% 7.38/1.50  --bmc1_ground_init                      false
% 7.38/1.50  --bmc1_pre_inst_next_state              false
% 7.38/1.50  --bmc1_pre_inst_state                   false
% 7.38/1.50  --bmc1_pre_inst_reach_state             false
% 7.38/1.50  --bmc1_out_unsat_core                   false
% 7.38/1.50  --bmc1_aig_witness_out                  false
% 7.38/1.50  --bmc1_verbose                          false
% 7.38/1.50  --bmc1_dump_clauses_tptp                false
% 7.38/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.38/1.50  --bmc1_dump_file                        -
% 7.38/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.38/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.38/1.50  --bmc1_ucm_extend_mode                  1
% 7.38/1.50  --bmc1_ucm_init_mode                    2
% 7.38/1.50  --bmc1_ucm_cone_mode                    none
% 7.38/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.38/1.50  --bmc1_ucm_relax_model                  4
% 7.38/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.38/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.38/1.50  --bmc1_ucm_layered_model                none
% 7.38/1.50  --bmc1_ucm_max_lemma_size               10
% 7.38/1.50  
% 7.38/1.50  ------ AIG Options
% 7.38/1.50  
% 7.38/1.50  --aig_mode                              false
% 7.38/1.50  
% 7.38/1.50  ------ Instantiation Options
% 7.38/1.50  
% 7.38/1.50  --instantiation_flag                    true
% 7.38/1.50  --inst_sos_flag                         true
% 7.38/1.50  --inst_sos_phase                        true
% 7.38/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.38/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.38/1.50  --inst_lit_sel_side                     num_symb
% 7.38/1.50  --inst_solver_per_active                1400
% 7.38/1.50  --inst_solver_calls_frac                1.
% 7.38/1.50  --inst_passive_queue_type               priority_queues
% 7.38/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.38/1.50  --inst_passive_queues_freq              [25;2]
% 7.38/1.50  --inst_dismatching                      true
% 7.38/1.50  --inst_eager_unprocessed_to_passive     true
% 7.38/1.50  --inst_prop_sim_given                   true
% 7.38/1.50  --inst_prop_sim_new                     false
% 7.38/1.50  --inst_subs_new                         false
% 7.38/1.50  --inst_eq_res_simp                      false
% 7.38/1.50  --inst_subs_given                       false
% 7.38/1.50  --inst_orphan_elimination               true
% 7.38/1.50  --inst_learning_loop_flag               true
% 7.38/1.50  --inst_learning_start                   3000
% 7.38/1.50  --inst_learning_factor                  2
% 7.38/1.50  --inst_start_prop_sim_after_learn       3
% 7.38/1.50  --inst_sel_renew                        solver
% 7.38/1.50  --inst_lit_activity_flag                true
% 7.38/1.50  --inst_restr_to_given                   false
% 7.38/1.50  --inst_activity_threshold               500
% 7.38/1.50  --inst_out_proof                        true
% 7.38/1.50  
% 7.38/1.50  ------ Resolution Options
% 7.38/1.50  
% 7.38/1.50  --resolution_flag                       true
% 7.38/1.50  --res_lit_sel                           adaptive
% 7.38/1.50  --res_lit_sel_side                      none
% 7.38/1.50  --res_ordering                          kbo
% 7.38/1.50  --res_to_prop_solver                    active
% 7.38/1.50  --res_prop_simpl_new                    false
% 7.38/1.50  --res_prop_simpl_given                  true
% 7.38/1.50  --res_passive_queue_type                priority_queues
% 7.38/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.38/1.50  --res_passive_queues_freq               [15;5]
% 7.38/1.50  --res_forward_subs                      full
% 7.38/1.50  --res_backward_subs                     full
% 7.38/1.50  --res_forward_subs_resolution           true
% 7.38/1.50  --res_backward_subs_resolution          true
% 7.38/1.50  --res_orphan_elimination                true
% 7.38/1.50  --res_time_limit                        2.
% 7.38/1.50  --res_out_proof                         true
% 7.38/1.50  
% 7.38/1.50  ------ Superposition Options
% 7.38/1.50  
% 7.38/1.50  --superposition_flag                    true
% 7.38/1.50  --sup_passive_queue_type                priority_queues
% 7.38/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.38/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.38/1.50  --demod_completeness_check              fast
% 7.38/1.50  --demod_use_ground                      true
% 7.38/1.50  --sup_to_prop_solver                    passive
% 7.38/1.50  --sup_prop_simpl_new                    true
% 7.38/1.50  --sup_prop_simpl_given                  true
% 7.38/1.50  --sup_fun_splitting                     true
% 7.38/1.50  --sup_smt_interval                      50000
% 7.38/1.50  
% 7.38/1.50  ------ Superposition Simplification Setup
% 7.38/1.50  
% 7.38/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.38/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.38/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.38/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.38/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.38/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.38/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.38/1.50  --sup_immed_triv                        [TrivRules]
% 7.38/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.38/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.38/1.50  --sup_immed_bw_main                     []
% 7.38/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.38/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.38/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.38/1.50  --sup_input_bw                          []
% 7.38/1.50  
% 7.38/1.50  ------ Combination Options
% 7.38/1.50  
% 7.38/1.50  --comb_res_mult                         3
% 7.38/1.50  --comb_sup_mult                         2
% 7.38/1.50  --comb_inst_mult                        10
% 7.38/1.50  
% 7.38/1.50  ------ Debug Options
% 7.38/1.50  
% 7.38/1.50  --dbg_backtrace                         false
% 7.38/1.50  --dbg_dump_prop_clauses                 false
% 7.38/1.50  --dbg_dump_prop_clauses_file            -
% 7.38/1.50  --dbg_out_stat                          false
% 7.38/1.50  ------ Parsing...
% 7.38/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.38/1.50  
% 7.38/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.38/1.50  
% 7.38/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.38/1.50  
% 7.38/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.38/1.50  ------ Proving...
% 7.38/1.50  ------ Problem Properties 
% 7.38/1.50  
% 7.38/1.50  
% 7.38/1.50  clauses                                 23
% 7.38/1.50  conjectures                             11
% 7.38/1.50  EPR                                     7
% 7.38/1.50  Horn                                    20
% 7.38/1.50  unary                                   11
% 7.38/1.50  binary                                  0
% 7.38/1.50  lits                                    78
% 7.38/1.50  lits eq                                 17
% 7.38/1.50  fd_pure                                 0
% 7.38/1.50  fd_pseudo                               0
% 7.38/1.50  fd_cond                                 0
% 7.38/1.50  fd_pseudo_cond                          5
% 7.38/1.50  AC symbols                              0
% 7.38/1.50  
% 7.38/1.50  ------ Schedule dynamic 5 is on 
% 7.38/1.50  
% 7.38/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.38/1.50  
% 7.38/1.50  
% 7.38/1.50  ------ 
% 7.38/1.50  Current options:
% 7.38/1.50  ------ 
% 7.38/1.50  
% 7.38/1.50  ------ Input Options
% 7.38/1.50  
% 7.38/1.50  --out_options                           all
% 7.38/1.50  --tptp_safe_out                         true
% 7.38/1.50  --problem_path                          ""
% 7.38/1.50  --include_path                          ""
% 7.38/1.50  --clausifier                            res/vclausify_rel
% 7.38/1.50  --clausifier_options                    ""
% 7.38/1.50  --stdin                                 false
% 7.38/1.50  --stats_out                             all
% 7.38/1.50  
% 7.38/1.50  ------ General Options
% 7.38/1.50  
% 7.38/1.50  --fof                                   false
% 7.38/1.50  --time_out_real                         305.
% 7.38/1.50  --time_out_virtual                      -1.
% 7.38/1.50  --symbol_type_check                     false
% 7.38/1.50  --clausify_out                          false
% 7.38/1.50  --sig_cnt_out                           false
% 7.38/1.50  --trig_cnt_out                          false
% 7.38/1.50  --trig_cnt_out_tolerance                1.
% 7.38/1.50  --trig_cnt_out_sk_spl                   false
% 7.38/1.50  --abstr_cl_out                          false
% 7.38/1.50  
% 7.38/1.50  ------ Global Options
% 7.38/1.50  
% 7.38/1.50  --schedule                              default
% 7.38/1.50  --add_important_lit                     false
% 7.38/1.50  --prop_solver_per_cl                    1000
% 7.38/1.50  --min_unsat_core                        false
% 7.38/1.50  --soft_assumptions                      false
% 7.38/1.50  --soft_lemma_size                       3
% 7.38/1.50  --prop_impl_unit_size                   0
% 7.38/1.50  --prop_impl_unit                        []
% 7.38/1.50  --share_sel_clauses                     true
% 7.38/1.50  --reset_solvers                         false
% 7.38/1.50  --bc_imp_inh                            [conj_cone]
% 7.38/1.50  --conj_cone_tolerance                   3.
% 7.38/1.50  --extra_neg_conj                        none
% 7.38/1.50  --large_theory_mode                     true
% 7.38/1.50  --prolific_symb_bound                   200
% 7.38/1.50  --lt_threshold                          2000
% 7.38/1.50  --clause_weak_htbl                      true
% 7.38/1.50  --gc_record_bc_elim                     false
% 7.38/1.50  
% 7.38/1.50  ------ Preprocessing Options
% 7.38/1.50  
% 7.38/1.50  --preprocessing_flag                    true
% 7.38/1.50  --time_out_prep_mult                    0.1
% 7.38/1.50  --splitting_mode                        input
% 7.38/1.50  --splitting_grd                         true
% 7.38/1.50  --splitting_cvd                         false
% 7.38/1.50  --splitting_cvd_svl                     false
% 7.38/1.50  --splitting_nvd                         32
% 7.38/1.50  --sub_typing                            true
% 7.38/1.50  --prep_gs_sim                           true
% 7.38/1.50  --prep_unflatten                        true
% 7.38/1.50  --prep_res_sim                          true
% 7.38/1.50  --prep_upred                            true
% 7.38/1.50  --prep_sem_filter                       exhaustive
% 7.38/1.50  --prep_sem_filter_out                   false
% 7.38/1.50  --pred_elim                             true
% 7.38/1.50  --res_sim_input                         true
% 7.38/1.50  --eq_ax_congr_red                       true
% 7.38/1.50  --pure_diseq_elim                       true
% 7.38/1.50  --brand_transform                       false
% 7.38/1.50  --non_eq_to_eq                          false
% 7.38/1.50  --prep_def_merge                        true
% 7.38/1.50  --prep_def_merge_prop_impl              false
% 7.38/1.50  --prep_def_merge_mbd                    true
% 7.38/1.50  --prep_def_merge_tr_red                 false
% 7.38/1.50  --prep_def_merge_tr_cl                  false
% 7.38/1.50  --smt_preprocessing                     true
% 7.38/1.50  --smt_ac_axioms                         fast
% 7.38/1.50  --preprocessed_out                      false
% 7.38/1.50  --preprocessed_stats                    false
% 7.38/1.50  
% 7.38/1.50  ------ Abstraction refinement Options
% 7.38/1.50  
% 7.38/1.50  --abstr_ref                             []
% 7.38/1.50  --abstr_ref_prep                        false
% 7.38/1.50  --abstr_ref_until_sat                   false
% 7.38/1.50  --abstr_ref_sig_restrict                funpre
% 7.38/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.38/1.50  --abstr_ref_under                       []
% 7.38/1.50  
% 7.38/1.50  ------ SAT Options
% 7.38/1.50  
% 7.38/1.50  --sat_mode                              false
% 7.38/1.50  --sat_fm_restart_options                ""
% 7.38/1.50  --sat_gr_def                            false
% 7.38/1.50  --sat_epr_types                         true
% 7.38/1.50  --sat_non_cyclic_types                  false
% 7.38/1.50  --sat_finite_models                     false
% 7.38/1.50  --sat_fm_lemmas                         false
% 7.38/1.50  --sat_fm_prep                           false
% 7.38/1.50  --sat_fm_uc_incr                        true
% 7.38/1.50  --sat_out_model                         small
% 7.38/1.50  --sat_out_clauses                       false
% 7.38/1.50  
% 7.38/1.50  ------ QBF Options
% 7.38/1.50  
% 7.38/1.50  --qbf_mode                              false
% 7.38/1.50  --qbf_elim_univ                         false
% 7.38/1.50  --qbf_dom_inst                          none
% 7.38/1.50  --qbf_dom_pre_inst                      false
% 7.38/1.50  --qbf_sk_in                             false
% 7.38/1.50  --qbf_pred_elim                         true
% 7.38/1.50  --qbf_split                             512
% 7.38/1.50  
% 7.38/1.50  ------ BMC1 Options
% 7.38/1.50  
% 7.38/1.50  --bmc1_incremental                      false
% 7.38/1.50  --bmc1_axioms                           reachable_all
% 7.38/1.50  --bmc1_min_bound                        0
% 7.38/1.50  --bmc1_max_bound                        -1
% 7.38/1.50  --bmc1_max_bound_default                -1
% 7.38/1.50  --bmc1_symbol_reachability              true
% 7.38/1.50  --bmc1_property_lemmas                  false
% 7.38/1.50  --bmc1_k_induction                      false
% 7.38/1.50  --bmc1_non_equiv_states                 false
% 7.38/1.50  --bmc1_deadlock                         false
% 7.38/1.50  --bmc1_ucm                              false
% 7.38/1.50  --bmc1_add_unsat_core                   none
% 7.38/1.50  --bmc1_unsat_core_children              false
% 7.38/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.38/1.50  --bmc1_out_stat                         full
% 7.38/1.50  --bmc1_ground_init                      false
% 7.38/1.50  --bmc1_pre_inst_next_state              false
% 7.38/1.50  --bmc1_pre_inst_state                   false
% 7.38/1.50  --bmc1_pre_inst_reach_state             false
% 7.38/1.50  --bmc1_out_unsat_core                   false
% 7.38/1.50  --bmc1_aig_witness_out                  false
% 7.38/1.50  --bmc1_verbose                          false
% 7.38/1.50  --bmc1_dump_clauses_tptp                false
% 7.38/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.38/1.50  --bmc1_dump_file                        -
% 7.38/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.38/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.38/1.50  --bmc1_ucm_extend_mode                  1
% 7.38/1.50  --bmc1_ucm_init_mode                    2
% 7.38/1.50  --bmc1_ucm_cone_mode                    none
% 7.38/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.38/1.50  --bmc1_ucm_relax_model                  4
% 7.38/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.38/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.38/1.50  --bmc1_ucm_layered_model                none
% 7.38/1.50  --bmc1_ucm_max_lemma_size               10
% 7.38/1.50  
% 7.38/1.50  ------ AIG Options
% 7.38/1.50  
% 7.38/1.50  --aig_mode                              false
% 7.38/1.50  
% 7.38/1.50  ------ Instantiation Options
% 7.38/1.50  
% 7.38/1.50  --instantiation_flag                    true
% 7.38/1.50  --inst_sos_flag                         true
% 7.38/1.50  --inst_sos_phase                        true
% 7.38/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.38/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.38/1.50  --inst_lit_sel_side                     none
% 7.38/1.50  --inst_solver_per_active                1400
% 7.38/1.50  --inst_solver_calls_frac                1.
% 7.38/1.50  --inst_passive_queue_type               priority_queues
% 7.38/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.38/1.50  --inst_passive_queues_freq              [25;2]
% 7.38/1.50  --inst_dismatching                      true
% 7.38/1.50  --inst_eager_unprocessed_to_passive     true
% 7.38/1.50  --inst_prop_sim_given                   true
% 7.38/1.50  --inst_prop_sim_new                     false
% 7.38/1.50  --inst_subs_new                         false
% 7.38/1.50  --inst_eq_res_simp                      false
% 7.38/1.50  --inst_subs_given                       false
% 7.38/1.50  --inst_orphan_elimination               true
% 7.38/1.50  --inst_learning_loop_flag               true
% 7.38/1.50  --inst_learning_start                   3000
% 7.38/1.50  --inst_learning_factor                  2
% 7.38/1.50  --inst_start_prop_sim_after_learn       3
% 7.38/1.50  --inst_sel_renew                        solver
% 7.38/1.50  --inst_lit_activity_flag                true
% 7.38/1.50  --inst_restr_to_given                   false
% 7.38/1.50  --inst_activity_threshold               500
% 7.38/1.50  --inst_out_proof                        true
% 7.38/1.50  
% 7.38/1.50  ------ Resolution Options
% 7.38/1.50  
% 7.38/1.50  --resolution_flag                       false
% 7.38/1.50  --res_lit_sel                           adaptive
% 7.38/1.50  --res_lit_sel_side                      none
% 7.38/1.50  --res_ordering                          kbo
% 7.38/1.50  --res_to_prop_solver                    active
% 7.38/1.50  --res_prop_simpl_new                    false
% 7.38/1.50  --res_prop_simpl_given                  true
% 7.38/1.50  --res_passive_queue_type                priority_queues
% 7.38/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.38/1.50  --res_passive_queues_freq               [15;5]
% 7.38/1.50  --res_forward_subs                      full
% 7.38/1.50  --res_backward_subs                     full
% 7.38/1.50  --res_forward_subs_resolution           true
% 7.38/1.50  --res_backward_subs_resolution          true
% 7.38/1.50  --res_orphan_elimination                true
% 7.38/1.50  --res_time_limit                        2.
% 7.38/1.50  --res_out_proof                         true
% 7.38/1.50  
% 7.38/1.50  ------ Superposition Options
% 7.38/1.50  
% 7.38/1.50  --superposition_flag                    true
% 7.38/1.50  --sup_passive_queue_type                priority_queues
% 7.38/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.38/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.38/1.50  --demod_completeness_check              fast
% 7.38/1.50  --demod_use_ground                      true
% 7.38/1.50  --sup_to_prop_solver                    passive
% 7.38/1.50  --sup_prop_simpl_new                    true
% 7.38/1.50  --sup_prop_simpl_given                  true
% 7.38/1.50  --sup_fun_splitting                     true
% 7.38/1.50  --sup_smt_interval                      50000
% 7.38/1.50  
% 7.38/1.50  ------ Superposition Simplification Setup
% 7.38/1.50  
% 7.38/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.38/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.38/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.38/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.38/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.38/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.38/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.38/1.50  --sup_immed_triv                        [TrivRules]
% 7.38/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.38/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.38/1.50  --sup_immed_bw_main                     []
% 7.38/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.38/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.38/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.38/1.50  --sup_input_bw                          []
% 7.38/1.50  
% 7.38/1.50  ------ Combination Options
% 7.38/1.50  
% 7.38/1.50  --comb_res_mult                         3
% 7.38/1.50  --comb_sup_mult                         2
% 7.38/1.50  --comb_inst_mult                        10
% 7.38/1.50  
% 7.38/1.50  ------ Debug Options
% 7.38/1.50  
% 7.38/1.50  --dbg_backtrace                         false
% 7.38/1.50  --dbg_dump_prop_clauses                 false
% 7.38/1.50  --dbg_dump_prop_clauses_file            -
% 7.38/1.50  --dbg_out_stat                          false
% 7.38/1.50  
% 7.38/1.50  
% 7.38/1.50  
% 7.38/1.50  
% 7.38/1.50  ------ Proving...
% 7.38/1.50  
% 7.38/1.50  
% 7.38/1.50  % SZS status Theorem for theBenchmark.p
% 7.38/1.50  
% 7.38/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.38/1.50  
% 7.38/1.50  fof(f5,conjecture,(
% 7.38/1.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ! [X3] : ((v1_funct_1(X3) & v1_relat_1(X3)) => ((k5_relat_1(X1,X2) = k5_relat_1(X1,X3) & k1_relat_1(X3) = X0 & k1_relat_1(X2) = X0 & k2_relat_1(X1) = X0) => X2 = X3))))),
% 7.38/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.50  
% 7.38/1.50  fof(f6,negated_conjecture,(
% 7.38/1.50    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ! [X3] : ((v1_funct_1(X3) & v1_relat_1(X3)) => ((k5_relat_1(X1,X2) = k5_relat_1(X1,X3) & k1_relat_1(X3) = X0 & k1_relat_1(X2) = X0 & k2_relat_1(X1) = X0) => X2 = X3))))),
% 7.38/1.50    inference(negated_conjecture,[],[f5])).
% 7.38/1.50  
% 7.38/1.50  fof(f15,plain,(
% 7.38/1.50    ? [X0,X1] : (? [X2] : (? [X3] : ((X2 != X3 & (k5_relat_1(X1,X2) = k5_relat_1(X1,X3) & k1_relat_1(X3) = X0 & k1_relat_1(X2) = X0 & k2_relat_1(X1) = X0)) & (v1_funct_1(X3) & v1_relat_1(X3))) & (v1_funct_1(X2) & v1_relat_1(X2))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 7.38/1.50    inference(ennf_transformation,[],[f6])).
% 7.38/1.50  
% 7.38/1.50  fof(f16,plain,(
% 7.38/1.50    ? [X0,X1] : (? [X2] : (? [X3] : (X2 != X3 & k5_relat_1(X1,X2) = k5_relat_1(X1,X3) & k1_relat_1(X3) = X0 & k1_relat_1(X2) = X0 & k2_relat_1(X1) = X0 & v1_funct_1(X3) & v1_relat_1(X3)) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 7.38/1.50    inference(flattening,[],[f15])).
% 7.38/1.50  
% 7.38/1.50  fof(f29,plain,(
% 7.38/1.50    ( ! [X2,X0,X1] : (? [X3] : (X2 != X3 & k5_relat_1(X1,X2) = k5_relat_1(X1,X3) & k1_relat_1(X3) = X0 & k1_relat_1(X2) = X0 & k2_relat_1(X1) = X0 & v1_funct_1(X3) & v1_relat_1(X3)) => (sK7 != X2 & k5_relat_1(X1,sK7) = k5_relat_1(X1,X2) & k1_relat_1(sK7) = X0 & k1_relat_1(X2) = X0 & k2_relat_1(X1) = X0 & v1_funct_1(sK7) & v1_relat_1(sK7))) )),
% 7.38/1.50    introduced(choice_axiom,[])).
% 7.38/1.50  
% 7.38/1.50  fof(f28,plain,(
% 7.38/1.50    ( ! [X0,X1] : (? [X2] : (? [X3] : (X2 != X3 & k5_relat_1(X1,X2) = k5_relat_1(X1,X3) & k1_relat_1(X3) = X0 & k1_relat_1(X2) = X0 & k2_relat_1(X1) = X0 & v1_funct_1(X3) & v1_relat_1(X3)) & v1_funct_1(X2) & v1_relat_1(X2)) => (? [X3] : (sK6 != X3 & k5_relat_1(X1,sK6) = k5_relat_1(X1,X3) & k1_relat_1(X3) = X0 & k1_relat_1(sK6) = X0 & k2_relat_1(X1) = X0 & v1_funct_1(X3) & v1_relat_1(X3)) & v1_funct_1(sK6) & v1_relat_1(sK6))) )),
% 7.38/1.50    introduced(choice_axiom,[])).
% 7.38/1.50  
% 7.38/1.50  fof(f27,plain,(
% 7.38/1.50    ? [X0,X1] : (? [X2] : (? [X3] : (X2 != X3 & k5_relat_1(X1,X2) = k5_relat_1(X1,X3) & k1_relat_1(X3) = X0 & k1_relat_1(X2) = X0 & k2_relat_1(X1) = X0 & v1_funct_1(X3) & v1_relat_1(X3)) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : (? [X3] : (X2 != X3 & k5_relat_1(sK5,X2) = k5_relat_1(sK5,X3) & k1_relat_1(X3) = sK4 & k1_relat_1(X2) = sK4 & k2_relat_1(sK5) = sK4 & v1_funct_1(X3) & v1_relat_1(X3)) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(sK5) & v1_relat_1(sK5))),
% 7.38/1.50    introduced(choice_axiom,[])).
% 7.38/1.50  
% 7.38/1.50  fof(f30,plain,(
% 7.38/1.50    ((sK6 != sK7 & k5_relat_1(sK5,sK6) = k5_relat_1(sK5,sK7) & k1_relat_1(sK7) = sK4 & k1_relat_1(sK6) = sK4 & k2_relat_1(sK5) = sK4 & v1_funct_1(sK7) & v1_relat_1(sK7)) & v1_funct_1(sK6) & v1_relat_1(sK6)) & v1_funct_1(sK5) & v1_relat_1(sK5)),
% 7.38/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f16,f29,f28,f27])).
% 7.38/1.50  
% 7.38/1.50  fof(f51,plain,(
% 7.38/1.50    k1_relat_1(sK7) = sK4),
% 7.38/1.50    inference(cnf_transformation,[],[f30])).
% 7.38/1.50  
% 7.38/1.50  fof(f50,plain,(
% 7.38/1.50    k1_relat_1(sK6) = sK4),
% 7.38/1.50    inference(cnf_transformation,[],[f30])).
% 7.38/1.50  
% 7.38/1.50  fof(f4,axiom,(
% 7.38/1.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 7.38/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.50  
% 7.38/1.50  fof(f13,plain,(
% 7.38/1.50    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.38/1.50    inference(ennf_transformation,[],[f4])).
% 7.38/1.50  
% 7.38/1.50  fof(f14,plain,(
% 7.38/1.50    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.38/1.50    inference(flattening,[],[f13])).
% 7.38/1.50  
% 7.38/1.50  fof(f25,plain,(
% 7.38/1.50    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X1)) != k1_funct_1(X1,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),k1_relat_1(X0))))),
% 7.38/1.50    introduced(choice_axiom,[])).
% 7.38/1.50  
% 7.38/1.50  fof(f26,plain,(
% 7.38/1.50    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK3(X0,X1)) != k1_funct_1(X1,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.38/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f14,f25])).
% 7.38/1.50  
% 7.38/1.50  fof(f41,plain,(
% 7.38/1.50    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK3(X0,X1),k1_relat_1(X0)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.38/1.50    inference(cnf_transformation,[],[f26])).
% 7.38/1.50  
% 7.38/1.50  fof(f45,plain,(
% 7.38/1.50    v1_relat_1(sK6)),
% 7.38/1.50    inference(cnf_transformation,[],[f30])).
% 7.38/1.50  
% 7.38/1.50  fof(f46,plain,(
% 7.38/1.50    v1_funct_1(sK6)),
% 7.38/1.50    inference(cnf_transformation,[],[f30])).
% 7.38/1.50  
% 7.38/1.50  fof(f47,plain,(
% 7.38/1.50    v1_relat_1(sK7)),
% 7.38/1.50    inference(cnf_transformation,[],[f30])).
% 7.38/1.50  
% 7.38/1.50  fof(f48,plain,(
% 7.38/1.50    v1_funct_1(sK7)),
% 7.38/1.50    inference(cnf_transformation,[],[f30])).
% 7.38/1.50  
% 7.38/1.50  fof(f53,plain,(
% 7.38/1.50    sK6 != sK7),
% 7.38/1.50    inference(cnf_transformation,[],[f30])).
% 7.38/1.50  
% 7.38/1.50  fof(f1,axiom,(
% 7.38/1.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 7.38/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.50  
% 7.38/1.50  fof(f7,plain,(
% 7.38/1.50    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.38/1.50    inference(ennf_transformation,[],[f1])).
% 7.38/1.50  
% 7.38/1.50  fof(f8,plain,(
% 7.38/1.50    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.38/1.50    inference(flattening,[],[f7])).
% 7.38/1.50  
% 7.38/1.50  fof(f17,plain,(
% 7.38/1.50    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.38/1.50    inference(nnf_transformation,[],[f8])).
% 7.38/1.50  
% 7.38/1.50  fof(f18,plain,(
% 7.38/1.50    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.38/1.50    inference(rectify,[],[f17])).
% 7.38/1.50  
% 7.38/1.50  fof(f21,plain,(
% 7.38/1.50    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X5)) = X5 & r2_hidden(sK2(X0,X5),k1_relat_1(X0))))),
% 7.38/1.50    introduced(choice_axiom,[])).
% 7.38/1.50  
% 7.38/1.50  fof(f20,plain,(
% 7.38/1.50    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK1(X0,X1)) = X2 & r2_hidden(sK1(X0,X1),k1_relat_1(X0))))) )),
% 7.38/1.50    introduced(choice_axiom,[])).
% 7.38/1.50  
% 7.38/1.50  fof(f19,plain,(
% 7.38/1.50    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK0(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK0(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK0(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK0(X0,X1),X1))))),
% 7.38/1.50    introduced(choice_axiom,[])).
% 7.38/1.50  
% 7.38/1.50  fof(f22,plain,(
% 7.38/1.50    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK0(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK0(X0,X1),X1)) & ((k1_funct_1(X0,sK1(X0,X1)) = sK0(X0,X1) & r2_hidden(sK1(X0,X1),k1_relat_1(X0))) | r2_hidden(sK0(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK2(X0,X5)) = X5 & r2_hidden(sK2(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.38/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f21,f20,f19])).
% 7.38/1.50  
% 7.38/1.50  fof(f31,plain,(
% 7.38/1.50    ( ! [X0,X5,X1] : (r2_hidden(sK2(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.38/1.50    inference(cnf_transformation,[],[f22])).
% 7.38/1.50  
% 7.38/1.50  fof(f57,plain,(
% 7.38/1.50    ( ! [X0,X5] : (r2_hidden(sK2(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.38/1.50    inference(equality_resolution,[],[f31])).
% 7.38/1.50  
% 7.38/1.50  fof(f52,plain,(
% 7.38/1.50    k5_relat_1(sK5,sK6) = k5_relat_1(sK5,sK7)),
% 7.38/1.50    inference(cnf_transformation,[],[f30])).
% 7.38/1.50  
% 7.38/1.50  fof(f2,axiom,(
% 7.38/1.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))))))),
% 7.38/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.50  
% 7.38/1.50  fof(f9,plain,(
% 7.38/1.50    ! [X0,X1] : (! [X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 7.38/1.50    inference(ennf_transformation,[],[f2])).
% 7.38/1.50  
% 7.38/1.50  fof(f10,plain,(
% 7.38/1.50    ! [X0,X1] : (! [X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.38/1.50    inference(flattening,[],[f9])).
% 7.38/1.50  
% 7.38/1.50  fof(f23,plain,(
% 7.38/1.50    ! [X0,X1] : (! [X2] : (((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | (~r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X2)))) & ((r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.38/1.50    inference(nnf_transformation,[],[f10])).
% 7.38/1.50  
% 7.38/1.50  fof(f24,plain,(
% 7.38/1.50    ! [X0,X1] : (! [X2] : (((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X2))) & ((r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.38/1.50    inference(flattening,[],[f23])).
% 7.38/1.50  
% 7.38/1.50  fof(f39,plain,(
% 7.38/1.50    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.38/1.50    inference(cnf_transformation,[],[f24])).
% 7.38/1.50  
% 7.38/1.50  fof(f43,plain,(
% 7.38/1.50    v1_relat_1(sK5)),
% 7.38/1.50    inference(cnf_transformation,[],[f30])).
% 7.38/1.50  
% 7.38/1.50  fof(f44,plain,(
% 7.38/1.50    v1_funct_1(sK5)),
% 7.38/1.50    inference(cnf_transformation,[],[f30])).
% 7.38/1.50  
% 7.38/1.50  fof(f49,plain,(
% 7.38/1.50    k2_relat_1(sK5) = sK4),
% 7.38/1.50    inference(cnf_transformation,[],[f30])).
% 7.38/1.50  
% 7.38/1.50  fof(f33,plain,(
% 7.38/1.50    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.38/1.50    inference(cnf_transformation,[],[f22])).
% 7.38/1.50  
% 7.38/1.50  fof(f54,plain,(
% 7.38/1.50    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.38/1.50    inference(equality_resolution,[],[f33])).
% 7.38/1.50  
% 7.38/1.50  fof(f55,plain,(
% 7.38/1.50    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.38/1.50    inference(equality_resolution,[],[f54])).
% 7.38/1.50  
% 7.38/1.50  fof(f3,axiom,(
% 7.38/1.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) => k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0))))),
% 7.38/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.50  
% 7.38/1.50  fof(f11,plain,(
% 7.38/1.50    ! [X0,X1] : (! [X2] : ((k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 7.38/1.50    inference(ennf_transformation,[],[f3])).
% 7.38/1.50  
% 7.38/1.50  fof(f12,plain,(
% 7.38/1.50    ! [X0,X1] : (! [X2] : (k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.38/1.50    inference(flattening,[],[f11])).
% 7.38/1.50  
% 7.38/1.50  fof(f40,plain,(
% 7.38/1.50    ( ! [X2,X0,X1] : (k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.38/1.50    inference(cnf_transformation,[],[f12])).
% 7.38/1.50  
% 7.38/1.50  fof(f32,plain,(
% 7.38/1.50    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK2(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.38/1.50    inference(cnf_transformation,[],[f22])).
% 7.38/1.50  
% 7.38/1.50  fof(f56,plain,(
% 7.38/1.50    ( ! [X0,X5] : (k1_funct_1(X0,sK2(X0,X5)) = X5 | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.38/1.50    inference(equality_resolution,[],[f32])).
% 7.38/1.50  
% 7.38/1.50  fof(f42,plain,(
% 7.38/1.50    ( ! [X0,X1] : (X0 = X1 | k1_funct_1(X0,sK3(X0,X1)) != k1_funct_1(X1,sK3(X0,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.38/1.50    inference(cnf_transformation,[],[f26])).
% 7.38/1.50  
% 7.38/1.50  cnf(c_14,negated_conjecture,
% 7.38/1.50      ( k1_relat_1(sK7) = sK4 ),
% 7.38/1.50      inference(cnf_transformation,[],[f51]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_15,negated_conjecture,
% 7.38/1.50      ( k1_relat_1(sK6) = sK4 ),
% 7.38/1.50      inference(cnf_transformation,[],[f50]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_11,plain,
% 7.38/1.50      ( r2_hidden(sK3(X0,X1),k1_relat_1(X0))
% 7.38/1.50      | ~ v1_relat_1(X0)
% 7.38/1.50      | ~ v1_relat_1(X1)
% 7.38/1.50      | ~ v1_funct_1(X0)
% 7.38/1.50      | ~ v1_funct_1(X1)
% 7.38/1.50      | X1 = X0
% 7.38/1.50      | k1_relat_1(X1) != k1_relat_1(X0) ),
% 7.38/1.50      inference(cnf_transformation,[],[f41]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_502,plain,
% 7.38/1.50      ( X0 = X1
% 7.38/1.50      | k1_relat_1(X0) != k1_relat_1(X1)
% 7.38/1.50      | r2_hidden(sK3(X1,X0),k1_relat_1(X1)) = iProver_top
% 7.38/1.50      | v1_relat_1(X1) != iProver_top
% 7.38/1.50      | v1_relat_1(X0) != iProver_top
% 7.38/1.50      | v1_funct_1(X1) != iProver_top
% 7.38/1.50      | v1_funct_1(X0) != iProver_top ),
% 7.38/1.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_1328,plain,
% 7.38/1.50      ( k1_relat_1(X0) != sK4
% 7.38/1.50      | sK6 = X0
% 7.38/1.50      | r2_hidden(sK3(sK6,X0),k1_relat_1(sK6)) = iProver_top
% 7.38/1.50      | v1_relat_1(X0) != iProver_top
% 7.38/1.50      | v1_relat_1(sK6) != iProver_top
% 7.38/1.50      | v1_funct_1(X0) != iProver_top
% 7.38/1.50      | v1_funct_1(sK6) != iProver_top ),
% 7.38/1.50      inference(superposition,[status(thm)],[c_15,c_502]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_1330,plain,
% 7.38/1.50      ( k1_relat_1(X0) != sK4
% 7.38/1.50      | sK6 = X0
% 7.38/1.50      | r2_hidden(sK3(sK6,X0),sK4) = iProver_top
% 7.38/1.50      | v1_relat_1(X0) != iProver_top
% 7.38/1.50      | v1_relat_1(sK6) != iProver_top
% 7.38/1.50      | v1_funct_1(X0) != iProver_top
% 7.38/1.50      | v1_funct_1(sK6) != iProver_top ),
% 7.38/1.50      inference(light_normalisation,[status(thm)],[c_1328,c_15]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_20,negated_conjecture,
% 7.38/1.50      ( v1_relat_1(sK6) ),
% 7.38/1.50      inference(cnf_transformation,[],[f45]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_25,plain,
% 7.38/1.50      ( v1_relat_1(sK6) = iProver_top ),
% 7.38/1.50      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_19,negated_conjecture,
% 7.38/1.50      ( v1_funct_1(sK6) ),
% 7.38/1.50      inference(cnf_transformation,[],[f46]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_26,plain,
% 7.38/1.50      ( v1_funct_1(sK6) = iProver_top ),
% 7.38/1.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_1641,plain,
% 7.38/1.50      ( v1_funct_1(X0) != iProver_top
% 7.38/1.50      | k1_relat_1(X0) != sK4
% 7.38/1.50      | sK6 = X0
% 7.38/1.50      | r2_hidden(sK3(sK6,X0),sK4) = iProver_top
% 7.38/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.38/1.50      inference(global_propositional_subsumption,
% 7.38/1.50                [status(thm)],
% 7.38/1.50                [c_1330,c_25,c_26]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_1642,plain,
% 7.38/1.50      ( k1_relat_1(X0) != sK4
% 7.38/1.50      | sK6 = X0
% 7.38/1.50      | r2_hidden(sK3(sK6,X0),sK4) = iProver_top
% 7.38/1.50      | v1_relat_1(X0) != iProver_top
% 7.38/1.50      | v1_funct_1(X0) != iProver_top ),
% 7.38/1.50      inference(renaming,[status(thm)],[c_1641]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_1647,plain,
% 7.38/1.50      ( sK7 = sK6
% 7.38/1.50      | r2_hidden(sK3(sK6,sK7),sK4) = iProver_top
% 7.38/1.50      | v1_relat_1(sK7) != iProver_top
% 7.38/1.50      | v1_funct_1(sK7) != iProver_top ),
% 7.38/1.50      inference(superposition,[status(thm)],[c_14,c_1642]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_18,negated_conjecture,
% 7.38/1.50      ( v1_relat_1(sK7) ),
% 7.38/1.50      inference(cnf_transformation,[],[f47]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_27,plain,
% 7.38/1.50      ( v1_relat_1(sK7) = iProver_top ),
% 7.38/1.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_17,negated_conjecture,
% 7.38/1.50      ( v1_funct_1(sK7) ),
% 7.38/1.50      inference(cnf_transformation,[],[f48]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_28,plain,
% 7.38/1.50      ( v1_funct_1(sK7) = iProver_top ),
% 7.38/1.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_12,negated_conjecture,
% 7.38/1.50      ( sK6 != sK7 ),
% 7.38/1.50      inference(cnf_transformation,[],[f53]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_203,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_544,plain,
% 7.38/1.50      ( sK7 != X0 | sK6 != X0 | sK6 = sK7 ),
% 7.38/1.50      inference(instantiation,[status(thm)],[c_203]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_876,plain,
% 7.38/1.50      ( sK7 != sK6 | sK6 = sK7 | sK6 != sK6 ),
% 7.38/1.50      inference(instantiation,[status(thm)],[c_544]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_202,plain,( X0 = X0 ),theory(equality) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_1040,plain,
% 7.38/1.50      ( sK6 = sK6 ),
% 7.38/1.50      inference(instantiation,[status(thm)],[c_202]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_1677,plain,
% 7.38/1.50      ( r2_hidden(sK3(sK6,sK7),sK4) = iProver_top ),
% 7.38/1.50      inference(global_propositional_subsumption,
% 7.38/1.50                [status(thm)],
% 7.38/1.50                [c_1647,c_27,c_28,c_12,c_876,c_1040]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_5,plain,
% 7.38/1.50      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 7.38/1.50      | r2_hidden(sK2(X1,X0),k1_relat_1(X1))
% 7.38/1.50      | ~ v1_relat_1(X1)
% 7.38/1.50      | ~ v1_funct_1(X1) ),
% 7.38/1.50      inference(cnf_transformation,[],[f57]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_508,plain,
% 7.38/1.50      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 7.38/1.50      | r2_hidden(sK2(X1,X0),k1_relat_1(X1)) = iProver_top
% 7.38/1.50      | v1_relat_1(X1) != iProver_top
% 7.38/1.50      | v1_funct_1(X1) != iProver_top ),
% 7.38/1.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_13,negated_conjecture,
% 7.38/1.50      ( k5_relat_1(sK5,sK6) = k5_relat_1(sK5,sK7) ),
% 7.38/1.50      inference(cnf_transformation,[],[f52]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_6,plain,
% 7.38/1.50      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 7.38/1.50      | r2_hidden(X0,k1_relat_1(k5_relat_1(X1,X2)))
% 7.38/1.50      | ~ r2_hidden(k1_funct_1(X1,X0),k1_relat_1(X2))
% 7.38/1.50      | ~ v1_relat_1(X2)
% 7.38/1.50      | ~ v1_relat_1(X1)
% 7.38/1.50      | ~ v1_funct_1(X2)
% 7.38/1.50      | ~ v1_funct_1(X1) ),
% 7.38/1.50      inference(cnf_transformation,[],[f39]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_507,plain,
% 7.38/1.50      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 7.38/1.50      | r2_hidden(X0,k1_relat_1(k5_relat_1(X1,X2))) = iProver_top
% 7.38/1.50      | r2_hidden(k1_funct_1(X1,X0),k1_relat_1(X2)) != iProver_top
% 7.38/1.50      | v1_relat_1(X1) != iProver_top
% 7.38/1.50      | v1_relat_1(X2) != iProver_top
% 7.38/1.50      | v1_funct_1(X1) != iProver_top
% 7.38/1.50      | v1_funct_1(X2) != iProver_top ),
% 7.38/1.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_3809,plain,
% 7.38/1.50      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 7.38/1.50      | r2_hidden(X0,k1_relat_1(k5_relat_1(X1,sK7))) = iProver_top
% 7.38/1.50      | r2_hidden(k1_funct_1(X1,X0),sK4) != iProver_top
% 7.38/1.50      | v1_relat_1(X1) != iProver_top
% 7.38/1.50      | v1_relat_1(sK7) != iProver_top
% 7.38/1.50      | v1_funct_1(X1) != iProver_top
% 7.38/1.50      | v1_funct_1(sK7) != iProver_top ),
% 7.38/1.50      inference(superposition,[status(thm)],[c_14,c_507]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_3836,plain,
% 7.38/1.50      ( v1_funct_1(X1) != iProver_top
% 7.38/1.50      | r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 7.38/1.50      | r2_hidden(X0,k1_relat_1(k5_relat_1(X1,sK7))) = iProver_top
% 7.38/1.50      | r2_hidden(k1_funct_1(X1,X0),sK4) != iProver_top
% 7.38/1.50      | v1_relat_1(X1) != iProver_top ),
% 7.38/1.50      inference(global_propositional_subsumption,
% 7.38/1.50                [status(thm)],
% 7.38/1.50                [c_3809,c_27,c_28]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_3837,plain,
% 7.38/1.50      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 7.38/1.50      | r2_hidden(X0,k1_relat_1(k5_relat_1(X1,sK7))) = iProver_top
% 7.38/1.50      | r2_hidden(k1_funct_1(X1,X0),sK4) != iProver_top
% 7.38/1.50      | v1_relat_1(X1) != iProver_top
% 7.38/1.50      | v1_funct_1(X1) != iProver_top ),
% 7.38/1.50      inference(renaming,[status(thm)],[c_3836]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_3842,plain,
% 7.38/1.50      ( r2_hidden(X0,k1_relat_1(k5_relat_1(sK5,sK6))) = iProver_top
% 7.38/1.50      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 7.38/1.50      | r2_hidden(k1_funct_1(sK5,X0),sK4) != iProver_top
% 7.38/1.50      | v1_relat_1(sK5) != iProver_top
% 7.38/1.50      | v1_funct_1(sK5) != iProver_top ),
% 7.38/1.50      inference(superposition,[status(thm)],[c_13,c_3837]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_22,negated_conjecture,
% 7.38/1.50      ( v1_relat_1(sK5) ),
% 7.38/1.50      inference(cnf_transformation,[],[f43]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_23,plain,
% 7.38/1.50      ( v1_relat_1(sK5) = iProver_top ),
% 7.38/1.50      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_21,negated_conjecture,
% 7.38/1.50      ( v1_funct_1(sK5) ),
% 7.38/1.50      inference(cnf_transformation,[],[f44]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_24,plain,
% 7.38/1.50      ( v1_funct_1(sK5) = iProver_top ),
% 7.38/1.50      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_16,negated_conjecture,
% 7.38/1.50      ( k2_relat_1(sK5) = sK4 ),
% 7.38/1.50      inference(cnf_transformation,[],[f49]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_3,plain,
% 7.38/1.50      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 7.38/1.50      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 7.38/1.50      | ~ v1_relat_1(X1)
% 7.38/1.50      | ~ v1_funct_1(X1) ),
% 7.38/1.50      inference(cnf_transformation,[],[f55]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_510,plain,
% 7.38/1.50      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 7.38/1.50      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
% 7.38/1.50      | v1_relat_1(X1) != iProver_top
% 7.38/1.50      | v1_funct_1(X1) != iProver_top ),
% 7.38/1.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_1185,plain,
% 7.38/1.50      ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 7.38/1.50      | r2_hidden(k1_funct_1(sK5,X0),sK4) = iProver_top
% 7.38/1.50      | v1_relat_1(sK5) != iProver_top
% 7.38/1.50      | v1_funct_1(sK5) != iProver_top ),
% 7.38/1.50      inference(superposition,[status(thm)],[c_16,c_510]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_1204,plain,
% 7.38/1.50      ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 7.38/1.50      | r2_hidden(k1_funct_1(sK5,X0),sK4) = iProver_top ),
% 7.38/1.50      inference(global_propositional_subsumption,
% 7.38/1.50                [status(thm)],
% 7.38/1.50                [c_1185,c_23,c_24]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_3886,plain,
% 7.38/1.50      ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 7.38/1.50      | r2_hidden(X0,k1_relat_1(k5_relat_1(sK5,sK6))) = iProver_top ),
% 7.38/1.50      inference(global_propositional_subsumption,
% 7.38/1.50                [status(thm)],
% 7.38/1.50                [c_3842,c_23,c_24,c_1185]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_3887,plain,
% 7.38/1.50      ( r2_hidden(X0,k1_relat_1(k5_relat_1(sK5,sK6))) = iProver_top
% 7.38/1.50      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 7.38/1.50      inference(renaming,[status(thm)],[c_3886]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_9,plain,
% 7.38/1.50      ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X1,X2)))
% 7.38/1.50      | ~ v1_relat_1(X2)
% 7.38/1.50      | ~ v1_relat_1(X1)
% 7.38/1.50      | ~ v1_funct_1(X2)
% 7.38/1.50      | ~ v1_funct_1(X1)
% 7.38/1.50      | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ),
% 7.38/1.50      inference(cnf_transformation,[],[f40]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_504,plain,
% 7.38/1.50      ( k1_funct_1(k5_relat_1(X0,X1),X2) = k1_funct_1(X1,k1_funct_1(X0,X2))
% 7.38/1.50      | r2_hidden(X2,k1_relat_1(k5_relat_1(X0,X1))) != iProver_top
% 7.38/1.50      | v1_relat_1(X0) != iProver_top
% 7.38/1.50      | v1_relat_1(X1) != iProver_top
% 7.38/1.50      | v1_funct_1(X0) != iProver_top
% 7.38/1.50      | v1_funct_1(X1) != iProver_top ),
% 7.38/1.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_3895,plain,
% 7.38/1.50      ( k1_funct_1(k5_relat_1(sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
% 7.38/1.50      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 7.38/1.50      | v1_relat_1(sK5) != iProver_top
% 7.38/1.50      | v1_relat_1(sK6) != iProver_top
% 7.38/1.50      | v1_funct_1(sK5) != iProver_top
% 7.38/1.50      | v1_funct_1(sK6) != iProver_top ),
% 7.38/1.50      inference(superposition,[status(thm)],[c_3887,c_504]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_17567,plain,
% 7.38/1.50      ( k1_funct_1(k5_relat_1(sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
% 7.38/1.50      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 7.38/1.50      inference(global_propositional_subsumption,
% 7.38/1.50                [status(thm)],
% 7.38/1.50                [c_3895,c_23,c_24,c_25,c_26]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_17577,plain,
% 7.38/1.50      ( k1_funct_1(sK6,k1_funct_1(sK5,sK2(sK5,X0))) = k1_funct_1(k5_relat_1(sK5,sK6),sK2(sK5,X0))
% 7.38/1.50      | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top
% 7.38/1.50      | v1_relat_1(sK5) != iProver_top
% 7.38/1.50      | v1_funct_1(sK5) != iProver_top ),
% 7.38/1.50      inference(superposition,[status(thm)],[c_508,c_17567]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_17604,plain,
% 7.38/1.50      ( k1_funct_1(sK6,k1_funct_1(sK5,sK2(sK5,X0))) = k1_funct_1(k5_relat_1(sK5,sK6),sK2(sK5,X0))
% 7.38/1.50      | r2_hidden(X0,sK4) != iProver_top
% 7.38/1.50      | v1_relat_1(sK5) != iProver_top
% 7.38/1.50      | v1_funct_1(sK5) != iProver_top ),
% 7.38/1.50      inference(light_normalisation,[status(thm)],[c_17577,c_16]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_17635,plain,
% 7.38/1.50      ( k1_funct_1(sK6,k1_funct_1(sK5,sK2(sK5,X0))) = k1_funct_1(k5_relat_1(sK5,sK6),sK2(sK5,X0))
% 7.38/1.50      | r2_hidden(X0,sK4) != iProver_top ),
% 7.38/1.50      inference(global_propositional_subsumption,
% 7.38/1.50                [status(thm)],
% 7.38/1.50                [c_17604,c_23,c_24]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_17666,plain,
% 7.38/1.50      ( k1_funct_1(sK6,k1_funct_1(sK5,sK2(sK5,sK3(sK6,sK7)))) = k1_funct_1(k5_relat_1(sK5,sK6),sK2(sK5,sK3(sK6,sK7))) ),
% 7.38/1.50      inference(superposition,[status(thm)],[c_1677,c_17635]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_4,plain,
% 7.38/1.50      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 7.38/1.50      | ~ v1_relat_1(X1)
% 7.38/1.50      | ~ v1_funct_1(X1)
% 7.38/1.50      | k1_funct_1(X1,sK2(X1,X0)) = X0 ),
% 7.38/1.50      inference(cnf_transformation,[],[f56]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_509,plain,
% 7.38/1.50      ( k1_funct_1(X0,sK2(X0,X1)) = X1
% 7.38/1.50      | r2_hidden(X1,k2_relat_1(X0)) != iProver_top
% 7.38/1.50      | v1_relat_1(X0) != iProver_top
% 7.38/1.50      | v1_funct_1(X0) != iProver_top ),
% 7.38/1.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_842,plain,
% 7.38/1.50      ( k1_funct_1(sK5,sK2(sK5,X0)) = X0
% 7.38/1.50      | r2_hidden(X0,sK4) != iProver_top
% 7.38/1.50      | v1_relat_1(sK5) != iProver_top
% 7.38/1.50      | v1_funct_1(sK5) != iProver_top ),
% 7.38/1.50      inference(superposition,[status(thm)],[c_16,c_509]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_911,plain,
% 7.38/1.50      ( k1_funct_1(sK5,sK2(sK5,X0)) = X0
% 7.38/1.50      | r2_hidden(X0,sK4) != iProver_top ),
% 7.38/1.50      inference(global_propositional_subsumption,
% 7.38/1.50                [status(thm)],
% 7.38/1.50                [c_842,c_23,c_24]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_1683,plain,
% 7.38/1.50      ( k1_funct_1(sK5,sK2(sK5,sK3(sK6,sK7))) = sK3(sK6,sK7) ),
% 7.38/1.50      inference(superposition,[status(thm)],[c_1677,c_911]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_2858,plain,
% 7.38/1.50      ( k1_funct_1(k5_relat_1(sK5,sK7),X0) = k1_funct_1(sK7,k1_funct_1(sK5,X0))
% 7.38/1.50      | r2_hidden(X0,k1_relat_1(k5_relat_1(sK5,sK6))) != iProver_top
% 7.38/1.50      | v1_relat_1(sK5) != iProver_top
% 7.38/1.50      | v1_relat_1(sK7) != iProver_top
% 7.38/1.50      | v1_funct_1(sK5) != iProver_top
% 7.38/1.50      | v1_funct_1(sK7) != iProver_top ),
% 7.38/1.50      inference(superposition,[status(thm)],[c_13,c_504]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_2859,plain,
% 7.38/1.50      ( k1_funct_1(k5_relat_1(sK5,sK6),X0) = k1_funct_1(sK7,k1_funct_1(sK5,X0))
% 7.38/1.50      | r2_hidden(X0,k1_relat_1(k5_relat_1(sK5,sK6))) != iProver_top
% 7.38/1.50      | v1_relat_1(sK5) != iProver_top
% 7.38/1.50      | v1_relat_1(sK7) != iProver_top
% 7.38/1.50      | v1_funct_1(sK5) != iProver_top
% 7.38/1.50      | v1_funct_1(sK7) != iProver_top ),
% 7.38/1.50      inference(light_normalisation,[status(thm)],[c_2858,c_13]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_3026,plain,
% 7.38/1.50      ( k1_funct_1(k5_relat_1(sK5,sK6),X0) = k1_funct_1(sK7,k1_funct_1(sK5,X0))
% 7.38/1.50      | r2_hidden(X0,k1_relat_1(k5_relat_1(sK5,sK6))) != iProver_top ),
% 7.38/1.50      inference(global_propositional_subsumption,
% 7.38/1.50                [status(thm)],
% 7.38/1.50                [c_2859,c_23,c_24,c_27,c_28]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_3896,plain,
% 7.38/1.50      ( k1_funct_1(k5_relat_1(sK5,sK6),X0) = k1_funct_1(sK7,k1_funct_1(sK5,X0))
% 7.38/1.50      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 7.38/1.50      inference(superposition,[status(thm)],[c_3887,c_3026]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_3992,plain,
% 7.38/1.50      ( k1_funct_1(sK7,k1_funct_1(sK5,sK2(sK5,X0))) = k1_funct_1(k5_relat_1(sK5,sK6),sK2(sK5,X0))
% 7.38/1.50      | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top
% 7.38/1.50      | v1_relat_1(sK5) != iProver_top
% 7.38/1.50      | v1_funct_1(sK5) != iProver_top ),
% 7.38/1.50      inference(superposition,[status(thm)],[c_508,c_3896]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_3996,plain,
% 7.38/1.50      ( k1_funct_1(sK7,k1_funct_1(sK5,sK2(sK5,X0))) = k1_funct_1(k5_relat_1(sK5,sK6),sK2(sK5,X0))
% 7.38/1.50      | r2_hidden(X0,sK4) != iProver_top
% 7.38/1.50      | v1_relat_1(sK5) != iProver_top
% 7.38/1.50      | v1_funct_1(sK5) != iProver_top ),
% 7.38/1.50      inference(light_normalisation,[status(thm)],[c_3992,c_16]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_4013,plain,
% 7.38/1.50      ( k1_funct_1(sK7,k1_funct_1(sK5,sK2(sK5,X0))) = k1_funct_1(k5_relat_1(sK5,sK6),sK2(sK5,X0))
% 7.38/1.50      | r2_hidden(X0,sK4) != iProver_top ),
% 7.38/1.50      inference(global_propositional_subsumption,
% 7.38/1.50                [status(thm)],
% 7.38/1.50                [c_3996,c_23,c_24]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_4029,plain,
% 7.38/1.50      ( k1_funct_1(k5_relat_1(sK5,sK6),sK2(sK5,sK3(sK6,sK7))) = k1_funct_1(sK7,k1_funct_1(sK5,sK2(sK5,sK3(sK6,sK7)))) ),
% 7.38/1.50      inference(superposition,[status(thm)],[c_1677,c_4013]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_4032,plain,
% 7.38/1.50      ( k1_funct_1(k5_relat_1(sK5,sK6),sK2(sK5,sK3(sK6,sK7))) = k1_funct_1(sK7,sK3(sK6,sK7)) ),
% 7.38/1.50      inference(light_normalisation,[status(thm)],[c_4029,c_1683]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_17671,plain,
% 7.38/1.50      ( k1_funct_1(sK6,sK3(sK6,sK7)) = k1_funct_1(sK7,sK3(sK6,sK7)) ),
% 7.38/1.50      inference(light_normalisation,
% 7.38/1.50                [status(thm)],
% 7.38/1.50                [c_17666,c_1683,c_4032]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_5133,plain,
% 7.38/1.50      ( k1_funct_1(sK7,sK3(sK6,sK7)) = k1_funct_1(sK7,sK3(sK6,sK7)) ),
% 7.38/1.50      inference(instantiation,[status(thm)],[c_202]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_1594,plain,
% 7.38/1.50      ( k1_funct_1(sK7,sK3(sK6,sK7)) != X0
% 7.38/1.50      | k1_funct_1(sK7,sK3(sK6,sK7)) = k1_funct_1(sK6,sK3(sK6,sK7))
% 7.38/1.50      | k1_funct_1(sK6,sK3(sK6,sK7)) != X0 ),
% 7.38/1.50      inference(instantiation,[status(thm)],[c_203]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_2094,plain,
% 7.38/1.50      ( k1_funct_1(sK7,sK3(sK6,sK7)) != k1_funct_1(sK7,sK3(sK6,sK7))
% 7.38/1.50      | k1_funct_1(sK7,sK3(sK6,sK7)) = k1_funct_1(sK6,sK3(sK6,sK7))
% 7.38/1.50      | k1_funct_1(sK6,sK3(sK6,sK7)) != k1_funct_1(sK7,sK3(sK6,sK7)) ),
% 7.38/1.50      inference(instantiation,[status(thm)],[c_1594]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_10,plain,
% 7.38/1.50      ( ~ v1_relat_1(X0)
% 7.38/1.50      | ~ v1_relat_1(X1)
% 7.38/1.50      | ~ v1_funct_1(X0)
% 7.38/1.50      | ~ v1_funct_1(X1)
% 7.38/1.50      | X1 = X0
% 7.38/1.50      | k1_funct_1(X1,sK3(X0,X1)) != k1_funct_1(X0,sK3(X0,X1))
% 7.38/1.50      | k1_relat_1(X1) != k1_relat_1(X0) ),
% 7.38/1.50      inference(cnf_transformation,[],[f42]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_559,plain,
% 7.38/1.50      ( ~ v1_relat_1(X0)
% 7.38/1.50      | ~ v1_relat_1(sK7)
% 7.38/1.50      | ~ v1_funct_1(X0)
% 7.38/1.50      | ~ v1_funct_1(sK7)
% 7.38/1.50      | k1_funct_1(sK7,sK3(X0,sK7)) != k1_funct_1(X0,sK3(X0,sK7))
% 7.38/1.50      | k1_relat_1(sK7) != k1_relat_1(X0)
% 7.38/1.50      | sK7 = X0 ),
% 7.38/1.50      inference(instantiation,[status(thm)],[c_10]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_726,plain,
% 7.38/1.50      ( ~ v1_relat_1(sK7)
% 7.38/1.50      | ~ v1_relat_1(sK6)
% 7.38/1.50      | ~ v1_funct_1(sK7)
% 7.38/1.50      | ~ v1_funct_1(sK6)
% 7.38/1.50      | k1_funct_1(sK7,sK3(sK6,sK7)) != k1_funct_1(sK6,sK3(sK6,sK7))
% 7.38/1.50      | k1_relat_1(sK7) != k1_relat_1(sK6)
% 7.38/1.50      | sK7 = sK6 ),
% 7.38/1.50      inference(instantiation,[status(thm)],[c_559]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_591,plain,
% 7.38/1.50      ( X0 != X1 | k1_relat_1(sK7) != X1 | k1_relat_1(sK7) = X0 ),
% 7.38/1.50      inference(instantiation,[status(thm)],[c_203]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_636,plain,
% 7.38/1.50      ( X0 != sK4 | k1_relat_1(sK7) = X0 | k1_relat_1(sK7) != sK4 ),
% 7.38/1.50      inference(instantiation,[status(thm)],[c_591]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_653,plain,
% 7.38/1.50      ( k1_relat_1(sK7) = k1_relat_1(sK6)
% 7.38/1.50      | k1_relat_1(sK7) != sK4
% 7.38/1.50      | k1_relat_1(sK6) != sK4 ),
% 7.38/1.50      inference(instantiation,[status(thm)],[c_636]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(contradiction,plain,
% 7.38/1.50      ( $false ),
% 7.38/1.50      inference(minisat,
% 7.38/1.50                [status(thm)],
% 7.38/1.50                [c_17671,c_5133,c_2094,c_1040,c_876,c_726,c_653,c_12,
% 7.38/1.50                 c_14,c_15,c_17,c_18,c_19,c_20]) ).
% 7.38/1.50  
% 7.38/1.50  
% 7.38/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.38/1.50  
% 7.38/1.50  ------                               Statistics
% 7.38/1.50  
% 7.38/1.50  ------ General
% 7.38/1.50  
% 7.38/1.50  abstr_ref_over_cycles:                  0
% 7.38/1.50  abstr_ref_under_cycles:                 0
% 7.38/1.50  gc_basic_clause_elim:                   0
% 7.38/1.50  forced_gc_time:                         0
% 7.38/1.50  parsing_time:                           0.014
% 7.38/1.50  unif_index_cands_time:                  0.
% 7.38/1.50  unif_index_add_time:                    0.
% 7.38/1.50  orderings_time:                         0.
% 7.38/1.50  out_proof_time:                         0.011
% 7.38/1.50  total_time:                             0.551
% 7.38/1.50  num_of_symbols:                         46
% 7.38/1.50  num_of_terms:                           12652
% 7.38/1.50  
% 7.38/1.50  ------ Preprocessing
% 7.38/1.50  
% 7.38/1.50  num_of_splits:                          0
% 7.38/1.50  num_of_split_atoms:                     0
% 7.38/1.50  num_of_reused_defs:                     0
% 7.38/1.50  num_eq_ax_congr_red:                    16
% 7.38/1.50  num_of_sem_filtered_clauses:            1
% 7.38/1.50  num_of_subtypes:                        0
% 7.38/1.50  monotx_restored_types:                  0
% 7.38/1.50  sat_num_of_epr_types:                   0
% 7.38/1.50  sat_num_of_non_cyclic_types:            0
% 7.38/1.50  sat_guarded_non_collapsed_types:        0
% 7.38/1.50  num_pure_diseq_elim:                    0
% 7.38/1.50  simp_replaced_by:                       0
% 7.38/1.50  res_preprocessed:                       88
% 7.38/1.50  prep_upred:                             0
% 7.38/1.50  prep_unflattend:                        0
% 7.38/1.50  smt_new_axioms:                         0
% 7.38/1.50  pred_elim_cands:                        3
% 7.38/1.50  pred_elim:                              0
% 7.38/1.50  pred_elim_cl:                           0
% 7.38/1.50  pred_elim_cycles:                       1
% 7.38/1.50  merged_defs:                            0
% 7.38/1.50  merged_defs_ncl:                        0
% 7.38/1.50  bin_hyper_res:                          0
% 7.38/1.50  prep_cycles:                            3
% 7.38/1.50  pred_elim_time:                         0.
% 7.38/1.50  splitting_time:                         0.
% 7.38/1.50  sem_filter_time:                        0.
% 7.38/1.50  monotx_time:                            0.001
% 7.38/1.50  subtype_inf_time:                       0.
% 7.38/1.50  
% 7.38/1.50  ------ Problem properties
% 7.38/1.50  
% 7.38/1.50  clauses:                                23
% 7.38/1.50  conjectures:                            11
% 7.38/1.50  epr:                                    7
% 7.38/1.50  horn:                                   20
% 7.38/1.50  ground:                                 11
% 7.38/1.50  unary:                                  11
% 7.38/1.50  binary:                                 0
% 7.38/1.50  lits:                                   78
% 7.38/1.50  lits_eq:                                17
% 7.38/1.50  fd_pure:                                0
% 7.38/1.50  fd_pseudo:                              0
% 7.38/1.50  fd_cond:                                0
% 7.38/1.50  fd_pseudo_cond:                         5
% 7.38/1.50  ac_symbols:                             0
% 7.38/1.50  
% 7.38/1.50  ------ Propositional Solver
% 7.38/1.50  
% 7.38/1.50  prop_solver_calls:                      30
% 7.38/1.50  prop_fast_solver_calls:                 1813
% 7.38/1.50  smt_solver_calls:                       0
% 7.38/1.50  smt_fast_solver_calls:                  0
% 7.38/1.50  prop_num_of_clauses:                    6211
% 7.38/1.50  prop_preprocess_simplified:             7720
% 7.38/1.50  prop_fo_subsumed:                       223
% 7.38/1.50  prop_solver_time:                       0.
% 7.38/1.50  smt_solver_time:                        0.
% 7.38/1.50  smt_fast_solver_time:                   0.
% 7.38/1.50  prop_fast_solver_time:                  0.
% 7.38/1.50  prop_unsat_core_time:                   0.
% 7.38/1.50  
% 7.38/1.50  ------ QBF
% 7.38/1.50  
% 7.38/1.50  qbf_q_res:                              0
% 7.38/1.50  qbf_num_tautologies:                    0
% 7.38/1.50  qbf_prep_cycles:                        0
% 7.38/1.50  
% 7.38/1.50  ------ BMC1
% 7.38/1.50  
% 7.38/1.50  bmc1_current_bound:                     -1
% 7.38/1.50  bmc1_last_solved_bound:                 -1
% 7.38/1.50  bmc1_unsat_core_size:                   -1
% 7.38/1.50  bmc1_unsat_core_parents_size:           -1
% 7.38/1.50  bmc1_merge_next_fun:                    0
% 7.38/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.38/1.50  
% 7.38/1.50  ------ Instantiation
% 7.38/1.50  
% 7.38/1.50  inst_num_of_clauses:                    1306
% 7.38/1.50  inst_num_in_passive:                    89
% 7.38/1.50  inst_num_in_active:                     826
% 7.38/1.50  inst_num_in_unprocessed:                391
% 7.38/1.50  inst_num_of_loops:                      930
% 7.38/1.50  inst_num_of_learning_restarts:          0
% 7.38/1.50  inst_num_moves_active_passive:          97
% 7.38/1.50  inst_lit_activity:                      0
% 7.38/1.50  inst_lit_activity_moves:                0
% 7.38/1.50  inst_num_tautologies:                   0
% 7.38/1.50  inst_num_prop_implied:                  0
% 7.38/1.50  inst_num_existing_simplified:           0
% 7.38/1.50  inst_num_eq_res_simplified:             0
% 7.38/1.50  inst_num_child_elim:                    0
% 7.38/1.50  inst_num_of_dismatching_blockings:      1860
% 7.38/1.50  inst_num_of_non_proper_insts:           3073
% 7.38/1.50  inst_num_of_duplicates:                 0
% 7.38/1.50  inst_inst_num_from_inst_to_res:         0
% 7.38/1.50  inst_dismatching_checking_time:         0.
% 7.38/1.50  
% 7.38/1.50  ------ Resolution
% 7.38/1.50  
% 7.38/1.50  res_num_of_clauses:                     0
% 7.38/1.50  res_num_in_passive:                     0
% 7.38/1.50  res_num_in_active:                      0
% 7.38/1.50  res_num_of_loops:                       91
% 7.38/1.50  res_forward_subset_subsumed:            666
% 7.38/1.50  res_backward_subset_subsumed:           2
% 7.38/1.50  res_forward_subsumed:                   0
% 7.38/1.50  res_backward_subsumed:                  0
% 7.38/1.50  res_forward_subsumption_resolution:     0
% 7.38/1.50  res_backward_subsumption_resolution:    0
% 7.38/1.50  res_clause_to_clause_subsumption:       2262
% 7.38/1.50  res_orphan_elimination:                 0
% 7.38/1.50  res_tautology_del:                      528
% 7.38/1.50  res_num_eq_res_simplified:              0
% 7.38/1.50  res_num_sel_changes:                    0
% 7.38/1.50  res_moves_from_active_to_pass:          0
% 7.38/1.50  
% 7.38/1.50  ------ Superposition
% 7.38/1.50  
% 7.38/1.50  sup_time_total:                         0.
% 7.38/1.50  sup_time_generating:                    0.
% 7.38/1.50  sup_time_sim_full:                      0.
% 7.38/1.50  sup_time_sim_immed:                     0.
% 7.38/1.50  
% 7.38/1.50  sup_num_of_clauses:                     1188
% 7.38/1.50  sup_num_in_active:                      186
% 7.38/1.50  sup_num_in_passive:                     1002
% 7.38/1.50  sup_num_of_loops:                       185
% 7.38/1.50  sup_fw_superposition:                   735
% 7.38/1.50  sup_bw_superposition:                   805
% 7.38/1.50  sup_immediate_simplified:               258
% 7.38/1.50  sup_given_eliminated:                   0
% 7.38/1.50  comparisons_done:                       0
% 7.38/1.50  comparisons_avoided:                    121
% 7.38/1.50  
% 7.38/1.50  ------ Simplifications
% 7.38/1.50  
% 7.38/1.50  
% 7.38/1.50  sim_fw_subset_subsumed:                 73
% 7.38/1.50  sim_bw_subset_subsumed:                 7
% 7.38/1.50  sim_fw_subsumed:                        8
% 7.38/1.50  sim_bw_subsumed:                        0
% 7.38/1.50  sim_fw_subsumption_res:                 0
% 7.38/1.50  sim_bw_subsumption_res:                 0
% 7.38/1.50  sim_tautology_del:                      36
% 7.38/1.50  sim_eq_tautology_del:                   213
% 7.38/1.50  sim_eq_res_simp:                        0
% 7.38/1.50  sim_fw_demodulated:                     17
% 7.38/1.50  sim_bw_demodulated:                     0
% 7.38/1.50  sim_light_normalised:                   165
% 7.38/1.50  sim_joinable_taut:                      0
% 7.38/1.50  sim_joinable_simp:                      0
% 7.38/1.50  sim_ac_normalised:                      0
% 7.38/1.50  sim_smt_subsumption:                    0
% 7.38/1.50  
%------------------------------------------------------------------------------
