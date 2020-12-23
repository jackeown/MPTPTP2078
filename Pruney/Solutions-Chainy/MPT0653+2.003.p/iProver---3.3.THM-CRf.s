%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:50:41 EST 2020

% Result     : Theorem 3.52s
% Output     : CNFRefutation 3.52s
% Verified   : 
% Statistics : Number of formulae       :  143 (1521 expanded)
%              Number of clauses        :   98 ( 411 expanded)
%              Number of leaves         :   15 ( 372 expanded)
%              Depth                    :   20
%              Number of atoms          :  571 (14831 expanded)
%              Number of equality atoms :  298 (6990 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   28 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
              & k2_relat_1(X0) = k1_relat_1(X1)
              & k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
                & k2_relat_1(X0) = k1_relat_1(X1)
                & k2_relat_1(X1) = k1_relat_1(X0)
                & v2_funct_1(X0) )
             => k2_funct_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f26,plain,(
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
     => ( k2_funct_1(X0) != sK2
        & ! [X3,X2] :
            ( ( ( k1_funct_1(X0,X2) = X3
                | k1_funct_1(sK2,X3) != X2 )
              & ( k1_funct_1(sK2,X3) = X2
                | k1_funct_1(X0,X2) != X3 ) )
            | ~ r2_hidden(X3,k1_relat_1(sK2))
            | ~ r2_hidden(X2,k1_relat_1(X0)) )
        & k2_relat_1(X0) = k1_relat_1(sK2)
        & k2_relat_1(sK2) = k1_relat_1(X0)
        & v2_funct_1(X0)
        & v1_funct_1(sK2)
        & v1_relat_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
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
          ( k2_funct_1(sK1) != X1
          & ! [X3,X2] :
              ( ( ( k1_funct_1(sK1,X2) = X3
                  | k1_funct_1(X1,X3) != X2 )
                & ( k1_funct_1(X1,X3) = X2
                  | k1_funct_1(sK1,X2) != X3 ) )
              | ~ r2_hidden(X3,k1_relat_1(X1))
              | ~ r2_hidden(X2,k1_relat_1(sK1)) )
          & k2_relat_1(sK1) = k1_relat_1(X1)
          & k2_relat_1(X1) = k1_relat_1(sK1)
          & v2_funct_1(sK1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( k2_funct_1(sK1) != sK2
    & ! [X2,X3] :
        ( ( ( k1_funct_1(sK1,X2) = X3
            | k1_funct_1(sK2,X3) != X2 )
          & ( k1_funct_1(sK2,X3) = X2
            | k1_funct_1(sK1,X2) != X3 ) )
        | ~ r2_hidden(X3,k1_relat_1(sK2))
        | ~ r2_hidden(X2,k1_relat_1(sK1)) )
    & k2_relat_1(sK1) = k1_relat_1(sK2)
    & k2_relat_1(sK2) = k1_relat_1(sK1)
    & v2_funct_1(sK1)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f24,f26,f25])).

fof(f44,plain,(
    k2_relat_1(sK1) = k1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f38,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f28,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
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
    inference(flattening,[],[f18])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1))
        & r2_hidden(sK0(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ( k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1))
            & r2_hidden(sK0(X0,X1),k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f22])).

fof(f36,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK0(X0,X1),k1_relat_1(X0))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f39,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f11,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f30,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f42,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f13,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f32,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f31,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f40,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f41,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f47,plain,(
    k2_funct_1(sK1) != sK2 ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k1_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
          & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f43,plain,(
    k2_relat_1(sK2) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f46,plain,(
    ! [X2,X3] :
      ( k1_funct_1(sK1,X2) = X3
      | k1_funct_1(sK2,X3) != X2
      | ~ r2_hidden(X3,k1_relat_1(sK2))
      | ~ r2_hidden(X2,k1_relat_1(sK1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f48,plain,(
    ! [X3] :
      ( k1_funct_1(sK1,k1_funct_1(sK2,X3)) = X3
      | ~ r2_hidden(X3,k1_relat_1(sK2))
      | ~ r2_hidden(k1_funct_1(sK2,X3),k1_relat_1(sK1)) ) ),
    inference(equality_resolution,[],[f46])).

fof(f37,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_13,negated_conjecture,
    ( k2_relat_1(sK1) = k1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_359,negated_conjecture,
    ( k2_relat_1(sK1) = k1_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_19,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_354,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_682,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_354])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_368,plain,
    ( ~ v1_relat_1(X0_43)
    | k1_relat_1(k4_relat_1(X0_43)) = k2_relat_1(X0_43) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_671,plain,
    ( k1_relat_1(k4_relat_1(X0_43)) = k2_relat_1(X0_43)
    | v1_relat_1(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_368])).

cnf(c_987,plain,
    ( k1_relat_1(k4_relat_1(sK1)) = k2_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_682,c_671])).

cnf(c_9,plain,
    ( r2_hidden(sK0(X0,X1),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | X1 = X0
    | k1_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_363,plain,
    ( r2_hidden(sK0(X0_43,X1_43),k1_relat_1(X0_43))
    | ~ v1_funct_1(X0_43)
    | ~ v1_funct_1(X1_43)
    | ~ v1_relat_1(X0_43)
    | ~ v1_relat_1(X1_43)
    | X1_43 = X0_43
    | k1_relat_1(X1_43) != k1_relat_1(X0_43) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_676,plain,
    ( X0_43 = X1_43
    | k1_relat_1(X0_43) != k1_relat_1(X1_43)
    | r2_hidden(sK0(X1_43,X0_43),k1_relat_1(X1_43)) = iProver_top
    | v1_funct_1(X0_43) != iProver_top
    | v1_funct_1(X1_43) != iProver_top
    | v1_relat_1(X0_43) != iProver_top
    | v1_relat_1(X1_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_363])).

cnf(c_2243,plain,
    ( k4_relat_1(sK1) = X0_43
    | k1_relat_1(X0_43) != k2_relat_1(sK1)
    | r2_hidden(sK0(X0_43,k4_relat_1(sK1)),k1_relat_1(X0_43)) = iProver_top
    | v1_funct_1(X0_43) != iProver_top
    | v1_funct_1(k4_relat_1(sK1)) != iProver_top
    | v1_relat_1(X0_43) != iProver_top
    | v1_relat_1(k4_relat_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_987,c_676])).

cnf(c_20,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_18,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_21,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_15,negated_conjecture,
    ( v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_194,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_15])).

cnf(c_195,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k2_funct_1(sK1) = k4_relat_1(sK1) ),
    inference(unflattening,[status(thm)],[c_194])).

cnf(c_53,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k2_funct_1(sK1) = k4_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_197,plain,
    ( k2_funct_1(sK1) = k4_relat_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_195,c_19,c_18,c_15,c_53])).

cnf(c_353,plain,
    ( k2_funct_1(sK1) = k4_relat_1(sK1) ),
    inference(subtyping,[status(esa)],[c_197])).

cnf(c_3,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_367,plain,
    ( ~ v1_funct_1(X0_43)
    | v1_funct_1(k2_funct_1(X0_43))
    | ~ v1_relat_1(X0_43) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_672,plain,
    ( v1_funct_1(X0_43) != iProver_top
    | v1_funct_1(k2_funct_1(X0_43)) = iProver_top
    | v1_relat_1(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_367])).

cnf(c_1222,plain,
    ( v1_funct_1(k4_relat_1(sK1)) = iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_353,c_672])).

cnf(c_4,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_366,plain,
    ( ~ v1_funct_1(X0_43)
    | ~ v1_relat_1(X0_43)
    | v1_relat_1(k2_funct_1(X0_43)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_673,plain,
    ( v1_funct_1(X0_43) != iProver_top
    | v1_relat_1(X0_43) != iProver_top
    | v1_relat_1(k2_funct_1(X0_43)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_366])).

cnf(c_1297,plain,
    ( v1_funct_1(sK1) != iProver_top
    | v1_relat_1(k4_relat_1(sK1)) = iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_353,c_673])).

cnf(c_10050,plain,
    ( v1_relat_1(X0_43) != iProver_top
    | k4_relat_1(sK1) = X0_43
    | k1_relat_1(X0_43) != k2_relat_1(sK1)
    | r2_hidden(sK0(X0_43,k4_relat_1(sK1)),k1_relat_1(X0_43)) = iProver_top
    | v1_funct_1(X0_43) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2243,c_20,c_21,c_1222,c_1297])).

cnf(c_10051,plain,
    ( k4_relat_1(sK1) = X0_43
    | k1_relat_1(X0_43) != k2_relat_1(sK1)
    | r2_hidden(sK0(X0_43,k4_relat_1(sK1)),k1_relat_1(X0_43)) = iProver_top
    | v1_funct_1(X0_43) != iProver_top
    | v1_relat_1(X0_43) != iProver_top ),
    inference(renaming,[status(thm)],[c_10050])).

cnf(c_10061,plain,
    ( k4_relat_1(sK1) = sK2
    | r2_hidden(sK0(sK2,k4_relat_1(sK1)),k1_relat_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_359,c_10051])).

cnf(c_10091,plain,
    ( k4_relat_1(sK1) = sK2
    | r2_hidden(sK0(sK2,k4_relat_1(sK1)),k2_relat_1(sK1)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10061,c_359])).

cnf(c_17,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_22,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_16,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_23,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_403,plain,
    ( ~ v1_relat_1(sK1)
    | k1_relat_1(k4_relat_1(sK1)) = k2_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_368])).

cnf(c_10,negated_conjecture,
    ( k2_funct_1(sK1) != sK2 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_362,negated_conjecture,
    ( k2_funct_1(sK1) != sK2 ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_700,plain,
    ( k4_relat_1(sK1) != sK2 ),
    inference(demodulation,[status(thm)],[c_353,c_362])).

cnf(c_373,plain,
    ( X0_43 = X0_43 ),
    theory(equality)).

cnf(c_882,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_373])).

cnf(c_379,plain,
    ( X0_43 != X1_43
    | k1_relat_1(X0_43) = k1_relat_1(X1_43) ),
    theory(equality)).

cnf(c_876,plain,
    ( sK2 != X0_43
    | k1_relat_1(sK2) = k1_relat_1(X0_43) ),
    inference(instantiation,[status(thm)],[c_379])).

cnf(c_913,plain,
    ( sK2 != sK2
    | k1_relat_1(sK2) = k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_876])).

cnf(c_375,plain,
    ( X0_42 != X1_42
    | X2_42 != X1_42
    | X2_42 = X0_42 ),
    theory(equality)).

cnf(c_874,plain,
    ( X0_42 != X1_42
    | k1_relat_1(sK2) != X1_42
    | k1_relat_1(sK2) = X0_42 ),
    inference(instantiation,[status(thm)],[c_375])).

cnf(c_928,plain,
    ( X0_42 != k1_relat_1(sK2)
    | k1_relat_1(sK2) = X0_42
    | k1_relat_1(sK2) != k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_874])).

cnf(c_949,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(sK1)
    | k2_relat_1(sK1) != k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_928])).

cnf(c_955,plain,
    ( X0_42 != X1_42
    | X0_42 = k1_relat_1(sK2)
    | k1_relat_1(sK2) != X1_42 ),
    inference(instantiation,[status(thm)],[c_375])).

cnf(c_1016,plain,
    ( X0_42 = k1_relat_1(sK2)
    | X0_42 != k2_relat_1(sK1)
    | k1_relat_1(sK2) != k2_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_955])).

cnf(c_1110,plain,
    ( k1_relat_1(k4_relat_1(sK1)) = k1_relat_1(sK2)
    | k1_relat_1(k4_relat_1(sK1)) != k2_relat_1(sK1)
    | k1_relat_1(sK2) != k2_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1016])).

cnf(c_915,plain,
    ( r2_hidden(sK0(sK2,X0_43),k1_relat_1(sK2))
    | ~ v1_funct_1(X0_43)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(X0_43)
    | ~ v1_relat_1(sK2)
    | X0_43 = sK2
    | k1_relat_1(X0_43) != k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_363])).

cnf(c_1212,plain,
    ( r2_hidden(sK0(sK2,k4_relat_1(sK1)),k1_relat_1(sK2))
    | ~ v1_funct_1(k4_relat_1(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(k4_relat_1(sK1))
    | ~ v1_relat_1(sK2)
    | k4_relat_1(sK1) = sK2
    | k1_relat_1(k4_relat_1(sK1)) != k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_915])).

cnf(c_1216,plain,
    ( k4_relat_1(sK1) = sK2
    | k1_relat_1(k4_relat_1(sK1)) != k1_relat_1(sK2)
    | r2_hidden(sK0(sK2,k4_relat_1(sK1)),k1_relat_1(sK2)) = iProver_top
    | v1_funct_1(k4_relat_1(sK1)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k4_relat_1(sK1)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1212])).

cnf(c_384,plain,
    ( ~ r2_hidden(X0_41,X0_42)
    | r2_hidden(X1_41,X1_42)
    | X1_42 != X0_42
    | X1_41 != X0_41 ),
    theory(equality)).

cnf(c_972,plain,
    ( r2_hidden(X0_41,X0_42)
    | ~ r2_hidden(sK0(sK2,X0_43),k1_relat_1(sK2))
    | X0_42 != k1_relat_1(sK2)
    | X0_41 != sK0(sK2,X0_43) ),
    inference(instantiation,[status(thm)],[c_384])).

cnf(c_1060,plain,
    ( r2_hidden(X0_41,k2_relat_1(sK1))
    | ~ r2_hidden(sK0(sK2,X0_43),k1_relat_1(sK2))
    | k2_relat_1(sK1) != k1_relat_1(sK2)
    | X0_41 != sK0(sK2,X0_43) ),
    inference(instantiation,[status(thm)],[c_972])).

cnf(c_2450,plain,
    ( r2_hidden(X0_41,k2_relat_1(sK1))
    | ~ r2_hidden(sK0(sK2,k4_relat_1(sK1)),k1_relat_1(sK2))
    | k2_relat_1(sK1) != k1_relat_1(sK2)
    | X0_41 != sK0(sK2,k4_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_1060])).

cnf(c_2710,plain,
    ( ~ r2_hidden(sK0(sK2,k4_relat_1(sK1)),k1_relat_1(sK2))
    | r2_hidden(sK0(sK2,k4_relat_1(sK1)),k2_relat_1(sK1))
    | k2_relat_1(sK1) != k1_relat_1(sK2)
    | sK0(sK2,k4_relat_1(sK1)) != sK0(sK2,k4_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_2450])).

cnf(c_2712,plain,
    ( k2_relat_1(sK1) != k1_relat_1(sK2)
    | sK0(sK2,k4_relat_1(sK1)) != sK0(sK2,k4_relat_1(sK1))
    | r2_hidden(sK0(sK2,k4_relat_1(sK1)),k1_relat_1(sK2)) != iProver_top
    | r2_hidden(sK0(sK2,k4_relat_1(sK1)),k2_relat_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2710])).

cnf(c_371,plain,
    ( X0_41 = X0_41 ),
    theory(equality)).

cnf(c_2711,plain,
    ( sK0(sK2,k4_relat_1(sK1)) = sK0(sK2,k4_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_371])).

cnf(c_10100,plain,
    ( r2_hidden(sK0(sK2,k4_relat_1(sK1)),k2_relat_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10091,c_19,c_20,c_21,c_22,c_23,c_403,c_359,c_700,c_882,c_913,c_949,c_1110,c_1216,c_1222,c_1297,c_2712,c_2711])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_365,plain,
    ( ~ r2_hidden(X0_41,k1_relat_1(X0_43))
    | r2_hidden(k1_funct_1(X0_43,X0_41),k2_relat_1(X0_43))
    | ~ v1_funct_1(X0_43)
    | ~ v1_relat_1(X0_43) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_674,plain,
    ( r2_hidden(X0_41,k1_relat_1(X0_43)) != iProver_top
    | r2_hidden(k1_funct_1(X0_43,X0_41),k2_relat_1(X0_43)) = iProver_top
    | v1_funct_1(X0_43) != iProver_top
    | v1_relat_1(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_365])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_202,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_15])).

cnf(c_203,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_202])).

cnf(c_207,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK1))
    | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_203,c_19,c_18])).

cnf(c_352,plain,
    ( ~ r2_hidden(X0_41,k1_relat_1(sK1))
    | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0_41)) = X0_41 ),
    inference(subtyping,[status(esa)],[c_207])).

cnf(c_683,plain,
    ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0_41)) = X0_41
    | r2_hidden(X0_41,k1_relat_1(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_352])).

cnf(c_14,negated_conjecture,
    ( k2_relat_1(sK2) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_358,negated_conjecture,
    ( k2_relat_1(sK2) = k1_relat_1(sK1) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_712,plain,
    ( k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,X0_41)) = X0_41
    | r2_hidden(X0_41,k2_relat_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_683,c_353,c_358])).

cnf(c_1333,plain,
    ( k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,k1_funct_1(sK2,X0_41))) = k1_funct_1(sK2,X0_41)
    | r2_hidden(X0_41,k1_relat_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_674,c_712])).

cnf(c_1360,plain,
    ( k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,k1_funct_1(sK2,X0_41))) = k1_funct_1(sK2,X0_41)
    | r2_hidden(X0_41,k2_relat_1(sK1)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1333,c_359])).

cnf(c_1666,plain,
    ( k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,k1_funct_1(sK2,X0_41))) = k1_funct_1(sK2,X0_41)
    | r2_hidden(X0_41,k2_relat_1(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1360,c_22,c_23])).

cnf(c_10147,plain,
    ( k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,k1_funct_1(sK2,sK0(sK2,k4_relat_1(sK1))))) = k1_funct_1(sK2,sK0(sK2,k4_relat_1(sK1))) ),
    inference(superposition,[status(thm)],[c_10100,c_1666])).

cnf(c_11,negated_conjecture,
    ( ~ r2_hidden(X0,k1_relat_1(sK2))
    | ~ r2_hidden(k1_funct_1(sK2,X0),k1_relat_1(sK1))
    | k1_funct_1(sK1,k1_funct_1(sK2,X0)) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_361,negated_conjecture,
    ( ~ r2_hidden(X0_41,k1_relat_1(sK2))
    | ~ r2_hidden(k1_funct_1(sK2,X0_41),k1_relat_1(sK1))
    | k1_funct_1(sK1,k1_funct_1(sK2,X0_41)) = X0_41 ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_677,plain,
    ( k1_funct_1(sK1,k1_funct_1(sK2,X0_41)) = X0_41
    | r2_hidden(X0_41,k1_relat_1(sK2)) != iProver_top
    | r2_hidden(k1_funct_1(sK2,X0_41),k1_relat_1(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_361])).

cnf(c_734,plain,
    ( k1_funct_1(sK1,k1_funct_1(sK2,X0_41)) = X0_41
    | r2_hidden(X0_41,k2_relat_1(sK1)) != iProver_top
    | r2_hidden(k1_funct_1(sK2,X0_41),k2_relat_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_677,c_358,c_359])).

cnf(c_1334,plain,
    ( k1_funct_1(sK1,k1_funct_1(sK2,X0_41)) = X0_41
    | r2_hidden(X0_41,k1_relat_1(sK2)) != iProver_top
    | r2_hidden(X0_41,k2_relat_1(sK1)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_674,c_734])).

cnf(c_1351,plain,
    ( k1_funct_1(sK1,k1_funct_1(sK2,X0_41)) = X0_41
    | r2_hidden(X0_41,k2_relat_1(sK1)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1334,c_359])).

cnf(c_1482,plain,
    ( k1_funct_1(sK1,k1_funct_1(sK2,X0_41)) = X0_41
    | r2_hidden(X0_41,k2_relat_1(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1351,c_22,c_23])).

cnf(c_10149,plain,
    ( k1_funct_1(sK1,k1_funct_1(sK2,sK0(sK2,k4_relat_1(sK1)))) = sK0(sK2,k4_relat_1(sK1)) ),
    inference(superposition,[status(thm)],[c_10100,c_1482])).

cnf(c_10153,plain,
    ( k1_funct_1(k4_relat_1(sK1),sK0(sK2,k4_relat_1(sK1))) = k1_funct_1(sK2,sK0(sK2,k4_relat_1(sK1))) ),
    inference(light_normalisation,[status(thm)],[c_10147,c_10149])).

cnf(c_8,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | X1 = X0
    | k1_funct_1(X1,sK0(X0,X1)) != k1_funct_1(X0,sK0(X0,X1))
    | k1_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_364,plain,
    ( ~ v1_funct_1(X0_43)
    | ~ v1_funct_1(X1_43)
    | ~ v1_relat_1(X0_43)
    | ~ v1_relat_1(X1_43)
    | X1_43 = X0_43
    | k1_relat_1(X1_43) != k1_relat_1(X0_43)
    | k1_funct_1(X1_43,sK0(X0_43,X1_43)) != k1_funct_1(X0_43,sK0(X0_43,X1_43)) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_914,plain,
    ( ~ v1_funct_1(X0_43)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(X0_43)
    | ~ v1_relat_1(sK2)
    | X0_43 = sK2
    | k1_relat_1(X0_43) != k1_relat_1(sK2)
    | k1_funct_1(X0_43,sK0(sK2,X0_43)) != k1_funct_1(sK2,sK0(sK2,X0_43)) ),
    inference(instantiation,[status(thm)],[c_364])).

cnf(c_1213,plain,
    ( ~ v1_funct_1(k4_relat_1(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(k4_relat_1(sK1))
    | ~ v1_relat_1(sK2)
    | k4_relat_1(sK1) = sK2
    | k1_relat_1(k4_relat_1(sK1)) != k1_relat_1(sK2)
    | k1_funct_1(k4_relat_1(sK1),sK0(sK2,k4_relat_1(sK1))) != k1_funct_1(sK2,sK0(sK2,k4_relat_1(sK1))) ),
    inference(instantiation,[status(thm)],[c_914])).

cnf(c_1214,plain,
    ( k4_relat_1(sK1) = sK2
    | k1_relat_1(k4_relat_1(sK1)) != k1_relat_1(sK2)
    | k1_funct_1(k4_relat_1(sK1),sK0(sK2,k4_relat_1(sK1))) != k1_funct_1(sK2,sK0(sK2,k4_relat_1(sK1)))
    | v1_funct_1(k4_relat_1(sK1)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k4_relat_1(sK1)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1213])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10153,c_1297,c_1222,c_1214,c_1110,c_949,c_913,c_882,c_700,c_359,c_403,c_23,c_22,c_21,c_20,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:59:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.52/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.52/0.99  
% 3.52/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.52/0.99  
% 3.52/0.99  ------  iProver source info
% 3.52/0.99  
% 3.52/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.52/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.52/0.99  git: non_committed_changes: false
% 3.52/0.99  git: last_make_outside_of_git: false
% 3.52/0.99  
% 3.52/0.99  ------ 
% 3.52/0.99  
% 3.52/0.99  ------ Input Options
% 3.52/0.99  
% 3.52/0.99  --out_options                           all
% 3.52/0.99  --tptp_safe_out                         true
% 3.52/0.99  --problem_path                          ""
% 3.52/0.99  --include_path                          ""
% 3.52/0.99  --clausifier                            res/vclausify_rel
% 3.52/0.99  --clausifier_options                    --mode clausify
% 3.52/0.99  --stdin                                 false
% 3.52/0.99  --stats_out                             all
% 3.52/0.99  
% 3.52/0.99  ------ General Options
% 3.52/0.99  
% 3.52/0.99  --fof                                   false
% 3.52/0.99  --time_out_real                         305.
% 3.52/0.99  --time_out_virtual                      -1.
% 3.52/0.99  --symbol_type_check                     false
% 3.52/0.99  --clausify_out                          false
% 3.52/0.99  --sig_cnt_out                           false
% 3.52/0.99  --trig_cnt_out                          false
% 3.52/0.99  --trig_cnt_out_tolerance                1.
% 3.52/0.99  --trig_cnt_out_sk_spl                   false
% 3.52/0.99  --abstr_cl_out                          false
% 3.52/0.99  
% 3.52/0.99  ------ Global Options
% 3.52/0.99  
% 3.52/0.99  --schedule                              default
% 3.52/0.99  --add_important_lit                     false
% 3.52/0.99  --prop_solver_per_cl                    1000
% 3.52/0.99  --min_unsat_core                        false
% 3.52/0.99  --soft_assumptions                      false
% 3.52/0.99  --soft_lemma_size                       3
% 3.52/0.99  --prop_impl_unit_size                   0
% 3.52/0.99  --prop_impl_unit                        []
% 3.52/0.99  --share_sel_clauses                     true
% 3.52/0.99  --reset_solvers                         false
% 3.52/0.99  --bc_imp_inh                            [conj_cone]
% 3.52/0.99  --conj_cone_tolerance                   3.
% 3.52/0.99  --extra_neg_conj                        none
% 3.52/0.99  --large_theory_mode                     true
% 3.52/0.99  --prolific_symb_bound                   200
% 3.52/0.99  --lt_threshold                          2000
% 3.52/0.99  --clause_weak_htbl                      true
% 3.52/0.99  --gc_record_bc_elim                     false
% 3.52/0.99  
% 3.52/0.99  ------ Preprocessing Options
% 3.52/0.99  
% 3.52/0.99  --preprocessing_flag                    true
% 3.52/0.99  --time_out_prep_mult                    0.1
% 3.52/0.99  --splitting_mode                        input
% 3.52/0.99  --splitting_grd                         true
% 3.52/0.99  --splitting_cvd                         false
% 3.52/0.99  --splitting_cvd_svl                     false
% 3.52/0.99  --splitting_nvd                         32
% 3.52/0.99  --sub_typing                            true
% 3.52/0.99  --prep_gs_sim                           true
% 3.52/0.99  --prep_unflatten                        true
% 3.52/0.99  --prep_res_sim                          true
% 3.52/0.99  --prep_upred                            true
% 3.52/0.99  --prep_sem_filter                       exhaustive
% 3.52/0.99  --prep_sem_filter_out                   false
% 3.52/0.99  --pred_elim                             true
% 3.52/0.99  --res_sim_input                         true
% 3.52/0.99  --eq_ax_congr_red                       true
% 3.52/0.99  --pure_diseq_elim                       true
% 3.52/0.99  --brand_transform                       false
% 3.52/0.99  --non_eq_to_eq                          false
% 3.52/0.99  --prep_def_merge                        true
% 3.52/0.99  --prep_def_merge_prop_impl              false
% 3.52/0.99  --prep_def_merge_mbd                    true
% 3.52/0.99  --prep_def_merge_tr_red                 false
% 3.52/0.99  --prep_def_merge_tr_cl                  false
% 3.52/0.99  --smt_preprocessing                     true
% 3.52/0.99  --smt_ac_axioms                         fast
% 3.52/0.99  --preprocessed_out                      false
% 3.52/0.99  --preprocessed_stats                    false
% 3.52/0.99  
% 3.52/0.99  ------ Abstraction refinement Options
% 3.52/0.99  
% 3.52/0.99  --abstr_ref                             []
% 3.52/0.99  --abstr_ref_prep                        false
% 3.52/0.99  --abstr_ref_until_sat                   false
% 3.52/0.99  --abstr_ref_sig_restrict                funpre
% 3.52/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.52/0.99  --abstr_ref_under                       []
% 3.52/0.99  
% 3.52/0.99  ------ SAT Options
% 3.52/0.99  
% 3.52/0.99  --sat_mode                              false
% 3.52/0.99  --sat_fm_restart_options                ""
% 3.52/0.99  --sat_gr_def                            false
% 3.52/0.99  --sat_epr_types                         true
% 3.52/0.99  --sat_non_cyclic_types                  false
% 3.52/0.99  --sat_finite_models                     false
% 3.52/0.99  --sat_fm_lemmas                         false
% 3.52/0.99  --sat_fm_prep                           false
% 3.52/0.99  --sat_fm_uc_incr                        true
% 3.52/0.99  --sat_out_model                         small
% 3.52/0.99  --sat_out_clauses                       false
% 3.52/0.99  
% 3.52/0.99  ------ QBF Options
% 3.52/0.99  
% 3.52/0.99  --qbf_mode                              false
% 3.52/0.99  --qbf_elim_univ                         false
% 3.52/0.99  --qbf_dom_inst                          none
% 3.52/0.99  --qbf_dom_pre_inst                      false
% 3.52/0.99  --qbf_sk_in                             false
% 3.52/0.99  --qbf_pred_elim                         true
% 3.52/0.99  --qbf_split                             512
% 3.52/0.99  
% 3.52/0.99  ------ BMC1 Options
% 3.52/0.99  
% 3.52/0.99  --bmc1_incremental                      false
% 3.52/0.99  --bmc1_axioms                           reachable_all
% 3.52/0.99  --bmc1_min_bound                        0
% 3.52/0.99  --bmc1_max_bound                        -1
% 3.52/0.99  --bmc1_max_bound_default                -1
% 3.52/0.99  --bmc1_symbol_reachability              true
% 3.52/0.99  --bmc1_property_lemmas                  false
% 3.52/0.99  --bmc1_k_induction                      false
% 3.52/0.99  --bmc1_non_equiv_states                 false
% 3.52/0.99  --bmc1_deadlock                         false
% 3.52/0.99  --bmc1_ucm                              false
% 3.52/0.99  --bmc1_add_unsat_core                   none
% 3.52/1.00  --bmc1_unsat_core_children              false
% 3.52/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.52/1.00  --bmc1_out_stat                         full
% 3.52/1.00  --bmc1_ground_init                      false
% 3.52/1.00  --bmc1_pre_inst_next_state              false
% 3.52/1.00  --bmc1_pre_inst_state                   false
% 3.52/1.00  --bmc1_pre_inst_reach_state             false
% 3.52/1.00  --bmc1_out_unsat_core                   false
% 3.52/1.00  --bmc1_aig_witness_out                  false
% 3.52/1.00  --bmc1_verbose                          false
% 3.52/1.00  --bmc1_dump_clauses_tptp                false
% 3.52/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.52/1.00  --bmc1_dump_file                        -
% 3.52/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.52/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.52/1.00  --bmc1_ucm_extend_mode                  1
% 3.52/1.00  --bmc1_ucm_init_mode                    2
% 3.52/1.00  --bmc1_ucm_cone_mode                    none
% 3.52/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.52/1.00  --bmc1_ucm_relax_model                  4
% 3.52/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.52/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.52/1.00  --bmc1_ucm_layered_model                none
% 3.52/1.00  --bmc1_ucm_max_lemma_size               10
% 3.52/1.00  
% 3.52/1.00  ------ AIG Options
% 3.52/1.00  
% 3.52/1.00  --aig_mode                              false
% 3.52/1.00  
% 3.52/1.00  ------ Instantiation Options
% 3.52/1.00  
% 3.52/1.00  --instantiation_flag                    true
% 3.52/1.00  --inst_sos_flag                         false
% 3.52/1.00  --inst_sos_phase                        true
% 3.52/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.52/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.52/1.00  --inst_lit_sel_side                     num_symb
% 3.52/1.00  --inst_solver_per_active                1400
% 3.52/1.00  --inst_solver_calls_frac                1.
% 3.52/1.00  --inst_passive_queue_type               priority_queues
% 3.52/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.52/1.00  --inst_passive_queues_freq              [25;2]
% 3.52/1.00  --inst_dismatching                      true
% 3.52/1.00  --inst_eager_unprocessed_to_passive     true
% 3.52/1.00  --inst_prop_sim_given                   true
% 3.52/1.00  --inst_prop_sim_new                     false
% 3.52/1.00  --inst_subs_new                         false
% 3.52/1.00  --inst_eq_res_simp                      false
% 3.52/1.00  --inst_subs_given                       false
% 3.52/1.00  --inst_orphan_elimination               true
% 3.52/1.00  --inst_learning_loop_flag               true
% 3.52/1.00  --inst_learning_start                   3000
% 3.52/1.00  --inst_learning_factor                  2
% 3.52/1.00  --inst_start_prop_sim_after_learn       3
% 3.52/1.00  --inst_sel_renew                        solver
% 3.52/1.00  --inst_lit_activity_flag                true
% 3.52/1.00  --inst_restr_to_given                   false
% 3.52/1.00  --inst_activity_threshold               500
% 3.52/1.00  --inst_out_proof                        true
% 3.52/1.00  
% 3.52/1.00  ------ Resolution Options
% 3.52/1.00  
% 3.52/1.00  --resolution_flag                       true
% 3.52/1.00  --res_lit_sel                           adaptive
% 3.52/1.00  --res_lit_sel_side                      none
% 3.52/1.00  --res_ordering                          kbo
% 3.52/1.00  --res_to_prop_solver                    active
% 3.52/1.00  --res_prop_simpl_new                    false
% 3.52/1.00  --res_prop_simpl_given                  true
% 3.52/1.00  --res_passive_queue_type                priority_queues
% 3.52/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.52/1.00  --res_passive_queues_freq               [15;5]
% 3.52/1.00  --res_forward_subs                      full
% 3.52/1.00  --res_backward_subs                     full
% 3.52/1.00  --res_forward_subs_resolution           true
% 3.52/1.00  --res_backward_subs_resolution          true
% 3.52/1.00  --res_orphan_elimination                true
% 3.52/1.00  --res_time_limit                        2.
% 3.52/1.00  --res_out_proof                         true
% 3.52/1.00  
% 3.52/1.00  ------ Superposition Options
% 3.52/1.00  
% 3.52/1.00  --superposition_flag                    true
% 3.52/1.00  --sup_passive_queue_type                priority_queues
% 3.52/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.52/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.52/1.00  --demod_completeness_check              fast
% 3.52/1.00  --demod_use_ground                      true
% 3.52/1.00  --sup_to_prop_solver                    passive
% 3.52/1.00  --sup_prop_simpl_new                    true
% 3.52/1.00  --sup_prop_simpl_given                  true
% 3.52/1.00  --sup_fun_splitting                     false
% 3.52/1.00  --sup_smt_interval                      50000
% 3.52/1.00  
% 3.52/1.00  ------ Superposition Simplification Setup
% 3.52/1.00  
% 3.52/1.00  --sup_indices_passive                   []
% 3.52/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.52/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.52/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.52/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.52/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.52/1.00  --sup_full_bw                           [BwDemod]
% 3.52/1.00  --sup_immed_triv                        [TrivRules]
% 3.52/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.52/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.52/1.00  --sup_immed_bw_main                     []
% 3.52/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.52/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.52/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.52/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.52/1.00  
% 3.52/1.00  ------ Combination Options
% 3.52/1.00  
% 3.52/1.00  --comb_res_mult                         3
% 3.52/1.00  --comb_sup_mult                         2
% 3.52/1.00  --comb_inst_mult                        10
% 3.52/1.00  
% 3.52/1.00  ------ Debug Options
% 3.52/1.00  
% 3.52/1.00  --dbg_backtrace                         false
% 3.52/1.00  --dbg_dump_prop_clauses                 false
% 3.52/1.00  --dbg_dump_prop_clauses_file            -
% 3.52/1.00  --dbg_out_stat                          false
% 3.52/1.00  ------ Parsing...
% 3.52/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.52/1.00  
% 3.52/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.52/1.00  
% 3.52/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.52/1.00  
% 3.52/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.52/1.00  ------ Proving...
% 3.52/1.00  ------ Problem Properties 
% 3.52/1.00  
% 3.52/1.00  
% 3.52/1.00  clauses                                 19
% 3.52/1.00  conjectures                             9
% 3.52/1.00  EPR                                     4
% 3.52/1.00  Horn                                    18
% 3.52/1.00  unary                                   8
% 3.52/1.00  binary                                  4
% 3.52/1.00  lits                                    46
% 3.52/1.00  lits eq                                 15
% 3.52/1.00  fd_pure                                 0
% 3.52/1.00  fd_pseudo                               0
% 3.52/1.00  fd_cond                                 0
% 3.52/1.00  fd_pseudo_cond                          2
% 3.52/1.00  AC symbols                              0
% 3.52/1.00  
% 3.52/1.00  ------ Schedule dynamic 5 is on 
% 3.52/1.00  
% 3.52/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.52/1.00  
% 3.52/1.00  
% 3.52/1.00  ------ 
% 3.52/1.00  Current options:
% 3.52/1.00  ------ 
% 3.52/1.00  
% 3.52/1.00  ------ Input Options
% 3.52/1.00  
% 3.52/1.00  --out_options                           all
% 3.52/1.00  --tptp_safe_out                         true
% 3.52/1.00  --problem_path                          ""
% 3.52/1.00  --include_path                          ""
% 3.52/1.00  --clausifier                            res/vclausify_rel
% 3.52/1.00  --clausifier_options                    --mode clausify
% 3.52/1.00  --stdin                                 false
% 3.52/1.00  --stats_out                             all
% 3.52/1.00  
% 3.52/1.00  ------ General Options
% 3.52/1.00  
% 3.52/1.00  --fof                                   false
% 3.52/1.00  --time_out_real                         305.
% 3.52/1.00  --time_out_virtual                      -1.
% 3.52/1.00  --symbol_type_check                     false
% 3.52/1.00  --clausify_out                          false
% 3.52/1.00  --sig_cnt_out                           false
% 3.52/1.00  --trig_cnt_out                          false
% 3.52/1.00  --trig_cnt_out_tolerance                1.
% 3.52/1.00  --trig_cnt_out_sk_spl                   false
% 3.52/1.00  --abstr_cl_out                          false
% 3.52/1.00  
% 3.52/1.00  ------ Global Options
% 3.52/1.00  
% 3.52/1.00  --schedule                              default
% 3.52/1.00  --add_important_lit                     false
% 3.52/1.00  --prop_solver_per_cl                    1000
% 3.52/1.00  --min_unsat_core                        false
% 3.52/1.00  --soft_assumptions                      false
% 3.52/1.00  --soft_lemma_size                       3
% 3.52/1.00  --prop_impl_unit_size                   0
% 3.52/1.00  --prop_impl_unit                        []
% 3.52/1.00  --share_sel_clauses                     true
% 3.52/1.00  --reset_solvers                         false
% 3.52/1.00  --bc_imp_inh                            [conj_cone]
% 3.52/1.00  --conj_cone_tolerance                   3.
% 3.52/1.00  --extra_neg_conj                        none
% 3.52/1.00  --large_theory_mode                     true
% 3.52/1.00  --prolific_symb_bound                   200
% 3.52/1.00  --lt_threshold                          2000
% 3.52/1.00  --clause_weak_htbl                      true
% 3.52/1.00  --gc_record_bc_elim                     false
% 3.52/1.00  
% 3.52/1.00  ------ Preprocessing Options
% 3.52/1.00  
% 3.52/1.00  --preprocessing_flag                    true
% 3.52/1.00  --time_out_prep_mult                    0.1
% 3.52/1.00  --splitting_mode                        input
% 3.52/1.00  --splitting_grd                         true
% 3.52/1.00  --splitting_cvd                         false
% 3.52/1.00  --splitting_cvd_svl                     false
% 3.52/1.00  --splitting_nvd                         32
% 3.52/1.00  --sub_typing                            true
% 3.52/1.00  --prep_gs_sim                           true
% 3.52/1.00  --prep_unflatten                        true
% 3.52/1.00  --prep_res_sim                          true
% 3.52/1.00  --prep_upred                            true
% 3.52/1.00  --prep_sem_filter                       exhaustive
% 3.52/1.00  --prep_sem_filter_out                   false
% 3.52/1.00  --pred_elim                             true
% 3.52/1.00  --res_sim_input                         true
% 3.52/1.00  --eq_ax_congr_red                       true
% 3.52/1.00  --pure_diseq_elim                       true
% 3.52/1.00  --brand_transform                       false
% 3.52/1.00  --non_eq_to_eq                          false
% 3.52/1.00  --prep_def_merge                        true
% 3.52/1.00  --prep_def_merge_prop_impl              false
% 3.52/1.00  --prep_def_merge_mbd                    true
% 3.52/1.00  --prep_def_merge_tr_red                 false
% 3.52/1.00  --prep_def_merge_tr_cl                  false
% 3.52/1.00  --smt_preprocessing                     true
% 3.52/1.00  --smt_ac_axioms                         fast
% 3.52/1.00  --preprocessed_out                      false
% 3.52/1.00  --preprocessed_stats                    false
% 3.52/1.00  
% 3.52/1.00  ------ Abstraction refinement Options
% 3.52/1.00  
% 3.52/1.00  --abstr_ref                             []
% 3.52/1.00  --abstr_ref_prep                        false
% 3.52/1.00  --abstr_ref_until_sat                   false
% 3.52/1.00  --abstr_ref_sig_restrict                funpre
% 3.52/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.52/1.00  --abstr_ref_under                       []
% 3.52/1.00  
% 3.52/1.00  ------ SAT Options
% 3.52/1.00  
% 3.52/1.00  --sat_mode                              false
% 3.52/1.00  --sat_fm_restart_options                ""
% 3.52/1.00  --sat_gr_def                            false
% 3.52/1.00  --sat_epr_types                         true
% 3.52/1.00  --sat_non_cyclic_types                  false
% 3.52/1.00  --sat_finite_models                     false
% 3.52/1.00  --sat_fm_lemmas                         false
% 3.52/1.00  --sat_fm_prep                           false
% 3.52/1.00  --sat_fm_uc_incr                        true
% 3.52/1.00  --sat_out_model                         small
% 3.52/1.00  --sat_out_clauses                       false
% 3.52/1.00  
% 3.52/1.00  ------ QBF Options
% 3.52/1.00  
% 3.52/1.00  --qbf_mode                              false
% 3.52/1.00  --qbf_elim_univ                         false
% 3.52/1.00  --qbf_dom_inst                          none
% 3.52/1.00  --qbf_dom_pre_inst                      false
% 3.52/1.00  --qbf_sk_in                             false
% 3.52/1.00  --qbf_pred_elim                         true
% 3.52/1.00  --qbf_split                             512
% 3.52/1.00  
% 3.52/1.00  ------ BMC1 Options
% 3.52/1.00  
% 3.52/1.00  --bmc1_incremental                      false
% 3.52/1.00  --bmc1_axioms                           reachable_all
% 3.52/1.00  --bmc1_min_bound                        0
% 3.52/1.00  --bmc1_max_bound                        -1
% 3.52/1.00  --bmc1_max_bound_default                -1
% 3.52/1.00  --bmc1_symbol_reachability              true
% 3.52/1.00  --bmc1_property_lemmas                  false
% 3.52/1.00  --bmc1_k_induction                      false
% 3.52/1.00  --bmc1_non_equiv_states                 false
% 3.52/1.00  --bmc1_deadlock                         false
% 3.52/1.00  --bmc1_ucm                              false
% 3.52/1.00  --bmc1_add_unsat_core                   none
% 3.52/1.00  --bmc1_unsat_core_children              false
% 3.52/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.52/1.00  --bmc1_out_stat                         full
% 3.52/1.00  --bmc1_ground_init                      false
% 3.52/1.00  --bmc1_pre_inst_next_state              false
% 3.52/1.00  --bmc1_pre_inst_state                   false
% 3.52/1.00  --bmc1_pre_inst_reach_state             false
% 3.52/1.00  --bmc1_out_unsat_core                   false
% 3.52/1.00  --bmc1_aig_witness_out                  false
% 3.52/1.00  --bmc1_verbose                          false
% 3.52/1.00  --bmc1_dump_clauses_tptp                false
% 3.52/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.52/1.00  --bmc1_dump_file                        -
% 3.52/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.52/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.52/1.00  --bmc1_ucm_extend_mode                  1
% 3.52/1.00  --bmc1_ucm_init_mode                    2
% 3.52/1.00  --bmc1_ucm_cone_mode                    none
% 3.52/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.52/1.00  --bmc1_ucm_relax_model                  4
% 3.52/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.52/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.52/1.00  --bmc1_ucm_layered_model                none
% 3.52/1.00  --bmc1_ucm_max_lemma_size               10
% 3.52/1.00  
% 3.52/1.00  ------ AIG Options
% 3.52/1.00  
% 3.52/1.00  --aig_mode                              false
% 3.52/1.00  
% 3.52/1.00  ------ Instantiation Options
% 3.52/1.00  
% 3.52/1.00  --instantiation_flag                    true
% 3.52/1.00  --inst_sos_flag                         false
% 3.52/1.00  --inst_sos_phase                        true
% 3.52/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.52/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.52/1.00  --inst_lit_sel_side                     none
% 3.52/1.00  --inst_solver_per_active                1400
% 3.52/1.00  --inst_solver_calls_frac                1.
% 3.52/1.00  --inst_passive_queue_type               priority_queues
% 3.52/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.52/1.00  --inst_passive_queues_freq              [25;2]
% 3.52/1.00  --inst_dismatching                      true
% 3.52/1.00  --inst_eager_unprocessed_to_passive     true
% 3.52/1.00  --inst_prop_sim_given                   true
% 3.52/1.00  --inst_prop_sim_new                     false
% 3.52/1.00  --inst_subs_new                         false
% 3.52/1.00  --inst_eq_res_simp                      false
% 3.52/1.00  --inst_subs_given                       false
% 3.52/1.00  --inst_orphan_elimination               true
% 3.52/1.00  --inst_learning_loop_flag               true
% 3.52/1.00  --inst_learning_start                   3000
% 3.52/1.00  --inst_learning_factor                  2
% 3.52/1.00  --inst_start_prop_sim_after_learn       3
% 3.52/1.00  --inst_sel_renew                        solver
% 3.52/1.00  --inst_lit_activity_flag                true
% 3.52/1.00  --inst_restr_to_given                   false
% 3.52/1.00  --inst_activity_threshold               500
% 3.52/1.00  --inst_out_proof                        true
% 3.52/1.00  
% 3.52/1.00  ------ Resolution Options
% 3.52/1.00  
% 3.52/1.00  --resolution_flag                       false
% 3.52/1.00  --res_lit_sel                           adaptive
% 3.52/1.00  --res_lit_sel_side                      none
% 3.52/1.00  --res_ordering                          kbo
% 3.52/1.00  --res_to_prop_solver                    active
% 3.52/1.00  --res_prop_simpl_new                    false
% 3.52/1.00  --res_prop_simpl_given                  true
% 3.52/1.00  --res_passive_queue_type                priority_queues
% 3.52/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.52/1.00  --res_passive_queues_freq               [15;5]
% 3.52/1.00  --res_forward_subs                      full
% 3.52/1.00  --res_backward_subs                     full
% 3.52/1.00  --res_forward_subs_resolution           true
% 3.52/1.00  --res_backward_subs_resolution          true
% 3.52/1.00  --res_orphan_elimination                true
% 3.52/1.00  --res_time_limit                        2.
% 3.52/1.00  --res_out_proof                         true
% 3.52/1.00  
% 3.52/1.00  ------ Superposition Options
% 3.52/1.00  
% 3.52/1.00  --superposition_flag                    true
% 3.52/1.00  --sup_passive_queue_type                priority_queues
% 3.52/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.52/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.52/1.00  --demod_completeness_check              fast
% 3.52/1.00  --demod_use_ground                      true
% 3.52/1.00  --sup_to_prop_solver                    passive
% 3.52/1.00  --sup_prop_simpl_new                    true
% 3.52/1.00  --sup_prop_simpl_given                  true
% 3.52/1.00  --sup_fun_splitting                     false
% 3.52/1.00  --sup_smt_interval                      50000
% 3.52/1.00  
% 3.52/1.00  ------ Superposition Simplification Setup
% 3.52/1.00  
% 3.52/1.00  --sup_indices_passive                   []
% 3.52/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.52/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.52/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.52/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.52/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.52/1.00  --sup_full_bw                           [BwDemod]
% 3.52/1.00  --sup_immed_triv                        [TrivRules]
% 3.52/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.52/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.52/1.00  --sup_immed_bw_main                     []
% 3.52/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.52/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.52/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.52/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.52/1.00  
% 3.52/1.00  ------ Combination Options
% 3.52/1.00  
% 3.52/1.00  --comb_res_mult                         3
% 3.52/1.00  --comb_sup_mult                         2
% 3.52/1.00  --comb_inst_mult                        10
% 3.52/1.00  
% 3.52/1.00  ------ Debug Options
% 3.52/1.00  
% 3.52/1.00  --dbg_backtrace                         false
% 3.52/1.00  --dbg_dump_prop_clauses                 false
% 3.52/1.00  --dbg_dump_prop_clauses_file            -
% 3.52/1.00  --dbg_out_stat                          false
% 3.52/1.00  
% 3.52/1.00  
% 3.52/1.00  
% 3.52/1.00  
% 3.52/1.00  ------ Proving...
% 3.52/1.00  
% 3.52/1.00  
% 3.52/1.00  % SZS status Theorem for theBenchmark.p
% 3.52/1.00  
% 3.52/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.52/1.00  
% 3.52/1.00  fof(f7,conjecture,(
% 3.52/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2,X3] : ((r2_hidden(X3,k1_relat_1(X1)) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,X2) = X3 <=> k1_funct_1(X1,X3) = X2)) & k2_relat_1(X0) = k1_relat_1(X1) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 3.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f8,negated_conjecture,(
% 3.52/1.00    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2,X3] : ((r2_hidden(X3,k1_relat_1(X1)) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,X2) = X3 <=> k1_funct_1(X1,X3) = X2)) & k2_relat_1(X0) = k1_relat_1(X1) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 3.52/1.00    inference(negated_conjecture,[],[f7])).
% 3.52/1.00  
% 3.52/1.00  fof(f20,plain,(
% 3.52/1.00    ? [X0] : (? [X1] : ((k2_funct_1(X0) != X1 & (! [X2,X3] : ((k1_funct_1(X0,X2) = X3 <=> k1_funct_1(X1,X3) = X2) | (~r2_hidden(X3,k1_relat_1(X1)) | ~r2_hidden(X2,k1_relat_1(X0)))) & k2_relat_1(X0) = k1_relat_1(X1) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 3.52/1.00    inference(ennf_transformation,[],[f8])).
% 3.52/1.00  
% 3.52/1.00  fof(f21,plain,(
% 3.52/1.00    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & ! [X2,X3] : ((k1_funct_1(X0,X2) = X3 <=> k1_funct_1(X1,X3) = X2) | ~r2_hidden(X3,k1_relat_1(X1)) | ~r2_hidden(X2,k1_relat_1(X0))) & k2_relat_1(X0) = k1_relat_1(X1) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 3.52/1.00    inference(flattening,[],[f20])).
% 3.52/1.00  
% 3.52/1.00  fof(f24,plain,(
% 3.52/1.00    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & ! [X2,X3] : (((k1_funct_1(X0,X2) = X3 | k1_funct_1(X1,X3) != X2) & (k1_funct_1(X1,X3) = X2 | k1_funct_1(X0,X2) != X3)) | ~r2_hidden(X3,k1_relat_1(X1)) | ~r2_hidden(X2,k1_relat_1(X0))) & k2_relat_1(X0) = k1_relat_1(X1) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 3.52/1.00    inference(nnf_transformation,[],[f21])).
% 3.52/1.00  
% 3.52/1.00  fof(f26,plain,(
% 3.52/1.00    ( ! [X0] : (? [X1] : (k2_funct_1(X0) != X1 & ! [X2,X3] : (((k1_funct_1(X0,X2) = X3 | k1_funct_1(X1,X3) != X2) & (k1_funct_1(X1,X3) = X2 | k1_funct_1(X0,X2) != X3)) | ~r2_hidden(X3,k1_relat_1(X1)) | ~r2_hidden(X2,k1_relat_1(X0))) & k2_relat_1(X0) = k1_relat_1(X1) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) => (k2_funct_1(X0) != sK2 & ! [X3,X2] : (((k1_funct_1(X0,X2) = X3 | k1_funct_1(sK2,X3) != X2) & (k1_funct_1(sK2,X3) = X2 | k1_funct_1(X0,X2) != X3)) | ~r2_hidden(X3,k1_relat_1(sK2)) | ~r2_hidden(X2,k1_relat_1(X0))) & k2_relat_1(X0) = k1_relat_1(sK2) & k2_relat_1(sK2) = k1_relat_1(X0) & v2_funct_1(X0) & v1_funct_1(sK2) & v1_relat_1(sK2))) )),
% 3.52/1.00    introduced(choice_axiom,[])).
% 3.52/1.00  
% 3.52/1.00  fof(f25,plain,(
% 3.52/1.00    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & ! [X2,X3] : (((k1_funct_1(X0,X2) = X3 | k1_funct_1(X1,X3) != X2) & (k1_funct_1(X1,X3) = X2 | k1_funct_1(X0,X2) != X3)) | ~r2_hidden(X3,k1_relat_1(X1)) | ~r2_hidden(X2,k1_relat_1(X0))) & k2_relat_1(X0) = k1_relat_1(X1) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k2_funct_1(sK1) != X1 & ! [X3,X2] : (((k1_funct_1(sK1,X2) = X3 | k1_funct_1(X1,X3) != X2) & (k1_funct_1(X1,X3) = X2 | k1_funct_1(sK1,X2) != X3)) | ~r2_hidden(X3,k1_relat_1(X1)) | ~r2_hidden(X2,k1_relat_1(sK1))) & k2_relat_1(sK1) = k1_relat_1(X1) & k2_relat_1(X1) = k1_relat_1(sK1) & v2_funct_1(sK1) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 3.52/1.00    introduced(choice_axiom,[])).
% 3.52/1.00  
% 3.52/1.00  fof(f27,plain,(
% 3.52/1.00    (k2_funct_1(sK1) != sK2 & ! [X2,X3] : (((k1_funct_1(sK1,X2) = X3 | k1_funct_1(sK2,X3) != X2) & (k1_funct_1(sK2,X3) = X2 | k1_funct_1(sK1,X2) != X3)) | ~r2_hidden(X3,k1_relat_1(sK2)) | ~r2_hidden(X2,k1_relat_1(sK1))) & k2_relat_1(sK1) = k1_relat_1(sK2) & k2_relat_1(sK2) = k1_relat_1(sK1) & v2_funct_1(sK1) & v1_funct_1(sK2) & v1_relat_1(sK2)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 3.52/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f24,f26,f25])).
% 3.52/1.00  
% 3.52/1.00  fof(f44,plain,(
% 3.52/1.00    k2_relat_1(sK1) = k1_relat_1(sK2)),
% 3.52/1.00    inference(cnf_transformation,[],[f27])).
% 3.52/1.00  
% 3.52/1.00  fof(f38,plain,(
% 3.52/1.00    v1_relat_1(sK1)),
% 3.52/1.00    inference(cnf_transformation,[],[f27])).
% 3.52/1.00  
% 3.52/1.00  fof(f1,axiom,(
% 3.52/1.00    ! [X0] : (v1_relat_1(X0) => (k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 3.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f9,plain,(
% 3.52/1.00    ! [X0] : ((k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.52/1.00    inference(ennf_transformation,[],[f1])).
% 3.52/1.00  
% 3.52/1.00  fof(f28,plain,(
% 3.52/1.00    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 3.52/1.00    inference(cnf_transformation,[],[f9])).
% 3.52/1.00  
% 3.52/1.00  fof(f6,axiom,(
% 3.52/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 3.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f18,plain,(
% 3.52/1.00    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.52/1.00    inference(ennf_transformation,[],[f6])).
% 3.52/1.00  
% 3.52/1.00  fof(f19,plain,(
% 3.52/1.00    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.52/1.00    inference(flattening,[],[f18])).
% 3.52/1.00  
% 3.52/1.00  fof(f22,plain,(
% 3.52/1.00    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) & r2_hidden(sK0(X0,X1),k1_relat_1(X0))))),
% 3.52/1.00    introduced(choice_axiom,[])).
% 3.52/1.00  
% 3.52/1.00  fof(f23,plain,(
% 3.52/1.00    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) & r2_hidden(sK0(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.52/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f22])).
% 3.52/1.00  
% 3.52/1.00  fof(f36,plain,(
% 3.52/1.00    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK0(X0,X1),k1_relat_1(X0)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.52/1.00    inference(cnf_transformation,[],[f23])).
% 3.52/1.00  
% 3.52/1.00  fof(f39,plain,(
% 3.52/1.00    v1_funct_1(sK1)),
% 3.52/1.00    inference(cnf_transformation,[],[f27])).
% 3.52/1.00  
% 3.52/1.00  fof(f2,axiom,(
% 3.52/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 3.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f10,plain,(
% 3.52/1.00    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.52/1.00    inference(ennf_transformation,[],[f2])).
% 3.52/1.00  
% 3.52/1.00  fof(f11,plain,(
% 3.52/1.00    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.52/1.00    inference(flattening,[],[f10])).
% 3.52/1.00  
% 3.52/1.00  fof(f30,plain,(
% 3.52/1.00    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.52/1.00    inference(cnf_transformation,[],[f11])).
% 3.52/1.00  
% 3.52/1.00  fof(f42,plain,(
% 3.52/1.00    v2_funct_1(sK1)),
% 3.52/1.00    inference(cnf_transformation,[],[f27])).
% 3.52/1.00  
% 3.52/1.00  fof(f3,axiom,(
% 3.52/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f12,plain,(
% 3.52/1.00    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.52/1.00    inference(ennf_transformation,[],[f3])).
% 3.52/1.00  
% 3.52/1.00  fof(f13,plain,(
% 3.52/1.00    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.52/1.00    inference(flattening,[],[f12])).
% 3.52/1.00  
% 3.52/1.00  fof(f32,plain,(
% 3.52/1.00    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.52/1.00    inference(cnf_transformation,[],[f13])).
% 3.52/1.00  
% 3.52/1.00  fof(f31,plain,(
% 3.52/1.00    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.52/1.00    inference(cnf_transformation,[],[f13])).
% 3.52/1.00  
% 3.52/1.00  fof(f40,plain,(
% 3.52/1.00    v1_relat_1(sK2)),
% 3.52/1.00    inference(cnf_transformation,[],[f27])).
% 3.52/1.00  
% 3.52/1.00  fof(f41,plain,(
% 3.52/1.00    v1_funct_1(sK2)),
% 3.52/1.00    inference(cnf_transformation,[],[f27])).
% 3.52/1.00  
% 3.52/1.00  fof(f47,plain,(
% 3.52/1.00    k2_funct_1(sK1) != sK2),
% 3.52/1.00    inference(cnf_transformation,[],[f27])).
% 3.52/1.00  
% 3.52/1.00  fof(f4,axiom,(
% 3.52/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 3.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f14,plain,(
% 3.52/1.00    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.52/1.00    inference(ennf_transformation,[],[f4])).
% 3.52/1.00  
% 3.52/1.00  fof(f15,plain,(
% 3.52/1.00    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.52/1.00    inference(flattening,[],[f14])).
% 3.52/1.00  
% 3.52/1.00  fof(f33,plain,(
% 3.52/1.00    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.52/1.00    inference(cnf_transformation,[],[f15])).
% 3.52/1.00  
% 3.52/1.00  fof(f5,axiom,(
% 3.52/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0)))),
% 3.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f16,plain,(
% 3.52/1.00    ! [X0,X1] : (((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) | (~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.52/1.00    inference(ennf_transformation,[],[f5])).
% 3.52/1.00  
% 3.52/1.00  fof(f17,plain,(
% 3.52/1.00    ! [X0,X1] : ((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.52/1.00    inference(flattening,[],[f16])).
% 3.52/1.00  
% 3.52/1.00  fof(f34,plain,(
% 3.52/1.00    ( ! [X0,X1] : (k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 | ~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.52/1.00    inference(cnf_transformation,[],[f17])).
% 3.52/1.00  
% 3.52/1.00  fof(f43,plain,(
% 3.52/1.00    k2_relat_1(sK2) = k1_relat_1(sK1)),
% 3.52/1.00    inference(cnf_transformation,[],[f27])).
% 3.52/1.00  
% 3.52/1.00  fof(f46,plain,(
% 3.52/1.00    ( ! [X2,X3] : (k1_funct_1(sK1,X2) = X3 | k1_funct_1(sK2,X3) != X2 | ~r2_hidden(X3,k1_relat_1(sK2)) | ~r2_hidden(X2,k1_relat_1(sK1))) )),
% 3.52/1.00    inference(cnf_transformation,[],[f27])).
% 3.52/1.00  
% 3.52/1.00  fof(f48,plain,(
% 3.52/1.00    ( ! [X3] : (k1_funct_1(sK1,k1_funct_1(sK2,X3)) = X3 | ~r2_hidden(X3,k1_relat_1(sK2)) | ~r2_hidden(k1_funct_1(sK2,X3),k1_relat_1(sK1))) )),
% 3.52/1.00    inference(equality_resolution,[],[f46])).
% 3.52/1.00  
% 3.52/1.00  fof(f37,plain,(
% 3.52/1.00    ( ! [X0,X1] : (X0 = X1 | k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.52/1.00    inference(cnf_transformation,[],[f23])).
% 3.52/1.00  
% 3.52/1.00  cnf(c_13,negated_conjecture,
% 3.52/1.00      ( k2_relat_1(sK1) = k1_relat_1(sK2) ),
% 3.52/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_359,negated_conjecture,
% 3.52/1.00      ( k2_relat_1(sK1) = k1_relat_1(sK2) ),
% 3.52/1.00      inference(subtyping,[status(esa)],[c_13]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_19,negated_conjecture,
% 3.52/1.00      ( v1_relat_1(sK1) ),
% 3.52/1.00      inference(cnf_transformation,[],[f38]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_354,negated_conjecture,
% 3.52/1.00      ( v1_relat_1(sK1) ),
% 3.52/1.00      inference(subtyping,[status(esa)],[c_19]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_682,plain,
% 3.52/1.00      ( v1_relat_1(sK1) = iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_354]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_1,plain,
% 3.52/1.00      ( ~ v1_relat_1(X0) | k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ),
% 3.52/1.00      inference(cnf_transformation,[],[f28]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_368,plain,
% 3.52/1.00      ( ~ v1_relat_1(X0_43)
% 3.52/1.00      | k1_relat_1(k4_relat_1(X0_43)) = k2_relat_1(X0_43) ),
% 3.52/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_671,plain,
% 3.52/1.00      ( k1_relat_1(k4_relat_1(X0_43)) = k2_relat_1(X0_43)
% 3.52/1.00      | v1_relat_1(X0_43) != iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_368]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_987,plain,
% 3.52/1.00      ( k1_relat_1(k4_relat_1(sK1)) = k2_relat_1(sK1) ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_682,c_671]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_9,plain,
% 3.52/1.00      ( r2_hidden(sK0(X0,X1),k1_relat_1(X0))
% 3.52/1.00      | ~ v1_funct_1(X0)
% 3.52/1.00      | ~ v1_funct_1(X1)
% 3.52/1.00      | ~ v1_relat_1(X0)
% 3.52/1.00      | ~ v1_relat_1(X1)
% 3.52/1.00      | X1 = X0
% 3.52/1.00      | k1_relat_1(X1) != k1_relat_1(X0) ),
% 3.52/1.00      inference(cnf_transformation,[],[f36]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_363,plain,
% 3.52/1.00      ( r2_hidden(sK0(X0_43,X1_43),k1_relat_1(X0_43))
% 3.52/1.00      | ~ v1_funct_1(X0_43)
% 3.52/1.00      | ~ v1_funct_1(X1_43)
% 3.52/1.00      | ~ v1_relat_1(X0_43)
% 3.52/1.00      | ~ v1_relat_1(X1_43)
% 3.52/1.00      | X1_43 = X0_43
% 3.52/1.00      | k1_relat_1(X1_43) != k1_relat_1(X0_43) ),
% 3.52/1.00      inference(subtyping,[status(esa)],[c_9]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_676,plain,
% 3.52/1.00      ( X0_43 = X1_43
% 3.52/1.00      | k1_relat_1(X0_43) != k1_relat_1(X1_43)
% 3.52/1.00      | r2_hidden(sK0(X1_43,X0_43),k1_relat_1(X1_43)) = iProver_top
% 3.52/1.00      | v1_funct_1(X0_43) != iProver_top
% 3.52/1.00      | v1_funct_1(X1_43) != iProver_top
% 3.52/1.00      | v1_relat_1(X0_43) != iProver_top
% 3.52/1.00      | v1_relat_1(X1_43) != iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_363]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2243,plain,
% 3.52/1.00      ( k4_relat_1(sK1) = X0_43
% 3.52/1.00      | k1_relat_1(X0_43) != k2_relat_1(sK1)
% 3.52/1.00      | r2_hidden(sK0(X0_43,k4_relat_1(sK1)),k1_relat_1(X0_43)) = iProver_top
% 3.52/1.00      | v1_funct_1(X0_43) != iProver_top
% 3.52/1.00      | v1_funct_1(k4_relat_1(sK1)) != iProver_top
% 3.52/1.00      | v1_relat_1(X0_43) != iProver_top
% 3.52/1.00      | v1_relat_1(k4_relat_1(sK1)) != iProver_top ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_987,c_676]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_20,plain,
% 3.52/1.00      ( v1_relat_1(sK1) = iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_18,negated_conjecture,
% 3.52/1.00      ( v1_funct_1(sK1) ),
% 3.52/1.00      inference(cnf_transformation,[],[f39]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_21,plain,
% 3.52/1.00      ( v1_funct_1(sK1) = iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2,plain,
% 3.52/1.00      ( ~ v1_funct_1(X0)
% 3.52/1.00      | ~ v2_funct_1(X0)
% 3.52/1.00      | ~ v1_relat_1(X0)
% 3.52/1.00      | k2_funct_1(X0) = k4_relat_1(X0) ),
% 3.52/1.00      inference(cnf_transformation,[],[f30]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_15,negated_conjecture,
% 3.52/1.00      ( v2_funct_1(sK1) ),
% 3.52/1.00      inference(cnf_transformation,[],[f42]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_194,plain,
% 3.52/1.00      ( ~ v1_funct_1(X0)
% 3.52/1.00      | ~ v1_relat_1(X0)
% 3.52/1.00      | k2_funct_1(X0) = k4_relat_1(X0)
% 3.52/1.00      | sK1 != X0 ),
% 3.52/1.00      inference(resolution_lifted,[status(thm)],[c_2,c_15]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_195,plain,
% 3.52/1.00      ( ~ v1_funct_1(sK1)
% 3.52/1.00      | ~ v1_relat_1(sK1)
% 3.52/1.00      | k2_funct_1(sK1) = k4_relat_1(sK1) ),
% 3.52/1.00      inference(unflattening,[status(thm)],[c_194]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_53,plain,
% 3.52/1.00      ( ~ v1_funct_1(sK1)
% 3.52/1.00      | ~ v2_funct_1(sK1)
% 3.52/1.00      | ~ v1_relat_1(sK1)
% 3.52/1.00      | k2_funct_1(sK1) = k4_relat_1(sK1) ),
% 3.52/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_197,plain,
% 3.52/1.00      ( k2_funct_1(sK1) = k4_relat_1(sK1) ),
% 3.52/1.00      inference(global_propositional_subsumption,
% 3.52/1.00                [status(thm)],
% 3.52/1.00                [c_195,c_19,c_18,c_15,c_53]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_353,plain,
% 3.52/1.00      ( k2_funct_1(sK1) = k4_relat_1(sK1) ),
% 3.52/1.00      inference(subtyping,[status(esa)],[c_197]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_3,plain,
% 3.52/1.00      ( ~ v1_funct_1(X0)
% 3.52/1.00      | v1_funct_1(k2_funct_1(X0))
% 3.52/1.00      | ~ v1_relat_1(X0) ),
% 3.52/1.00      inference(cnf_transformation,[],[f32]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_367,plain,
% 3.52/1.00      ( ~ v1_funct_1(X0_43)
% 3.52/1.00      | v1_funct_1(k2_funct_1(X0_43))
% 3.52/1.00      | ~ v1_relat_1(X0_43) ),
% 3.52/1.00      inference(subtyping,[status(esa)],[c_3]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_672,plain,
% 3.52/1.00      ( v1_funct_1(X0_43) != iProver_top
% 3.52/1.00      | v1_funct_1(k2_funct_1(X0_43)) = iProver_top
% 3.52/1.00      | v1_relat_1(X0_43) != iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_367]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_1222,plain,
% 3.52/1.00      ( v1_funct_1(k4_relat_1(sK1)) = iProver_top
% 3.52/1.00      | v1_funct_1(sK1) != iProver_top
% 3.52/1.00      | v1_relat_1(sK1) != iProver_top ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_353,c_672]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_4,plain,
% 3.52/1.00      ( ~ v1_funct_1(X0)
% 3.52/1.00      | ~ v1_relat_1(X0)
% 3.52/1.00      | v1_relat_1(k2_funct_1(X0)) ),
% 3.52/1.00      inference(cnf_transformation,[],[f31]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_366,plain,
% 3.52/1.00      ( ~ v1_funct_1(X0_43)
% 3.52/1.00      | ~ v1_relat_1(X0_43)
% 3.52/1.00      | v1_relat_1(k2_funct_1(X0_43)) ),
% 3.52/1.00      inference(subtyping,[status(esa)],[c_4]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_673,plain,
% 3.52/1.00      ( v1_funct_1(X0_43) != iProver_top
% 3.52/1.00      | v1_relat_1(X0_43) != iProver_top
% 3.52/1.00      | v1_relat_1(k2_funct_1(X0_43)) = iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_366]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_1297,plain,
% 3.52/1.00      ( v1_funct_1(sK1) != iProver_top
% 3.52/1.00      | v1_relat_1(k4_relat_1(sK1)) = iProver_top
% 3.52/1.00      | v1_relat_1(sK1) != iProver_top ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_353,c_673]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_10050,plain,
% 3.52/1.00      ( v1_relat_1(X0_43) != iProver_top
% 3.52/1.00      | k4_relat_1(sK1) = X0_43
% 3.52/1.00      | k1_relat_1(X0_43) != k2_relat_1(sK1)
% 3.52/1.00      | r2_hidden(sK0(X0_43,k4_relat_1(sK1)),k1_relat_1(X0_43)) = iProver_top
% 3.52/1.00      | v1_funct_1(X0_43) != iProver_top ),
% 3.52/1.00      inference(global_propositional_subsumption,
% 3.52/1.00                [status(thm)],
% 3.52/1.00                [c_2243,c_20,c_21,c_1222,c_1297]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_10051,plain,
% 3.52/1.00      ( k4_relat_1(sK1) = X0_43
% 3.52/1.00      | k1_relat_1(X0_43) != k2_relat_1(sK1)
% 3.52/1.00      | r2_hidden(sK0(X0_43,k4_relat_1(sK1)),k1_relat_1(X0_43)) = iProver_top
% 3.52/1.00      | v1_funct_1(X0_43) != iProver_top
% 3.52/1.00      | v1_relat_1(X0_43) != iProver_top ),
% 3.52/1.00      inference(renaming,[status(thm)],[c_10050]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_10061,plain,
% 3.52/1.00      ( k4_relat_1(sK1) = sK2
% 3.52/1.00      | r2_hidden(sK0(sK2,k4_relat_1(sK1)),k1_relat_1(sK2)) = iProver_top
% 3.52/1.00      | v1_funct_1(sK2) != iProver_top
% 3.52/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_359,c_10051]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_10091,plain,
% 3.52/1.00      ( k4_relat_1(sK1) = sK2
% 3.52/1.00      | r2_hidden(sK0(sK2,k4_relat_1(sK1)),k2_relat_1(sK1)) = iProver_top
% 3.52/1.00      | v1_funct_1(sK2) != iProver_top
% 3.52/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.52/1.00      inference(light_normalisation,[status(thm)],[c_10061,c_359]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_17,negated_conjecture,
% 3.52/1.00      ( v1_relat_1(sK2) ),
% 3.52/1.00      inference(cnf_transformation,[],[f40]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_22,plain,
% 3.52/1.00      ( v1_relat_1(sK2) = iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_16,negated_conjecture,
% 3.52/1.00      ( v1_funct_1(sK2) ),
% 3.52/1.00      inference(cnf_transformation,[],[f41]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_23,plain,
% 3.52/1.00      ( v1_funct_1(sK2) = iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_403,plain,
% 3.52/1.00      ( ~ v1_relat_1(sK1)
% 3.52/1.00      | k1_relat_1(k4_relat_1(sK1)) = k2_relat_1(sK1) ),
% 3.52/1.00      inference(instantiation,[status(thm)],[c_368]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_10,negated_conjecture,
% 3.52/1.00      ( k2_funct_1(sK1) != sK2 ),
% 3.52/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_362,negated_conjecture,
% 3.52/1.00      ( k2_funct_1(sK1) != sK2 ),
% 3.52/1.00      inference(subtyping,[status(esa)],[c_10]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_700,plain,
% 3.52/1.00      ( k4_relat_1(sK1) != sK2 ),
% 3.52/1.00      inference(demodulation,[status(thm)],[c_353,c_362]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_373,plain,( X0_43 = X0_43 ),theory(equality) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_882,plain,
% 3.52/1.00      ( sK2 = sK2 ),
% 3.52/1.00      inference(instantiation,[status(thm)],[c_373]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_379,plain,
% 3.52/1.00      ( X0_43 != X1_43 | k1_relat_1(X0_43) = k1_relat_1(X1_43) ),
% 3.52/1.00      theory(equality) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_876,plain,
% 3.52/1.00      ( sK2 != X0_43 | k1_relat_1(sK2) = k1_relat_1(X0_43) ),
% 3.52/1.00      inference(instantiation,[status(thm)],[c_379]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_913,plain,
% 3.52/1.00      ( sK2 != sK2 | k1_relat_1(sK2) = k1_relat_1(sK2) ),
% 3.52/1.00      inference(instantiation,[status(thm)],[c_876]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_375,plain,
% 3.52/1.00      ( X0_42 != X1_42 | X2_42 != X1_42 | X2_42 = X0_42 ),
% 3.52/1.00      theory(equality) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_874,plain,
% 3.52/1.00      ( X0_42 != X1_42
% 3.52/1.00      | k1_relat_1(sK2) != X1_42
% 3.52/1.00      | k1_relat_1(sK2) = X0_42 ),
% 3.52/1.00      inference(instantiation,[status(thm)],[c_375]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_928,plain,
% 3.52/1.00      ( X0_42 != k1_relat_1(sK2)
% 3.52/1.00      | k1_relat_1(sK2) = X0_42
% 3.52/1.00      | k1_relat_1(sK2) != k1_relat_1(sK2) ),
% 3.52/1.00      inference(instantiation,[status(thm)],[c_874]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_949,plain,
% 3.52/1.00      ( k1_relat_1(sK2) != k1_relat_1(sK2)
% 3.52/1.00      | k1_relat_1(sK2) = k2_relat_1(sK1)
% 3.52/1.00      | k2_relat_1(sK1) != k1_relat_1(sK2) ),
% 3.52/1.00      inference(instantiation,[status(thm)],[c_928]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_955,plain,
% 3.52/1.00      ( X0_42 != X1_42
% 3.52/1.00      | X0_42 = k1_relat_1(sK2)
% 3.52/1.00      | k1_relat_1(sK2) != X1_42 ),
% 3.52/1.00      inference(instantiation,[status(thm)],[c_375]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_1016,plain,
% 3.52/1.00      ( X0_42 = k1_relat_1(sK2)
% 3.52/1.00      | X0_42 != k2_relat_1(sK1)
% 3.52/1.00      | k1_relat_1(sK2) != k2_relat_1(sK1) ),
% 3.52/1.00      inference(instantiation,[status(thm)],[c_955]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_1110,plain,
% 3.52/1.00      ( k1_relat_1(k4_relat_1(sK1)) = k1_relat_1(sK2)
% 3.52/1.00      | k1_relat_1(k4_relat_1(sK1)) != k2_relat_1(sK1)
% 3.52/1.00      | k1_relat_1(sK2) != k2_relat_1(sK1) ),
% 3.52/1.00      inference(instantiation,[status(thm)],[c_1016]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_915,plain,
% 3.52/1.00      ( r2_hidden(sK0(sK2,X0_43),k1_relat_1(sK2))
% 3.52/1.00      | ~ v1_funct_1(X0_43)
% 3.52/1.00      | ~ v1_funct_1(sK2)
% 3.52/1.00      | ~ v1_relat_1(X0_43)
% 3.52/1.00      | ~ v1_relat_1(sK2)
% 3.52/1.00      | X0_43 = sK2
% 3.52/1.00      | k1_relat_1(X0_43) != k1_relat_1(sK2) ),
% 3.52/1.00      inference(instantiation,[status(thm)],[c_363]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_1212,plain,
% 3.52/1.00      ( r2_hidden(sK0(sK2,k4_relat_1(sK1)),k1_relat_1(sK2))
% 3.52/1.00      | ~ v1_funct_1(k4_relat_1(sK1))
% 3.52/1.00      | ~ v1_funct_1(sK2)
% 3.52/1.00      | ~ v1_relat_1(k4_relat_1(sK1))
% 3.52/1.00      | ~ v1_relat_1(sK2)
% 3.52/1.00      | k4_relat_1(sK1) = sK2
% 3.52/1.00      | k1_relat_1(k4_relat_1(sK1)) != k1_relat_1(sK2) ),
% 3.52/1.00      inference(instantiation,[status(thm)],[c_915]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_1216,plain,
% 3.52/1.00      ( k4_relat_1(sK1) = sK2
% 3.52/1.00      | k1_relat_1(k4_relat_1(sK1)) != k1_relat_1(sK2)
% 3.52/1.00      | r2_hidden(sK0(sK2,k4_relat_1(sK1)),k1_relat_1(sK2)) = iProver_top
% 3.52/1.00      | v1_funct_1(k4_relat_1(sK1)) != iProver_top
% 3.52/1.00      | v1_funct_1(sK2) != iProver_top
% 3.52/1.00      | v1_relat_1(k4_relat_1(sK1)) != iProver_top
% 3.52/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_1212]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_384,plain,
% 3.52/1.00      ( ~ r2_hidden(X0_41,X0_42)
% 3.52/1.00      | r2_hidden(X1_41,X1_42)
% 3.52/1.00      | X1_42 != X0_42
% 3.52/1.00      | X1_41 != X0_41 ),
% 3.52/1.00      theory(equality) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_972,plain,
% 3.52/1.00      ( r2_hidden(X0_41,X0_42)
% 3.52/1.00      | ~ r2_hidden(sK0(sK2,X0_43),k1_relat_1(sK2))
% 3.52/1.00      | X0_42 != k1_relat_1(sK2)
% 3.52/1.00      | X0_41 != sK0(sK2,X0_43) ),
% 3.52/1.00      inference(instantiation,[status(thm)],[c_384]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_1060,plain,
% 3.52/1.00      ( r2_hidden(X0_41,k2_relat_1(sK1))
% 3.52/1.00      | ~ r2_hidden(sK0(sK2,X0_43),k1_relat_1(sK2))
% 3.52/1.00      | k2_relat_1(sK1) != k1_relat_1(sK2)
% 3.52/1.00      | X0_41 != sK0(sK2,X0_43) ),
% 3.52/1.00      inference(instantiation,[status(thm)],[c_972]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2450,plain,
% 3.52/1.00      ( r2_hidden(X0_41,k2_relat_1(sK1))
% 3.52/1.00      | ~ r2_hidden(sK0(sK2,k4_relat_1(sK1)),k1_relat_1(sK2))
% 3.52/1.00      | k2_relat_1(sK1) != k1_relat_1(sK2)
% 3.52/1.00      | X0_41 != sK0(sK2,k4_relat_1(sK1)) ),
% 3.52/1.00      inference(instantiation,[status(thm)],[c_1060]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2710,plain,
% 3.52/1.00      ( ~ r2_hidden(sK0(sK2,k4_relat_1(sK1)),k1_relat_1(sK2))
% 3.52/1.00      | r2_hidden(sK0(sK2,k4_relat_1(sK1)),k2_relat_1(sK1))
% 3.52/1.00      | k2_relat_1(sK1) != k1_relat_1(sK2)
% 3.52/1.00      | sK0(sK2,k4_relat_1(sK1)) != sK0(sK2,k4_relat_1(sK1)) ),
% 3.52/1.00      inference(instantiation,[status(thm)],[c_2450]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2712,plain,
% 3.52/1.00      ( k2_relat_1(sK1) != k1_relat_1(sK2)
% 3.52/1.00      | sK0(sK2,k4_relat_1(sK1)) != sK0(sK2,k4_relat_1(sK1))
% 3.52/1.00      | r2_hidden(sK0(sK2,k4_relat_1(sK1)),k1_relat_1(sK2)) != iProver_top
% 3.52/1.00      | r2_hidden(sK0(sK2,k4_relat_1(sK1)),k2_relat_1(sK1)) = iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_2710]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_371,plain,( X0_41 = X0_41 ),theory(equality) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2711,plain,
% 3.52/1.00      ( sK0(sK2,k4_relat_1(sK1)) = sK0(sK2,k4_relat_1(sK1)) ),
% 3.52/1.00      inference(instantiation,[status(thm)],[c_371]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_10100,plain,
% 3.52/1.00      ( r2_hidden(sK0(sK2,k4_relat_1(sK1)),k2_relat_1(sK1)) = iProver_top ),
% 3.52/1.00      inference(global_propositional_subsumption,
% 3.52/1.00                [status(thm)],
% 3.52/1.00                [c_10091,c_19,c_20,c_21,c_22,c_23,c_403,c_359,c_700,
% 3.52/1.00                 c_882,c_913,c_949,c_1110,c_1216,c_1222,c_1297,c_2712,
% 3.52/1.00                 c_2711]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_5,plain,
% 3.52/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.52/1.00      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 3.52/1.00      | ~ v1_funct_1(X1)
% 3.52/1.00      | ~ v1_relat_1(X1) ),
% 3.52/1.00      inference(cnf_transformation,[],[f33]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_365,plain,
% 3.52/1.00      ( ~ r2_hidden(X0_41,k1_relat_1(X0_43))
% 3.52/1.00      | r2_hidden(k1_funct_1(X0_43,X0_41),k2_relat_1(X0_43))
% 3.52/1.00      | ~ v1_funct_1(X0_43)
% 3.52/1.00      | ~ v1_relat_1(X0_43) ),
% 3.52/1.00      inference(subtyping,[status(esa)],[c_5]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_674,plain,
% 3.52/1.00      ( r2_hidden(X0_41,k1_relat_1(X0_43)) != iProver_top
% 3.52/1.00      | r2_hidden(k1_funct_1(X0_43,X0_41),k2_relat_1(X0_43)) = iProver_top
% 3.52/1.00      | v1_funct_1(X0_43) != iProver_top
% 3.52/1.00      | v1_relat_1(X0_43) != iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_365]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_7,plain,
% 3.52/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.52/1.00      | ~ v1_funct_1(X1)
% 3.52/1.00      | ~ v2_funct_1(X1)
% 3.52/1.00      | ~ v1_relat_1(X1)
% 3.52/1.00      | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ),
% 3.52/1.00      inference(cnf_transformation,[],[f34]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_202,plain,
% 3.52/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.52/1.00      | ~ v1_funct_1(X1)
% 3.52/1.00      | ~ v1_relat_1(X1)
% 3.52/1.00      | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0
% 3.52/1.00      | sK1 != X1 ),
% 3.52/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_15]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_203,plain,
% 3.52/1.00      ( ~ r2_hidden(X0,k1_relat_1(sK1))
% 3.52/1.00      | ~ v1_funct_1(sK1)
% 3.52/1.00      | ~ v1_relat_1(sK1)
% 3.52/1.00      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 ),
% 3.52/1.00      inference(unflattening,[status(thm)],[c_202]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_207,plain,
% 3.52/1.00      ( ~ r2_hidden(X0,k1_relat_1(sK1))
% 3.52/1.00      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 ),
% 3.52/1.00      inference(global_propositional_subsumption,
% 3.52/1.00                [status(thm)],
% 3.52/1.00                [c_203,c_19,c_18]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_352,plain,
% 3.52/1.00      ( ~ r2_hidden(X0_41,k1_relat_1(sK1))
% 3.52/1.00      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0_41)) = X0_41 ),
% 3.52/1.00      inference(subtyping,[status(esa)],[c_207]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_683,plain,
% 3.52/1.00      ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0_41)) = X0_41
% 3.52/1.00      | r2_hidden(X0_41,k1_relat_1(sK1)) != iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_352]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_14,negated_conjecture,
% 3.52/1.00      ( k2_relat_1(sK2) = k1_relat_1(sK1) ),
% 3.52/1.00      inference(cnf_transformation,[],[f43]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_358,negated_conjecture,
% 3.52/1.00      ( k2_relat_1(sK2) = k1_relat_1(sK1) ),
% 3.52/1.00      inference(subtyping,[status(esa)],[c_14]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_712,plain,
% 3.52/1.00      ( k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,X0_41)) = X0_41
% 3.52/1.00      | r2_hidden(X0_41,k2_relat_1(sK2)) != iProver_top ),
% 3.52/1.00      inference(light_normalisation,[status(thm)],[c_683,c_353,c_358]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_1333,plain,
% 3.52/1.00      ( k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,k1_funct_1(sK2,X0_41))) = k1_funct_1(sK2,X0_41)
% 3.52/1.00      | r2_hidden(X0_41,k1_relat_1(sK2)) != iProver_top
% 3.52/1.00      | v1_funct_1(sK2) != iProver_top
% 3.52/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_674,c_712]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_1360,plain,
% 3.52/1.00      ( k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,k1_funct_1(sK2,X0_41))) = k1_funct_1(sK2,X0_41)
% 3.52/1.00      | r2_hidden(X0_41,k2_relat_1(sK1)) != iProver_top
% 3.52/1.00      | v1_funct_1(sK2) != iProver_top
% 3.52/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.52/1.00      inference(light_normalisation,[status(thm)],[c_1333,c_359]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_1666,plain,
% 3.52/1.00      ( k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,k1_funct_1(sK2,X0_41))) = k1_funct_1(sK2,X0_41)
% 3.52/1.00      | r2_hidden(X0_41,k2_relat_1(sK1)) != iProver_top ),
% 3.52/1.00      inference(global_propositional_subsumption,
% 3.52/1.00                [status(thm)],
% 3.52/1.00                [c_1360,c_22,c_23]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_10147,plain,
% 3.52/1.00      ( k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,k1_funct_1(sK2,sK0(sK2,k4_relat_1(sK1))))) = k1_funct_1(sK2,sK0(sK2,k4_relat_1(sK1))) ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_10100,c_1666]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_11,negated_conjecture,
% 3.52/1.00      ( ~ r2_hidden(X0,k1_relat_1(sK2))
% 3.52/1.00      | ~ r2_hidden(k1_funct_1(sK2,X0),k1_relat_1(sK1))
% 3.52/1.00      | k1_funct_1(sK1,k1_funct_1(sK2,X0)) = X0 ),
% 3.52/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_361,negated_conjecture,
% 3.52/1.00      ( ~ r2_hidden(X0_41,k1_relat_1(sK2))
% 3.52/1.00      | ~ r2_hidden(k1_funct_1(sK2,X0_41),k1_relat_1(sK1))
% 3.52/1.00      | k1_funct_1(sK1,k1_funct_1(sK2,X0_41)) = X0_41 ),
% 3.52/1.00      inference(subtyping,[status(esa)],[c_11]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_677,plain,
% 3.52/1.00      ( k1_funct_1(sK1,k1_funct_1(sK2,X0_41)) = X0_41
% 3.52/1.00      | r2_hidden(X0_41,k1_relat_1(sK2)) != iProver_top
% 3.52/1.00      | r2_hidden(k1_funct_1(sK2,X0_41),k1_relat_1(sK1)) != iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_361]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_734,plain,
% 3.52/1.00      ( k1_funct_1(sK1,k1_funct_1(sK2,X0_41)) = X0_41
% 3.52/1.00      | r2_hidden(X0_41,k2_relat_1(sK1)) != iProver_top
% 3.52/1.00      | r2_hidden(k1_funct_1(sK2,X0_41),k2_relat_1(sK2)) != iProver_top ),
% 3.52/1.00      inference(light_normalisation,[status(thm)],[c_677,c_358,c_359]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_1334,plain,
% 3.52/1.00      ( k1_funct_1(sK1,k1_funct_1(sK2,X0_41)) = X0_41
% 3.52/1.00      | r2_hidden(X0_41,k1_relat_1(sK2)) != iProver_top
% 3.52/1.00      | r2_hidden(X0_41,k2_relat_1(sK1)) != iProver_top
% 3.52/1.00      | v1_funct_1(sK2) != iProver_top
% 3.52/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_674,c_734]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_1351,plain,
% 3.52/1.00      ( k1_funct_1(sK1,k1_funct_1(sK2,X0_41)) = X0_41
% 3.52/1.00      | r2_hidden(X0_41,k2_relat_1(sK1)) != iProver_top
% 3.52/1.00      | v1_funct_1(sK2) != iProver_top
% 3.52/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.52/1.00      inference(light_normalisation,[status(thm)],[c_1334,c_359]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_1482,plain,
% 3.52/1.00      ( k1_funct_1(sK1,k1_funct_1(sK2,X0_41)) = X0_41
% 3.52/1.00      | r2_hidden(X0_41,k2_relat_1(sK1)) != iProver_top ),
% 3.52/1.00      inference(global_propositional_subsumption,
% 3.52/1.00                [status(thm)],
% 3.52/1.00                [c_1351,c_22,c_23]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_10149,plain,
% 3.52/1.00      ( k1_funct_1(sK1,k1_funct_1(sK2,sK0(sK2,k4_relat_1(sK1)))) = sK0(sK2,k4_relat_1(sK1)) ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_10100,c_1482]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_10153,plain,
% 3.52/1.00      ( k1_funct_1(k4_relat_1(sK1),sK0(sK2,k4_relat_1(sK1))) = k1_funct_1(sK2,sK0(sK2,k4_relat_1(sK1))) ),
% 3.52/1.00      inference(light_normalisation,[status(thm)],[c_10147,c_10149]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_8,plain,
% 3.52/1.00      ( ~ v1_funct_1(X0)
% 3.52/1.00      | ~ v1_funct_1(X1)
% 3.52/1.00      | ~ v1_relat_1(X0)
% 3.52/1.00      | ~ v1_relat_1(X1)
% 3.52/1.00      | X1 = X0
% 3.52/1.00      | k1_funct_1(X1,sK0(X0,X1)) != k1_funct_1(X0,sK0(X0,X1))
% 3.52/1.00      | k1_relat_1(X1) != k1_relat_1(X0) ),
% 3.52/1.00      inference(cnf_transformation,[],[f37]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_364,plain,
% 3.52/1.00      ( ~ v1_funct_1(X0_43)
% 3.52/1.00      | ~ v1_funct_1(X1_43)
% 3.52/1.00      | ~ v1_relat_1(X0_43)
% 3.52/1.00      | ~ v1_relat_1(X1_43)
% 3.52/1.00      | X1_43 = X0_43
% 3.52/1.00      | k1_relat_1(X1_43) != k1_relat_1(X0_43)
% 3.52/1.00      | k1_funct_1(X1_43,sK0(X0_43,X1_43)) != k1_funct_1(X0_43,sK0(X0_43,X1_43)) ),
% 3.52/1.00      inference(subtyping,[status(esa)],[c_8]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_914,plain,
% 3.52/1.00      ( ~ v1_funct_1(X0_43)
% 3.52/1.00      | ~ v1_funct_1(sK2)
% 3.52/1.00      | ~ v1_relat_1(X0_43)
% 3.52/1.00      | ~ v1_relat_1(sK2)
% 3.52/1.00      | X0_43 = sK2
% 3.52/1.00      | k1_relat_1(X0_43) != k1_relat_1(sK2)
% 3.52/1.00      | k1_funct_1(X0_43,sK0(sK2,X0_43)) != k1_funct_1(sK2,sK0(sK2,X0_43)) ),
% 3.52/1.00      inference(instantiation,[status(thm)],[c_364]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_1213,plain,
% 3.52/1.00      ( ~ v1_funct_1(k4_relat_1(sK1))
% 3.52/1.00      | ~ v1_funct_1(sK2)
% 3.52/1.00      | ~ v1_relat_1(k4_relat_1(sK1))
% 3.52/1.00      | ~ v1_relat_1(sK2)
% 3.52/1.00      | k4_relat_1(sK1) = sK2
% 3.52/1.00      | k1_relat_1(k4_relat_1(sK1)) != k1_relat_1(sK2)
% 3.52/1.00      | k1_funct_1(k4_relat_1(sK1),sK0(sK2,k4_relat_1(sK1))) != k1_funct_1(sK2,sK0(sK2,k4_relat_1(sK1))) ),
% 3.52/1.00      inference(instantiation,[status(thm)],[c_914]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_1214,plain,
% 3.52/1.00      ( k4_relat_1(sK1) = sK2
% 3.52/1.00      | k1_relat_1(k4_relat_1(sK1)) != k1_relat_1(sK2)
% 3.52/1.00      | k1_funct_1(k4_relat_1(sK1),sK0(sK2,k4_relat_1(sK1))) != k1_funct_1(sK2,sK0(sK2,k4_relat_1(sK1)))
% 3.52/1.00      | v1_funct_1(k4_relat_1(sK1)) != iProver_top
% 3.52/1.00      | v1_funct_1(sK2) != iProver_top
% 3.52/1.00      | v1_relat_1(k4_relat_1(sK1)) != iProver_top
% 3.52/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_1213]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(contradiction,plain,
% 3.52/1.00      ( $false ),
% 3.52/1.00      inference(minisat,
% 3.52/1.00                [status(thm)],
% 3.52/1.00                [c_10153,c_1297,c_1222,c_1214,c_1110,c_949,c_913,c_882,
% 3.52/1.00                 c_700,c_359,c_403,c_23,c_22,c_21,c_20,c_19]) ).
% 3.52/1.00  
% 3.52/1.00  
% 3.52/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.52/1.00  
% 3.52/1.00  ------                               Statistics
% 3.52/1.00  
% 3.52/1.00  ------ General
% 3.52/1.00  
% 3.52/1.00  abstr_ref_over_cycles:                  0
% 3.52/1.00  abstr_ref_under_cycles:                 0
% 3.52/1.00  gc_basic_clause_elim:                   0
% 3.52/1.00  forced_gc_time:                         0
% 3.52/1.00  parsing_time:                           0.012
% 3.52/1.00  unif_index_cands_time:                  0.
% 3.52/1.00  unif_index_add_time:                    0.
% 3.52/1.00  orderings_time:                         0.
% 3.52/1.00  out_proof_time:                         0.009
% 3.52/1.00  total_time:                             0.301
% 3.52/1.00  num_of_symbols:                         47
% 3.52/1.00  num_of_terms:                           3740
% 3.52/1.00  
% 3.52/1.00  ------ Preprocessing
% 3.52/1.00  
% 3.52/1.00  num_of_splits:                          0
% 3.52/1.00  num_of_split_atoms:                     0
% 3.52/1.00  num_of_reused_defs:                     0
% 3.52/1.00  num_eq_ax_congr_red:                    8
% 3.52/1.00  num_of_sem_filtered_clauses:            1
% 3.52/1.00  num_of_subtypes:                        3
% 3.52/1.00  monotx_restored_types:                  0
% 3.52/1.00  sat_num_of_epr_types:                   0
% 3.52/1.00  sat_num_of_non_cyclic_types:            0
% 3.52/1.00  sat_guarded_non_collapsed_types:        2
% 3.52/1.00  num_pure_diseq_elim:                    0
% 3.52/1.00  simp_replaced_by:                       0
% 3.52/1.00  res_preprocessed:                       108
% 3.52/1.00  prep_upred:                             0
% 3.52/1.00  prep_unflattend:                        3
% 3.52/1.00  smt_new_axioms:                         0
% 3.52/1.00  pred_elim_cands:                        3
% 3.52/1.00  pred_elim:                              1
% 3.52/1.00  pred_elim_cl:                           1
% 3.52/1.00  pred_elim_cycles:                       3
% 3.52/1.00  merged_defs:                            0
% 3.52/1.00  merged_defs_ncl:                        0
% 3.52/1.00  bin_hyper_res:                          0
% 3.52/1.00  prep_cycles:                            4
% 3.52/1.00  pred_elim_time:                         0.001
% 3.52/1.00  splitting_time:                         0.
% 3.52/1.00  sem_filter_time:                        0.
% 3.52/1.00  monotx_time:                            0.
% 3.52/1.00  subtype_inf_time:                       0.
% 3.52/1.00  
% 3.52/1.00  ------ Problem properties
% 3.52/1.00  
% 3.52/1.00  clauses:                                19
% 3.52/1.00  conjectures:                            9
% 3.52/1.00  epr:                                    4
% 3.52/1.00  horn:                                   18
% 3.52/1.00  ground:                                 8
% 3.52/1.00  unary:                                  8
% 3.52/1.00  binary:                                 4
% 3.52/1.00  lits:                                   46
% 3.52/1.00  lits_eq:                                15
% 3.52/1.00  fd_pure:                                0
% 3.52/1.00  fd_pseudo:                              0
% 3.52/1.00  fd_cond:                                0
% 3.52/1.00  fd_pseudo_cond:                         2
% 3.52/1.00  ac_symbols:                             0
% 3.52/1.00  
% 3.52/1.00  ------ Propositional Solver
% 3.52/1.00  
% 3.52/1.00  prop_solver_calls:                      33
% 3.52/1.00  prop_fast_solver_calls:                 1239
% 3.52/1.00  smt_solver_calls:                       0
% 3.52/1.00  smt_fast_solver_calls:                  0
% 3.52/1.00  prop_num_of_clauses:                    2879
% 3.52/1.00  prop_preprocess_simplified:             5982
% 3.52/1.00  prop_fo_subsumed:                       207
% 3.52/1.00  prop_solver_time:                       0.
% 3.52/1.00  smt_solver_time:                        0.
% 3.52/1.00  smt_fast_solver_time:                   0.
% 3.52/1.00  prop_fast_solver_time:                  0.
% 3.52/1.00  prop_unsat_core_time:                   0.
% 3.52/1.00  
% 3.52/1.00  ------ QBF
% 3.52/1.00  
% 3.52/1.00  qbf_q_res:                              0
% 3.52/1.00  qbf_num_tautologies:                    0
% 3.52/1.00  qbf_prep_cycles:                        0
% 3.52/1.00  
% 3.52/1.00  ------ BMC1
% 3.52/1.00  
% 3.52/1.00  bmc1_current_bound:                     -1
% 3.52/1.00  bmc1_last_solved_bound:                 -1
% 3.52/1.00  bmc1_unsat_core_size:                   -1
% 3.52/1.00  bmc1_unsat_core_parents_size:           -1
% 3.52/1.00  bmc1_merge_next_fun:                    0
% 3.52/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.52/1.00  
% 3.52/1.00  ------ Instantiation
% 3.52/1.00  
% 3.52/1.00  inst_num_of_clauses:                    939
% 3.52/1.00  inst_num_in_passive:                    311
% 3.52/1.00  inst_num_in_active:                     594
% 3.52/1.00  inst_num_in_unprocessed:                34
% 3.52/1.00  inst_num_of_loops:                      630
% 3.52/1.00  inst_num_of_learning_restarts:          0
% 3.52/1.00  inst_num_moves_active_passive:          25
% 3.52/1.00  inst_lit_activity:                      0
% 3.52/1.00  inst_lit_activity_moves:                0
% 3.52/1.00  inst_num_tautologies:                   0
% 3.52/1.00  inst_num_prop_implied:                  0
% 3.52/1.00  inst_num_existing_simplified:           0
% 3.52/1.00  inst_num_eq_res_simplified:             0
% 3.52/1.00  inst_num_child_elim:                    0
% 3.52/1.00  inst_num_of_dismatching_blockings:      617
% 3.52/1.00  inst_num_of_non_proper_insts:           1615
% 3.52/1.00  inst_num_of_duplicates:                 0
% 3.52/1.00  inst_inst_num_from_inst_to_res:         0
% 3.52/1.00  inst_dismatching_checking_time:         0.
% 3.52/1.00  
% 3.52/1.00  ------ Resolution
% 3.52/1.00  
% 3.52/1.00  res_num_of_clauses:                     0
% 3.52/1.00  res_num_in_passive:                     0
% 3.52/1.00  res_num_in_active:                      0
% 3.52/1.00  res_num_of_loops:                       112
% 3.52/1.00  res_forward_subset_subsumed:            471
% 3.52/1.00  res_backward_subset_subsumed:           2
% 3.52/1.00  res_forward_subsumed:                   0
% 3.52/1.00  res_backward_subsumed:                  0
% 3.52/1.00  res_forward_subsumption_resolution:     0
% 3.52/1.00  res_backward_subsumption_resolution:    0
% 3.52/1.00  res_clause_to_clause_subsumption:       1811
% 3.52/1.00  res_orphan_elimination:                 0
% 3.52/1.00  res_tautology_del:                      324
% 3.52/1.00  res_num_eq_res_simplified:              0
% 3.52/1.00  res_num_sel_changes:                    0
% 3.52/1.00  res_moves_from_active_to_pass:          0
% 3.52/1.00  
% 3.52/1.00  ------ Superposition
% 3.52/1.00  
% 3.52/1.00  sup_time_total:                         0.
% 3.52/1.00  sup_time_generating:                    0.
% 3.52/1.00  sup_time_sim_full:                      0.
% 3.52/1.00  sup_time_sim_immed:                     0.
% 3.52/1.00  
% 3.52/1.00  sup_num_of_clauses:                     244
% 3.52/1.00  sup_num_in_active:                      124
% 3.52/1.00  sup_num_in_passive:                     120
% 3.52/1.00  sup_num_of_loops:                       125
% 3.52/1.00  sup_fw_superposition:                   163
% 3.52/1.00  sup_bw_superposition:                   114
% 3.52/1.00  sup_immediate_simplified:               161
% 3.52/1.00  sup_given_eliminated:                   0
% 3.52/1.00  comparisons_done:                       0
% 3.52/1.00  comparisons_avoided:                    0
% 3.52/1.00  
% 3.52/1.00  ------ Simplifications
% 3.52/1.00  
% 3.52/1.00  
% 3.52/1.00  sim_fw_subset_subsumed:                 4
% 3.52/1.00  sim_bw_subset_subsumed:                 2
% 3.52/1.00  sim_fw_subsumed:                        0
% 3.52/1.00  sim_bw_subsumed:                        0
% 3.52/1.00  sim_fw_subsumption_res:                 0
% 3.52/1.00  sim_bw_subsumption_res:                 0
% 3.52/1.00  sim_tautology_del:                      0
% 3.52/1.00  sim_eq_tautology_del:                   49
% 3.52/1.00  sim_eq_res_simp:                        0
% 3.52/1.00  sim_fw_demodulated:                     0
% 3.52/1.00  sim_bw_demodulated:                     1
% 3.52/1.00  sim_light_normalised:                   161
% 3.52/1.00  sim_joinable_taut:                      0
% 3.52/1.00  sim_joinable_simp:                      0
% 3.52/1.00  sim_ac_normalised:                      0
% 3.52/1.00  sim_smt_subsumption:                    0
% 3.52/1.00  
%------------------------------------------------------------------------------
