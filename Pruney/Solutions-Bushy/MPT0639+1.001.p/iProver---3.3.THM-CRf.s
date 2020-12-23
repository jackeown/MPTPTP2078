%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0639+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:47 EST 2020

% Result     : Theorem 1.86s
% Output     : CNFRefutation 1.86s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 560 expanded)
%              Number of clauses        :   85 ( 172 expanded)
%              Number of leaves         :    9 ( 116 expanded)
%              Depth                    :   20
%              Number of atoms          :  662 (3565 expanded)
%              Number of equality atoms :  241 ( 526 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal clause size      :   14 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    inference(ennf_transformation,[],[f1])).

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
    inference(flattening,[],[f8])).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f21,plain,(
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
    inference(rectify,[],[f20])).

fof(f22,plain,(
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

fof(f23,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f22])).

fof(f31,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | r2_hidden(sK1(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
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

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

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
    inference(nnf_transformation,[],[f15])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

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

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0)
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0)
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( v2_funct_1(X1)
              & v2_funct_1(X0) )
           => v2_funct_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( v2_funct_1(X1)
                & v2_funct_1(X0) )
             => v2_funct_1(k5_relat_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_funct_1(k5_relat_1(X0,X1))
          & v2_funct_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_funct_1(k5_relat_1(X0,X1))
          & v2_funct_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v2_funct_1(k5_relat_1(X0,X1))
          & v2_funct_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ~ v2_funct_1(k5_relat_1(X0,sK3))
        & v2_funct_1(sK3)
        & v2_funct_1(X0)
        & v1_funct_1(sK3)
        & v1_relat_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_funct_1(k5_relat_1(X0,X1))
            & v2_funct_1(X1)
            & v2_funct_1(X0)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ v2_funct_1(k5_relat_1(sK2,X1))
          & v2_funct_1(X1)
          & v2_funct_1(sK2)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    & v2_funct_1(sK3)
    & v2_funct_1(sK2)
    & v1_funct_1(sK3)
    & v1_relat_1(sK3)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f19,f27,f26])).

fof(f47,plain,(
    ~ v2_funct_1(k5_relat_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f28])).

fof(f30,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | r2_hidden(sK0(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f41,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f42,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f43,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f44,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f32,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f29,plain,(
    ! [X4,X0,X3] :
      ( X3 = X4
      | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f33,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | sK0(X0) != sK1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f46,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f45,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_2,plain,
    ( r2_hidden(sK1(X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_846,plain,
    ( r2_hidden(sK1(X0_39),k1_relat_1(X0_39))
    | ~ v1_relat_1(X0_39)
    | ~ v1_funct_1(X0_39)
    | v2_funct_1(X0_39) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1133,plain,
    ( r2_hidden(sK1(X0_39),k1_relat_1(X0_39)) = iProver_top
    | v1_relat_1(X0_39) != iProver_top
    | v1_funct_1(X0_39) != iProver_top
    | v2_funct_1(X0_39) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_846])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X1,X2)))
    | r2_hidden(k1_funct_1(X1,X0),k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_840,plain,
    ( ~ r2_hidden(X0_40,k1_relat_1(k5_relat_1(X0_39,X1_39)))
    | r2_hidden(k1_funct_1(X0_39,X0_40),k1_relat_1(X1_39))
    | ~ v1_relat_1(X1_39)
    | ~ v1_relat_1(X0_39)
    | ~ v1_funct_1(X1_39)
    | ~ v1_funct_1(X0_39) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1139,plain,
    ( r2_hidden(X0_40,k1_relat_1(k5_relat_1(X0_39,X1_39))) != iProver_top
    | r2_hidden(k1_funct_1(X0_39,X0_40),k1_relat_1(X1_39)) = iProver_top
    | v1_relat_1(X1_39) != iProver_top
    | v1_relat_1(X0_39) != iProver_top
    | v1_funct_1(X1_39) != iProver_top
    | v1_funct_1(X0_39) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_840])).

cnf(c_1753,plain,
    ( r2_hidden(k1_funct_1(X0_39,sK1(k5_relat_1(X0_39,X1_39))),k1_relat_1(X1_39)) = iProver_top
    | v1_relat_1(X1_39) != iProver_top
    | v1_relat_1(X0_39) != iProver_top
    | v1_relat_1(k5_relat_1(X0_39,X1_39)) != iProver_top
    | v1_funct_1(X1_39) != iProver_top
    | v1_funct_1(X0_39) != iProver_top
    | v1_funct_1(k5_relat_1(X0_39,X1_39)) != iProver_top
    | v2_funct_1(k5_relat_1(X0_39,X1_39)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1133,c_1139])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | v1_funct_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_842,plain,
    ( ~ v1_relat_1(X0_39)
    | ~ v1_relat_1(X1_39)
    | ~ v1_funct_1(X0_39)
    | ~ v1_funct_1(X1_39)
    | v1_funct_1(k5_relat_1(X0_39,X1_39)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1137,plain,
    ( v1_relat_1(X0_39) != iProver_top
    | v1_relat_1(X1_39) != iProver_top
    | v1_funct_1(X0_39) != iProver_top
    | v1_funct_1(X1_39) != iProver_top
    | v1_funct_1(k5_relat_1(X1_39,X0_39)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_842])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_843,plain,
    ( ~ v1_relat_1(X0_39)
    | ~ v1_relat_1(X1_39)
    | v1_relat_1(k5_relat_1(X0_39,X1_39)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1136,plain,
    ( v1_relat_1(X0_39) != iProver_top
    | v1_relat_1(X1_39) != iProver_top
    | v1_relat_1(k5_relat_1(X1_39,X0_39)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_843])).

cnf(c_2729,plain,
    ( r2_hidden(k1_funct_1(X0_39,sK1(k5_relat_1(X0_39,X1_39))),k1_relat_1(X1_39)) = iProver_top
    | v1_relat_1(X1_39) != iProver_top
    | v1_relat_1(X0_39) != iProver_top
    | v1_funct_1(X1_39) != iProver_top
    | v1_funct_1(X0_39) != iProver_top
    | v2_funct_1(k5_relat_1(X0_39,X1_39)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1753,c_1137,c_1136])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(X0,k1_relat_1(k5_relat_1(X1,X2)))
    | ~ r2_hidden(k1_funct_1(X1,X0),k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_841,plain,
    ( ~ r2_hidden(X0_40,k1_relat_1(X0_39))
    | r2_hidden(X0_40,k1_relat_1(k5_relat_1(X0_39,X1_39)))
    | ~ r2_hidden(k1_funct_1(X0_39,X0_40),k1_relat_1(X1_39))
    | ~ v1_relat_1(X1_39)
    | ~ v1_relat_1(X0_39)
    | ~ v1_funct_1(X1_39)
    | ~ v1_funct_1(X0_39) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1138,plain,
    ( r2_hidden(X0_40,k1_relat_1(X0_39)) != iProver_top
    | r2_hidden(X0_40,k1_relat_1(k5_relat_1(X0_39,X1_39))) = iProver_top
    | r2_hidden(k1_funct_1(X0_39,X0_40),k1_relat_1(X1_39)) != iProver_top
    | v1_relat_1(X1_39) != iProver_top
    | v1_relat_1(X0_39) != iProver_top
    | v1_funct_1(X1_39) != iProver_top
    | v1_funct_1(X0_39) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_841])).

cnf(c_2736,plain,
    ( r2_hidden(sK1(k5_relat_1(X0_39,X1_39)),k1_relat_1(X0_39)) != iProver_top
    | r2_hidden(sK1(k5_relat_1(X0_39,X1_39)),k1_relat_1(k5_relat_1(X0_39,X1_39))) = iProver_top
    | v1_relat_1(X0_39) != iProver_top
    | v1_relat_1(X1_39) != iProver_top
    | v1_funct_1(X0_39) != iProver_top
    | v1_funct_1(X1_39) != iProver_top
    | v2_funct_1(k5_relat_1(X0_39,X1_39)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2729,c_1138])).

cnf(c_10,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X1,X2)))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_839,plain,
    ( r2_hidden(X0_40,k1_relat_1(X0_39))
    | ~ r2_hidden(X0_40,k1_relat_1(k5_relat_1(X0_39,X1_39)))
    | ~ v1_relat_1(X1_39)
    | ~ v1_relat_1(X0_39)
    | ~ v1_funct_1(X1_39)
    | ~ v1_funct_1(X0_39) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1140,plain,
    ( r2_hidden(X0_40,k1_relat_1(X0_39)) = iProver_top
    | r2_hidden(X0_40,k1_relat_1(k5_relat_1(X0_39,X1_39))) != iProver_top
    | v1_relat_1(X1_39) != iProver_top
    | v1_relat_1(X0_39) != iProver_top
    | v1_funct_1(X1_39) != iProver_top
    | v1_funct_1(X0_39) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_839])).

cnf(c_1647,plain,
    ( r2_hidden(sK1(k5_relat_1(X0_39,X1_39)),k1_relat_1(X0_39)) = iProver_top
    | v1_relat_1(X1_39) != iProver_top
    | v1_relat_1(X0_39) != iProver_top
    | v1_relat_1(k5_relat_1(X0_39,X1_39)) != iProver_top
    | v1_funct_1(X1_39) != iProver_top
    | v1_funct_1(X0_39) != iProver_top
    | v1_funct_1(k5_relat_1(X0_39,X1_39)) != iProver_top
    | v2_funct_1(k5_relat_1(X0_39,X1_39)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1133,c_1140])).

cnf(c_2229,plain,
    ( r2_hidden(sK1(k5_relat_1(X0_39,X1_39)),k1_relat_1(X0_39)) = iProver_top
    | v1_relat_1(X1_39) != iProver_top
    | v1_relat_1(X0_39) != iProver_top
    | v1_funct_1(X1_39) != iProver_top
    | v1_funct_1(X0_39) != iProver_top
    | v2_funct_1(k5_relat_1(X0_39,X1_39)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1647,c_1137,c_1136])).

cnf(c_2912,plain,
    ( r2_hidden(sK1(k5_relat_1(X0_39,X1_39)),k1_relat_1(k5_relat_1(X0_39,X1_39))) = iProver_top
    | v1_relat_1(X0_39) != iProver_top
    | v1_relat_1(X1_39) != iProver_top
    | v1_funct_1(X0_39) != iProver_top
    | v1_funct_1(X1_39) != iProver_top
    | v2_funct_1(k5_relat_1(X0_39,X1_39)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2736,c_2229])).

cnf(c_2913,plain,
    ( r2_hidden(sK1(k5_relat_1(X0_39,X1_39)),k1_relat_1(k5_relat_1(X0_39,X1_39))) = iProver_top
    | v1_relat_1(X1_39) != iProver_top
    | v1_relat_1(X0_39) != iProver_top
    | v1_funct_1(X1_39) != iProver_top
    | v1_funct_1(X0_39) != iProver_top
    | v2_funct_1(k5_relat_1(X0_39,X1_39)) = iProver_top ),
    inference(renaming,[status(thm)],[c_2912])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X1,X2)))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_838,plain,
    ( ~ r2_hidden(X0_40,k1_relat_1(k5_relat_1(X0_39,X1_39)))
    | ~ v1_relat_1(X1_39)
    | ~ v1_relat_1(X0_39)
    | ~ v1_funct_1(X1_39)
    | ~ v1_funct_1(X0_39)
    | k1_funct_1(k5_relat_1(X0_39,X1_39),X0_40) = k1_funct_1(X1_39,k1_funct_1(X0_39,X0_40)) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1141,plain,
    ( k1_funct_1(k5_relat_1(X0_39,X1_39),X0_40) = k1_funct_1(X1_39,k1_funct_1(X0_39,X0_40))
    | r2_hidden(X0_40,k1_relat_1(k5_relat_1(X0_39,X1_39))) != iProver_top
    | v1_relat_1(X1_39) != iProver_top
    | v1_relat_1(X0_39) != iProver_top
    | v1_funct_1(X1_39) != iProver_top
    | v1_funct_1(X0_39) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_838])).

cnf(c_2924,plain,
    ( k1_funct_1(X0_39,k1_funct_1(X1_39,sK1(k5_relat_1(X1_39,X0_39)))) = k1_funct_1(k5_relat_1(X1_39,X0_39),sK1(k5_relat_1(X1_39,X0_39)))
    | v1_relat_1(X1_39) != iProver_top
    | v1_relat_1(X0_39) != iProver_top
    | v1_funct_1(X1_39) != iProver_top
    | v1_funct_1(X0_39) != iProver_top
    | v2_funct_1(k5_relat_1(X1_39,X0_39)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2913,c_1141])).

cnf(c_12,negated_conjecture,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_837,negated_conjecture,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3)) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1142,plain,
    ( v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_837])).

cnf(c_2961,plain,
    ( k1_funct_1(sK3,k1_funct_1(sK2,sK1(k5_relat_1(sK2,sK3)))) = k1_funct_1(k5_relat_1(sK2,sK3),sK1(k5_relat_1(sK2,sK3)))
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2924,c_1142])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_845,plain,
    ( r2_hidden(sK0(X0_39),k1_relat_1(X0_39))
    | ~ v1_relat_1(X0_39)
    | ~ v1_funct_1(X0_39)
    | v2_funct_1(X0_39) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1134,plain,
    ( r2_hidden(sK0(X0_39),k1_relat_1(X0_39)) = iProver_top
    | v1_relat_1(X0_39) != iProver_top
    | v1_funct_1(X0_39) != iProver_top
    | v2_funct_1(X0_39) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_845])).

cnf(c_1752,plain,
    ( r2_hidden(k1_funct_1(X0_39,sK0(k5_relat_1(X0_39,X1_39))),k1_relat_1(X1_39)) = iProver_top
    | v1_relat_1(X1_39) != iProver_top
    | v1_relat_1(X0_39) != iProver_top
    | v1_relat_1(k5_relat_1(X0_39,X1_39)) != iProver_top
    | v1_funct_1(X1_39) != iProver_top
    | v1_funct_1(X0_39) != iProver_top
    | v1_funct_1(k5_relat_1(X0_39,X1_39)) != iProver_top
    | v2_funct_1(k5_relat_1(X0_39,X1_39)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1134,c_1139])).

cnf(c_2314,plain,
    ( r2_hidden(k1_funct_1(X0_39,sK0(k5_relat_1(X0_39,X1_39))),k1_relat_1(X1_39)) = iProver_top
    | v1_relat_1(X1_39) != iProver_top
    | v1_relat_1(X0_39) != iProver_top
    | v1_funct_1(X1_39) != iProver_top
    | v1_funct_1(X0_39) != iProver_top
    | v2_funct_1(k5_relat_1(X0_39,X1_39)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1752,c_1137,c_1136])).

cnf(c_2321,plain,
    ( r2_hidden(sK0(k5_relat_1(X0_39,X1_39)),k1_relat_1(X0_39)) != iProver_top
    | r2_hidden(sK0(k5_relat_1(X0_39,X1_39)),k1_relat_1(k5_relat_1(X0_39,X1_39))) = iProver_top
    | v1_relat_1(X0_39) != iProver_top
    | v1_relat_1(X1_39) != iProver_top
    | v1_funct_1(X0_39) != iProver_top
    | v1_funct_1(X1_39) != iProver_top
    | v2_funct_1(k5_relat_1(X0_39,X1_39)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2314,c_1138])).

cnf(c_1646,plain,
    ( r2_hidden(sK0(k5_relat_1(X0_39,X1_39)),k1_relat_1(X0_39)) = iProver_top
    | v1_relat_1(X1_39) != iProver_top
    | v1_relat_1(X0_39) != iProver_top
    | v1_relat_1(k5_relat_1(X0_39,X1_39)) != iProver_top
    | v1_funct_1(X1_39) != iProver_top
    | v1_funct_1(X0_39) != iProver_top
    | v1_funct_1(k5_relat_1(X0_39,X1_39)) != iProver_top
    | v2_funct_1(k5_relat_1(X0_39,X1_39)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1134,c_1140])).

cnf(c_2078,plain,
    ( r2_hidden(sK0(k5_relat_1(X0_39,X1_39)),k1_relat_1(X0_39)) = iProver_top
    | v1_relat_1(X1_39) != iProver_top
    | v1_relat_1(X0_39) != iProver_top
    | v1_funct_1(X1_39) != iProver_top
    | v1_funct_1(X0_39) != iProver_top
    | v2_funct_1(k5_relat_1(X0_39,X1_39)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1646,c_1137,c_1136])).

cnf(c_2468,plain,
    ( r2_hidden(sK0(k5_relat_1(X0_39,X1_39)),k1_relat_1(k5_relat_1(X0_39,X1_39))) = iProver_top
    | v1_relat_1(X0_39) != iProver_top
    | v1_relat_1(X1_39) != iProver_top
    | v1_funct_1(X0_39) != iProver_top
    | v1_funct_1(X1_39) != iProver_top
    | v2_funct_1(k5_relat_1(X0_39,X1_39)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2321,c_2078])).

cnf(c_2469,plain,
    ( r2_hidden(sK0(k5_relat_1(X0_39,X1_39)),k1_relat_1(k5_relat_1(X0_39,X1_39))) = iProver_top
    | v1_relat_1(X1_39) != iProver_top
    | v1_relat_1(X0_39) != iProver_top
    | v1_funct_1(X1_39) != iProver_top
    | v1_funct_1(X0_39) != iProver_top
    | v2_funct_1(k5_relat_1(X0_39,X1_39)) = iProver_top ),
    inference(renaming,[status(thm)],[c_2468])).

cnf(c_2480,plain,
    ( k1_funct_1(X0_39,k1_funct_1(X1_39,sK0(k5_relat_1(X1_39,X0_39)))) = k1_funct_1(k5_relat_1(X1_39,X0_39),sK0(k5_relat_1(X1_39,X0_39)))
    | v1_relat_1(X1_39) != iProver_top
    | v1_relat_1(X0_39) != iProver_top
    | v1_funct_1(X1_39) != iProver_top
    | v1_funct_1(X0_39) != iProver_top
    | v2_funct_1(k5_relat_1(X1_39,X0_39)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2469,c_1141])).

cnf(c_2548,plain,
    ( k1_funct_1(sK3,k1_funct_1(sK2,sK0(k5_relat_1(sK2,sK3)))) = k1_funct_1(k5_relat_1(sK2,sK3),sK0(k5_relat_1(sK2,sK3)))
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2480,c_1142])).

cnf(c_18,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_19,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_17,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_20,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_16,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_21,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_15,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_22,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2551,plain,
    ( k1_funct_1(sK3,k1_funct_1(sK2,sK0(k5_relat_1(sK2,sK3)))) = k1_funct_1(k5_relat_1(sK2,sK3),sK0(k5_relat_1(sK2,sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2548,c_19,c_20,c_21,c_22])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_847,plain,
    ( ~ v1_relat_1(X0_39)
    | ~ v1_funct_1(X0_39)
    | v2_funct_1(X0_39)
    | k1_funct_1(X0_39,sK1(X0_39)) = k1_funct_1(X0_39,sK0(X0_39)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1132,plain,
    ( k1_funct_1(X0_39,sK1(X0_39)) = k1_funct_1(X0_39,sK0(X0_39))
    | v1_relat_1(X0_39) != iProver_top
    | v1_funct_1(X0_39) != iProver_top
    | v2_funct_1(X0_39) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_847])).

cnf(c_1543,plain,
    ( k1_funct_1(k5_relat_1(X0_39,X1_39),sK0(k5_relat_1(X0_39,X1_39))) = k1_funct_1(k5_relat_1(X0_39,X1_39),sK1(k5_relat_1(X0_39,X1_39)))
    | v1_relat_1(X0_39) != iProver_top
    | v1_relat_1(X1_39) != iProver_top
    | v1_funct_1(k5_relat_1(X0_39,X1_39)) != iProver_top
    | v2_funct_1(k5_relat_1(X0_39,X1_39)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1136,c_1132])).

cnf(c_1962,plain,
    ( k1_funct_1(k5_relat_1(X0_39,X1_39),sK0(k5_relat_1(X0_39,X1_39))) = k1_funct_1(k5_relat_1(X0_39,X1_39),sK1(k5_relat_1(X0_39,X1_39)))
    | v1_relat_1(X0_39) != iProver_top
    | v1_relat_1(X1_39) != iProver_top
    | v1_funct_1(X0_39) != iProver_top
    | v1_funct_1(X1_39) != iProver_top
    | v2_funct_1(k5_relat_1(X0_39,X1_39)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1137,c_1543])).

cnf(c_1973,plain,
    ( k1_funct_1(k5_relat_1(sK2,sK3),sK0(k5_relat_1(sK2,sK3))) = k1_funct_1(k5_relat_1(sK2,sK3),sK1(k5_relat_1(sK2,sK3)))
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1962,c_1142])).

cnf(c_2155,plain,
    ( k1_funct_1(k5_relat_1(sK2,sK3),sK0(k5_relat_1(sK2,sK3))) = k1_funct_1(k5_relat_1(sK2,sK3),sK1(k5_relat_1(sK2,sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1973,c_19,c_20,c_21,c_22])).

cnf(c_2555,plain,
    ( k1_funct_1(sK3,k1_funct_1(sK2,sK0(k5_relat_1(sK2,sK3)))) = k1_funct_1(k5_relat_1(sK2,sK3),sK1(k5_relat_1(sK2,sK3))) ),
    inference(demodulation,[status(thm)],[c_2551,c_2155])).

cnf(c_2962,plain,
    ( k1_funct_1(sK3,k1_funct_1(sK2,sK1(k5_relat_1(sK2,sK3)))) = k1_funct_1(sK3,k1_funct_1(sK2,sK0(k5_relat_1(sK2,sK3))))
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2961,c_2555])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | X0 = X2
    | k1_funct_1(X1,X0) != k1_funct_1(X1,X2) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_844,plain,
    ( ~ r2_hidden(X0_40,k1_relat_1(X0_39))
    | ~ r2_hidden(X1_40,k1_relat_1(X0_39))
    | ~ v1_relat_1(X0_39)
    | ~ v1_funct_1(X0_39)
    | ~ v2_funct_1(X0_39)
    | X0_40 = X1_40
    | k1_funct_1(X0_39,X0_40) != k1_funct_1(X0_39,X1_40) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1467,plain,
    ( ~ r2_hidden(k1_funct_1(X0_39,sK1(k5_relat_1(sK2,sK3))),k1_relat_1(X1_39))
    | ~ r2_hidden(k1_funct_1(X0_39,sK0(k5_relat_1(sK2,sK3))),k1_relat_1(X1_39))
    | ~ v1_relat_1(X1_39)
    | ~ v1_funct_1(X1_39)
    | ~ v2_funct_1(X1_39)
    | k1_funct_1(X1_39,k1_funct_1(X0_39,sK1(k5_relat_1(sK2,sK3)))) != k1_funct_1(X1_39,k1_funct_1(X0_39,sK0(k5_relat_1(sK2,sK3))))
    | k1_funct_1(X0_39,sK1(k5_relat_1(sK2,sK3))) = k1_funct_1(X0_39,sK0(k5_relat_1(sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_844])).

cnf(c_1686,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK1(k5_relat_1(sK2,sK3))),k1_relat_1(sK3))
    | ~ r2_hidden(k1_funct_1(sK2,sK0(k5_relat_1(sK2,sK3))),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | k1_funct_1(sK3,k1_funct_1(sK2,sK1(k5_relat_1(sK2,sK3)))) != k1_funct_1(sK3,k1_funct_1(sK2,sK0(k5_relat_1(sK2,sK3))))
    | k1_funct_1(sK2,sK1(k5_relat_1(sK2,sK3))) = k1_funct_1(sK2,sK0(k5_relat_1(sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_1467])).

cnf(c_1384,plain,
    ( ~ r2_hidden(sK1(k5_relat_1(sK2,sK3)),k1_relat_1(X0_39))
    | ~ r2_hidden(sK0(k5_relat_1(sK2,sK3)),k1_relat_1(X0_39))
    | ~ v1_relat_1(X0_39)
    | ~ v1_funct_1(X0_39)
    | ~ v2_funct_1(X0_39)
    | k1_funct_1(X0_39,sK1(k5_relat_1(sK2,sK3))) != k1_funct_1(X0_39,sK0(k5_relat_1(sK2,sK3)))
    | sK1(k5_relat_1(sK2,sK3)) = sK0(k5_relat_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_844])).

cnf(c_1386,plain,
    ( ~ r2_hidden(sK1(k5_relat_1(sK2,sK3)),k1_relat_1(sK2))
    | ~ r2_hidden(sK0(k5_relat_1(sK2,sK3)),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k1_funct_1(sK2,sK1(k5_relat_1(sK2,sK3))) != k1_funct_1(sK2,sK0(k5_relat_1(sK2,sK3)))
    | sK1(k5_relat_1(sK2,sK3)) = sK0(k5_relat_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_1384])).

cnf(c_1366,plain,
    ( r2_hidden(k1_funct_1(sK2,sK1(k5_relat_1(sK2,sK3))),k1_relat_1(sK3))
    | ~ r2_hidden(sK1(k5_relat_1(sK2,sK3)),k1_relat_1(k5_relat_1(sK2,sK3)))
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_840])).

cnf(c_1367,plain,
    ( ~ r2_hidden(sK1(k5_relat_1(sK2,sK3)),k1_relat_1(k5_relat_1(sK2,sK3)))
    | r2_hidden(sK1(k5_relat_1(sK2,sK3)),k1_relat_1(sK2))
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_839])).

cnf(c_1347,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0(k5_relat_1(sK2,sK3))),k1_relat_1(sK3))
    | ~ r2_hidden(sK0(k5_relat_1(sK2,sK3)),k1_relat_1(k5_relat_1(sK2,sK3)))
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_840])).

cnf(c_1348,plain,
    ( ~ r2_hidden(sK0(k5_relat_1(sK2,sK3)),k1_relat_1(k5_relat_1(sK2,sK3)))
    | r2_hidden(sK0(k5_relat_1(sK2,sK3)),k1_relat_1(sK2))
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_839])).

cnf(c_1337,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | v1_funct_1(k5_relat_1(sK2,sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_842])).

cnf(c_1332,plain,
    ( v1_relat_1(k5_relat_1(sK2,sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_843])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | sK1(X0) != sK0(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_848,plain,
    ( ~ v1_relat_1(X0_39)
    | ~ v1_funct_1(X0_39)
    | v2_funct_1(X0_39)
    | sK1(X0_39) != sK0(X0_39) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1322,plain,
    ( ~ v1_relat_1(k5_relat_1(sK2,sK3))
    | ~ v1_funct_1(k5_relat_1(sK2,sK3))
    | v2_funct_1(k5_relat_1(sK2,sK3))
    | sK1(k5_relat_1(sK2,sK3)) != sK0(k5_relat_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_848])).

cnf(c_318,plain,
    ( r2_hidden(sK1(X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k5_relat_1(sK2,sK3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_12])).

cnf(c_319,plain,
    ( r2_hidden(sK1(k5_relat_1(sK2,sK3)),k1_relat_1(k5_relat_1(sK2,sK3)))
    | ~ v1_relat_1(k5_relat_1(sK2,sK3))
    | ~ v1_funct_1(k5_relat_1(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_318])).

cnf(c_305,plain,
    ( r2_hidden(sK0(X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k5_relat_1(sK2,sK3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_12])).

cnf(c_306,plain,
    ( r2_hidden(sK0(k5_relat_1(sK2,sK3)),k1_relat_1(k5_relat_1(sK2,sK3)))
    | ~ v1_relat_1(k5_relat_1(sK2,sK3))
    | ~ v1_funct_1(k5_relat_1(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_305])).

cnf(c_13,negated_conjecture,
    ( v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_14,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f45])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2962,c_1686,c_1386,c_1366,c_1367,c_1347,c_1348,c_1337,c_1332,c_1322,c_319,c_306,c_12,c_13,c_14,c_22,c_15,c_21,c_16,c_20,c_17,c_19,c_18])).


%------------------------------------------------------------------------------
