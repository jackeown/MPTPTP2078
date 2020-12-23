%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0654+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:49 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 862 expanded)
%              Number of clauses        :   68 ( 215 expanded)
%              Number of leaves         :   11 ( 173 expanded)
%              Depth                    :   21
%              Number of atoms          :  502 (4006 expanded)
%              Number of equality atoms :  258 (1648 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f14,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
          & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
    ! [X0] :
      ( ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f51,plain,(
    ! [X0] :
      ( k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
            & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f27,plain,(
    ? [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) != k6_relat_1(k2_relat_1(X0))
        | k5_relat_1(X0,k2_funct_1(X0)) != k6_relat_1(k1_relat_1(X0)) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
    ? [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) != k6_relat_1(k2_relat_1(X0))
        | k5_relat_1(X0,k2_funct_1(X0)) != k6_relat_1(k1_relat_1(X0)) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f34,plain,
    ( ? [X0] :
        ( ( k5_relat_1(k2_funct_1(X0),X0) != k6_relat_1(k2_relat_1(X0))
          | k5_relat_1(X0,k2_funct_1(X0)) != k6_relat_1(k1_relat_1(X0)) )
        & v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ( k5_relat_1(k2_funct_1(sK1),sK1) != k6_relat_1(k2_relat_1(sK1))
        | k5_relat_1(sK1,k2_funct_1(sK1)) != k6_relat_1(k1_relat_1(sK1)) )
      & v2_funct_1(sK1)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ( k5_relat_1(k2_funct_1(sK1),sK1) != k6_relat_1(k2_relat_1(sK1))
      | k5_relat_1(sK1,k2_funct_1(sK1)) != k6_relat_1(k1_relat_1(sK1)) )
    & v2_funct_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f34])).

fof(f55,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f53,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f54,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X2] :
                ( k1_funct_1(X1,X2) = X2
                | ~ r2_hidden(X2,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X2] :
                ( k1_funct_1(X1,X2) = X2
                | ~ r2_hidden(X2,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X1,X2) != X2
          & r2_hidden(X2,X0) )
     => ( k1_funct_1(X1,sK0(X0,X1)) != sK0(X0,X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( k1_funct_1(X1,sK0(X0,X1)) != sK0(X0,X1)
            & r2_hidden(sK0(X0,X1),X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = X1
      | r2_hidden(sK0(X0,X1),X0)
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f58,plain,(
    ! [X1] :
      ( k6_relat_1(k1_relat_1(X1)) = X1
      | r2_hidden(sK0(k1_relat_1(X1),X1),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f43])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(X1,X3) = X3
      | ~ r2_hidden(X3,X0)
      | k6_relat_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f59,plain,(
    ! [X0,X3] :
      ( k1_funct_1(k6_relat_1(X0),X3) = X3
      | ~ r2_hidden(X3,X0)
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f42])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = X1
      | k1_funct_1(X1,sK0(X0,X1)) != sK0(X0,X1)
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f57,plain,(
    ! [X1] :
      ( k6_relat_1(k1_relat_1(X1)) = X1
      | k1_funct_1(X1,sK0(k1_relat_1(X1),X1)) != sK0(k1_relat_1(X1),X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f44])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k2_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
          & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
        & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 )
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
        & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 )
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f56,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) != k6_relat_1(k2_relat_1(sK1))
    | k5_relat_1(sK1,k2_funct_1(sK1)) != k6_relat_1(k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f35])).

fof(f1,axiom,(
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
    inference(ennf_transformation,[],[f1])).

fof(f12,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f36,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f37,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f49,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k1_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
          & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | v1_funct_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_986,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(k5_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_987,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_16,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_18,negated_conjecture,
    ( v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_301,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_18])).

cnf(c_302,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | k1_relat_1(k5_relat_1(k2_funct_1(sK1),sK1)) = k2_relat_1(sK1) ),
    inference(unflattening,[status(thm)],[c_301])).

cnf(c_20,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_19,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_25,plain,
    ( ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | k1_relat_1(k5_relat_1(k2_funct_1(sK1),sK1)) = k2_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_304,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1(sK1),sK1)) = k2_relat_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_302,c_20,c_19,c_18,c_25])).

cnf(c_6,plain,
    ( r2_hidden(sK0(k1_relat_1(X0),X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k6_relat_1(k1_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_984,plain,
    ( k6_relat_1(k1_relat_1(X0)) = X0
    | r2_hidden(sK0(k1_relat_1(X0),X0),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_relat_1(k6_relat_1(X1))
    | ~ v1_funct_1(k6_relat_1(X1))
    | k1_funct_1(k6_relat_1(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_983,plain,
    ( k1_funct_1(k6_relat_1(X0),X1) = X1
    | r2_hidden(X1,X0) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top
    | v1_funct_1(k6_relat_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1734,plain,
    ( k1_funct_1(k6_relat_1(k1_relat_1(X0)),sK0(k1_relat_1(X0),X0)) = sK0(k1_relat_1(X0),X0)
    | k6_relat_1(k1_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k6_relat_1(k1_relat_1(X0))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k6_relat_1(k1_relat_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_984,c_983])).

cnf(c_1795,plain,
    ( k1_funct_1(k6_relat_1(k1_relat_1(k5_relat_1(k2_funct_1(sK1),sK1))),sK0(k1_relat_1(k5_relat_1(k2_funct_1(sK1),sK1)),k5_relat_1(k2_funct_1(sK1),sK1))) = sK0(k1_relat_1(k5_relat_1(k2_funct_1(sK1),sK1)),k5_relat_1(k2_funct_1(sK1),sK1))
    | k6_relat_1(k1_relat_1(k5_relat_1(k2_funct_1(sK1),sK1))) = k5_relat_1(k2_funct_1(sK1),sK1)
    | v1_relat_1(k5_relat_1(k2_funct_1(sK1),sK1)) != iProver_top
    | v1_relat_1(k6_relat_1(k2_relat_1(sK1))) != iProver_top
    | v1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1)) != iProver_top
    | v1_funct_1(k6_relat_1(k1_relat_1(k5_relat_1(k2_funct_1(sK1),sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_304,c_1734])).

cnf(c_1816,plain,
    ( k1_funct_1(k6_relat_1(k2_relat_1(sK1)),sK0(k2_relat_1(sK1),k5_relat_1(k2_funct_1(sK1),sK1))) = sK0(k2_relat_1(sK1),k5_relat_1(k2_funct_1(sK1),sK1))
    | k5_relat_1(k2_funct_1(sK1),sK1) = k6_relat_1(k2_relat_1(sK1))
    | v1_relat_1(k5_relat_1(k2_funct_1(sK1),sK1)) != iProver_top
    | v1_relat_1(k6_relat_1(k2_relat_1(sK1))) != iProver_top
    | v1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1)) != iProver_top
    | v1_funct_1(k6_relat_1(k2_relat_1(sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1795,c_304])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_funct_1(X0,sK0(k1_relat_1(X0),X0)) != sK0(k1_relat_1(X0),X0)
    | k6_relat_1(k1_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_985,plain,
    ( k1_funct_1(X0,sK0(k1_relat_1(X0),X0)) != sK0(k1_relat_1(X0),X0)
    | k6_relat_1(k1_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1503,plain,
    ( k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0(k2_relat_1(sK1),k5_relat_1(k2_funct_1(sK1),sK1))) != sK0(k1_relat_1(k5_relat_1(k2_funct_1(sK1),sK1)),k5_relat_1(k2_funct_1(sK1),sK1))
    | k6_relat_1(k1_relat_1(k5_relat_1(k2_funct_1(sK1),sK1))) = k5_relat_1(k2_funct_1(sK1),sK1)
    | v1_relat_1(k5_relat_1(k2_funct_1(sK1),sK1)) != iProver_top
    | v1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_304,c_985])).

cnf(c_1518,plain,
    ( k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0(k2_relat_1(sK1),k5_relat_1(k2_funct_1(sK1),sK1))) != sK0(k2_relat_1(sK1),k5_relat_1(k2_funct_1(sK1),sK1))
    | k5_relat_1(k2_funct_1(sK1),sK1) = k6_relat_1(k2_relat_1(sK1))
    | v1_relat_1(k5_relat_1(k2_funct_1(sK1),sK1)) != iProver_top
    | v1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1503,c_304])).

cnf(c_1732,plain,
    ( k6_relat_1(k1_relat_1(k5_relat_1(k2_funct_1(sK1),sK1))) = k5_relat_1(k2_funct_1(sK1),sK1)
    | r2_hidden(sK0(k2_relat_1(sK1),k5_relat_1(k2_funct_1(sK1),sK1)),k2_relat_1(sK1)) = iProver_top
    | v1_relat_1(k5_relat_1(k2_funct_1(sK1),sK1)) != iProver_top
    | v1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_304,c_984])).

cnf(c_1778,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_relat_1(k2_relat_1(sK1))
    | r2_hidden(sK0(k2_relat_1(sK1),k5_relat_1(k2_funct_1(sK1),sK1)),k2_relat_1(sK1)) = iProver_top
    | v1_relat_1(k5_relat_1(k2_funct_1(sK1),sK1)) != iProver_top
    | v1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1732,c_304])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_247,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_18])).

cnf(c_248,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),X0) = X0 ),
    inference(unflattening,[status(thm)],[c_247])).

cnf(c_252,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK1))
    | k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_248,c_20,c_19])).

cnf(c_978,plain,
    ( k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),X0) = X0
    | r2_hidden(X0,k2_relat_1(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_252])).

cnf(c_2086,plain,
    ( k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0(k2_relat_1(sK1),k5_relat_1(k2_funct_1(sK1),sK1))) = sK0(k2_relat_1(sK1),k5_relat_1(k2_funct_1(sK1),sK1))
    | k5_relat_1(k2_funct_1(sK1),sK1) = k6_relat_1(k2_relat_1(sK1))
    | v1_relat_1(k5_relat_1(k2_funct_1(sK1),sK1)) != iProver_top
    | v1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1778,c_978])).

cnf(c_2203,plain,
    ( v1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1)) != iProver_top
    | k5_relat_1(k2_funct_1(sK1),sK1) = k6_relat_1(k2_relat_1(sK1))
    | v1_relat_1(k5_relat_1(k2_funct_1(sK1),sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1816,c_1518,c_2086])).

cnf(c_2204,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_relat_1(k2_relat_1(sK1))
    | v1_relat_1(k5_relat_1(k2_funct_1(sK1),sK1)) != iProver_top
    | v1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2203])).

cnf(c_2210,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_relat_1(k2_relat_1(sK1))
    | v1_relat_1(k2_funct_1(sK1)) != iProver_top
    | v1_relat_1(sK1) != iProver_top
    | v1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_987,c_2204])).

cnf(c_21,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_22,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_17,negated_conjecture,
    ( k5_relat_1(k2_funct_1(sK1),sK1) != k6_relat_1(k2_relat_1(sK1))
    | k5_relat_1(sK1,k2_funct_1(sK1)) != k6_relat_1(k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_69,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_71,plain,
    ( v1_relat_1(k2_funct_1(sK1)) = iProver_top
    | v1_relat_1(sK1) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_69])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_72,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_74,plain,
    ( v1_relat_1(sK1) != iProver_top
    | v1_funct_1(k2_funct_1(sK1)) = iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_72])).

cnf(c_14,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_317,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_18])).

cnf(c_318,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | k1_relat_1(k5_relat_1(sK1,k2_funct_1(sK1))) = k1_relat_1(sK1) ),
    inference(unflattening,[status(thm)],[c_317])).

cnf(c_31,plain,
    ( ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | k1_relat_1(k5_relat_1(sK1,k2_funct_1(sK1))) = k1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_320,plain,
    ( k1_relat_1(k5_relat_1(sK1,k2_funct_1(sK1))) = k1_relat_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_318,c_20,c_19,c_18,c_31])).

cnf(c_1796,plain,
    ( k1_funct_1(k6_relat_1(k1_relat_1(k5_relat_1(sK1,k2_funct_1(sK1)))),sK0(k1_relat_1(k5_relat_1(sK1,k2_funct_1(sK1))),k5_relat_1(sK1,k2_funct_1(sK1)))) = sK0(k1_relat_1(k5_relat_1(sK1,k2_funct_1(sK1))),k5_relat_1(sK1,k2_funct_1(sK1)))
    | k6_relat_1(k1_relat_1(k5_relat_1(sK1,k2_funct_1(sK1)))) = k5_relat_1(sK1,k2_funct_1(sK1))
    | v1_relat_1(k5_relat_1(sK1,k2_funct_1(sK1))) != iProver_top
    | v1_relat_1(k6_relat_1(k1_relat_1(sK1))) != iProver_top
    | v1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1))) != iProver_top
    | v1_funct_1(k6_relat_1(k1_relat_1(k5_relat_1(sK1,k2_funct_1(sK1))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_320,c_1734])).

cnf(c_1803,plain,
    ( k1_funct_1(k6_relat_1(k1_relat_1(sK1)),sK0(k1_relat_1(sK1),k5_relat_1(sK1,k2_funct_1(sK1)))) = sK0(k1_relat_1(sK1),k5_relat_1(sK1,k2_funct_1(sK1)))
    | k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1))
    | v1_relat_1(k5_relat_1(sK1,k2_funct_1(sK1))) != iProver_top
    | v1_relat_1(k6_relat_1(k1_relat_1(sK1))) != iProver_top
    | v1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1))) != iProver_top
    | v1_funct_1(k6_relat_1(k1_relat_1(sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1796,c_320])).

cnf(c_1504,plain,
    ( k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0(k1_relat_1(sK1),k5_relat_1(sK1,k2_funct_1(sK1)))) != sK0(k1_relat_1(k5_relat_1(sK1,k2_funct_1(sK1))),k5_relat_1(sK1,k2_funct_1(sK1)))
    | k6_relat_1(k1_relat_1(k5_relat_1(sK1,k2_funct_1(sK1)))) = k5_relat_1(sK1,k2_funct_1(sK1))
    | v1_relat_1(k5_relat_1(sK1,k2_funct_1(sK1))) != iProver_top
    | v1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_320,c_985])).

cnf(c_1509,plain,
    ( k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0(k1_relat_1(sK1),k5_relat_1(sK1,k2_funct_1(sK1)))) != sK0(k1_relat_1(sK1),k5_relat_1(sK1,k2_funct_1(sK1)))
    | k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1))
    | v1_relat_1(k5_relat_1(sK1,k2_funct_1(sK1))) != iProver_top
    | v1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1504,c_320])).

cnf(c_1733,plain,
    ( k6_relat_1(k1_relat_1(k5_relat_1(sK1,k2_funct_1(sK1)))) = k5_relat_1(sK1,k2_funct_1(sK1))
    | r2_hidden(sK0(k1_relat_1(sK1),k5_relat_1(sK1,k2_funct_1(sK1))),k1_relat_1(sK1)) = iProver_top
    | v1_relat_1(k5_relat_1(sK1,k2_funct_1(sK1))) != iProver_top
    | v1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_320,c_984])).

cnf(c_1769,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1))
    | r2_hidden(sK0(k1_relat_1(sK1),k5_relat_1(sK1,k2_funct_1(sK1))),k1_relat_1(sK1)) = iProver_top
    | v1_relat_1(k5_relat_1(sK1,k2_funct_1(sK1))) != iProver_top
    | v1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1733,c_320])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_283,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_18])).

cnf(c_284,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),X0) = X0 ),
    inference(unflattening,[status(thm)],[c_283])).

cnf(c_288,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK1))
    | k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_284,c_20,c_19])).

cnf(c_976,plain,
    ( k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),X0) = X0
    | r2_hidden(X0,k1_relat_1(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_288])).

cnf(c_2060,plain,
    ( k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0(k1_relat_1(sK1),k5_relat_1(sK1,k2_funct_1(sK1)))) = sK0(k1_relat_1(sK1),k5_relat_1(sK1,k2_funct_1(sK1)))
    | k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1))
    | v1_relat_1(k5_relat_1(sK1,k2_funct_1(sK1))) != iProver_top
    | v1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1769,c_976])).

cnf(c_2193,plain,
    ( v1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1))) != iProver_top
    | k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1))
    | v1_relat_1(k5_relat_1(sK1,k2_funct_1(sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1803,c_1509,c_2060])).

cnf(c_2194,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1))
    | v1_relat_1(k5_relat_1(sK1,k2_funct_1(sK1))) != iProver_top
    | v1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2193])).

cnf(c_2200,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1))
    | v1_relat_1(k2_funct_1(sK1)) != iProver_top
    | v1_relat_1(sK1) != iProver_top
    | v1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_987,c_2194])).

cnf(c_2346,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1))
    | v1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2200,c_21,c_22,c_71])).

cnf(c_2352,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1))
    | v1_relat_1(k2_funct_1(sK1)) != iProver_top
    | v1_relat_1(sK1) != iProver_top
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_986,c_2346])).

cnf(c_2355,plain,
    ( v1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2210,c_21,c_22,c_17,c_71,c_74,c_2352])).

cnf(c_2360,plain,
    ( v1_relat_1(k2_funct_1(sK1)) != iProver_top
    | v1_relat_1(sK1) != iProver_top
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_986,c_2355])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2360,c_74,c_71,c_22,c_21])).


%------------------------------------------------------------------------------
