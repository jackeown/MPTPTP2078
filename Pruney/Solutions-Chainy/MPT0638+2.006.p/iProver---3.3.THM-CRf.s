%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:50:13 EST 2020

% Result     : Theorem 55.19s
% Output     : CNFRefutation 55.19s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 402 expanded)
%              Number of clauses        :   57 ( 105 expanded)
%              Number of leaves         :   15 ( 107 expanded)
%              Depth                    :   21
%              Number of atoms          :  403 (2350 expanded)
%              Number of equality atoms :  213 (1095 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = X0
              & k2_relat_1(X0) = k1_relat_1(X1) )
           => k6_relat_1(k1_relat_1(X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( k5_relat_1(X0,X1) = X0
                & k2_relat_1(X0) = k1_relat_1(X1) )
             => k6_relat_1(k1_relat_1(X1)) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k6_relat_1(k1_relat_1(X1)) != X1
          & k5_relat_1(X0,X1) = X0
          & k2_relat_1(X0) = k1_relat_1(X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k6_relat_1(k1_relat_1(X1)) != X1
          & k5_relat_1(X0,X1) = X0
          & k2_relat_1(X0) = k1_relat_1(X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k6_relat_1(k1_relat_1(X1)) != X1
          & k5_relat_1(X0,X1) = X0
          & k2_relat_1(X0) = k1_relat_1(X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( k6_relat_1(k1_relat_1(sK5)) != sK5
        & k5_relat_1(X0,sK5) = X0
        & k2_relat_1(X0) = k1_relat_1(sK5)
        & v1_funct_1(sK5)
        & v1_relat_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k6_relat_1(k1_relat_1(X1)) != X1
            & k5_relat_1(X0,X1) = X0
            & k2_relat_1(X0) = k1_relat_1(X1)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k6_relat_1(k1_relat_1(X1)) != X1
          & k5_relat_1(sK4,X1) = sK4
          & k2_relat_1(sK4) = k1_relat_1(X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK4)
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( k6_relat_1(k1_relat_1(sK5)) != sK5
    & k5_relat_1(sK4,sK5) = sK4
    & k2_relat_1(sK4) = k1_relat_1(sK5)
    & v1_funct_1(sK5)
    & v1_relat_1(sK5)
    & v1_funct_1(sK4)
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f14,f29,f28])).

fof(f47,plain,(
    k2_relat_1(sK4) = k1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X1,X2) != X2
          & r2_hidden(X2,X0) )
     => ( k1_funct_1(X1,sK3(X0,X1)) != sK3(X0,X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( k1_funct_1(X1,sK3(X0,X1)) != sK3(X0,X1)
            & r2_hidden(sK3(X0,X1),X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f24])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = X1
      | r2_hidden(sK3(X0,X1),X0)
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f53,plain,(
    ! [X1] :
      ( k6_relat_1(k1_relat_1(X1)) = X1
      | r2_hidden(sK3(k1_relat_1(X1),X1),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f38])).

fof(f45,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f30])).

fof(f46,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f30])).

fof(f49,plain,(
    k6_relat_1(k1_relat_1(sK5)) != sK5 ),
    inference(cnf_transformation,[],[f30])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f15])).

fof(f19,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK2(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK1(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK0(X0,X1)),X0)
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK0(X0,X1)),X0)
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK0(X0,X1)),X0)
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK1(X0,X1),sK0(X0,X1)),X0)
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK2(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f19,f18,f17])).

fof(f31,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK2(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f51,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK2(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f31])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f43,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f30])).

fof(f44,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f30])).

fof(f48,plain,(
    k5_relat_1(sK4,sK5) = sK4 ),
    inference(cnf_transformation,[],[f30])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f7])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = X1
      | k1_funct_1(X1,sK3(X0,X1)) != sK3(X0,X1)
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f52,plain,(
    ! [X1] :
      ( k6_relat_1(k1_relat_1(X1)) = X1
      | k1_funct_1(X1,sK3(k1_relat_1(X1),X1)) != sK3(k1_relat_1(X1),X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f39])).

cnf(c_188,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_91111,plain,
    ( X0 != X1
    | X0 = sK3(k1_relat_1(X2),X2)
    | sK3(k1_relat_1(X2),X2) != X1 ),
    inference(instantiation,[status(thm)],[c_188])).

cnf(c_91254,plain,
    ( X0 != sK3(X1,X2)
    | X0 = sK3(k1_relat_1(X2),X2)
    | sK3(k1_relat_1(X2),X2) != sK3(X1,X2) ),
    inference(instantiation,[status(thm)],[c_91111])).

cnf(c_93120,plain,
    ( X0 = sK3(k1_relat_1(sK5),sK5)
    | X0 != sK3(k2_relat_1(sK4),sK5)
    | sK3(k1_relat_1(sK5),sK5) != sK3(k2_relat_1(sK4),sK5) ),
    inference(instantiation,[status(thm)],[c_91254])).

cnf(c_187805,plain,
    ( sK3(k1_relat_1(sK5),sK5) != sK3(k2_relat_1(sK4),sK5)
    | k1_funct_1(X0,sK3(k2_relat_1(sK4),sK5)) = sK3(k1_relat_1(sK5),sK5)
    | k1_funct_1(X0,sK3(k2_relat_1(sK4),sK5)) != sK3(k2_relat_1(sK4),sK5) ),
    inference(instantiation,[status(thm)],[c_93120])).

cnf(c_187807,plain,
    ( sK3(k1_relat_1(sK5),sK5) != sK3(k2_relat_1(sK4),sK5)
    | k1_funct_1(sK5,sK3(k2_relat_1(sK4),sK5)) = sK3(k1_relat_1(sK5),sK5)
    | k1_funct_1(sK5,sK3(k2_relat_1(sK4),sK5)) != sK3(k2_relat_1(sK4),sK5) ),
    inference(instantiation,[status(thm)],[c_187805])).

cnf(c_14,negated_conjecture,
    ( k2_relat_1(sK4) = k1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_6,plain,
    ( r2_hidden(sK3(k1_relat_1(X0),X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k6_relat_1(k1_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_506,plain,
    ( k6_relat_1(k1_relat_1(X0)) = X0
    | r2_hidden(sK3(k1_relat_1(X0),X0),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1212,plain,
    ( k6_relat_1(k1_relat_1(sK5)) = sK5
    | r2_hidden(sK3(k2_relat_1(sK4),sK5),k2_relat_1(sK4)) = iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_14,c_506])).

cnf(c_16,negated_conjecture,
    ( v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_21,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_15,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_22,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_12,negated_conjecture,
    ( k6_relat_1(k1_relat_1(sK5)) != sK5 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1313,plain,
    ( r2_hidden(sK3(k2_relat_1(sK4),sK5),k2_relat_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1212,c_21,c_22,c_12])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(k4_tarski(sK2(X1,X0),X0),X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_509,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(sK2(X1,X0),X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_10,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_502,plain,
    ( k1_funct_1(X0,X1) = X2
    | r2_hidden(k4_tarski(X1,X2),X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1073,plain,
    ( k1_funct_1(X0,sK2(X0,X1)) = X1
    | r2_hidden(X1,k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_509,c_502])).

cnf(c_1966,plain,
    ( k1_funct_1(sK4,sK2(sK4,sK3(k2_relat_1(sK4),sK5))) = sK3(k2_relat_1(sK4),sK5)
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1313,c_1073])).

cnf(c_18,negated_conjecture,
    ( v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_19,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_17,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_20,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_10410,plain,
    ( k1_funct_1(sK4,sK2(sK4,sK3(k2_relat_1(sK4),sK5))) = sK3(k2_relat_1(sK4),sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1966,c_19,c_20])).

cnf(c_13,negated_conjecture,
    ( k5_relat_1(sK4,sK5) = sK4 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_499,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_11,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_501,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_884,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(sK2(X1,X0),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_509,c_501])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_508,plain,
    ( k1_funct_1(k5_relat_1(X0,X1),X2) = k1_funct_1(X1,k1_funct_1(X0,X2))
    | r2_hidden(X2,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1740,plain,
    ( k1_funct_1(X0,k1_funct_1(X1,sK2(X1,X2))) = k1_funct_1(k5_relat_1(X1,X0),sK2(X1,X2))
    | r2_hidden(X2,k2_relat_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_884,c_508])).

cnf(c_6138,plain,
    ( k1_funct_1(k5_relat_1(sK4,X0),sK2(sK4,sK3(k2_relat_1(sK4),sK5))) = k1_funct_1(X0,k1_funct_1(sK4,sK2(sK4,sK3(k2_relat_1(sK4),sK5))))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1313,c_1740])).

cnf(c_171559,plain,
    ( v1_funct_1(X0) != iProver_top
    | k1_funct_1(k5_relat_1(sK4,X0),sK2(sK4,sK3(k2_relat_1(sK4),sK5))) = k1_funct_1(X0,k1_funct_1(sK4,sK2(sK4,sK3(k2_relat_1(sK4),sK5))))
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6138,c_19,c_20])).

cnf(c_171560,plain,
    ( k1_funct_1(k5_relat_1(sK4,X0),sK2(sK4,sK3(k2_relat_1(sK4),sK5))) = k1_funct_1(X0,k1_funct_1(sK4,sK2(sK4,sK3(k2_relat_1(sK4),sK5))))
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_171559])).

cnf(c_171565,plain,
    ( k1_funct_1(sK5,k1_funct_1(sK4,sK2(sK4,sK3(k2_relat_1(sK4),sK5)))) = k1_funct_1(k5_relat_1(sK4,sK5),sK2(sK4,sK3(k2_relat_1(sK4),sK5)))
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_499,c_171560])).

cnf(c_171655,plain,
    ( k1_funct_1(sK5,k1_funct_1(sK4,sK2(sK4,sK3(k2_relat_1(sK4),sK5)))) = k1_funct_1(k5_relat_1(sK4,sK5),sK2(sK4,sK3(k2_relat_1(sK4),sK5))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_171565,c_22])).

cnf(c_171657,plain,
    ( k1_funct_1(sK5,k1_funct_1(sK4,sK2(sK4,sK3(k2_relat_1(sK4),sK5)))) = k1_funct_1(sK4,sK2(sK4,sK3(k2_relat_1(sK4),sK5))) ),
    inference(superposition,[status(thm)],[c_13,c_171655])).

cnf(c_171898,plain,
    ( k1_funct_1(sK4,sK2(sK4,sK3(k2_relat_1(sK4),sK5))) = k1_funct_1(sK5,sK3(k2_relat_1(sK4),sK5)) ),
    inference(superposition,[status(thm)],[c_10410,c_171657])).

cnf(c_172163,plain,
    ( k1_funct_1(sK5,sK3(k2_relat_1(sK4),sK5)) = sK3(k2_relat_1(sK4),sK5) ),
    inference(superposition,[status(thm)],[c_171898,c_10410])).

cnf(c_198,plain,
    ( X0 != X1
    | sK3(X0,X2) = sK3(X1,X2) ),
    theory(equality)).

cnf(c_716,plain,
    ( sK3(k1_relat_1(X0),X0) = sK3(X1,X0)
    | k1_relat_1(X0) != X1 ),
    inference(instantiation,[status(thm)],[c_198])).

cnf(c_2011,plain,
    ( sK3(k1_relat_1(sK5),sK5) = sK3(k2_relat_1(sK4),sK5)
    | k1_relat_1(sK5) != k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_716])).

cnf(c_749,plain,
    ( X0 != X1
    | k1_relat_1(sK5) != X1
    | k1_relat_1(sK5) = X0 ),
    inference(instantiation,[status(thm)],[c_188])).

cnf(c_1028,plain,
    ( X0 != k1_relat_1(X1)
    | k1_relat_1(sK5) = X0
    | k1_relat_1(sK5) != k1_relat_1(X1) ),
    inference(instantiation,[status(thm)],[c_749])).

cnf(c_1365,plain,
    ( k1_relat_1(sK5) != k1_relat_1(sK5)
    | k1_relat_1(sK5) = k2_relat_1(sK4)
    | k2_relat_1(sK4) != k1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1028])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_funct_1(X0,sK3(k1_relat_1(X0),X0)) != sK3(k1_relat_1(X0),X0)
    | k6_relat_1(k1_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_507,plain,
    ( k1_funct_1(X0,sK3(k1_relat_1(X0),X0)) != sK3(k1_relat_1(X0),X0)
    | k6_relat_1(k1_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1320,plain,
    ( k1_funct_1(sK5,sK3(k2_relat_1(sK4),sK5)) != sK3(k1_relat_1(sK5),sK5)
    | k6_relat_1(k1_relat_1(sK5)) = sK5
    | v1_relat_1(sK5) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_14,c_507])).

cnf(c_187,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_210,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_187])).

cnf(c_194,plain,
    ( X0 != X1
    | k1_relat_1(X0) = k1_relat_1(X1) ),
    theory(equality)).

cnf(c_204,plain,
    ( k1_relat_1(sK5) = k1_relat_1(sK5)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_194])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_187807,c_172163,c_2011,c_1365,c_1320,c_210,c_204,c_12,c_14,c_22,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:22:56 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 55.19/7.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 55.19/7.50  
% 55.19/7.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 55.19/7.50  
% 55.19/7.50  ------  iProver source info
% 55.19/7.50  
% 55.19/7.50  git: date: 2020-06-30 10:37:57 +0100
% 55.19/7.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 55.19/7.50  git: non_committed_changes: false
% 55.19/7.50  git: last_make_outside_of_git: false
% 55.19/7.50  
% 55.19/7.50  ------ 
% 55.19/7.50  ------ Parsing...
% 55.19/7.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 55.19/7.50  
% 55.19/7.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 55.19/7.50  
% 55.19/7.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 55.19/7.50  
% 55.19/7.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 55.19/7.50  ------ Proving...
% 55.19/7.50  ------ Problem Properties 
% 55.19/7.50  
% 55.19/7.50  
% 55.19/7.50  clauses                                 19
% 55.19/7.50  conjectures                             7
% 55.19/7.50  EPR                                     4
% 55.19/7.50  Horn                                    17
% 55.19/7.50  unary                                   7
% 55.19/7.50  binary                                  2
% 55.19/7.50  lits                                    50
% 55.19/7.50  lits eq                                 12
% 55.19/7.50  fd_pure                                 0
% 55.19/7.50  fd_pseudo                               0
% 55.19/7.50  fd_cond                                 0
% 55.19/7.50  fd_pseudo_cond                          3
% 55.19/7.50  AC symbols                              0
% 55.19/7.50  
% 55.19/7.50  ------ Input Options Time Limit: Unbounded
% 55.19/7.50  
% 55.19/7.50  
% 55.19/7.50  ------ 
% 55.19/7.50  Current options:
% 55.19/7.50  ------ 
% 55.19/7.50  
% 55.19/7.50  
% 55.19/7.50  
% 55.19/7.50  
% 55.19/7.50  ------ Proving...
% 55.19/7.50  
% 55.19/7.50  
% 55.19/7.50  % SZS status Theorem for theBenchmark.p
% 55.19/7.50  
% 55.19/7.50  % SZS output start CNFRefutation for theBenchmark.p
% 55.19/7.50  
% 55.19/7.50  fof(f5,conjecture,(
% 55.19/7.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = X0 & k2_relat_1(X0) = k1_relat_1(X1)) => k6_relat_1(k1_relat_1(X1)) = X1)))),
% 55.19/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.19/7.50  
% 55.19/7.50  fof(f6,negated_conjecture,(
% 55.19/7.50    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = X0 & k2_relat_1(X0) = k1_relat_1(X1)) => k6_relat_1(k1_relat_1(X1)) = X1)))),
% 55.19/7.50    inference(negated_conjecture,[],[f5])).
% 55.19/7.50  
% 55.19/7.50  fof(f13,plain,(
% 55.19/7.50    ? [X0] : (? [X1] : ((k6_relat_1(k1_relat_1(X1)) != X1 & (k5_relat_1(X0,X1) = X0 & k2_relat_1(X0) = k1_relat_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 55.19/7.50    inference(ennf_transformation,[],[f6])).
% 55.19/7.50  
% 55.19/7.50  fof(f14,plain,(
% 55.19/7.50    ? [X0] : (? [X1] : (k6_relat_1(k1_relat_1(X1)) != X1 & k5_relat_1(X0,X1) = X0 & k2_relat_1(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 55.19/7.50    inference(flattening,[],[f13])).
% 55.19/7.50  
% 55.19/7.50  fof(f29,plain,(
% 55.19/7.50    ( ! [X0] : (? [X1] : (k6_relat_1(k1_relat_1(X1)) != X1 & k5_relat_1(X0,X1) = X0 & k2_relat_1(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(k1_relat_1(sK5)) != sK5 & k5_relat_1(X0,sK5) = X0 & k2_relat_1(X0) = k1_relat_1(sK5) & v1_funct_1(sK5) & v1_relat_1(sK5))) )),
% 55.19/7.50    introduced(choice_axiom,[])).
% 55.19/7.50  
% 55.19/7.50  fof(f28,plain,(
% 55.19/7.50    ? [X0] : (? [X1] : (k6_relat_1(k1_relat_1(X1)) != X1 & k5_relat_1(X0,X1) = X0 & k2_relat_1(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k6_relat_1(k1_relat_1(X1)) != X1 & k5_relat_1(sK4,X1) = sK4 & k2_relat_1(sK4) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK4) & v1_relat_1(sK4))),
% 55.19/7.50    introduced(choice_axiom,[])).
% 55.19/7.50  
% 55.19/7.50  fof(f30,plain,(
% 55.19/7.50    (k6_relat_1(k1_relat_1(sK5)) != sK5 & k5_relat_1(sK4,sK5) = sK4 & k2_relat_1(sK4) = k1_relat_1(sK5) & v1_funct_1(sK5) & v1_relat_1(sK5)) & v1_funct_1(sK4) & v1_relat_1(sK4)),
% 55.19/7.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f14,f29,f28])).
% 55.19/7.50  
% 55.19/7.50  fof(f47,plain,(
% 55.19/7.50    k2_relat_1(sK4) = k1_relat_1(sK5)),
% 55.19/7.50    inference(cnf_transformation,[],[f30])).
% 55.19/7.50  
% 55.19/7.50  fof(f3,axiom,(
% 55.19/7.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(X0) = X1 <=> (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = X2) & k1_relat_1(X1) = X0)))),
% 55.19/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.19/7.50  
% 55.19/7.50  fof(f9,plain,(
% 55.19/7.50    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 55.19/7.50    inference(ennf_transformation,[],[f3])).
% 55.19/7.50  
% 55.19/7.50  fof(f10,plain,(
% 55.19/7.50    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 55.19/7.50    inference(flattening,[],[f9])).
% 55.19/7.50  
% 55.19/7.50  fof(f21,plain,(
% 55.19/7.50    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0)) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 55.19/7.50    inference(nnf_transformation,[],[f10])).
% 55.19/7.50  
% 55.19/7.50  fof(f22,plain,(
% 55.19/7.50    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 55.19/7.50    inference(flattening,[],[f21])).
% 55.19/7.50  
% 55.19/7.50  fof(f23,plain,(
% 55.19/7.50    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 55.19/7.50    inference(rectify,[],[f22])).
% 55.19/7.50  
% 55.19/7.50  fof(f24,plain,(
% 55.19/7.50    ! [X1,X0] : (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) => (k1_funct_1(X1,sK3(X0,X1)) != sK3(X0,X1) & r2_hidden(sK3(X0,X1),X0)))),
% 55.19/7.50    introduced(choice_axiom,[])).
% 55.19/7.50  
% 55.19/7.50  fof(f25,plain,(
% 55.19/7.50    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (k1_funct_1(X1,sK3(X0,X1)) != sK3(X0,X1) & r2_hidden(sK3(X0,X1),X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 55.19/7.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f24])).
% 55.19/7.50  
% 55.19/7.50  fof(f38,plain,(
% 55.19/7.50    ( ! [X0,X1] : (k6_relat_1(X0) = X1 | r2_hidden(sK3(X0,X1),X0) | k1_relat_1(X1) != X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 55.19/7.50    inference(cnf_transformation,[],[f25])).
% 55.19/7.50  
% 55.19/7.50  fof(f53,plain,(
% 55.19/7.50    ( ! [X1] : (k6_relat_1(k1_relat_1(X1)) = X1 | r2_hidden(sK3(k1_relat_1(X1),X1),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 55.19/7.50    inference(equality_resolution,[],[f38])).
% 55.19/7.50  
% 55.19/7.50  fof(f45,plain,(
% 55.19/7.50    v1_relat_1(sK5)),
% 55.19/7.50    inference(cnf_transformation,[],[f30])).
% 55.19/7.50  
% 55.19/7.50  fof(f46,plain,(
% 55.19/7.50    v1_funct_1(sK5)),
% 55.19/7.50    inference(cnf_transformation,[],[f30])).
% 55.19/7.50  
% 55.19/7.50  fof(f49,plain,(
% 55.19/7.50    k6_relat_1(k1_relat_1(sK5)) != sK5),
% 55.19/7.50    inference(cnf_transformation,[],[f30])).
% 55.19/7.50  
% 55.19/7.50  fof(f1,axiom,(
% 55.19/7.50    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 55.19/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.19/7.50  
% 55.19/7.50  fof(f15,plain,(
% 55.19/7.50    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 55.19/7.50    inference(nnf_transformation,[],[f1])).
% 55.19/7.50  
% 55.19/7.50  fof(f16,plain,(
% 55.19/7.50    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 55.19/7.50    inference(rectify,[],[f15])).
% 55.19/7.50  
% 55.19/7.50  fof(f19,plain,(
% 55.19/7.50    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK2(X0,X5),X5),X0))),
% 55.19/7.50    introduced(choice_axiom,[])).
% 55.19/7.50  
% 55.19/7.50  fof(f18,plain,(
% 55.19/7.50    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) => r2_hidden(k4_tarski(sK1(X0,X1),X2),X0))) )),
% 55.19/7.50    introduced(choice_axiom,[])).
% 55.19/7.50  
% 55.19/7.50  fof(f17,plain,(
% 55.19/7.50    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK0(X0,X1)),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK0(X0,X1)),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 55.19/7.50    introduced(choice_axiom,[])).
% 55.19/7.50  
% 55.19/7.50  fof(f20,plain,(
% 55.19/7.50    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK0(X0,X1)),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r2_hidden(k4_tarski(sK1(X0,X1),sK0(X0,X1)),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK2(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 55.19/7.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f19,f18,f17])).
% 55.19/7.50  
% 55.19/7.50  fof(f31,plain,(
% 55.19/7.50    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK2(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 55.19/7.50    inference(cnf_transformation,[],[f20])).
% 55.19/7.50  
% 55.19/7.50  fof(f51,plain,(
% 55.19/7.50    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK2(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 55.19/7.50    inference(equality_resolution,[],[f31])).
% 55.19/7.50  
% 55.19/7.50  fof(f4,axiom,(
% 55.19/7.50    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 55.19/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.19/7.50  
% 55.19/7.50  fof(f11,plain,(
% 55.19/7.50    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 55.19/7.50    inference(ennf_transformation,[],[f4])).
% 55.19/7.50  
% 55.19/7.50  fof(f12,plain,(
% 55.19/7.50    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 55.19/7.50    inference(flattening,[],[f11])).
% 55.19/7.50  
% 55.19/7.50  fof(f26,plain,(
% 55.19/7.50    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 55.19/7.50    inference(nnf_transformation,[],[f12])).
% 55.19/7.50  
% 55.19/7.50  fof(f27,plain,(
% 55.19/7.50    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 55.19/7.50    inference(flattening,[],[f26])).
% 55.19/7.50  
% 55.19/7.50  fof(f41,plain,(
% 55.19/7.50    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 55.19/7.50    inference(cnf_transformation,[],[f27])).
% 55.19/7.50  
% 55.19/7.50  fof(f43,plain,(
% 55.19/7.50    v1_relat_1(sK4)),
% 55.19/7.50    inference(cnf_transformation,[],[f30])).
% 55.19/7.50  
% 55.19/7.50  fof(f44,plain,(
% 55.19/7.50    v1_funct_1(sK4)),
% 55.19/7.50    inference(cnf_transformation,[],[f30])).
% 55.19/7.50  
% 55.19/7.50  fof(f48,plain,(
% 55.19/7.50    k5_relat_1(sK4,sK5) = sK4),
% 55.19/7.50    inference(cnf_transformation,[],[f30])).
% 55.19/7.50  
% 55.19/7.50  fof(f40,plain,(
% 55.19/7.50    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 55.19/7.50    inference(cnf_transformation,[],[f27])).
% 55.19/7.50  
% 55.19/7.50  fof(f2,axiom,(
% 55.19/7.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0))))),
% 55.19/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.19/7.50  
% 55.19/7.50  fof(f7,plain,(
% 55.19/7.50    ! [X0,X1] : (! [X2] : ((k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 55.19/7.50    inference(ennf_transformation,[],[f2])).
% 55.19/7.50  
% 55.19/7.50  fof(f8,plain,(
% 55.19/7.50    ! [X0,X1] : (! [X2] : (k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 55.19/7.50    inference(flattening,[],[f7])).
% 55.19/7.50  
% 55.19/7.50  fof(f35,plain,(
% 55.19/7.50    ( ! [X2,X0,X1] : (k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 55.19/7.50    inference(cnf_transformation,[],[f8])).
% 55.19/7.50  
% 55.19/7.50  fof(f39,plain,(
% 55.19/7.50    ( ! [X0,X1] : (k6_relat_1(X0) = X1 | k1_funct_1(X1,sK3(X0,X1)) != sK3(X0,X1) | k1_relat_1(X1) != X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 55.19/7.50    inference(cnf_transformation,[],[f25])).
% 55.19/7.50  
% 55.19/7.50  fof(f52,plain,(
% 55.19/7.50    ( ! [X1] : (k6_relat_1(k1_relat_1(X1)) = X1 | k1_funct_1(X1,sK3(k1_relat_1(X1),X1)) != sK3(k1_relat_1(X1),X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 55.19/7.50    inference(equality_resolution,[],[f39])).
% 55.19/7.50  
% 55.19/7.50  cnf(c_188,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 55.19/7.50  
% 55.19/7.50  cnf(c_91111,plain,
% 55.19/7.50      ( X0 != X1
% 55.19/7.50      | X0 = sK3(k1_relat_1(X2),X2)
% 55.19/7.50      | sK3(k1_relat_1(X2),X2) != X1 ),
% 55.19/7.50      inference(instantiation,[status(thm)],[c_188]) ).
% 55.19/7.50  
% 55.19/7.50  cnf(c_91254,plain,
% 55.19/7.50      ( X0 != sK3(X1,X2)
% 55.19/7.50      | X0 = sK3(k1_relat_1(X2),X2)
% 55.19/7.50      | sK3(k1_relat_1(X2),X2) != sK3(X1,X2) ),
% 55.19/7.50      inference(instantiation,[status(thm)],[c_91111]) ).
% 55.19/7.50  
% 55.19/7.50  cnf(c_93120,plain,
% 55.19/7.50      ( X0 = sK3(k1_relat_1(sK5),sK5)
% 55.19/7.50      | X0 != sK3(k2_relat_1(sK4),sK5)
% 55.19/7.50      | sK3(k1_relat_1(sK5),sK5) != sK3(k2_relat_1(sK4),sK5) ),
% 55.19/7.50      inference(instantiation,[status(thm)],[c_91254]) ).
% 55.19/7.50  
% 55.19/7.50  cnf(c_187805,plain,
% 55.19/7.50      ( sK3(k1_relat_1(sK5),sK5) != sK3(k2_relat_1(sK4),sK5)
% 55.19/7.50      | k1_funct_1(X0,sK3(k2_relat_1(sK4),sK5)) = sK3(k1_relat_1(sK5),sK5)
% 55.19/7.50      | k1_funct_1(X0,sK3(k2_relat_1(sK4),sK5)) != sK3(k2_relat_1(sK4),sK5) ),
% 55.19/7.50      inference(instantiation,[status(thm)],[c_93120]) ).
% 55.19/7.50  
% 55.19/7.50  cnf(c_187807,plain,
% 55.19/7.50      ( sK3(k1_relat_1(sK5),sK5) != sK3(k2_relat_1(sK4),sK5)
% 55.19/7.50      | k1_funct_1(sK5,sK3(k2_relat_1(sK4),sK5)) = sK3(k1_relat_1(sK5),sK5)
% 55.19/7.50      | k1_funct_1(sK5,sK3(k2_relat_1(sK4),sK5)) != sK3(k2_relat_1(sK4),sK5) ),
% 55.19/7.50      inference(instantiation,[status(thm)],[c_187805]) ).
% 55.19/7.50  
% 55.19/7.50  cnf(c_14,negated_conjecture,
% 55.19/7.50      ( k2_relat_1(sK4) = k1_relat_1(sK5) ),
% 55.19/7.50      inference(cnf_transformation,[],[f47]) ).
% 55.19/7.50  
% 55.19/7.50  cnf(c_6,plain,
% 55.19/7.50      ( r2_hidden(sK3(k1_relat_1(X0),X0),k1_relat_1(X0))
% 55.19/7.50      | ~ v1_relat_1(X0)
% 55.19/7.50      | ~ v1_funct_1(X0)
% 55.19/7.50      | k6_relat_1(k1_relat_1(X0)) = X0 ),
% 55.19/7.50      inference(cnf_transformation,[],[f53]) ).
% 55.19/7.50  
% 55.19/7.50  cnf(c_506,plain,
% 55.19/7.50      ( k6_relat_1(k1_relat_1(X0)) = X0
% 55.19/7.50      | r2_hidden(sK3(k1_relat_1(X0),X0),k1_relat_1(X0)) = iProver_top
% 55.19/7.50      | v1_relat_1(X0) != iProver_top
% 55.19/7.50      | v1_funct_1(X0) != iProver_top ),
% 55.19/7.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 55.19/7.50  
% 55.19/7.50  cnf(c_1212,plain,
% 55.19/7.50      ( k6_relat_1(k1_relat_1(sK5)) = sK5
% 55.19/7.50      | r2_hidden(sK3(k2_relat_1(sK4),sK5),k2_relat_1(sK4)) = iProver_top
% 55.19/7.50      | v1_relat_1(sK5) != iProver_top
% 55.19/7.50      | v1_funct_1(sK5) != iProver_top ),
% 55.19/7.50      inference(superposition,[status(thm)],[c_14,c_506]) ).
% 55.19/7.50  
% 55.19/7.50  cnf(c_16,negated_conjecture,
% 55.19/7.50      ( v1_relat_1(sK5) ),
% 55.19/7.50      inference(cnf_transformation,[],[f45]) ).
% 55.19/7.50  
% 55.19/7.50  cnf(c_21,plain,
% 55.19/7.50      ( v1_relat_1(sK5) = iProver_top ),
% 55.19/7.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 55.19/7.50  
% 55.19/7.50  cnf(c_15,negated_conjecture,
% 55.19/7.50      ( v1_funct_1(sK5) ),
% 55.19/7.50      inference(cnf_transformation,[],[f46]) ).
% 55.19/7.50  
% 55.19/7.50  cnf(c_22,plain,
% 55.19/7.50      ( v1_funct_1(sK5) = iProver_top ),
% 55.19/7.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 55.19/7.50  
% 55.19/7.50  cnf(c_12,negated_conjecture,
% 55.19/7.50      ( k6_relat_1(k1_relat_1(sK5)) != sK5 ),
% 55.19/7.50      inference(cnf_transformation,[],[f49]) ).
% 55.19/7.50  
% 55.19/7.50  cnf(c_1313,plain,
% 55.19/7.50      ( r2_hidden(sK3(k2_relat_1(sK4),sK5),k2_relat_1(sK4)) = iProver_top ),
% 55.19/7.50      inference(global_propositional_subsumption,
% 55.19/7.50                [status(thm)],
% 55.19/7.50                [c_1212,c_21,c_22,c_12]) ).
% 55.19/7.50  
% 55.19/7.50  cnf(c_3,plain,
% 55.19/7.50      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 55.19/7.50      | r2_hidden(k4_tarski(sK2(X1,X0),X0),X1) ),
% 55.19/7.50      inference(cnf_transformation,[],[f51]) ).
% 55.19/7.50  
% 55.19/7.50  cnf(c_509,plain,
% 55.19/7.50      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 55.19/7.50      | r2_hidden(k4_tarski(sK2(X1,X0),X0),X1) = iProver_top ),
% 55.19/7.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 55.19/7.50  
% 55.19/7.50  cnf(c_10,plain,
% 55.19/7.50      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 55.19/7.50      | ~ v1_relat_1(X2)
% 55.19/7.50      | ~ v1_funct_1(X2)
% 55.19/7.50      | k1_funct_1(X2,X0) = X1 ),
% 55.19/7.50      inference(cnf_transformation,[],[f41]) ).
% 55.19/7.50  
% 55.19/7.50  cnf(c_502,plain,
% 55.19/7.50      ( k1_funct_1(X0,X1) = X2
% 55.19/7.50      | r2_hidden(k4_tarski(X1,X2),X0) != iProver_top
% 55.19/7.50      | v1_relat_1(X0) != iProver_top
% 55.19/7.50      | v1_funct_1(X0) != iProver_top ),
% 55.19/7.50      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 55.19/7.50  
% 55.19/7.50  cnf(c_1073,plain,
% 55.19/7.50      ( k1_funct_1(X0,sK2(X0,X1)) = X1
% 55.19/7.50      | r2_hidden(X1,k2_relat_1(X0)) != iProver_top
% 55.19/7.50      | v1_relat_1(X0) != iProver_top
% 55.19/7.50      | v1_funct_1(X0) != iProver_top ),
% 55.19/7.50      inference(superposition,[status(thm)],[c_509,c_502]) ).
% 55.19/7.50  
% 55.19/7.50  cnf(c_1966,plain,
% 55.19/7.50      ( k1_funct_1(sK4,sK2(sK4,sK3(k2_relat_1(sK4),sK5))) = sK3(k2_relat_1(sK4),sK5)
% 55.19/7.50      | v1_relat_1(sK4) != iProver_top
% 55.19/7.50      | v1_funct_1(sK4) != iProver_top ),
% 55.19/7.50      inference(superposition,[status(thm)],[c_1313,c_1073]) ).
% 55.19/7.50  
% 55.19/7.50  cnf(c_18,negated_conjecture,
% 55.19/7.50      ( v1_relat_1(sK4) ),
% 55.19/7.50      inference(cnf_transformation,[],[f43]) ).
% 55.19/7.50  
% 55.19/7.50  cnf(c_19,plain,
% 55.19/7.50      ( v1_relat_1(sK4) = iProver_top ),
% 55.19/7.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 55.19/7.50  
% 55.19/7.50  cnf(c_17,negated_conjecture,
% 55.19/7.50      ( v1_funct_1(sK4) ),
% 55.19/7.50      inference(cnf_transformation,[],[f44]) ).
% 55.19/7.50  
% 55.19/7.50  cnf(c_20,plain,
% 55.19/7.50      ( v1_funct_1(sK4) = iProver_top ),
% 55.19/7.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 55.19/7.50  
% 55.19/7.50  cnf(c_10410,plain,
% 55.19/7.50      ( k1_funct_1(sK4,sK2(sK4,sK3(k2_relat_1(sK4),sK5))) = sK3(k2_relat_1(sK4),sK5) ),
% 55.19/7.50      inference(global_propositional_subsumption,
% 55.19/7.50                [status(thm)],
% 55.19/7.50                [c_1966,c_19,c_20]) ).
% 55.19/7.50  
% 55.19/7.50  cnf(c_13,negated_conjecture,
% 55.19/7.50      ( k5_relat_1(sK4,sK5) = sK4 ),
% 55.19/7.50      inference(cnf_transformation,[],[f48]) ).
% 55.19/7.50  
% 55.19/7.50  cnf(c_499,plain,
% 55.19/7.50      ( v1_relat_1(sK5) = iProver_top ),
% 55.19/7.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 55.19/7.50  
% 55.19/7.50  cnf(c_11,plain,
% 55.19/7.50      ( r2_hidden(X0,k1_relat_1(X1))
% 55.19/7.50      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 55.19/7.50      | ~ v1_relat_1(X1)
% 55.19/7.50      | ~ v1_funct_1(X1) ),
% 55.19/7.50      inference(cnf_transformation,[],[f40]) ).
% 55.19/7.50  
% 55.19/7.50  cnf(c_501,plain,
% 55.19/7.50      ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
% 55.19/7.50      | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top
% 55.19/7.50      | v1_relat_1(X1) != iProver_top
% 55.19/7.50      | v1_funct_1(X1) != iProver_top ),
% 55.19/7.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 55.19/7.50  
% 55.19/7.50  cnf(c_884,plain,
% 55.19/7.50      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 55.19/7.50      | r2_hidden(sK2(X1,X0),k1_relat_1(X1)) = iProver_top
% 55.19/7.50      | v1_relat_1(X1) != iProver_top
% 55.19/7.50      | v1_funct_1(X1) != iProver_top ),
% 55.19/7.50      inference(superposition,[status(thm)],[c_509,c_501]) ).
% 55.19/7.50  
% 55.19/7.50  cnf(c_4,plain,
% 55.19/7.50      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 55.19/7.50      | ~ v1_relat_1(X2)
% 55.19/7.50      | ~ v1_relat_1(X1)
% 55.19/7.50      | ~ v1_funct_1(X2)
% 55.19/7.50      | ~ v1_funct_1(X1)
% 55.19/7.50      | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ),
% 55.19/7.50      inference(cnf_transformation,[],[f35]) ).
% 55.19/7.50  
% 55.19/7.50  cnf(c_508,plain,
% 55.19/7.50      ( k1_funct_1(k5_relat_1(X0,X1),X2) = k1_funct_1(X1,k1_funct_1(X0,X2))
% 55.19/7.50      | r2_hidden(X2,k1_relat_1(X0)) != iProver_top
% 55.19/7.50      | v1_relat_1(X0) != iProver_top
% 55.19/7.50      | v1_relat_1(X1) != iProver_top
% 55.19/7.50      | v1_funct_1(X0) != iProver_top
% 55.19/7.50      | v1_funct_1(X1) != iProver_top ),
% 55.19/7.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 55.19/7.50  
% 55.19/7.50  cnf(c_1740,plain,
% 55.19/7.50      ( k1_funct_1(X0,k1_funct_1(X1,sK2(X1,X2))) = k1_funct_1(k5_relat_1(X1,X0),sK2(X1,X2))
% 55.19/7.50      | r2_hidden(X2,k2_relat_1(X1)) != iProver_top
% 55.19/7.50      | v1_relat_1(X1) != iProver_top
% 55.19/7.50      | v1_relat_1(X0) != iProver_top
% 55.19/7.50      | v1_funct_1(X1) != iProver_top
% 55.19/7.50      | v1_funct_1(X0) != iProver_top ),
% 55.19/7.50      inference(superposition,[status(thm)],[c_884,c_508]) ).
% 55.19/7.50  
% 55.19/7.50  cnf(c_6138,plain,
% 55.19/7.50      ( k1_funct_1(k5_relat_1(sK4,X0),sK2(sK4,sK3(k2_relat_1(sK4),sK5))) = k1_funct_1(X0,k1_funct_1(sK4,sK2(sK4,sK3(k2_relat_1(sK4),sK5))))
% 55.19/7.50      | v1_relat_1(X0) != iProver_top
% 55.19/7.50      | v1_relat_1(sK4) != iProver_top
% 55.19/7.50      | v1_funct_1(X0) != iProver_top
% 55.19/7.50      | v1_funct_1(sK4) != iProver_top ),
% 55.19/7.50      inference(superposition,[status(thm)],[c_1313,c_1740]) ).
% 55.19/7.50  
% 55.19/7.50  cnf(c_171559,plain,
% 55.19/7.50      ( v1_funct_1(X0) != iProver_top
% 55.19/7.50      | k1_funct_1(k5_relat_1(sK4,X0),sK2(sK4,sK3(k2_relat_1(sK4),sK5))) = k1_funct_1(X0,k1_funct_1(sK4,sK2(sK4,sK3(k2_relat_1(sK4),sK5))))
% 55.19/7.50      | v1_relat_1(X0) != iProver_top ),
% 55.19/7.50      inference(global_propositional_subsumption,
% 55.19/7.50                [status(thm)],
% 55.19/7.50                [c_6138,c_19,c_20]) ).
% 55.19/7.50  
% 55.19/7.50  cnf(c_171560,plain,
% 55.19/7.50      ( k1_funct_1(k5_relat_1(sK4,X0),sK2(sK4,sK3(k2_relat_1(sK4),sK5))) = k1_funct_1(X0,k1_funct_1(sK4,sK2(sK4,sK3(k2_relat_1(sK4),sK5))))
% 55.19/7.50      | v1_relat_1(X0) != iProver_top
% 55.19/7.50      | v1_funct_1(X0) != iProver_top ),
% 55.19/7.50      inference(renaming,[status(thm)],[c_171559]) ).
% 55.19/7.50  
% 55.19/7.50  cnf(c_171565,plain,
% 55.19/7.50      ( k1_funct_1(sK5,k1_funct_1(sK4,sK2(sK4,sK3(k2_relat_1(sK4),sK5)))) = k1_funct_1(k5_relat_1(sK4,sK5),sK2(sK4,sK3(k2_relat_1(sK4),sK5)))
% 55.19/7.50      | v1_funct_1(sK5) != iProver_top ),
% 55.19/7.50      inference(superposition,[status(thm)],[c_499,c_171560]) ).
% 55.19/7.50  
% 55.19/7.50  cnf(c_171655,plain,
% 55.19/7.50      ( k1_funct_1(sK5,k1_funct_1(sK4,sK2(sK4,sK3(k2_relat_1(sK4),sK5)))) = k1_funct_1(k5_relat_1(sK4,sK5),sK2(sK4,sK3(k2_relat_1(sK4),sK5))) ),
% 55.19/7.50      inference(global_propositional_subsumption,
% 55.19/7.50                [status(thm)],
% 55.19/7.50                [c_171565,c_22]) ).
% 55.19/7.50  
% 55.19/7.50  cnf(c_171657,plain,
% 55.19/7.50      ( k1_funct_1(sK5,k1_funct_1(sK4,sK2(sK4,sK3(k2_relat_1(sK4),sK5)))) = k1_funct_1(sK4,sK2(sK4,sK3(k2_relat_1(sK4),sK5))) ),
% 55.19/7.50      inference(superposition,[status(thm)],[c_13,c_171655]) ).
% 55.19/7.50  
% 55.19/7.50  cnf(c_171898,plain,
% 55.19/7.50      ( k1_funct_1(sK4,sK2(sK4,sK3(k2_relat_1(sK4),sK5))) = k1_funct_1(sK5,sK3(k2_relat_1(sK4),sK5)) ),
% 55.19/7.50      inference(superposition,[status(thm)],[c_10410,c_171657]) ).
% 55.19/7.50  
% 55.19/7.50  cnf(c_172163,plain,
% 55.19/7.50      ( k1_funct_1(sK5,sK3(k2_relat_1(sK4),sK5)) = sK3(k2_relat_1(sK4),sK5) ),
% 55.19/7.50      inference(superposition,[status(thm)],[c_171898,c_10410]) ).
% 55.19/7.50  
% 55.19/7.50  cnf(c_198,plain,
% 55.19/7.50      ( X0 != X1 | sK3(X0,X2) = sK3(X1,X2) ),
% 55.19/7.50      theory(equality) ).
% 55.19/7.50  
% 55.19/7.50  cnf(c_716,plain,
% 55.19/7.50      ( sK3(k1_relat_1(X0),X0) = sK3(X1,X0) | k1_relat_1(X0) != X1 ),
% 55.19/7.50      inference(instantiation,[status(thm)],[c_198]) ).
% 55.19/7.50  
% 55.19/7.50  cnf(c_2011,plain,
% 55.19/7.50      ( sK3(k1_relat_1(sK5),sK5) = sK3(k2_relat_1(sK4),sK5)
% 55.19/7.50      | k1_relat_1(sK5) != k2_relat_1(sK4) ),
% 55.19/7.50      inference(instantiation,[status(thm)],[c_716]) ).
% 55.19/7.50  
% 55.19/7.50  cnf(c_749,plain,
% 55.19/7.50      ( X0 != X1 | k1_relat_1(sK5) != X1 | k1_relat_1(sK5) = X0 ),
% 55.19/7.50      inference(instantiation,[status(thm)],[c_188]) ).
% 55.19/7.50  
% 55.19/7.50  cnf(c_1028,plain,
% 55.19/7.50      ( X0 != k1_relat_1(X1)
% 55.19/7.50      | k1_relat_1(sK5) = X0
% 55.19/7.50      | k1_relat_1(sK5) != k1_relat_1(X1) ),
% 55.19/7.50      inference(instantiation,[status(thm)],[c_749]) ).
% 55.19/7.50  
% 55.19/7.50  cnf(c_1365,plain,
% 55.19/7.50      ( k1_relat_1(sK5) != k1_relat_1(sK5)
% 55.19/7.50      | k1_relat_1(sK5) = k2_relat_1(sK4)
% 55.19/7.50      | k2_relat_1(sK4) != k1_relat_1(sK5) ),
% 55.19/7.50      inference(instantiation,[status(thm)],[c_1028]) ).
% 55.19/7.50  
% 55.19/7.50  cnf(c_5,plain,
% 55.19/7.50      ( ~ v1_relat_1(X0)
% 55.19/7.50      | ~ v1_funct_1(X0)
% 55.19/7.50      | k1_funct_1(X0,sK3(k1_relat_1(X0),X0)) != sK3(k1_relat_1(X0),X0)
% 55.19/7.50      | k6_relat_1(k1_relat_1(X0)) = X0 ),
% 55.19/7.50      inference(cnf_transformation,[],[f52]) ).
% 55.19/7.50  
% 55.19/7.50  cnf(c_507,plain,
% 55.19/7.50      ( k1_funct_1(X0,sK3(k1_relat_1(X0),X0)) != sK3(k1_relat_1(X0),X0)
% 55.19/7.50      | k6_relat_1(k1_relat_1(X0)) = X0
% 55.19/7.50      | v1_relat_1(X0) != iProver_top
% 55.19/7.50      | v1_funct_1(X0) != iProver_top ),
% 55.19/7.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 55.19/7.50  
% 55.19/7.50  cnf(c_1320,plain,
% 55.19/7.50      ( k1_funct_1(sK5,sK3(k2_relat_1(sK4),sK5)) != sK3(k1_relat_1(sK5),sK5)
% 55.19/7.50      | k6_relat_1(k1_relat_1(sK5)) = sK5
% 55.19/7.50      | v1_relat_1(sK5) != iProver_top
% 55.19/7.50      | v1_funct_1(sK5) != iProver_top ),
% 55.19/7.50      inference(superposition,[status(thm)],[c_14,c_507]) ).
% 55.19/7.50  
% 55.19/7.50  cnf(c_187,plain,( X0 = X0 ),theory(equality) ).
% 55.19/7.50  
% 55.19/7.50  cnf(c_210,plain,
% 55.19/7.50      ( sK5 = sK5 ),
% 55.19/7.50      inference(instantiation,[status(thm)],[c_187]) ).
% 55.19/7.50  
% 55.19/7.50  cnf(c_194,plain,
% 55.19/7.50      ( X0 != X1 | k1_relat_1(X0) = k1_relat_1(X1) ),
% 55.19/7.50      theory(equality) ).
% 55.19/7.50  
% 55.19/7.50  cnf(c_204,plain,
% 55.19/7.50      ( k1_relat_1(sK5) = k1_relat_1(sK5) | sK5 != sK5 ),
% 55.19/7.50      inference(instantiation,[status(thm)],[c_194]) ).
% 55.19/7.50  
% 55.19/7.50  cnf(contradiction,plain,
% 55.19/7.50      ( $false ),
% 55.19/7.50      inference(minisat,
% 55.19/7.50                [status(thm)],
% 55.19/7.50                [c_187807,c_172163,c_2011,c_1365,c_1320,c_210,c_204,c_12,
% 55.19/7.50                 c_14,c_22,c_21]) ).
% 55.19/7.50  
% 55.19/7.50  
% 55.19/7.50  % SZS output end CNFRefutation for theBenchmark.p
% 55.19/7.50  
% 55.19/7.50  ------                               Statistics
% 55.19/7.50  
% 55.19/7.50  ------ Selected
% 55.19/7.50  
% 55.19/7.50  total_time:                             6.939
% 55.19/7.50  
%------------------------------------------------------------------------------
