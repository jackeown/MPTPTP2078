%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0939+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:28 EST 2020

% Result     : Theorem 1.06s
% Output     : CNFRefutation 1.06s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 188 expanded)
%              Number of clauses        :   59 (  72 expanded)
%              Number of leaves         :   14 (  36 expanded)
%              Depth                    :   17
%              Number of atoms          :  445 ( 939 expanded)
%              Number of equality atoms :   88 ( 164 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   17 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => v3_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_ordinal1(X1)
          | ~ m1_subset_1(X1,X0) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
      | ~ m1_subset_1(X1,X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X1,X0)
        | r1_ordinal1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) ) )
          & k3_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X2,X3] :
                ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r1_tarski(X2,X3) )
                  & ( r1_tarski(X2,X3)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
                | ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X2,X3] :
                ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r1_tarski(X2,X3) )
                  & ( r1_tarski(X2,X3)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
                | ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X4,X5] :
                ( ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r1_tarski(X4,X5) )
                  & ( r1_tarski(X4,X5)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r1_tarski(X2,X3)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r1_tarski(X2,X3)
            | r2_hidden(k4_tarski(X2,X3),X1) )
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
     => ( ( ~ r1_tarski(sK0(X0,X1),sK1(X0,X1))
          | ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) )
        & ( r1_tarski(sK0(X0,X1),sK1(X0,X1))
          | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) )
        & r2_hidden(sK1(X0,X1),X0)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ( ( ~ r1_tarski(sK0(X0,X1),sK1(X0,X1))
              | ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) )
            & ( r1_tarski(sK0(X0,X1),sK1(X0,X1))
              | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) )
            & r2_hidden(sK1(X0,X1),X0)
            & r2_hidden(sK0(X0,X1),X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X4,X5] :
                ( ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r1_tarski(X4,X5) )
                  & ( r1_tarski(X4,X5)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f26])).

fof(f41,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r1_tarski(X4,X5)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f62,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0))
      | ~ r1_tarski(X4,X5)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f41])).

fof(f6,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r6_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ~ ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                & ~ r2_hidden(k4_tarski(X2,X3),X0)
                & X2 != X3
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r6_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(k4_tarski(X2,X3),X0)
              | X2 = X3
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r6_relat_2(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                & ~ r2_hidden(k4_tarski(X2,X3),X0)
                & X2 != X3
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) )
          & ( ! [X2,X3] :
                ( r2_hidden(k4_tarski(X3,X2),X0)
                | r2_hidden(k4_tarski(X2,X3),X0)
                | X2 = X3
                | ~ r2_hidden(X3,X1)
                | ~ r2_hidden(X2,X1) )
            | ~ r6_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r6_relat_2(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                & ~ r2_hidden(k4_tarski(X2,X3),X0)
                & X2 != X3
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X5,X4),X0)
                | r2_hidden(k4_tarski(X4,X5),X0)
                | X4 = X5
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X1) )
            | ~ r6_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X3,X2),X0)
          & ~ r2_hidden(k4_tarski(X2,X3),X0)
          & X2 != X3
          & r2_hidden(X3,X1)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0)
        & ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
        & sK2(X0,X1) != sK3(X0,X1)
        & r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r6_relat_2(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0)
              & ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
              & sK2(X0,X1) != sK3(X0,X1)
              & r2_hidden(sK3(X0,X1),X1)
              & r2_hidden(sK2(X0,X1),X1) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X5,X4),X0)
                | r2_hidden(k4_tarski(X4,X5),X0)
                | X4 = X5
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X1) )
            | ~ r6_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f29,f30])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r6_relat_2(X0,X1)
      | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v6_relat_2(X0)
      <=> r6_relat_2(X0,k3_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ( v6_relat_2(X0)
      <=> r6_relat_2(X0,k3_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f22,plain,(
    ! [X0] :
      ( ( ( v6_relat_2(X0)
          | ~ r6_relat_2(X0,k3_relat_1(X0)) )
        & ( r6_relat_2(X0,k3_relat_1(X0))
          | ~ v6_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f38,plain,(
    ! [X0] :
      ( v6_relat_2(X0)
      | ~ r6_relat_2(X0,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f9,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v6_relat_2(k1_wellord2(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => v6_relat_2(k1_wellord2(X0)) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f21,plain,(
    ? [X0] :
      ( ~ v6_relat_2(k1_wellord2(X0))
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f33,plain,
    ( ? [X0] :
        ( ~ v6_relat_2(k1_wellord2(X0))
        & v3_ordinal1(X0) )
   => ( ~ v6_relat_2(k1_wellord2(sK4))
      & v3_ordinal1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ~ v6_relat_2(k1_wellord2(sK4))
    & v3_ordinal1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f33])).

fof(f57,plain,(
    ~ v6_relat_2(k1_wellord2(sK4)) ),
    inference(cnf_transformation,[],[f34])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f64,plain,(
    ! [X0] :
      ( k3_relat_1(k1_wellord2(X0)) = X0
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r6_relat_2(X0,X1)
      | ~ r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r6_relat_2(X0,X1)
      | r2_hidden(sK3(X0,X1),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r6_relat_2(X0,X1)
      | r2_hidden(sK2(X0,X1),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f56,plain,(
    v3_ordinal1(sK4) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ v3_ordinal1(X1)
    | v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_261,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1)
    | v3_ordinal1(X0) ),
    inference(resolution,[status(thm)],[c_20,c_0])).

cnf(c_2960,plain,
    ( ~ r2_hidden(sK3(k1_wellord2(X0),X1),X2)
    | ~ v3_ordinal1(X2)
    | v3_ordinal1(sK3(k1_wellord2(X0),X1)) ),
    inference(instantiation,[status(thm)],[c_261])).

cnf(c_2962,plain,
    ( ~ r2_hidden(sK3(k1_wellord2(sK4),sK4),sK4)
    | v3_ordinal1(sK3(k1_wellord2(sK4),sK4))
    | ~ v3_ordinal1(sK4) ),
    inference(instantiation,[status(thm)],[c_2960])).

cnf(c_1,plain,
    ( r1_ordinal1(X0,X1)
    | r1_ordinal1(X1,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1885,plain,
    ( r1_ordinal1(X0,X1) = iProver_top
    | r1_ordinal1(X1,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_19,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_ordinal1(X0,X1)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1883,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_ordinal1(X0,X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2195,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_ordinal1(X1,X0) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1885,c_1883])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | r2_hidden(k4_tarski(X2,X0),k1_wellord2(X1))
    | ~ r1_tarski(X2,X0)
    | ~ v1_relat_1(k1_wellord2(X1)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_17,plain,
    ( v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_425,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | r2_hidden(k4_tarski(X0,X2),k1_wellord2(X1))
    | ~ r1_tarski(X0,X2)
    | k1_wellord2(X3) != k1_wellord2(X1) ),
    inference(resolution_lifted,[status(thm)],[c_8,c_17])).

cnf(c_1869,plain,
    ( k1_wellord2(X0) != k1_wellord2(X1)
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(X3,X1) != iProver_top
    | r2_hidden(k4_tarski(X2,X3),k1_wellord2(X1)) = iProver_top
    | r1_tarski(X2,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_425])).

cnf(c_2455,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(k4_tarski(X0,X2),k1_wellord2(X1)) = iProver_top
    | r1_tarski(X0,X2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1869])).

cnf(c_12,plain,
    ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
    | r6_relat_2(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_327,plain,
    ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
    | r6_relat_2(X0,X1)
    | k1_wellord2(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_17])).

cnf(c_328,plain,
    ( ~ r2_hidden(k4_tarski(sK2(k1_wellord2(X0),X1),sK3(k1_wellord2(X0),X1)),k1_wellord2(X0))
    | r6_relat_2(k1_wellord2(X0),X1) ),
    inference(unflattening,[status(thm)],[c_327])).

cnf(c_1876,plain,
    ( r2_hidden(k4_tarski(sK2(k1_wellord2(X0),X1),sK3(k1_wellord2(X0),X1)),k1_wellord2(X0)) != iProver_top
    | r6_relat_2(k1_wellord2(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_328])).

cnf(c_2617,plain,
    ( r2_hidden(sK2(k1_wellord2(X0),X1),X0) != iProver_top
    | r2_hidden(sK3(k1_wellord2(X0),X1),X0) != iProver_top
    | r1_tarski(sK2(k1_wellord2(X0),X1),sK3(k1_wellord2(X0),X1)) != iProver_top
    | r6_relat_2(k1_wellord2(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2455,c_1876])).

cnf(c_2916,plain,
    ( r2_hidden(sK2(k1_wellord2(X0),X1),X0) != iProver_top
    | r2_hidden(sK3(k1_wellord2(X0),X1),X0) != iProver_top
    | r6_relat_2(k1_wellord2(X0),X1) = iProver_top
    | r1_ordinal1(sK3(k1_wellord2(X0),X1),sK2(k1_wellord2(X0),X1)) = iProver_top
    | v3_ordinal1(sK2(k1_wellord2(X0),X1)) != iProver_top
    | v3_ordinal1(sK3(k1_wellord2(X0),X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2195,c_2617])).

cnf(c_2917,plain,
    ( ~ r2_hidden(sK2(k1_wellord2(X0),X1),X0)
    | ~ r2_hidden(sK3(k1_wellord2(X0),X1),X0)
    | r6_relat_2(k1_wellord2(X0),X1)
    | r1_ordinal1(sK3(k1_wellord2(X0),X1),sK2(k1_wellord2(X0),X1))
    | ~ v3_ordinal1(sK2(k1_wellord2(X0),X1))
    | ~ v3_ordinal1(sK3(k1_wellord2(X0),X1)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2916])).

cnf(c_2919,plain,
    ( ~ r2_hidden(sK2(k1_wellord2(sK4),sK4),sK4)
    | ~ r2_hidden(sK3(k1_wellord2(sK4),sK4),sK4)
    | r6_relat_2(k1_wellord2(sK4),sK4)
    | r1_ordinal1(sK3(k1_wellord2(sK4),sK4),sK2(k1_wellord2(sK4),sK4))
    | ~ v3_ordinal1(sK2(k1_wellord2(sK4),sK4))
    | ~ v3_ordinal1(sK3(k1_wellord2(sK4),sK4)) ),
    inference(instantiation,[status(thm)],[c_2917])).

cnf(c_2878,plain,
    ( ~ r2_hidden(sK2(k1_wellord2(X0),X1),X2)
    | ~ v3_ordinal1(X2)
    | v3_ordinal1(sK2(k1_wellord2(X0),X1)) ),
    inference(instantiation,[status(thm)],[c_261])).

cnf(c_2880,plain,
    ( ~ r2_hidden(sK2(k1_wellord2(sK4),sK4),sK4)
    | v3_ordinal1(sK2(k1_wellord2(sK4),sK4))
    | ~ v3_ordinal1(sK4) ),
    inference(instantiation,[status(thm)],[c_2878])).

cnf(c_2424,plain,
    ( r1_tarski(sK3(k1_wellord2(X0),X1),sK2(k1_wellord2(X2),X1))
    | ~ r1_ordinal1(sK3(k1_wellord2(X0),X1),sK2(k1_wellord2(X2),X1))
    | ~ v3_ordinal1(sK2(k1_wellord2(X2),X1))
    | ~ v3_ordinal1(sK3(k1_wellord2(X0),X1)) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_2426,plain,
    ( r1_tarski(sK3(k1_wellord2(sK4),sK4),sK2(k1_wellord2(sK4),sK4))
    | ~ r1_ordinal1(sK3(k1_wellord2(sK4),sK4),sK2(k1_wellord2(sK4),sK4))
    | ~ v3_ordinal1(sK2(k1_wellord2(sK4),sK4))
    | ~ v3_ordinal1(sK3(k1_wellord2(sK4),sK4)) ),
    inference(instantiation,[status(thm)],[c_2424])).

cnf(c_2024,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(sK3(k1_wellord2(X2),X1),X1)
    | r2_hidden(k4_tarski(sK3(k1_wellord2(X2),X1),X0),k1_wellord2(X1))
    | ~ r1_tarski(sK3(k1_wellord2(X2),X1),X0)
    | k1_wellord2(X3) != k1_wellord2(X1) ),
    inference(instantiation,[status(thm)],[c_425])).

cnf(c_2122,plain,
    ( ~ r2_hidden(sK2(k1_wellord2(X0),X1),X1)
    | ~ r2_hidden(sK3(k1_wellord2(X2),X1),X1)
    | r2_hidden(k4_tarski(sK3(k1_wellord2(X2),X1),sK2(k1_wellord2(X0),X1)),k1_wellord2(X1))
    | ~ r1_tarski(sK3(k1_wellord2(X2),X1),sK2(k1_wellord2(X0),X1))
    | k1_wellord2(X3) != k1_wellord2(X1) ),
    inference(instantiation,[status(thm)],[c_2024])).

cnf(c_2124,plain,
    ( ~ r2_hidden(sK2(k1_wellord2(sK4),sK4),sK4)
    | ~ r2_hidden(sK3(k1_wellord2(sK4),sK4),sK4)
    | r2_hidden(k4_tarski(sK3(k1_wellord2(sK4),sK4),sK2(k1_wellord2(sK4),sK4)),k1_wellord2(sK4))
    | ~ r1_tarski(sK3(k1_wellord2(sK4),sK4),sK2(k1_wellord2(sK4),sK4))
    | k1_wellord2(sK4) != k1_wellord2(sK4) ),
    inference(instantiation,[status(thm)],[c_2122])).

cnf(c_2,plain,
    ( ~ r6_relat_2(X0,k3_relat_1(X0))
    | ~ v1_relat_1(X0)
    | v6_relat_2(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_21,negated_conjecture,
    ( ~ v6_relat_2(k1_wellord2(sK4)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_278,plain,
    ( ~ r6_relat_2(X0,k3_relat_1(X0))
    | ~ v1_relat_1(X0)
    | k1_wellord2(sK4) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_21])).

cnf(c_279,plain,
    ( ~ r6_relat_2(k1_wellord2(sK4),k3_relat_1(k1_wellord2(sK4)))
    | ~ v1_relat_1(k1_wellord2(sK4)) ),
    inference(unflattening,[status(thm)],[c_278])).

cnf(c_35,plain,
    ( v1_relat_1(k1_wellord2(sK4)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_281,plain,
    ( ~ r6_relat_2(k1_wellord2(sK4),k3_relat_1(k1_wellord2(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_279,c_35])).

cnf(c_1880,plain,
    ( r6_relat_2(k1_wellord2(sK4),k3_relat_1(k1_wellord2(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_281])).

cnf(c_10,plain,
    ( ~ v1_relat_1(k1_wellord2(X0))
    | k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_145,plain,
    ( k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10,c_17])).

cnf(c_1890,plain,
    ( r6_relat_2(k1_wellord2(sK4),sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1880,c_145])).

cnf(c_1987,plain,
    ( ~ r6_relat_2(k1_wellord2(sK4),sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1890])).

cnf(c_1524,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1549,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_1524])).

cnf(c_1529,plain,
    ( X0 != X1
    | k1_wellord2(X0) = k1_wellord2(X1) ),
    theory(equality)).

cnf(c_1540,plain,
    ( k1_wellord2(sK4) = k1_wellord2(sK4)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1529])).

cnf(c_11,plain,
    ( ~ r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0)
    | r6_relat_2(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_339,plain,
    ( ~ r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0)
    | r6_relat_2(X0,X1)
    | k1_wellord2(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_17])).

cnf(c_340,plain,
    ( ~ r2_hidden(k4_tarski(sK3(k1_wellord2(X0),X1),sK2(k1_wellord2(X0),X1)),k1_wellord2(X0))
    | r6_relat_2(k1_wellord2(X0),X1) ),
    inference(unflattening,[status(thm)],[c_339])).

cnf(c_342,plain,
    ( ~ r2_hidden(k4_tarski(sK3(k1_wellord2(sK4),sK4),sK2(k1_wellord2(sK4),sK4)),k1_wellord2(sK4))
    | r6_relat_2(k1_wellord2(sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_340])).

cnf(c_14,plain,
    ( r2_hidden(sK3(X0,X1),X1)
    | r6_relat_2(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_303,plain,
    ( r2_hidden(sK3(X0,X1),X1)
    | r6_relat_2(X0,X1)
    | k1_wellord2(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_17])).

cnf(c_304,plain,
    ( r2_hidden(sK3(k1_wellord2(X0),X1),X1)
    | r6_relat_2(k1_wellord2(X0),X1) ),
    inference(unflattening,[status(thm)],[c_303])).

cnf(c_306,plain,
    ( r2_hidden(sK3(k1_wellord2(sK4),sK4),sK4)
    | r6_relat_2(k1_wellord2(sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_304])).

cnf(c_15,plain,
    ( r2_hidden(sK2(X0,X1),X1)
    | r6_relat_2(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_291,plain,
    ( r2_hidden(sK2(X0,X1),X1)
    | r6_relat_2(X0,X1)
    | k1_wellord2(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_17])).

cnf(c_292,plain,
    ( r2_hidden(sK2(k1_wellord2(X0),X1),X1)
    | r6_relat_2(k1_wellord2(X0),X1) ),
    inference(unflattening,[status(thm)],[c_291])).

cnf(c_294,plain,
    ( r2_hidden(sK2(k1_wellord2(sK4),sK4),sK4)
    | r6_relat_2(k1_wellord2(sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_292])).

cnf(c_22,negated_conjecture,
    ( v3_ordinal1(sK4) ),
    inference(cnf_transformation,[],[f56])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2962,c_2919,c_2880,c_2426,c_2124,c_1987,c_1549,c_1540,c_342,c_306,c_294,c_22])).


%------------------------------------------------------------------------------
