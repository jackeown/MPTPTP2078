%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:50:24 EST 2020

% Result     : Theorem 3.09s
% Output     : CNFRefutation 3.09s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 760 expanded)
%              Number of clauses        :   68 ( 208 expanded)
%              Number of leaves         :   14 ( 161 expanded)
%              Depth                    :   21
%              Number of atoms          :  480 (3670 expanded)
%              Number of equality atoms :  161 (1021 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k2_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
          & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( r2_hidden(X0,k2_relat_1(X1))
            & v2_funct_1(X1) )
         => ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
            & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0
        | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0 )
      & r2_hidden(X0,k2_relat_1(X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0
        | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0 )
      & r2_hidden(X0,k2_relat_1(X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f37,plain,
    ( ? [X0,X1] :
        ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0
          | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0 )
        & r2_hidden(X0,k2_relat_1(X1))
        & v2_funct_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ( k1_funct_1(k5_relat_1(k2_funct_1(sK6),sK6),sK5) != sK5
        | k1_funct_1(sK6,k1_funct_1(k2_funct_1(sK6),sK5)) != sK5 )
      & r2_hidden(sK5,k2_relat_1(sK6))
      & v2_funct_1(sK6)
      & v1_funct_1(sK6)
      & v1_relat_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ( k1_funct_1(k5_relat_1(k2_funct_1(sK6),sK6),sK5) != sK5
      | k1_funct_1(sK6,k1_funct_1(k2_funct_1(sK6),sK5)) != sK5 )
    & r2_hidden(sK5,k2_relat_1(sK6))
    & v2_funct_1(sK6)
    & v1_funct_1(sK6)
    & v1_relat_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f24,f37])).

fof(f58,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f38])).

fof(f60,plain,(
    r2_hidden(sK5,k2_relat_1(sK6)) ),
    inference(cnf_transformation,[],[f38])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
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

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f29,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK2(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK1(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
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

fof(f30,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f29,f28,f27])).

fof(f39,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK2(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f63,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK2(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f57,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f38])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f66,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f56])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
            & ( ! [X2,X3] :
                  ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X3,X2),X0) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X5,X4),X0) )
                  & ( r2_hidden(k4_tarski(X5,X4),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f31])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r2_hidden(k4_tarski(X3,X2),X0)
            | r2_hidden(k4_tarski(X2,X3),X1) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
          | ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) )
        & ( r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
          | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ( ( ~ r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
                  | ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) )
                & ( r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
                  | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X5,X4),X0) )
                  & ( r2_hidden(k4_tarski(X5,X4),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f32,f33])).

fof(f44,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r2_hidden(k4_tarski(X5,X4),X0)
      | k4_relat_1(X0) != X1
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f64,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X4),X0)
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f47,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f16,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f50,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f59,plain,(
    v2_funct_1(sK6) ),
    inference(cnf_transformation,[],[f38])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f18,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f52,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f61,plain,
    ( k1_funct_1(k5_relat_1(k2_funct_1(sK6),sK6),sK5) != sK5
    | k1_funct_1(sK6,k1_funct_1(k2_funct_1(sK6),sK5)) != sK5 ),
    inference(cnf_transformation,[],[f38])).

fof(f43,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X4),X0)
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | k4_relat_1(X0) != X1
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f65,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X5,X4),X0)
      | ~ r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0))
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f43])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_703,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_19,negated_conjecture,
    ( r2_hidden(sK5,k2_relat_1(sK6)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_704,plain,
    ( r2_hidden(sK5,k2_relat_1(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(k4_tarski(sK2(X1,X0),X0),X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_716,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(sK2(X1,X0),X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_16,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_705,plain,
    ( k1_funct_1(X0,X1) = X2
    | r2_hidden(k4_tarski(X1,X2),X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1299,plain,
    ( k1_funct_1(X0,sK2(X0,X1)) = X1
    | r2_hidden(X1,k2_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_716,c_705])).

cnf(c_2893,plain,
    ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK5
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_704,c_1299])).

cnf(c_22,negated_conjecture,
    ( v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_886,plain,
    ( r2_hidden(k4_tarski(sK2(sK6,sK5),sK5),sK6)
    | ~ r2_hidden(sK5,k2_relat_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_905,plain,
    ( ~ r2_hidden(k4_tarski(sK2(sK6,sK5),sK5),sK6)
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | k1_funct_1(sK6,sK2(sK6,sK5)) = sK5 ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_3075,plain,
    ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2893,c_22,c_21,c_19,c_886,c_905])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_706,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3078,plain,
    ( r2_hidden(sK2(sK6,sK5),k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k4_tarski(sK2(sK6,sK5),sK5),sK6) = iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3075,c_706])).

cnf(c_26,plain,
    ( r2_hidden(sK5,k2_relat_1(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_887,plain,
    ( r2_hidden(k4_tarski(sK2(sK6,sK5),sK5),sK6) = iProver_top
    | r2_hidden(sK5,k2_relat_1(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_886])).

cnf(c_3081,plain,
    ( r2_hidden(k4_tarski(sK2(sK6,sK5),sK5),sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3078,c_26,c_887])).

cnf(c_6,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | r2_hidden(k4_tarski(X1,X0),k4_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(k4_relat_1(X2)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_713,plain,
    ( r2_hidden(k4_tarski(X0,X1),X2) != iProver_top
    | r2_hidden(k4_tarski(X1,X0),k4_relat_1(X2)) = iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(k4_relat_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k4_relat_1(X0)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_711,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_803,plain,
    ( r2_hidden(k4_tarski(X0,X1),X2) != iProver_top
    | r2_hidden(k4_tarski(X1,X0),k4_relat_1(X2)) = iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_713,c_711])).

cnf(c_10,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_710,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1797,plain,
    ( r2_hidden(X0,k1_relat_1(k4_relat_1(X1))) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k4_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_803,c_710])).

cnf(c_5546,plain,
    ( r2_hidden(X0,k1_relat_1(k4_relat_1(X1))) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1797,c_711])).

cnf(c_5556,plain,
    ( r2_hidden(sK5,k1_relat_1(k4_relat_1(sK6))) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3081,c_5546])).

cnf(c_23,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_54,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_56,plain,
    ( v1_relat_1(k4_relat_1(sK6)) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_54])).

cnf(c_906,plain,
    ( ~ r2_hidden(k4_tarski(sK2(sK6,sK5),sK5),sK6)
    | r2_hidden(k4_tarski(sK5,sK2(sK6,sK5)),k4_relat_1(sK6))
    | ~ v1_relat_1(k4_relat_1(sK6))
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_907,plain,
    ( r2_hidden(k4_tarski(sK2(sK6,sK5),sK5),sK6) != iProver_top
    | r2_hidden(k4_tarski(sK5,sK2(sK6,sK5)),k4_relat_1(sK6)) = iProver_top
    | v1_relat_1(k4_relat_1(sK6)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_906])).

cnf(c_972,plain,
    ( ~ r2_hidden(k4_tarski(sK5,sK2(sK6,sK5)),k4_relat_1(sK6))
    | r2_hidden(sK5,k1_relat_1(k4_relat_1(sK6)))
    | ~ v1_relat_1(k4_relat_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_973,plain,
    ( r2_hidden(k4_tarski(sK5,sK2(sK6,sK5)),k4_relat_1(sK6)) != iProver_top
    | r2_hidden(sK5,k1_relat_1(k4_relat_1(sK6))) = iProver_top
    | v1_relat_1(k4_relat_1(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_972])).

cnf(c_5834,plain,
    ( r2_hidden(sK5,k1_relat_1(k4_relat_1(sK6))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5556,c_23,c_26,c_56,c_887,c_907,c_973])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_707,plain,
    ( k1_funct_1(k5_relat_1(X0,X1),X2) = k1_funct_1(X1,k1_funct_1(X0,X2))
    | r2_hidden(X2,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_5839,plain,
    ( k1_funct_1(X0,k1_funct_1(k4_relat_1(sK6),sK5)) = k1_funct_1(k5_relat_1(k4_relat_1(sK6),X0),sK5)
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k4_relat_1(sK6)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5834,c_707])).

cnf(c_24,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_11,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_20,negated_conjecture,
    ( v2_funct_1(sK6) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_250,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_20])).

cnf(c_251,plain,
    ( ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | k2_funct_1(sK6) = k4_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_250])).

cnf(c_46,plain,
    ( ~ v1_funct_1(sK6)
    | ~ v2_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | k2_funct_1(sK6) = k4_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_253,plain,
    ( k2_funct_1(sK6) = k4_relat_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_251,c_22,c_21,c_20,c_46])).

cnf(c_12,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_709,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1193,plain,
    ( v1_funct_1(k4_relat_1(sK6)) = iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_253,c_709])).

cnf(c_7139,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_funct_1(X0,k1_funct_1(k4_relat_1(sK6),sK5)) = k1_funct_1(k5_relat_1(k4_relat_1(sK6),X0),sK5)
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5839,c_23,c_24,c_56,c_1193])).

cnf(c_7140,plain,
    ( k1_funct_1(X0,k1_funct_1(k4_relat_1(sK6),sK5)) = k1_funct_1(k5_relat_1(k4_relat_1(sK6),X0),sK5)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_7139])).

cnf(c_7149,plain,
    ( k1_funct_1(sK6,k1_funct_1(k4_relat_1(sK6),sK5)) = k1_funct_1(k5_relat_1(k4_relat_1(sK6),sK6),sK5)
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_703,c_7140])).

cnf(c_5841,plain,
    ( k1_funct_1(sK6,k1_funct_1(k4_relat_1(sK6),sK5)) = k1_funct_1(k5_relat_1(k4_relat_1(sK6),sK6),sK5)
    | v1_funct_1(k4_relat_1(sK6)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(k4_relat_1(sK6)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5839])).

cnf(c_7173,plain,
    ( k1_funct_1(sK6,k1_funct_1(k4_relat_1(sK6),sK5)) = k1_funct_1(k5_relat_1(k4_relat_1(sK6),sK6),sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7149,c_23,c_24,c_56,c_1193,c_5841])).

cnf(c_18,negated_conjecture,
    ( k1_funct_1(k5_relat_1(k2_funct_1(sK6),sK6),sK5) != sK5
    | k1_funct_1(sK6,k1_funct_1(k2_funct_1(sK6),sK5)) != sK5 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_752,plain,
    ( k1_funct_1(k5_relat_1(k4_relat_1(sK6),sK6),sK5) != sK5
    | k1_funct_1(sK6,k1_funct_1(k4_relat_1(sK6),sK5)) != sK5 ),
    inference(light_normalisation,[status(thm)],[c_18,c_253])).

cnf(c_7176,plain,
    ( k1_funct_1(sK6,k1_funct_1(k4_relat_1(sK6),sK5)) != sK5 ),
    inference(demodulation,[status(thm)],[c_7173,c_752])).

cnf(c_6866,plain,
    ( ~ r2_hidden(k4_tarski(k1_funct_1(k4_relat_1(sK6),sK5),sK5),X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X0,k1_funct_1(k4_relat_1(sK6),sK5)) = sK5 ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_6873,plain,
    ( ~ r2_hidden(k4_tarski(k1_funct_1(k4_relat_1(sK6),sK5),sK5),sK6)
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | k1_funct_1(sK6,k1_funct_1(k4_relat_1(sK6),sK5)) = sK5 ),
    inference(instantiation,[status(thm)],[c_6866])).

cnf(c_7,plain,
    ( r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X1,X0),k4_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(k4_relat_1(X2)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1998,plain,
    ( r2_hidden(k4_tarski(k1_funct_1(k4_relat_1(sK6),sK5),sK5),sK6)
    | ~ r2_hidden(k4_tarski(sK5,k1_funct_1(k4_relat_1(sK6),sK5)),k4_relat_1(sK6))
    | ~ v1_relat_1(k4_relat_1(sK6))
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1011,plain,
    ( r2_hidden(k4_tarski(sK5,k1_funct_1(X0,sK5)),X0)
    | ~ r2_hidden(sK5,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1474,plain,
    ( r2_hidden(k4_tarski(sK5,k1_funct_1(k4_relat_1(sK6),sK5)),k4_relat_1(sK6))
    | ~ r2_hidden(sK5,k1_relat_1(k4_relat_1(sK6)))
    | ~ v1_funct_1(k4_relat_1(sK6))
    | ~ v1_relat_1(k4_relat_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_1011])).

cnf(c_1194,plain,
    ( v1_funct_1(k4_relat_1(sK6))
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1193])).

cnf(c_55,plain,
    ( v1_relat_1(k4_relat_1(sK6))
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7176,c_6873,c_1998,c_1474,c_1194,c_972,c_906,c_886,c_55,c_19,c_21,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:57:39 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.09/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.09/0.99  
% 3.09/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.09/0.99  
% 3.09/0.99  ------  iProver source info
% 3.09/0.99  
% 3.09/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.09/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.09/0.99  git: non_committed_changes: false
% 3.09/0.99  git: last_make_outside_of_git: false
% 3.09/0.99  
% 3.09/0.99  ------ 
% 3.09/0.99  
% 3.09/0.99  ------ Input Options
% 3.09/0.99  
% 3.09/0.99  --out_options                           all
% 3.09/0.99  --tptp_safe_out                         true
% 3.09/0.99  --problem_path                          ""
% 3.09/0.99  --include_path                          ""
% 3.09/0.99  --clausifier                            res/vclausify_rel
% 3.09/0.99  --clausifier_options                    --mode clausify
% 3.09/0.99  --stdin                                 false
% 3.09/0.99  --stats_out                             all
% 3.09/0.99  
% 3.09/0.99  ------ General Options
% 3.09/0.99  
% 3.09/0.99  --fof                                   false
% 3.09/0.99  --time_out_real                         305.
% 3.09/0.99  --time_out_virtual                      -1.
% 3.09/0.99  --symbol_type_check                     false
% 3.09/0.99  --clausify_out                          false
% 3.09/0.99  --sig_cnt_out                           false
% 3.09/0.99  --trig_cnt_out                          false
% 3.09/0.99  --trig_cnt_out_tolerance                1.
% 3.09/0.99  --trig_cnt_out_sk_spl                   false
% 3.09/0.99  --abstr_cl_out                          false
% 3.09/0.99  
% 3.09/0.99  ------ Global Options
% 3.09/0.99  
% 3.09/0.99  --schedule                              default
% 3.09/0.99  --add_important_lit                     false
% 3.09/0.99  --prop_solver_per_cl                    1000
% 3.09/0.99  --min_unsat_core                        false
% 3.09/0.99  --soft_assumptions                      false
% 3.09/0.99  --soft_lemma_size                       3
% 3.09/0.99  --prop_impl_unit_size                   0
% 3.09/0.99  --prop_impl_unit                        []
% 3.09/0.99  --share_sel_clauses                     true
% 3.09/0.99  --reset_solvers                         false
% 3.09/0.99  --bc_imp_inh                            [conj_cone]
% 3.09/0.99  --conj_cone_tolerance                   3.
% 3.09/0.99  --extra_neg_conj                        none
% 3.09/0.99  --large_theory_mode                     true
% 3.09/0.99  --prolific_symb_bound                   200
% 3.09/0.99  --lt_threshold                          2000
% 3.09/0.99  --clause_weak_htbl                      true
% 3.09/0.99  --gc_record_bc_elim                     false
% 3.09/0.99  
% 3.09/0.99  ------ Preprocessing Options
% 3.09/0.99  
% 3.09/0.99  --preprocessing_flag                    true
% 3.09/0.99  --time_out_prep_mult                    0.1
% 3.09/0.99  --splitting_mode                        input
% 3.09/0.99  --splitting_grd                         true
% 3.09/0.99  --splitting_cvd                         false
% 3.09/0.99  --splitting_cvd_svl                     false
% 3.09/0.99  --splitting_nvd                         32
% 3.09/0.99  --sub_typing                            true
% 3.09/0.99  --prep_gs_sim                           true
% 3.09/0.99  --prep_unflatten                        true
% 3.09/0.99  --prep_res_sim                          true
% 3.09/0.99  --prep_upred                            true
% 3.09/0.99  --prep_sem_filter                       exhaustive
% 3.09/0.99  --prep_sem_filter_out                   false
% 3.09/0.99  --pred_elim                             true
% 3.09/0.99  --res_sim_input                         true
% 3.09/0.99  --eq_ax_congr_red                       true
% 3.09/0.99  --pure_diseq_elim                       true
% 3.09/0.99  --brand_transform                       false
% 3.09/0.99  --non_eq_to_eq                          false
% 3.09/0.99  --prep_def_merge                        true
% 3.09/0.99  --prep_def_merge_prop_impl              false
% 3.09/0.99  --prep_def_merge_mbd                    true
% 3.09/0.99  --prep_def_merge_tr_red                 false
% 3.09/0.99  --prep_def_merge_tr_cl                  false
% 3.09/0.99  --smt_preprocessing                     true
% 3.09/0.99  --smt_ac_axioms                         fast
% 3.09/0.99  --preprocessed_out                      false
% 3.09/0.99  --preprocessed_stats                    false
% 3.09/0.99  
% 3.09/0.99  ------ Abstraction refinement Options
% 3.09/0.99  
% 3.09/0.99  --abstr_ref                             []
% 3.09/0.99  --abstr_ref_prep                        false
% 3.09/0.99  --abstr_ref_until_sat                   false
% 3.09/0.99  --abstr_ref_sig_restrict                funpre
% 3.09/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.09/0.99  --abstr_ref_under                       []
% 3.09/0.99  
% 3.09/0.99  ------ SAT Options
% 3.09/0.99  
% 3.09/0.99  --sat_mode                              false
% 3.09/0.99  --sat_fm_restart_options                ""
% 3.09/0.99  --sat_gr_def                            false
% 3.09/0.99  --sat_epr_types                         true
% 3.09/0.99  --sat_non_cyclic_types                  false
% 3.09/0.99  --sat_finite_models                     false
% 3.09/0.99  --sat_fm_lemmas                         false
% 3.09/0.99  --sat_fm_prep                           false
% 3.09/0.99  --sat_fm_uc_incr                        true
% 3.09/0.99  --sat_out_model                         small
% 3.09/0.99  --sat_out_clauses                       false
% 3.09/0.99  
% 3.09/0.99  ------ QBF Options
% 3.09/0.99  
% 3.09/0.99  --qbf_mode                              false
% 3.09/0.99  --qbf_elim_univ                         false
% 3.09/0.99  --qbf_dom_inst                          none
% 3.09/0.99  --qbf_dom_pre_inst                      false
% 3.09/0.99  --qbf_sk_in                             false
% 3.09/0.99  --qbf_pred_elim                         true
% 3.09/0.99  --qbf_split                             512
% 3.09/0.99  
% 3.09/0.99  ------ BMC1 Options
% 3.09/0.99  
% 3.09/0.99  --bmc1_incremental                      false
% 3.09/0.99  --bmc1_axioms                           reachable_all
% 3.09/0.99  --bmc1_min_bound                        0
% 3.09/0.99  --bmc1_max_bound                        -1
% 3.09/0.99  --bmc1_max_bound_default                -1
% 3.09/0.99  --bmc1_symbol_reachability              true
% 3.09/0.99  --bmc1_property_lemmas                  false
% 3.09/0.99  --bmc1_k_induction                      false
% 3.09/0.99  --bmc1_non_equiv_states                 false
% 3.09/0.99  --bmc1_deadlock                         false
% 3.09/0.99  --bmc1_ucm                              false
% 3.09/0.99  --bmc1_add_unsat_core                   none
% 3.09/0.99  --bmc1_unsat_core_children              false
% 3.09/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.09/0.99  --bmc1_out_stat                         full
% 3.09/0.99  --bmc1_ground_init                      false
% 3.09/0.99  --bmc1_pre_inst_next_state              false
% 3.09/0.99  --bmc1_pre_inst_state                   false
% 3.09/0.99  --bmc1_pre_inst_reach_state             false
% 3.09/0.99  --bmc1_out_unsat_core                   false
% 3.09/0.99  --bmc1_aig_witness_out                  false
% 3.09/0.99  --bmc1_verbose                          false
% 3.09/0.99  --bmc1_dump_clauses_tptp                false
% 3.09/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.09/0.99  --bmc1_dump_file                        -
% 3.09/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.09/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.09/0.99  --bmc1_ucm_extend_mode                  1
% 3.09/0.99  --bmc1_ucm_init_mode                    2
% 3.09/0.99  --bmc1_ucm_cone_mode                    none
% 3.09/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.09/0.99  --bmc1_ucm_relax_model                  4
% 3.09/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.09/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.09/0.99  --bmc1_ucm_layered_model                none
% 3.09/0.99  --bmc1_ucm_max_lemma_size               10
% 3.09/0.99  
% 3.09/0.99  ------ AIG Options
% 3.09/0.99  
% 3.09/0.99  --aig_mode                              false
% 3.09/0.99  
% 3.09/0.99  ------ Instantiation Options
% 3.09/0.99  
% 3.09/0.99  --instantiation_flag                    true
% 3.09/0.99  --inst_sos_flag                         false
% 3.09/0.99  --inst_sos_phase                        true
% 3.09/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.09/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.09/0.99  --inst_lit_sel_side                     num_symb
% 3.09/0.99  --inst_solver_per_active                1400
% 3.09/0.99  --inst_solver_calls_frac                1.
% 3.09/0.99  --inst_passive_queue_type               priority_queues
% 3.09/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.09/0.99  --inst_passive_queues_freq              [25;2]
% 3.09/0.99  --inst_dismatching                      true
% 3.09/0.99  --inst_eager_unprocessed_to_passive     true
% 3.09/0.99  --inst_prop_sim_given                   true
% 3.09/0.99  --inst_prop_sim_new                     false
% 3.09/0.99  --inst_subs_new                         false
% 3.09/0.99  --inst_eq_res_simp                      false
% 3.09/0.99  --inst_subs_given                       false
% 3.09/0.99  --inst_orphan_elimination               true
% 3.09/0.99  --inst_learning_loop_flag               true
% 3.09/0.99  --inst_learning_start                   3000
% 3.09/0.99  --inst_learning_factor                  2
% 3.09/0.99  --inst_start_prop_sim_after_learn       3
% 3.09/0.99  --inst_sel_renew                        solver
% 3.09/0.99  --inst_lit_activity_flag                true
% 3.09/0.99  --inst_restr_to_given                   false
% 3.09/0.99  --inst_activity_threshold               500
% 3.09/0.99  --inst_out_proof                        true
% 3.09/0.99  
% 3.09/0.99  ------ Resolution Options
% 3.09/0.99  
% 3.09/0.99  --resolution_flag                       true
% 3.09/0.99  --res_lit_sel                           adaptive
% 3.09/0.99  --res_lit_sel_side                      none
% 3.09/0.99  --res_ordering                          kbo
% 3.09/0.99  --res_to_prop_solver                    active
% 3.09/0.99  --res_prop_simpl_new                    false
% 3.09/0.99  --res_prop_simpl_given                  true
% 3.09/0.99  --res_passive_queue_type                priority_queues
% 3.09/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.09/0.99  --res_passive_queues_freq               [15;5]
% 3.09/0.99  --res_forward_subs                      full
% 3.09/0.99  --res_backward_subs                     full
% 3.09/0.99  --res_forward_subs_resolution           true
% 3.09/0.99  --res_backward_subs_resolution          true
% 3.09/0.99  --res_orphan_elimination                true
% 3.09/0.99  --res_time_limit                        2.
% 3.09/0.99  --res_out_proof                         true
% 3.09/0.99  
% 3.09/0.99  ------ Superposition Options
% 3.09/0.99  
% 3.09/0.99  --superposition_flag                    true
% 3.09/0.99  --sup_passive_queue_type                priority_queues
% 3.09/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.09/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.09/0.99  --demod_completeness_check              fast
% 3.09/0.99  --demod_use_ground                      true
% 3.09/0.99  --sup_to_prop_solver                    passive
% 3.09/0.99  --sup_prop_simpl_new                    true
% 3.09/0.99  --sup_prop_simpl_given                  true
% 3.09/0.99  --sup_fun_splitting                     false
% 3.09/0.99  --sup_smt_interval                      50000
% 3.09/0.99  
% 3.09/0.99  ------ Superposition Simplification Setup
% 3.09/0.99  
% 3.09/0.99  --sup_indices_passive                   []
% 3.09/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.09/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.09/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.09/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.09/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.09/0.99  --sup_full_bw                           [BwDemod]
% 3.09/0.99  --sup_immed_triv                        [TrivRules]
% 3.09/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.09/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.09/0.99  --sup_immed_bw_main                     []
% 3.09/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.09/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.09/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.09/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.09/0.99  
% 3.09/0.99  ------ Combination Options
% 3.09/0.99  
% 3.09/0.99  --comb_res_mult                         3
% 3.09/0.99  --comb_sup_mult                         2
% 3.09/0.99  --comb_inst_mult                        10
% 3.09/0.99  
% 3.09/0.99  ------ Debug Options
% 3.09/0.99  
% 3.09/0.99  --dbg_backtrace                         false
% 3.09/0.99  --dbg_dump_prop_clauses                 false
% 3.09/0.99  --dbg_dump_prop_clauses_file            -
% 3.09/0.99  --dbg_out_stat                          false
% 3.09/0.99  ------ Parsing...
% 3.09/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.09/0.99  
% 3.09/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.09/0.99  
% 3.09/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.09/0.99  
% 3.09/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.09/0.99  ------ Proving...
% 3.09/0.99  ------ Problem Properties 
% 3.09/0.99  
% 3.09/0.99  
% 3.09/0.99  clauses                                 20
% 3.09/0.99  conjectures                             4
% 3.09/0.99  EPR                                     2
% 3.09/0.99  Horn                                    18
% 3.09/0.99  unary                                   4
% 3.09/0.99  binary                                  4
% 3.09/0.99  lits                                    59
% 3.09/0.99  lits eq                                 9
% 3.09/0.99  fd_pure                                 0
% 3.09/0.99  fd_pseudo                               0
% 3.09/0.99  fd_cond                                 0
% 3.09/0.99  fd_pseudo_cond                          5
% 3.09/0.99  AC symbols                              0
% 3.09/0.99  
% 3.09/0.99  ------ Schedule dynamic 5 is on 
% 3.09/0.99  
% 3.09/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.09/0.99  
% 3.09/0.99  
% 3.09/0.99  ------ 
% 3.09/0.99  Current options:
% 3.09/0.99  ------ 
% 3.09/0.99  
% 3.09/0.99  ------ Input Options
% 3.09/0.99  
% 3.09/0.99  --out_options                           all
% 3.09/0.99  --tptp_safe_out                         true
% 3.09/0.99  --problem_path                          ""
% 3.09/0.99  --include_path                          ""
% 3.09/0.99  --clausifier                            res/vclausify_rel
% 3.09/0.99  --clausifier_options                    --mode clausify
% 3.09/0.99  --stdin                                 false
% 3.09/0.99  --stats_out                             all
% 3.09/0.99  
% 3.09/0.99  ------ General Options
% 3.09/0.99  
% 3.09/0.99  --fof                                   false
% 3.09/0.99  --time_out_real                         305.
% 3.09/0.99  --time_out_virtual                      -1.
% 3.09/0.99  --symbol_type_check                     false
% 3.09/0.99  --clausify_out                          false
% 3.09/0.99  --sig_cnt_out                           false
% 3.09/0.99  --trig_cnt_out                          false
% 3.09/0.99  --trig_cnt_out_tolerance                1.
% 3.09/0.99  --trig_cnt_out_sk_spl                   false
% 3.09/0.99  --abstr_cl_out                          false
% 3.09/0.99  
% 3.09/0.99  ------ Global Options
% 3.09/0.99  
% 3.09/0.99  --schedule                              default
% 3.09/0.99  --add_important_lit                     false
% 3.09/0.99  --prop_solver_per_cl                    1000
% 3.09/0.99  --min_unsat_core                        false
% 3.09/0.99  --soft_assumptions                      false
% 3.09/0.99  --soft_lemma_size                       3
% 3.09/0.99  --prop_impl_unit_size                   0
% 3.09/0.99  --prop_impl_unit                        []
% 3.09/0.99  --share_sel_clauses                     true
% 3.09/0.99  --reset_solvers                         false
% 3.09/0.99  --bc_imp_inh                            [conj_cone]
% 3.09/0.99  --conj_cone_tolerance                   3.
% 3.09/0.99  --extra_neg_conj                        none
% 3.09/0.99  --large_theory_mode                     true
% 3.09/0.99  --prolific_symb_bound                   200
% 3.09/0.99  --lt_threshold                          2000
% 3.09/0.99  --clause_weak_htbl                      true
% 3.09/0.99  --gc_record_bc_elim                     false
% 3.09/0.99  
% 3.09/0.99  ------ Preprocessing Options
% 3.09/0.99  
% 3.09/0.99  --preprocessing_flag                    true
% 3.09/0.99  --time_out_prep_mult                    0.1
% 3.09/0.99  --splitting_mode                        input
% 3.09/0.99  --splitting_grd                         true
% 3.09/0.99  --splitting_cvd                         false
% 3.09/0.99  --splitting_cvd_svl                     false
% 3.09/0.99  --splitting_nvd                         32
% 3.09/0.99  --sub_typing                            true
% 3.09/0.99  --prep_gs_sim                           true
% 3.09/0.99  --prep_unflatten                        true
% 3.09/0.99  --prep_res_sim                          true
% 3.09/0.99  --prep_upred                            true
% 3.09/0.99  --prep_sem_filter                       exhaustive
% 3.09/0.99  --prep_sem_filter_out                   false
% 3.09/0.99  --pred_elim                             true
% 3.09/0.99  --res_sim_input                         true
% 3.09/0.99  --eq_ax_congr_red                       true
% 3.09/0.99  --pure_diseq_elim                       true
% 3.09/0.99  --brand_transform                       false
% 3.09/0.99  --non_eq_to_eq                          false
% 3.09/0.99  --prep_def_merge                        true
% 3.09/0.99  --prep_def_merge_prop_impl              false
% 3.09/0.99  --prep_def_merge_mbd                    true
% 3.09/0.99  --prep_def_merge_tr_red                 false
% 3.09/0.99  --prep_def_merge_tr_cl                  false
% 3.09/0.99  --smt_preprocessing                     true
% 3.09/0.99  --smt_ac_axioms                         fast
% 3.09/0.99  --preprocessed_out                      false
% 3.09/0.99  --preprocessed_stats                    false
% 3.09/0.99  
% 3.09/0.99  ------ Abstraction refinement Options
% 3.09/0.99  
% 3.09/0.99  --abstr_ref                             []
% 3.09/0.99  --abstr_ref_prep                        false
% 3.09/0.99  --abstr_ref_until_sat                   false
% 3.09/0.99  --abstr_ref_sig_restrict                funpre
% 3.09/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.09/0.99  --abstr_ref_under                       []
% 3.09/0.99  
% 3.09/0.99  ------ SAT Options
% 3.09/0.99  
% 3.09/0.99  --sat_mode                              false
% 3.09/0.99  --sat_fm_restart_options                ""
% 3.09/0.99  --sat_gr_def                            false
% 3.09/0.99  --sat_epr_types                         true
% 3.09/0.99  --sat_non_cyclic_types                  false
% 3.09/0.99  --sat_finite_models                     false
% 3.09/0.99  --sat_fm_lemmas                         false
% 3.09/0.99  --sat_fm_prep                           false
% 3.09/0.99  --sat_fm_uc_incr                        true
% 3.09/0.99  --sat_out_model                         small
% 3.09/0.99  --sat_out_clauses                       false
% 3.09/0.99  
% 3.09/0.99  ------ QBF Options
% 3.09/0.99  
% 3.09/0.99  --qbf_mode                              false
% 3.09/0.99  --qbf_elim_univ                         false
% 3.09/0.99  --qbf_dom_inst                          none
% 3.09/0.99  --qbf_dom_pre_inst                      false
% 3.09/0.99  --qbf_sk_in                             false
% 3.09/0.99  --qbf_pred_elim                         true
% 3.09/0.99  --qbf_split                             512
% 3.09/0.99  
% 3.09/0.99  ------ BMC1 Options
% 3.09/0.99  
% 3.09/0.99  --bmc1_incremental                      false
% 3.09/0.99  --bmc1_axioms                           reachable_all
% 3.09/0.99  --bmc1_min_bound                        0
% 3.09/0.99  --bmc1_max_bound                        -1
% 3.09/0.99  --bmc1_max_bound_default                -1
% 3.09/0.99  --bmc1_symbol_reachability              true
% 3.09/0.99  --bmc1_property_lemmas                  false
% 3.09/0.99  --bmc1_k_induction                      false
% 3.09/0.99  --bmc1_non_equiv_states                 false
% 3.09/0.99  --bmc1_deadlock                         false
% 3.09/0.99  --bmc1_ucm                              false
% 3.09/0.99  --bmc1_add_unsat_core                   none
% 3.09/0.99  --bmc1_unsat_core_children              false
% 3.09/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.09/0.99  --bmc1_out_stat                         full
% 3.09/0.99  --bmc1_ground_init                      false
% 3.09/0.99  --bmc1_pre_inst_next_state              false
% 3.09/0.99  --bmc1_pre_inst_state                   false
% 3.09/0.99  --bmc1_pre_inst_reach_state             false
% 3.09/0.99  --bmc1_out_unsat_core                   false
% 3.09/0.99  --bmc1_aig_witness_out                  false
% 3.09/0.99  --bmc1_verbose                          false
% 3.09/0.99  --bmc1_dump_clauses_tptp                false
% 3.09/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.09/0.99  --bmc1_dump_file                        -
% 3.09/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.09/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.09/0.99  --bmc1_ucm_extend_mode                  1
% 3.09/0.99  --bmc1_ucm_init_mode                    2
% 3.09/0.99  --bmc1_ucm_cone_mode                    none
% 3.09/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.09/0.99  --bmc1_ucm_relax_model                  4
% 3.09/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.09/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.09/0.99  --bmc1_ucm_layered_model                none
% 3.09/0.99  --bmc1_ucm_max_lemma_size               10
% 3.09/0.99  
% 3.09/0.99  ------ AIG Options
% 3.09/0.99  
% 3.09/0.99  --aig_mode                              false
% 3.09/0.99  
% 3.09/0.99  ------ Instantiation Options
% 3.09/0.99  
% 3.09/0.99  --instantiation_flag                    true
% 3.09/0.99  --inst_sos_flag                         false
% 3.09/0.99  --inst_sos_phase                        true
% 3.09/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.09/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.09/0.99  --inst_lit_sel_side                     none
% 3.09/0.99  --inst_solver_per_active                1400
% 3.09/0.99  --inst_solver_calls_frac                1.
% 3.09/0.99  --inst_passive_queue_type               priority_queues
% 3.09/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.09/0.99  --inst_passive_queues_freq              [25;2]
% 3.09/0.99  --inst_dismatching                      true
% 3.09/0.99  --inst_eager_unprocessed_to_passive     true
% 3.09/0.99  --inst_prop_sim_given                   true
% 3.09/0.99  --inst_prop_sim_new                     false
% 3.09/0.99  --inst_subs_new                         false
% 3.09/0.99  --inst_eq_res_simp                      false
% 3.09/0.99  --inst_subs_given                       false
% 3.09/0.99  --inst_orphan_elimination               true
% 3.09/0.99  --inst_learning_loop_flag               true
% 3.09/0.99  --inst_learning_start                   3000
% 3.09/0.99  --inst_learning_factor                  2
% 3.09/0.99  --inst_start_prop_sim_after_learn       3
% 3.09/0.99  --inst_sel_renew                        solver
% 3.09/0.99  --inst_lit_activity_flag                true
% 3.09/0.99  --inst_restr_to_given                   false
% 3.09/0.99  --inst_activity_threshold               500
% 3.09/0.99  --inst_out_proof                        true
% 3.09/0.99  
% 3.09/0.99  ------ Resolution Options
% 3.09/0.99  
% 3.09/0.99  --resolution_flag                       false
% 3.09/0.99  --res_lit_sel                           adaptive
% 3.09/0.99  --res_lit_sel_side                      none
% 3.09/0.99  --res_ordering                          kbo
% 3.09/0.99  --res_to_prop_solver                    active
% 3.09/0.99  --res_prop_simpl_new                    false
% 3.09/0.99  --res_prop_simpl_given                  true
% 3.09/0.99  --res_passive_queue_type                priority_queues
% 3.09/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.09/0.99  --res_passive_queues_freq               [15;5]
% 3.09/0.99  --res_forward_subs                      full
% 3.09/0.99  --res_backward_subs                     full
% 3.09/0.99  --res_forward_subs_resolution           true
% 3.09/0.99  --res_backward_subs_resolution          true
% 3.09/0.99  --res_orphan_elimination                true
% 3.09/0.99  --res_time_limit                        2.
% 3.09/0.99  --res_out_proof                         true
% 3.09/0.99  
% 3.09/0.99  ------ Superposition Options
% 3.09/0.99  
% 3.09/0.99  --superposition_flag                    true
% 3.09/0.99  --sup_passive_queue_type                priority_queues
% 3.09/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.09/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.09/0.99  --demod_completeness_check              fast
% 3.09/0.99  --demod_use_ground                      true
% 3.09/0.99  --sup_to_prop_solver                    passive
% 3.09/0.99  --sup_prop_simpl_new                    true
% 3.09/0.99  --sup_prop_simpl_given                  true
% 3.09/0.99  --sup_fun_splitting                     false
% 3.09/0.99  --sup_smt_interval                      50000
% 3.09/0.99  
% 3.09/0.99  ------ Superposition Simplification Setup
% 3.09/0.99  
% 3.09/0.99  --sup_indices_passive                   []
% 3.09/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.09/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.09/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.09/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.09/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.09/0.99  --sup_full_bw                           [BwDemod]
% 3.09/0.99  --sup_immed_triv                        [TrivRules]
% 3.09/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.09/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.09/0.99  --sup_immed_bw_main                     []
% 3.09/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.09/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.09/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.09/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.09/0.99  
% 3.09/0.99  ------ Combination Options
% 3.09/0.99  
% 3.09/0.99  --comb_res_mult                         3
% 3.09/0.99  --comb_sup_mult                         2
% 3.09/0.99  --comb_inst_mult                        10
% 3.09/0.99  
% 3.09/0.99  ------ Debug Options
% 3.09/0.99  
% 3.09/0.99  --dbg_backtrace                         false
% 3.09/0.99  --dbg_dump_prop_clauses                 false
% 3.09/0.99  --dbg_dump_prop_clauses_file            -
% 3.09/0.99  --dbg_out_stat                          false
% 3.09/0.99  
% 3.09/0.99  
% 3.09/0.99  
% 3.09/0.99  
% 3.09/0.99  ------ Proving...
% 3.09/0.99  
% 3.09/0.99  
% 3.09/0.99  % SZS status Theorem for theBenchmark.p
% 3.09/0.99  
% 3.09/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.09/0.99  
% 3.09/0.99  fof(f9,conjecture,(
% 3.09/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0 & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0)))),
% 3.09/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.09/0.99  
% 3.09/0.99  fof(f10,negated_conjecture,(
% 3.09/0.99    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0 & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0)))),
% 3.09/0.99    inference(negated_conjecture,[],[f9])).
% 3.09/0.99  
% 3.09/0.99  fof(f23,plain,(
% 3.09/0.99    ? [X0,X1] : (((k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0 | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0) & (r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 3.09/0.99    inference(ennf_transformation,[],[f10])).
% 3.09/0.99  
% 3.09/0.99  fof(f24,plain,(
% 3.09/0.99    ? [X0,X1] : ((k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0 | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0) & r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 3.09/0.99    inference(flattening,[],[f23])).
% 3.09/0.99  
% 3.09/0.99  fof(f37,plain,(
% 3.09/0.99    ? [X0,X1] : ((k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0 | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0) & r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => ((k1_funct_1(k5_relat_1(k2_funct_1(sK6),sK6),sK5) != sK5 | k1_funct_1(sK6,k1_funct_1(k2_funct_1(sK6),sK5)) != sK5) & r2_hidden(sK5,k2_relat_1(sK6)) & v2_funct_1(sK6) & v1_funct_1(sK6) & v1_relat_1(sK6))),
% 3.09/0.99    introduced(choice_axiom,[])).
% 3.09/0.99  
% 3.09/0.99  fof(f38,plain,(
% 3.09/0.99    (k1_funct_1(k5_relat_1(k2_funct_1(sK6),sK6),sK5) != sK5 | k1_funct_1(sK6,k1_funct_1(k2_funct_1(sK6),sK5)) != sK5) & r2_hidden(sK5,k2_relat_1(sK6)) & v2_funct_1(sK6) & v1_funct_1(sK6) & v1_relat_1(sK6)),
% 3.09/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f24,f37])).
% 3.09/0.99  
% 3.09/0.99  fof(f58,plain,(
% 3.09/0.99    v1_funct_1(sK6)),
% 3.09/0.99    inference(cnf_transformation,[],[f38])).
% 3.09/0.99  
% 3.09/0.99  fof(f60,plain,(
% 3.09/0.99    r2_hidden(sK5,k2_relat_1(sK6))),
% 3.09/0.99    inference(cnf_transformation,[],[f38])).
% 3.09/0.99  
% 3.09/0.99  fof(f1,axiom,(
% 3.09/0.99    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 3.09/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.09/0.99  
% 3.09/0.99  fof(f25,plain,(
% 3.09/0.99    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 3.09/0.99    inference(nnf_transformation,[],[f1])).
% 3.09/0.99  
% 3.09/0.99  fof(f26,plain,(
% 3.09/0.99    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 3.09/0.99    inference(rectify,[],[f25])).
% 3.09/0.99  
% 3.09/0.99  fof(f29,plain,(
% 3.09/0.99    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK2(X0,X5),X5),X0))),
% 3.09/0.99    introduced(choice_axiom,[])).
% 3.09/0.99  
% 3.09/0.99  fof(f28,plain,(
% 3.09/0.99    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) => r2_hidden(k4_tarski(sK1(X0,X1),X2),X0))) )),
% 3.09/0.99    introduced(choice_axiom,[])).
% 3.09/0.99  
% 3.09/0.99  fof(f27,plain,(
% 3.09/0.99    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK0(X0,X1)),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK0(X0,X1)),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 3.09/0.99    introduced(choice_axiom,[])).
% 3.09/0.99  
% 3.09/0.99  fof(f30,plain,(
% 3.09/0.99    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK0(X0,X1)),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r2_hidden(k4_tarski(sK1(X0,X1),sK0(X0,X1)),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK2(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 3.09/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f29,f28,f27])).
% 3.09/0.99  
% 3.09/0.99  fof(f39,plain,(
% 3.09/0.99    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK2(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 3.09/0.99    inference(cnf_transformation,[],[f30])).
% 3.09/0.99  
% 3.09/0.99  fof(f63,plain,(
% 3.09/0.99    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK2(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 3.09/0.99    inference(equality_resolution,[],[f39])).
% 3.09/0.99  
% 3.09/0.99  fof(f8,axiom,(
% 3.09/0.99    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 3.09/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.09/0.99  
% 3.09/0.99  fof(f21,plain,(
% 3.09/0.99    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.09/0.99    inference(ennf_transformation,[],[f8])).
% 3.09/0.99  
% 3.09/0.99  fof(f22,plain,(
% 3.09/0.99    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.09/0.99    inference(flattening,[],[f21])).
% 3.09/0.99  
% 3.09/0.99  fof(f35,plain,(
% 3.09/0.99    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.09/0.99    inference(nnf_transformation,[],[f22])).
% 3.09/0.99  
% 3.09/0.99  fof(f36,plain,(
% 3.09/0.99    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.09/0.99    inference(flattening,[],[f35])).
% 3.09/0.99  
% 3.09/0.99  fof(f55,plain,(
% 3.09/0.99    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.09/0.99    inference(cnf_transformation,[],[f36])).
% 3.09/0.99  
% 3.09/0.99  fof(f57,plain,(
% 3.09/0.99    v1_relat_1(sK6)),
% 3.09/0.99    inference(cnf_transformation,[],[f38])).
% 3.09/0.99  
% 3.09/0.99  fof(f56,plain,(
% 3.09/0.99    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.09/0.99    inference(cnf_transformation,[],[f36])).
% 3.09/0.99  
% 3.09/0.99  fof(f66,plain,(
% 3.09/0.99    ( ! [X2,X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.09/0.99    inference(equality_resolution,[],[f56])).
% 3.09/0.99  
% 3.09/0.99  fof(f2,axiom,(
% 3.09/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (k4_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> r2_hidden(k4_tarski(X3,X2),X0)))))),
% 3.09/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.09/0.99  
% 3.09/0.99  fof(f11,plain,(
% 3.09/0.99    ! [X0] : (! [X1] : ((k4_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> r2_hidden(k4_tarski(X3,X2),X0))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.09/0.99    inference(ennf_transformation,[],[f2])).
% 3.09/0.99  
% 3.09/0.99  fof(f31,plain,(
% 3.09/0.99    ! [X0] : (! [X1] : (((k4_relat_1(X0) = X1 | ? [X2,X3] : ((~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X3,X2),X0)) & (r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X1))) | k4_relat_1(X0) != X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.09/0.99    inference(nnf_transformation,[],[f11])).
% 3.09/0.99  
% 3.09/0.99  fof(f32,plain,(
% 3.09/0.99    ! [X0] : (! [X1] : (((k4_relat_1(X0) = X1 | ? [X2,X3] : ((~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X5,X4),X0)) & (r2_hidden(k4_tarski(X5,X4),X0) | ~r2_hidden(k4_tarski(X4,X5),X1))) | k4_relat_1(X0) != X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.09/0.99    inference(rectify,[],[f31])).
% 3.09/0.99  
% 3.09/0.99  fof(f33,plain,(
% 3.09/0.99    ! [X1,X0] : (? [X2,X3] : ((~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(k4_tarski(X2,X3),X1))) => ((~r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0) | ~r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)) & (r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0) | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1))))),
% 3.09/0.99    introduced(choice_axiom,[])).
% 3.09/0.99  
% 3.09/0.99  fof(f34,plain,(
% 3.09/0.99    ! [X0] : (! [X1] : (((k4_relat_1(X0) = X1 | ((~r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0) | ~r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)) & (r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0) | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X5,X4),X0)) & (r2_hidden(k4_tarski(X5,X4),X0) | ~r2_hidden(k4_tarski(X4,X5),X1))) | k4_relat_1(X0) != X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.09/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f32,f33])).
% 3.09/0.99  
% 3.09/0.99  fof(f44,plain,(
% 3.09/0.99    ( ! [X4,X0,X5,X1] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X5,X4),X0) | k4_relat_1(X0) != X1 | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.09/0.99    inference(cnf_transformation,[],[f34])).
% 3.09/0.99  
% 3.09/0.99  fof(f64,plain,(
% 3.09/0.99    ( ! [X4,X0,X5] : (r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0)) | ~r2_hidden(k4_tarski(X5,X4),X0) | ~v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 3.09/0.99    inference(equality_resolution,[],[f44])).
% 3.09/0.99  
% 3.09/0.99  fof(f3,axiom,(
% 3.09/0.99    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 3.09/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.09/0.99  
% 3.09/0.99  fof(f12,plain,(
% 3.09/0.99    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.09/0.99    inference(ennf_transformation,[],[f3])).
% 3.09/0.99  
% 3.09/0.99  fof(f47,plain,(
% 3.09/0.99    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 3.09/0.99    inference(cnf_transformation,[],[f12])).
% 3.09/0.99  
% 3.09/0.99  fof(f4,axiom,(
% 3.09/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 3.09/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.09/0.99  
% 3.09/0.99  fof(f13,plain,(
% 3.09/0.99    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 3.09/0.99    inference(ennf_transformation,[],[f4])).
% 3.09/0.99  
% 3.09/0.99  fof(f14,plain,(
% 3.09/0.99    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 3.09/0.99    inference(flattening,[],[f13])).
% 3.09/0.99  
% 3.09/0.99  fof(f48,plain,(
% 3.09/0.99    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 3.09/0.99    inference(cnf_transformation,[],[f14])).
% 3.09/0.99  
% 3.09/0.99  fof(f7,axiom,(
% 3.09/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0))))),
% 3.09/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.09/0.99  
% 3.09/0.99  fof(f19,plain,(
% 3.09/0.99    ! [X0,X1] : (! [X2] : ((k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.09/0.99    inference(ennf_transformation,[],[f7])).
% 3.09/0.99  
% 3.09/0.99  fof(f20,plain,(
% 3.09/0.99    ! [X0,X1] : (! [X2] : (k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.09/0.99    inference(flattening,[],[f19])).
% 3.09/0.99  
% 3.09/0.99  fof(f53,plain,(
% 3.09/0.99    ( ! [X2,X0,X1] : (k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.09/0.99    inference(cnf_transformation,[],[f20])).
% 3.09/0.99  
% 3.09/0.99  fof(f5,axiom,(
% 3.09/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 3.09/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.09/0.99  
% 3.09/0.99  fof(f15,plain,(
% 3.09/0.99    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.09/0.99    inference(ennf_transformation,[],[f5])).
% 3.09/0.99  
% 3.09/0.99  fof(f16,plain,(
% 3.09/0.99    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.09/0.99    inference(flattening,[],[f15])).
% 3.09/0.99  
% 3.09/0.99  fof(f50,plain,(
% 3.09/0.99    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.09/0.99    inference(cnf_transformation,[],[f16])).
% 3.09/0.99  
% 3.09/0.99  fof(f59,plain,(
% 3.09/0.99    v2_funct_1(sK6)),
% 3.09/0.99    inference(cnf_transformation,[],[f38])).
% 3.09/0.99  
% 3.09/0.99  fof(f6,axiom,(
% 3.09/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.09/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.09/0.99  
% 3.09/0.99  fof(f17,plain,(
% 3.09/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.09/0.99    inference(ennf_transformation,[],[f6])).
% 3.09/0.99  
% 3.09/0.99  fof(f18,plain,(
% 3.09/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.09/0.99    inference(flattening,[],[f17])).
% 3.09/0.99  
% 3.09/0.99  fof(f52,plain,(
% 3.09/0.99    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.09/0.99    inference(cnf_transformation,[],[f18])).
% 3.09/0.99  
% 3.09/0.99  fof(f61,plain,(
% 3.09/0.99    k1_funct_1(k5_relat_1(k2_funct_1(sK6),sK6),sK5) != sK5 | k1_funct_1(sK6,k1_funct_1(k2_funct_1(sK6),sK5)) != sK5),
% 3.09/0.99    inference(cnf_transformation,[],[f38])).
% 3.09/0.99  
% 3.09/0.99  fof(f43,plain,(
% 3.09/0.99    ( ! [X4,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X4),X0) | ~r2_hidden(k4_tarski(X4,X5),X1) | k4_relat_1(X0) != X1 | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.09/0.99    inference(cnf_transformation,[],[f34])).
% 3.09/0.99  
% 3.09/0.99  fof(f65,plain,(
% 3.09/0.99    ( ! [X4,X0,X5] : (r2_hidden(k4_tarski(X5,X4),X0) | ~r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0)) | ~v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 3.09/1.00    inference(equality_resolution,[],[f43])).
% 3.09/1.00  
% 3.09/1.00  cnf(c_21,negated_conjecture,
% 3.09/1.00      ( v1_funct_1(sK6) ),
% 3.09/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_703,plain,
% 3.09/1.00      ( v1_funct_1(sK6) = iProver_top ),
% 3.09/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_19,negated_conjecture,
% 3.09/1.00      ( r2_hidden(sK5,k2_relat_1(sK6)) ),
% 3.09/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_704,plain,
% 3.09/1.00      ( r2_hidden(sK5,k2_relat_1(sK6)) = iProver_top ),
% 3.09/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_3,plain,
% 3.09/1.00      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 3.09/1.00      | r2_hidden(k4_tarski(sK2(X1,X0),X0),X1) ),
% 3.09/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_716,plain,
% 3.09/1.00      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 3.09/1.00      | r2_hidden(k4_tarski(sK2(X1,X0),X0),X1) = iProver_top ),
% 3.09/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_16,plain,
% 3.09/1.00      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 3.09/1.00      | ~ v1_funct_1(X2)
% 3.09/1.00      | ~ v1_relat_1(X2)
% 3.09/1.00      | k1_funct_1(X2,X0) = X1 ),
% 3.09/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_705,plain,
% 3.09/1.00      ( k1_funct_1(X0,X1) = X2
% 3.09/1.00      | r2_hidden(k4_tarski(X1,X2),X0) != iProver_top
% 3.09/1.00      | v1_funct_1(X0) != iProver_top
% 3.09/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.09/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_1299,plain,
% 3.09/1.00      ( k1_funct_1(X0,sK2(X0,X1)) = X1
% 3.09/1.00      | r2_hidden(X1,k2_relat_1(X0)) != iProver_top
% 3.09/1.00      | v1_funct_1(X0) != iProver_top
% 3.09/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.09/1.00      inference(superposition,[status(thm)],[c_716,c_705]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_2893,plain,
% 3.09/1.00      ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK5
% 3.09/1.00      | v1_funct_1(sK6) != iProver_top
% 3.09/1.00      | v1_relat_1(sK6) != iProver_top ),
% 3.09/1.00      inference(superposition,[status(thm)],[c_704,c_1299]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_22,negated_conjecture,
% 3.09/1.00      ( v1_relat_1(sK6) ),
% 3.09/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_886,plain,
% 3.09/1.00      ( r2_hidden(k4_tarski(sK2(sK6,sK5),sK5),sK6)
% 3.09/1.00      | ~ r2_hidden(sK5,k2_relat_1(sK6)) ),
% 3.09/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_905,plain,
% 3.09/1.00      ( ~ r2_hidden(k4_tarski(sK2(sK6,sK5),sK5),sK6)
% 3.09/1.00      | ~ v1_funct_1(sK6)
% 3.09/1.00      | ~ v1_relat_1(sK6)
% 3.09/1.00      | k1_funct_1(sK6,sK2(sK6,sK5)) = sK5 ),
% 3.09/1.00      inference(instantiation,[status(thm)],[c_16]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_3075,plain,
% 3.09/1.00      ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK5 ),
% 3.09/1.00      inference(global_propositional_subsumption,
% 3.09/1.00                [status(thm)],
% 3.09/1.00                [c_2893,c_22,c_21,c_19,c_886,c_905]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_15,plain,
% 3.09/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.09/1.00      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 3.09/1.00      | ~ v1_funct_1(X1)
% 3.09/1.00      | ~ v1_relat_1(X1) ),
% 3.09/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_706,plain,
% 3.09/1.00      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 3.09/1.00      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1) = iProver_top
% 3.09/1.00      | v1_funct_1(X1) != iProver_top
% 3.09/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.09/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_3078,plain,
% 3.09/1.00      ( r2_hidden(sK2(sK6,sK5),k1_relat_1(sK6)) != iProver_top
% 3.09/1.00      | r2_hidden(k4_tarski(sK2(sK6,sK5),sK5),sK6) = iProver_top
% 3.09/1.00      | v1_funct_1(sK6) != iProver_top
% 3.09/1.00      | v1_relat_1(sK6) != iProver_top ),
% 3.09/1.00      inference(superposition,[status(thm)],[c_3075,c_706]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_26,plain,
% 3.09/1.00      ( r2_hidden(sK5,k2_relat_1(sK6)) = iProver_top ),
% 3.09/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_887,plain,
% 3.09/1.00      ( r2_hidden(k4_tarski(sK2(sK6,sK5),sK5),sK6) = iProver_top
% 3.09/1.00      | r2_hidden(sK5,k2_relat_1(sK6)) != iProver_top ),
% 3.09/1.00      inference(predicate_to_equality,[status(thm)],[c_886]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_3081,plain,
% 3.09/1.00      ( r2_hidden(k4_tarski(sK2(sK6,sK5),sK5),sK6) = iProver_top ),
% 3.09/1.00      inference(global_propositional_subsumption,
% 3.09/1.00                [status(thm)],
% 3.09/1.00                [c_3078,c_26,c_887]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_6,plain,
% 3.09/1.00      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 3.09/1.00      | r2_hidden(k4_tarski(X1,X0),k4_relat_1(X2))
% 3.09/1.00      | ~ v1_relat_1(X2)
% 3.09/1.00      | ~ v1_relat_1(k4_relat_1(X2)) ),
% 3.09/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_713,plain,
% 3.09/1.00      ( r2_hidden(k4_tarski(X0,X1),X2) != iProver_top
% 3.09/1.00      | r2_hidden(k4_tarski(X1,X0),k4_relat_1(X2)) = iProver_top
% 3.09/1.00      | v1_relat_1(X2) != iProver_top
% 3.09/1.00      | v1_relat_1(k4_relat_1(X2)) != iProver_top ),
% 3.09/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_8,plain,
% 3.09/1.00      ( ~ v1_relat_1(X0) | v1_relat_1(k4_relat_1(X0)) ),
% 3.09/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_711,plain,
% 3.09/1.00      ( v1_relat_1(X0) != iProver_top
% 3.09/1.00      | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
% 3.09/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_803,plain,
% 3.09/1.00      ( r2_hidden(k4_tarski(X0,X1),X2) != iProver_top
% 3.09/1.00      | r2_hidden(k4_tarski(X1,X0),k4_relat_1(X2)) = iProver_top
% 3.09/1.00      | v1_relat_1(X2) != iProver_top ),
% 3.09/1.00      inference(forward_subsumption_resolution,
% 3.09/1.00                [status(thm)],
% 3.09/1.00                [c_713,c_711]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_10,plain,
% 3.09/1.00      ( r2_hidden(X0,k1_relat_1(X1))
% 3.09/1.00      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 3.09/1.00      | ~ v1_relat_1(X1) ),
% 3.09/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_710,plain,
% 3.09/1.00      ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
% 3.09/1.00      | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top
% 3.09/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.09/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_1797,plain,
% 3.09/1.00      ( r2_hidden(X0,k1_relat_1(k4_relat_1(X1))) = iProver_top
% 3.09/1.00      | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top
% 3.09/1.00      | v1_relat_1(X1) != iProver_top
% 3.09/1.00      | v1_relat_1(k4_relat_1(X1)) != iProver_top ),
% 3.09/1.00      inference(superposition,[status(thm)],[c_803,c_710]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_5546,plain,
% 3.09/1.00      ( r2_hidden(X0,k1_relat_1(k4_relat_1(X1))) = iProver_top
% 3.09/1.00      | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top
% 3.09/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.09/1.00      inference(forward_subsumption_resolution,
% 3.09/1.00                [status(thm)],
% 3.09/1.00                [c_1797,c_711]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_5556,plain,
% 3.09/1.00      ( r2_hidden(sK5,k1_relat_1(k4_relat_1(sK6))) = iProver_top
% 3.09/1.00      | v1_relat_1(sK6) != iProver_top ),
% 3.09/1.00      inference(superposition,[status(thm)],[c_3081,c_5546]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_23,plain,
% 3.09/1.00      ( v1_relat_1(sK6) = iProver_top ),
% 3.09/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_54,plain,
% 3.09/1.00      ( v1_relat_1(X0) != iProver_top
% 3.09/1.00      | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
% 3.09/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_56,plain,
% 3.09/1.00      ( v1_relat_1(k4_relat_1(sK6)) = iProver_top
% 3.09/1.00      | v1_relat_1(sK6) != iProver_top ),
% 3.09/1.00      inference(instantiation,[status(thm)],[c_54]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_906,plain,
% 3.09/1.00      ( ~ r2_hidden(k4_tarski(sK2(sK6,sK5),sK5),sK6)
% 3.09/1.00      | r2_hidden(k4_tarski(sK5,sK2(sK6,sK5)),k4_relat_1(sK6))
% 3.09/1.00      | ~ v1_relat_1(k4_relat_1(sK6))
% 3.09/1.00      | ~ v1_relat_1(sK6) ),
% 3.09/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_907,plain,
% 3.09/1.00      ( r2_hidden(k4_tarski(sK2(sK6,sK5),sK5),sK6) != iProver_top
% 3.09/1.00      | r2_hidden(k4_tarski(sK5,sK2(sK6,sK5)),k4_relat_1(sK6)) = iProver_top
% 3.09/1.00      | v1_relat_1(k4_relat_1(sK6)) != iProver_top
% 3.09/1.00      | v1_relat_1(sK6) != iProver_top ),
% 3.09/1.00      inference(predicate_to_equality,[status(thm)],[c_906]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_972,plain,
% 3.09/1.00      ( ~ r2_hidden(k4_tarski(sK5,sK2(sK6,sK5)),k4_relat_1(sK6))
% 3.09/1.00      | r2_hidden(sK5,k1_relat_1(k4_relat_1(sK6)))
% 3.09/1.00      | ~ v1_relat_1(k4_relat_1(sK6)) ),
% 3.09/1.00      inference(instantiation,[status(thm)],[c_10]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_973,plain,
% 3.09/1.00      ( r2_hidden(k4_tarski(sK5,sK2(sK6,sK5)),k4_relat_1(sK6)) != iProver_top
% 3.09/1.00      | r2_hidden(sK5,k1_relat_1(k4_relat_1(sK6))) = iProver_top
% 3.09/1.00      | v1_relat_1(k4_relat_1(sK6)) != iProver_top ),
% 3.09/1.00      inference(predicate_to_equality,[status(thm)],[c_972]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_5834,plain,
% 3.09/1.00      ( r2_hidden(sK5,k1_relat_1(k4_relat_1(sK6))) = iProver_top ),
% 3.09/1.00      inference(global_propositional_subsumption,
% 3.09/1.00                [status(thm)],
% 3.09/1.00                [c_5556,c_23,c_26,c_56,c_887,c_907,c_973]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_14,plain,
% 3.09/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.09/1.00      | ~ v1_funct_1(X2)
% 3.09/1.00      | ~ v1_funct_1(X1)
% 3.09/1.00      | ~ v1_relat_1(X1)
% 3.09/1.00      | ~ v1_relat_1(X2)
% 3.09/1.00      | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ),
% 3.09/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_707,plain,
% 3.09/1.00      ( k1_funct_1(k5_relat_1(X0,X1),X2) = k1_funct_1(X1,k1_funct_1(X0,X2))
% 3.09/1.00      | r2_hidden(X2,k1_relat_1(X0)) != iProver_top
% 3.09/1.00      | v1_funct_1(X0) != iProver_top
% 3.09/1.00      | v1_funct_1(X1) != iProver_top
% 3.09/1.00      | v1_relat_1(X0) != iProver_top
% 3.09/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.09/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_5839,plain,
% 3.09/1.00      ( k1_funct_1(X0,k1_funct_1(k4_relat_1(sK6),sK5)) = k1_funct_1(k5_relat_1(k4_relat_1(sK6),X0),sK5)
% 3.09/1.00      | v1_funct_1(X0) != iProver_top
% 3.09/1.00      | v1_funct_1(k4_relat_1(sK6)) != iProver_top
% 3.09/1.00      | v1_relat_1(X0) != iProver_top
% 3.09/1.00      | v1_relat_1(k4_relat_1(sK6)) != iProver_top ),
% 3.09/1.00      inference(superposition,[status(thm)],[c_5834,c_707]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_24,plain,
% 3.09/1.00      ( v1_funct_1(sK6) = iProver_top ),
% 3.09/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_11,plain,
% 3.09/1.00      ( ~ v1_funct_1(X0)
% 3.09/1.00      | ~ v2_funct_1(X0)
% 3.09/1.00      | ~ v1_relat_1(X0)
% 3.09/1.00      | k2_funct_1(X0) = k4_relat_1(X0) ),
% 3.09/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_20,negated_conjecture,
% 3.09/1.00      ( v2_funct_1(sK6) ),
% 3.09/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_250,plain,
% 3.09/1.00      ( ~ v1_funct_1(X0)
% 3.09/1.00      | ~ v1_relat_1(X0)
% 3.09/1.00      | k2_funct_1(X0) = k4_relat_1(X0)
% 3.09/1.00      | sK6 != X0 ),
% 3.09/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_20]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_251,plain,
% 3.09/1.00      ( ~ v1_funct_1(sK6)
% 3.09/1.00      | ~ v1_relat_1(sK6)
% 3.09/1.00      | k2_funct_1(sK6) = k4_relat_1(sK6) ),
% 3.09/1.00      inference(unflattening,[status(thm)],[c_250]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_46,plain,
% 3.09/1.00      ( ~ v1_funct_1(sK6)
% 3.09/1.00      | ~ v2_funct_1(sK6)
% 3.09/1.00      | ~ v1_relat_1(sK6)
% 3.09/1.00      | k2_funct_1(sK6) = k4_relat_1(sK6) ),
% 3.09/1.00      inference(instantiation,[status(thm)],[c_11]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_253,plain,
% 3.09/1.00      ( k2_funct_1(sK6) = k4_relat_1(sK6) ),
% 3.09/1.00      inference(global_propositional_subsumption,
% 3.09/1.00                [status(thm)],
% 3.09/1.00                [c_251,c_22,c_21,c_20,c_46]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_12,plain,
% 3.09/1.00      ( ~ v1_funct_1(X0)
% 3.09/1.00      | v1_funct_1(k2_funct_1(X0))
% 3.09/1.00      | ~ v1_relat_1(X0) ),
% 3.09/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_709,plain,
% 3.09/1.00      ( v1_funct_1(X0) != iProver_top
% 3.09/1.00      | v1_funct_1(k2_funct_1(X0)) = iProver_top
% 3.09/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.09/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_1193,plain,
% 3.09/1.00      ( v1_funct_1(k4_relat_1(sK6)) = iProver_top
% 3.09/1.00      | v1_funct_1(sK6) != iProver_top
% 3.09/1.00      | v1_relat_1(sK6) != iProver_top ),
% 3.09/1.00      inference(superposition,[status(thm)],[c_253,c_709]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_7139,plain,
% 3.09/1.00      ( v1_relat_1(X0) != iProver_top
% 3.09/1.00      | k1_funct_1(X0,k1_funct_1(k4_relat_1(sK6),sK5)) = k1_funct_1(k5_relat_1(k4_relat_1(sK6),X0),sK5)
% 3.09/1.00      | v1_funct_1(X0) != iProver_top ),
% 3.09/1.00      inference(global_propositional_subsumption,
% 3.09/1.00                [status(thm)],
% 3.09/1.00                [c_5839,c_23,c_24,c_56,c_1193]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_7140,plain,
% 3.09/1.00      ( k1_funct_1(X0,k1_funct_1(k4_relat_1(sK6),sK5)) = k1_funct_1(k5_relat_1(k4_relat_1(sK6),X0),sK5)
% 3.09/1.00      | v1_funct_1(X0) != iProver_top
% 3.09/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.09/1.00      inference(renaming,[status(thm)],[c_7139]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_7149,plain,
% 3.09/1.00      ( k1_funct_1(sK6,k1_funct_1(k4_relat_1(sK6),sK5)) = k1_funct_1(k5_relat_1(k4_relat_1(sK6),sK6),sK5)
% 3.09/1.00      | v1_relat_1(sK6) != iProver_top ),
% 3.09/1.00      inference(superposition,[status(thm)],[c_703,c_7140]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_5841,plain,
% 3.09/1.00      ( k1_funct_1(sK6,k1_funct_1(k4_relat_1(sK6),sK5)) = k1_funct_1(k5_relat_1(k4_relat_1(sK6),sK6),sK5)
% 3.09/1.00      | v1_funct_1(k4_relat_1(sK6)) != iProver_top
% 3.09/1.00      | v1_funct_1(sK6) != iProver_top
% 3.09/1.00      | v1_relat_1(k4_relat_1(sK6)) != iProver_top
% 3.09/1.00      | v1_relat_1(sK6) != iProver_top ),
% 3.09/1.00      inference(instantiation,[status(thm)],[c_5839]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_7173,plain,
% 3.09/1.00      ( k1_funct_1(sK6,k1_funct_1(k4_relat_1(sK6),sK5)) = k1_funct_1(k5_relat_1(k4_relat_1(sK6),sK6),sK5) ),
% 3.09/1.00      inference(global_propositional_subsumption,
% 3.09/1.00                [status(thm)],
% 3.09/1.00                [c_7149,c_23,c_24,c_56,c_1193,c_5841]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_18,negated_conjecture,
% 3.09/1.00      ( k1_funct_1(k5_relat_1(k2_funct_1(sK6),sK6),sK5) != sK5
% 3.09/1.00      | k1_funct_1(sK6,k1_funct_1(k2_funct_1(sK6),sK5)) != sK5 ),
% 3.09/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_752,plain,
% 3.09/1.00      ( k1_funct_1(k5_relat_1(k4_relat_1(sK6),sK6),sK5) != sK5
% 3.09/1.00      | k1_funct_1(sK6,k1_funct_1(k4_relat_1(sK6),sK5)) != sK5 ),
% 3.09/1.00      inference(light_normalisation,[status(thm)],[c_18,c_253]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_7176,plain,
% 3.09/1.00      ( k1_funct_1(sK6,k1_funct_1(k4_relat_1(sK6),sK5)) != sK5 ),
% 3.09/1.00      inference(demodulation,[status(thm)],[c_7173,c_752]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_6866,plain,
% 3.09/1.00      ( ~ r2_hidden(k4_tarski(k1_funct_1(k4_relat_1(sK6),sK5),sK5),X0)
% 3.09/1.00      | ~ v1_funct_1(X0)
% 3.09/1.00      | ~ v1_relat_1(X0)
% 3.09/1.00      | k1_funct_1(X0,k1_funct_1(k4_relat_1(sK6),sK5)) = sK5 ),
% 3.09/1.00      inference(instantiation,[status(thm)],[c_16]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_6873,plain,
% 3.09/1.00      ( ~ r2_hidden(k4_tarski(k1_funct_1(k4_relat_1(sK6),sK5),sK5),sK6)
% 3.09/1.00      | ~ v1_funct_1(sK6)
% 3.09/1.00      | ~ v1_relat_1(sK6)
% 3.09/1.00      | k1_funct_1(sK6,k1_funct_1(k4_relat_1(sK6),sK5)) = sK5 ),
% 3.09/1.00      inference(instantiation,[status(thm)],[c_6866]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_7,plain,
% 3.09/1.00      ( r2_hidden(k4_tarski(X0,X1),X2)
% 3.09/1.00      | ~ r2_hidden(k4_tarski(X1,X0),k4_relat_1(X2))
% 3.09/1.00      | ~ v1_relat_1(X2)
% 3.09/1.00      | ~ v1_relat_1(k4_relat_1(X2)) ),
% 3.09/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_1998,plain,
% 3.09/1.00      ( r2_hidden(k4_tarski(k1_funct_1(k4_relat_1(sK6),sK5),sK5),sK6)
% 3.09/1.00      | ~ r2_hidden(k4_tarski(sK5,k1_funct_1(k4_relat_1(sK6),sK5)),k4_relat_1(sK6))
% 3.09/1.00      | ~ v1_relat_1(k4_relat_1(sK6))
% 3.09/1.00      | ~ v1_relat_1(sK6) ),
% 3.09/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_1011,plain,
% 3.09/1.00      ( r2_hidden(k4_tarski(sK5,k1_funct_1(X0,sK5)),X0)
% 3.09/1.00      | ~ r2_hidden(sK5,k1_relat_1(X0))
% 3.09/1.00      | ~ v1_funct_1(X0)
% 3.09/1.00      | ~ v1_relat_1(X0) ),
% 3.09/1.00      inference(instantiation,[status(thm)],[c_15]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_1474,plain,
% 3.09/1.00      ( r2_hidden(k4_tarski(sK5,k1_funct_1(k4_relat_1(sK6),sK5)),k4_relat_1(sK6))
% 3.09/1.00      | ~ r2_hidden(sK5,k1_relat_1(k4_relat_1(sK6)))
% 3.09/1.00      | ~ v1_funct_1(k4_relat_1(sK6))
% 3.09/1.00      | ~ v1_relat_1(k4_relat_1(sK6)) ),
% 3.09/1.00      inference(instantiation,[status(thm)],[c_1011]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_1194,plain,
% 3.09/1.00      ( v1_funct_1(k4_relat_1(sK6))
% 3.09/1.00      | ~ v1_funct_1(sK6)
% 3.09/1.00      | ~ v1_relat_1(sK6) ),
% 3.09/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1193]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_55,plain,
% 3.09/1.00      ( v1_relat_1(k4_relat_1(sK6)) | ~ v1_relat_1(sK6) ),
% 3.09/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(contradiction,plain,
% 3.09/1.00      ( $false ),
% 3.09/1.00      inference(minisat,
% 3.09/1.00                [status(thm)],
% 3.09/1.00                [c_7176,c_6873,c_1998,c_1474,c_1194,c_972,c_906,c_886,
% 3.09/1.00                 c_55,c_19,c_21,c_22]) ).
% 3.09/1.00  
% 3.09/1.00  
% 3.09/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.09/1.00  
% 3.09/1.00  ------                               Statistics
% 3.09/1.00  
% 3.09/1.00  ------ General
% 3.09/1.00  
% 3.09/1.00  abstr_ref_over_cycles:                  0
% 3.09/1.00  abstr_ref_under_cycles:                 0
% 3.09/1.00  gc_basic_clause_elim:                   0
% 3.09/1.00  forced_gc_time:                         0
% 3.09/1.00  parsing_time:                           0.008
% 3.09/1.00  unif_index_cands_time:                  0.
% 3.09/1.00  unif_index_add_time:                    0.
% 3.09/1.00  orderings_time:                         0.
% 3.09/1.00  out_proof_time:                         0.01
% 3.09/1.00  total_time:                             0.254
% 3.09/1.00  num_of_symbols:                         49
% 3.09/1.00  num_of_terms:                           8252
% 3.09/1.00  
% 3.09/1.00  ------ Preprocessing
% 3.09/1.00  
% 3.09/1.00  num_of_splits:                          0
% 3.09/1.00  num_of_split_atoms:                     0
% 3.09/1.00  num_of_reused_defs:                     0
% 3.09/1.00  num_eq_ax_congr_red:                    34
% 3.09/1.00  num_of_sem_filtered_clauses:            1
% 3.09/1.00  num_of_subtypes:                        0
% 3.09/1.00  monotx_restored_types:                  0
% 3.09/1.00  sat_num_of_epr_types:                   0
% 3.09/1.00  sat_num_of_non_cyclic_types:            0
% 3.09/1.00  sat_guarded_non_collapsed_types:        0
% 3.09/1.00  num_pure_diseq_elim:                    0
% 3.09/1.00  simp_replaced_by:                       0
% 3.09/1.00  res_preprocessed:                       104
% 3.09/1.00  prep_upred:                             0
% 3.09/1.00  prep_unflattend:                        1
% 3.09/1.00  smt_new_axioms:                         0
% 3.09/1.00  pred_elim_cands:                        3
% 3.09/1.00  pred_elim:                              1
% 3.09/1.00  pred_elim_cl:                           1
% 3.09/1.00  pred_elim_cycles:                       3
% 3.09/1.00  merged_defs:                            0
% 3.09/1.00  merged_defs_ncl:                        0
% 3.09/1.00  bin_hyper_res:                          0
% 3.09/1.00  prep_cycles:                            4
% 3.09/1.00  pred_elim_time:                         0.001
% 3.09/1.00  splitting_time:                         0.
% 3.09/1.00  sem_filter_time:                        0.
% 3.09/1.00  monotx_time:                            0.
% 3.09/1.00  subtype_inf_time:                       0.
% 3.09/1.00  
% 3.09/1.00  ------ Problem properties
% 3.09/1.00  
% 3.09/1.00  clauses:                                20
% 3.09/1.00  conjectures:                            4
% 3.09/1.00  epr:                                    2
% 3.09/1.00  horn:                                   18
% 3.09/1.00  ground:                                 5
% 3.09/1.00  unary:                                  4
% 3.09/1.00  binary:                                 4
% 3.09/1.00  lits:                                   59
% 3.09/1.00  lits_eq:                                9
% 3.09/1.00  fd_pure:                                0
% 3.09/1.00  fd_pseudo:                              0
% 3.09/1.00  fd_cond:                                0
% 3.09/1.00  fd_pseudo_cond:                         5
% 3.09/1.00  ac_symbols:                             0
% 3.09/1.00  
% 3.09/1.00  ------ Propositional Solver
% 3.09/1.00  
% 3.09/1.00  prop_solver_calls:                      27
% 3.09/1.00  prop_fast_solver_calls:                 859
% 3.09/1.00  smt_solver_calls:                       0
% 3.09/1.00  smt_fast_solver_calls:                  0
% 3.09/1.00  prop_num_of_clauses:                    2735
% 3.09/1.00  prop_preprocess_simplified:             6527
% 3.09/1.00  prop_fo_subsumed:                       27
% 3.09/1.00  prop_solver_time:                       0.
% 3.09/1.00  smt_solver_time:                        0.
% 3.09/1.00  smt_fast_solver_time:                   0.
% 3.09/1.00  prop_fast_solver_time:                  0.
% 3.09/1.00  prop_unsat_core_time:                   0.
% 3.09/1.00  
% 3.09/1.00  ------ QBF
% 3.09/1.00  
% 3.09/1.00  qbf_q_res:                              0
% 3.09/1.00  qbf_num_tautologies:                    0
% 3.09/1.00  qbf_prep_cycles:                        0
% 3.09/1.00  
% 3.09/1.00  ------ BMC1
% 3.09/1.00  
% 3.09/1.00  bmc1_current_bound:                     -1
% 3.09/1.00  bmc1_last_solved_bound:                 -1
% 3.09/1.00  bmc1_unsat_core_size:                   -1
% 3.09/1.00  bmc1_unsat_core_parents_size:           -1
% 3.09/1.00  bmc1_merge_next_fun:                    0
% 3.09/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.09/1.00  
% 3.09/1.00  ------ Instantiation
% 3.09/1.00  
% 3.09/1.00  inst_num_of_clauses:                    728
% 3.09/1.00  inst_num_in_passive:                    310
% 3.09/1.00  inst_num_in_active:                     289
% 3.09/1.00  inst_num_in_unprocessed:                129
% 3.09/1.00  inst_num_of_loops:                      340
% 3.09/1.00  inst_num_of_learning_restarts:          0
% 3.09/1.00  inst_num_moves_active_passive:          48
% 3.09/1.00  inst_lit_activity:                      0
% 3.09/1.00  inst_lit_activity_moves:                0
% 3.09/1.00  inst_num_tautologies:                   0
% 3.09/1.00  inst_num_prop_implied:                  0
% 3.09/1.00  inst_num_existing_simplified:           0
% 3.09/1.00  inst_num_eq_res_simplified:             0
% 3.09/1.00  inst_num_child_elim:                    0
% 3.09/1.00  inst_num_of_dismatching_blockings:      278
% 3.09/1.00  inst_num_of_non_proper_insts:           564
% 3.09/1.00  inst_num_of_duplicates:                 0
% 3.09/1.00  inst_inst_num_from_inst_to_res:         0
% 3.09/1.00  inst_dismatching_checking_time:         0.
% 3.09/1.00  
% 3.09/1.00  ------ Resolution
% 3.09/1.00  
% 3.09/1.00  res_num_of_clauses:                     0
% 3.09/1.00  res_num_in_passive:                     0
% 3.09/1.00  res_num_in_active:                      0
% 3.09/1.00  res_num_of_loops:                       108
% 3.09/1.00  res_forward_subset_subsumed:            31
% 3.09/1.00  res_backward_subset_subsumed:           0
% 3.09/1.00  res_forward_subsumed:                   0
% 3.09/1.00  res_backward_subsumed:                  0
% 3.09/1.00  res_forward_subsumption_resolution:     0
% 3.09/1.00  res_backward_subsumption_resolution:    0
% 3.09/1.00  res_clause_to_clause_subsumption:       567
% 3.09/1.00  res_orphan_elimination:                 0
% 3.09/1.00  res_tautology_del:                      46
% 3.09/1.00  res_num_eq_res_simplified:              0
% 3.09/1.00  res_num_sel_changes:                    0
% 3.09/1.00  res_moves_from_active_to_pass:          0
% 3.09/1.00  
% 3.09/1.00  ------ Superposition
% 3.09/1.00  
% 3.09/1.00  sup_time_total:                         0.
% 3.09/1.00  sup_time_generating:                    0.
% 3.09/1.00  sup_time_sim_full:                      0.
% 3.09/1.00  sup_time_sim_immed:                     0.
% 3.09/1.00  
% 3.09/1.00  sup_num_of_clauses:                     217
% 3.09/1.00  sup_num_in_active:                      66
% 3.09/1.00  sup_num_in_passive:                     151
% 3.09/1.00  sup_num_of_loops:                       67
% 3.09/1.00  sup_fw_superposition:                   93
% 3.09/1.00  sup_bw_superposition:                   145
% 3.09/1.00  sup_immediate_simplified:               15
% 3.09/1.00  sup_given_eliminated:                   0
% 3.09/1.00  comparisons_done:                       0
% 3.09/1.00  comparisons_avoided:                    2
% 3.09/1.00  
% 3.09/1.00  ------ Simplifications
% 3.09/1.00  
% 3.09/1.00  
% 3.09/1.00  sim_fw_subset_subsumed:                 6
% 3.09/1.00  sim_bw_subset_subsumed:                 0
% 3.09/1.00  sim_fw_subsumed:                        6
% 3.09/1.00  sim_bw_subsumed:                        0
% 3.09/1.00  sim_fw_subsumption_res:                 3
% 3.09/1.00  sim_bw_subsumption_res:                 0
% 3.09/1.00  sim_tautology_del:                      13
% 3.09/1.00  sim_eq_tautology_del:                   7
% 3.09/1.00  sim_eq_res_simp:                        0
% 3.09/1.00  sim_fw_demodulated:                     0
% 3.09/1.00  sim_bw_demodulated:                     1
% 3.09/1.00  sim_light_normalised:                   4
% 3.09/1.00  sim_joinable_taut:                      0
% 3.09/1.00  sim_joinable_simp:                      0
% 3.09/1.00  sim_ac_normalised:                      0
% 3.09/1.00  sim_smt_subsumption:                    0
% 3.09/1.00  
%------------------------------------------------------------------------------
