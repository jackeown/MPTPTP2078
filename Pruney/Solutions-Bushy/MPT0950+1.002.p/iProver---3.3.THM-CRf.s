%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0950+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:29 EST 2020

% Result     : Theorem 7.36s
% Output     : CNFRefutation 7.36s
% Verified   : 
% Statistics : Number of formulae       :  187 (2695 expanded)
%              Number of clauses        :  116 ( 997 expanded)
%              Number of leaves         :   20 ( 508 expanded)
%              Depth                    :   34
%              Number of atoms          :  657 (9850 expanded)
%              Number of equality atoms :  288 (2285 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   17 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,conjecture,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ( r1_tarski(X0,X1)
       => r1_ordinal1(k2_wellord2(k1_wellord2(X0)),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v3_ordinal1(X1)
       => ( r1_tarski(X0,X1)
         => r1_ordinal1(k2_wellord2(k1_wellord2(X0)),X1) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f49,plain,(
    ? [X0,X1] :
      ( ~ r1_ordinal1(k2_wellord2(k1_wellord2(X0)),X1)
      & r1_tarski(X0,X1)
      & v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f50,plain,(
    ? [X0,X1] :
      ( ~ r1_ordinal1(k2_wellord2(k1_wellord2(X0)),X1)
      & r1_tarski(X0,X1)
      & v3_ordinal1(X1) ) ),
    inference(flattening,[],[f49])).

fof(f61,plain,
    ( ? [X0,X1] :
        ( ~ r1_ordinal1(k2_wellord2(k1_wellord2(X0)),X1)
        & r1_tarski(X0,X1)
        & v3_ordinal1(X1) )
   => ( ~ r1_ordinal1(k2_wellord2(k1_wellord2(sK3)),sK4)
      & r1_tarski(sK3,sK4)
      & v3_ordinal1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,
    ( ~ r1_ordinal1(k2_wellord2(k1_wellord2(sK3)),sK4)
    & r1_tarski(sK3,sK4)
    & v3_ordinal1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f50,f61])).

fof(f93,plain,(
    r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f62])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
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

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f51,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f52,plain,(
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
    inference(flattening,[],[f51])).

fof(f53,plain,(
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
    inference(rectify,[],[f52])).

fof(f54,plain,(
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

fof(f55,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f53,f54])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f101,plain,(
    ! [X0] :
      ( k3_relat_1(k1_wellord2(X0)) = X0
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f66])).

fof(f7,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( ! [X2] :
              ~ ( r4_wellord1(k2_wellord1(X1,k1_wellord1(X1,X2)),k2_wellord1(X1,X0))
                & r2_hidden(X2,k3_relat_1(X1)) )
          & ~ r4_wellord1(X1,k2_wellord1(X1,X0))
          & v2_wellord1(X1)
          & r1_tarski(X0,k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r4_wellord1(k2_wellord1(X1,k1_wellord1(X1,X2)),k2_wellord1(X1,X0))
          & r2_hidden(X2,k3_relat_1(X1)) )
      | r4_wellord1(X1,k2_wellord1(X1,X0))
      | ~ v2_wellord1(X1)
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r4_wellord1(k2_wellord1(X1,k1_wellord1(X1,X2)),k2_wellord1(X1,X0))
          & r2_hidden(X2,k3_relat_1(X1)) )
      | r4_wellord1(X1,k2_wellord1(X1,X0))
      | ~ v2_wellord1(X1)
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f43])).

fof(f59,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r4_wellord1(k2_wellord1(X1,k1_wellord1(X1,X2)),k2_wellord1(X1,X0))
          & r2_hidden(X2,k3_relat_1(X1)) )
     => ( r4_wellord1(k2_wellord1(X1,k1_wellord1(X1,sK2(X0,X1))),k2_wellord1(X1,X0))
        & r2_hidden(sK2(X0,X1),k3_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( r4_wellord1(k2_wellord1(X1,k1_wellord1(X1,sK2(X0,X1))),k2_wellord1(X1,X0))
        & r2_hidden(sK2(X0,X1),k3_relat_1(X1)) )
      | r4_wellord1(X1,k2_wellord1(X1,X0))
      | ~ v2_wellord1(X1)
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f44,f59])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),k3_relat_1(X1))
      | r4_wellord1(X1,k2_wellord1(X1,X0))
      | ~ v2_wellord1(X1)
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f92,plain,(
    v3_ordinal1(sK4) ),
    inference(cnf_transformation,[],[f62])).

fof(f19,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( r1_tarski(X1,X0)
         => v2_wellord1(k1_wellord2(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_wellord1(k1_wellord2(X1))
          | ~ r1_tarski(X1,X0) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f91,plain,(
    ! [X0,X1] :
      ( v2_wellord1(k1_wellord2(X1))
      | ~ r1_tarski(X1,X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X1,X0)
        | r1_ordinal1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f10,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
           => k1_wellord1(k1_wellord2(X1),X0) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k1_wellord1(k1_wellord2(X1),X0) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f81,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f2,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => v3_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_ordinal1(X1)
          | ~ m1_subset_1(X1,X0) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
      | ~ m1_subset_1(X1,X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r4_wellord1(X0,X1)
           => r4_wellord1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f41])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r4_wellord1(X1,X0)
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f94,plain,(
    ~ r1_ordinal1(k2_wellord2(k1_wellord2(sK3)),sK4) ),
    inference(cnf_transformation,[],[f62])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( k2_wellord2(X0) = X1
            <=> r4_wellord1(X0,k1_wellord2(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_wellord2(X0) = X1
          <=> r4_wellord1(X0,k1_wellord2(X1)) )
          | ~ v3_ordinal1(X1) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_wellord2(X0) = X1
          <=> r4_wellord1(X0,k1_wellord2(X1)) )
          | ~ v3_ordinal1(X1) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k2_wellord2(X0) = X1
              | ~ r4_wellord1(X0,k1_wellord2(X1)) )
            & ( r4_wellord1(X0,k1_wellord2(X1))
              | k2_wellord2(X0) != X1 ) )
          | ~ v3_ordinal1(X1) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k2_wellord2(X0) = X1
      | ~ r4_wellord1(X0,k1_wellord2(X1))
      | ~ v3_ordinal1(X1)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r4_wellord1(k2_wellord1(X1,k1_wellord1(X1,sK2(X0,X1))),k2_wellord1(X1,X0))
      | r4_wellord1(X1,k2_wellord1(X1,X0))
      | ~ v2_wellord1(X1)
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f1,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v1_ordinal1(X0) ) ),
    inference(pure_predicate_removal,[],[f1])).

fof(f24,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f63,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) )
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | ~ r2_hidden(X1,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_30,negated_conjecture,
    ( r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_3900,plain,
    ( r1_tarski(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_27,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_3903,plain,
    ( k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_4283,plain,
    ( k2_wellord1(k1_wellord2(sK4),sK3) = k1_wellord2(sK3) ),
    inference(superposition,[status(thm)],[c_3900,c_3903])).

cnf(c_9,plain,
    ( ~ v1_relat_1(k1_wellord2(X0))
    | k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_13,plain,
    ( v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_215,plain,
    ( k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9,c_13])).

cnf(c_24,plain,
    ( r4_wellord1(X0,k2_wellord1(X0,X1))
    | r2_hidden(sK2(X1,X0),k3_relat_1(X0))
    | ~ r1_tarski(X1,k3_relat_1(X0))
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_3906,plain,
    ( r4_wellord1(X0,k2_wellord1(X0,X1)) = iProver_top
    | r2_hidden(sK2(X1,X0),k3_relat_1(X0)) = iProver_top
    | r1_tarski(X1,k3_relat_1(X0)) != iProver_top
    | v2_wellord1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_5678,plain,
    ( r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),X1)) = iProver_top
    | r2_hidden(sK2(X1,k1_wellord2(X0)),X0) = iProver_top
    | r1_tarski(X1,k3_relat_1(k1_wellord2(X0))) != iProver_top
    | v2_wellord1(k1_wellord2(X0)) != iProver_top
    | v1_relat_1(k1_wellord2(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_215,c_3906])).

cnf(c_5734,plain,
    ( r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),X1)) = iProver_top
    | r2_hidden(sK2(X1,k1_wellord2(X0)),X0) = iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | v2_wellord1(k1_wellord2(X0)) != iProver_top
    | v1_relat_1(k1_wellord2(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5678,c_215])).

cnf(c_78,plain,
    ( v1_relat_1(k1_wellord2(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_14220,plain,
    ( v2_wellord1(k1_wellord2(X0)) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r2_hidden(sK2(X1,k1_wellord2(X0)),X0) = iProver_top
    | r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),X1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5734,c_78])).

cnf(c_14221,plain,
    ( r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),X1)) = iProver_top
    | r2_hidden(sK2(X1,k1_wellord2(X0)),X0) = iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | v2_wellord1(k1_wellord2(X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_14220])).

cnf(c_14231,plain,
    ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top
    | r2_hidden(sK2(sK3,k1_wellord2(sK4)),sK4) = iProver_top
    | r1_tarski(sK3,sK4) != iProver_top
    | v2_wellord1(k1_wellord2(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4283,c_14221])).

cnf(c_31,negated_conjecture,
    ( v3_ordinal1(sK4) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_32,plain,
    ( v3_ordinal1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_33,plain,
    ( r1_tarski(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_28,plain,
    ( ~ r1_tarski(X0,X1)
    | v2_wellord1(k1_wellord2(X0))
    | ~ v3_ordinal1(X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_35,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v2_wellord1(k1_wellord2(X0)) = iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_37,plain,
    ( r1_tarski(sK4,sK4) != iProver_top
    | v2_wellord1(k1_wellord2(sK4)) = iProver_top
    | v3_ordinal1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_16,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_ordinal1(X0,X1)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_69,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_ordinal1(X0,X1) != iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_71,plain,
    ( r1_tarski(sK4,sK4) = iProver_top
    | r1_ordinal1(sK4,sK4) != iProver_top
    | v3_ordinal1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_69])).

cnf(c_2,plain,
    ( r1_ordinal1(X0,X1)
    | r1_ordinal1(X1,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_111,plain,
    ( r1_ordinal1(X0,X1) = iProver_top
    | r1_ordinal1(X1,X0) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_113,plain,
    ( r1_ordinal1(sK4,sK4) = iProver_top
    | v3_ordinal1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_111])).

cnf(c_14476,plain,
    ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top
    | r2_hidden(sK2(sK3,k1_wellord2(sK4)),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14231,c_32,c_33,c_37,c_71,c_113])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1)
    | k1_wellord1(k1_wellord2(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ v3_ordinal1(X1)
    | v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_197,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1)
    | k1_wellord1(k1_wellord2(X1),X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_17,c_18,c_1])).

cnf(c_3898,plain,
    ( k1_wellord1(k1_wellord2(X0),X1) = X1
    | r2_hidden(X1,X0) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_197])).

cnf(c_14489,plain,
    ( k1_wellord1(k1_wellord2(sK4),sK2(sK3,k1_wellord2(sK4))) = sK2(sK3,k1_wellord2(sK4))
    | r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top
    | v3_ordinal1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_14476,c_3898])).

cnf(c_16087,plain,
    ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top
    | k1_wellord1(k1_wellord2(sK4),sK2(sK3,k1_wellord2(sK4))) = sK2(sK3,k1_wellord2(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14489,c_32])).

cnf(c_16088,plain,
    ( k1_wellord1(k1_wellord2(sK4),sK2(sK3,k1_wellord2(sK4))) = sK2(sK3,k1_wellord2(sK4))
    | r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_16087])).

cnf(c_22,plain,
    ( ~ r4_wellord1(X0,X1)
    | r4_wellord1(X1,X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_3908,plain,
    ( r4_wellord1(X0,X1) != iProver_top
    | r4_wellord1(X1,X0) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_16094,plain,
    ( k1_wellord1(k1_wellord2(sK4),sK2(sK3,k1_wellord2(sK4))) = sK2(sK3,k1_wellord2(sK4))
    | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4)) = iProver_top
    | v1_relat_1(k1_wellord2(sK4)) != iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_16088,c_3908])).

cnf(c_29,negated_conjecture,
    ( ~ r1_ordinal1(k2_wellord2(k1_wellord2(sK3)),sK4) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_80,plain,
    ( v1_relat_1(k1_wellord2(sK4)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_78])).

cnf(c_112,plain,
    ( r1_ordinal1(sK4,sK4)
    | ~ v3_ordinal1(sK4) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1586,plain,
    ( v2_wellord1(k1_wellord2(X0))
    | ~ v3_ordinal1(X1)
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_30])).

cnf(c_1587,plain,
    ( v2_wellord1(k1_wellord2(sK3))
    | ~ v3_ordinal1(sK4) ),
    inference(unflattening,[status(thm)],[c_1586])).

cnf(c_1588,plain,
    ( v2_wellord1(k1_wellord2(sK3)) = iProver_top
    | v3_ordinal1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1587])).

cnf(c_3338,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3373,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_3338])).

cnf(c_3341,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_ordinal1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_4213,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_ordinal1(k2_wellord2(k1_wellord2(sK3)),sK4)
    | k2_wellord2(k1_wellord2(sK3)) != X0
    | sK4 != X1 ),
    inference(instantiation,[status(thm)],[c_3341])).

cnf(c_4215,plain,
    ( r1_ordinal1(k2_wellord2(k1_wellord2(sK3)),sK4)
    | ~ r1_ordinal1(sK4,sK4)
    | k2_wellord2(k1_wellord2(sK3)) != sK4
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_4213])).

cnf(c_4432,plain,
    ( v1_relat_1(k1_wellord2(sK3)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_4433,plain,
    ( v1_relat_1(k1_wellord2(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4432])).

cnf(c_11,plain,
    ( ~ r4_wellord1(X0,k1_wellord2(X1))
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0)
    | ~ v3_ordinal1(X1)
    | k2_wellord2(X0) = X1 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_4208,plain,
    ( ~ r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
    | ~ v2_wellord1(k1_wellord2(X0))
    | ~ v1_relat_1(k1_wellord2(X0))
    | ~ v3_ordinal1(X1)
    | k2_wellord2(k1_wellord2(X0)) = X1 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_9069,plain,
    ( ~ r4_wellord1(k1_wellord2(sK3),k1_wellord2(X0))
    | ~ v2_wellord1(k1_wellord2(sK3))
    | ~ v1_relat_1(k1_wellord2(sK3))
    | ~ v3_ordinal1(X0)
    | k2_wellord2(k1_wellord2(sK3)) = X0 ),
    inference(instantiation,[status(thm)],[c_4208])).

cnf(c_9070,plain,
    ( k2_wellord2(k1_wellord2(sK3)) = X0
    | r4_wellord1(k1_wellord2(sK3),k1_wellord2(X0)) != iProver_top
    | v2_wellord1(k1_wellord2(sK3)) != iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9069])).

cnf(c_9072,plain,
    ( k2_wellord2(k1_wellord2(sK3)) = sK4
    | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4)) != iProver_top
    | v2_wellord1(k1_wellord2(sK3)) != iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top
    | v3_ordinal1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_9070])).

cnf(c_19511,plain,
    ( k1_wellord1(k1_wellord2(sK4),sK2(sK3,k1_wellord2(sK4))) = sK2(sK3,k1_wellord2(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16094,c_31,c_32,c_29,c_80,c_112,c_1588,c_3373,c_4215,c_4433,c_9072])).

cnf(c_23,plain,
    ( r4_wellord1(X0,k2_wellord1(X0,X1))
    | r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,sK2(X1,X0))),k2_wellord1(X0,X1))
    | ~ r1_tarski(X1,k3_relat_1(X0))
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_3907,plain,
    ( r4_wellord1(X0,k2_wellord1(X0,X1)) = iProver_top
    | r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,sK2(X1,X0))),k2_wellord1(X0,X1)) = iProver_top
    | r1_tarski(X1,k3_relat_1(X0)) != iProver_top
    | v2_wellord1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_6663,plain,
    ( r4_wellord1(k2_wellord1(k1_wellord2(sK4),k1_wellord1(k1_wellord2(sK4),sK2(sK3,k1_wellord2(sK4)))),k1_wellord2(sK3)) = iProver_top
    | r4_wellord1(k1_wellord2(sK4),k2_wellord1(k1_wellord2(sK4),sK3)) = iProver_top
    | r1_tarski(sK3,k3_relat_1(k1_wellord2(sK4))) != iProver_top
    | v2_wellord1(k1_wellord2(sK4)) != iProver_top
    | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4283,c_3907])).

cnf(c_6710,plain,
    ( r4_wellord1(k2_wellord1(k1_wellord2(sK4),k1_wellord1(k1_wellord2(sK4),sK2(sK3,k1_wellord2(sK4)))),k1_wellord2(sK3)) = iProver_top
    | r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top
    | r1_tarski(sK3,k3_relat_1(k1_wellord2(sK4))) != iProver_top
    | v2_wellord1(k1_wellord2(sK4)) != iProver_top
    | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6663,c_4283])).

cnf(c_6711,plain,
    ( r4_wellord1(k2_wellord1(k1_wellord2(sK4),k1_wellord1(k1_wellord2(sK4),sK2(sK3,k1_wellord2(sK4)))),k1_wellord2(sK3)) = iProver_top
    | r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top
    | r1_tarski(sK3,sK4) != iProver_top
    | v2_wellord1(k1_wellord2(sK4)) != iProver_top
    | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6710,c_215])).

cnf(c_6949,plain,
    ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top
    | r4_wellord1(k2_wellord1(k1_wellord2(sK4),k1_wellord1(k1_wellord2(sK4),sK2(sK3,k1_wellord2(sK4)))),k1_wellord2(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6711,c_32,c_33,c_37,c_71,c_80,c_113])).

cnf(c_6950,plain,
    ( r4_wellord1(k2_wellord1(k1_wellord2(sK4),k1_wellord1(k1_wellord2(sK4),sK2(sK3,k1_wellord2(sK4)))),k1_wellord2(sK3)) = iProver_top
    | r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_6949])).

cnf(c_6956,plain,
    ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top
    | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK4),k1_wellord1(k1_wellord2(sK4),sK2(sK3,k1_wellord2(sK4))))) = iProver_top
    | v1_relat_1(k2_wellord1(k1_wellord2(sK4),k1_wellord1(k1_wellord2(sK4),sK2(sK3,k1_wellord2(sK4))))) != iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6950,c_3908])).

cnf(c_7245,plain,
    ( v1_relat_1(k2_wellord1(k1_wellord2(sK4),k1_wellord1(k1_wellord2(sK4),sK2(sK3,k1_wellord2(sK4))))) != iProver_top
    | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK4),k1_wellord1(k1_wellord2(sK4),sK2(sK3,k1_wellord2(sK4))))) = iProver_top
    | r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6956,c_4433])).

cnf(c_7246,plain,
    ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top
    | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK4),k1_wellord1(k1_wellord2(sK4),sK2(sK3,k1_wellord2(sK4))))) = iProver_top
    | v1_relat_1(k2_wellord1(k1_wellord2(sK4),k1_wellord1(k1_wellord2(sK4),sK2(sK3,k1_wellord2(sK4))))) != iProver_top ),
    inference(renaming,[status(thm)],[c_7245])).

cnf(c_19515,plain,
    ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top
    | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK4),sK2(sK3,k1_wellord2(sK4)))) = iProver_top
    | v1_relat_1(k2_wellord1(k1_wellord2(sK4),sK2(sK3,k1_wellord2(sK4)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_19511,c_7246])).

cnf(c_457,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1)
    | v3_ordinal1(X0) ),
    inference(resolution,[status(thm)],[c_18,c_1])).

cnf(c_3895,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_457])).

cnf(c_14486,plain,
    ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top
    | v3_ordinal1(sK2(sK3,k1_wellord2(sK4))) = iProver_top
    | v3_ordinal1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_14476,c_3895])).

cnf(c_14899,plain,
    ( v3_ordinal1(sK2(sK3,k1_wellord2(sK4))) = iProver_top
    | r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14486,c_32])).

cnf(c_14900,plain,
    ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top
    | v3_ordinal1(sK2(sK3,k1_wellord2(sK4))) = iProver_top ),
    inference(renaming,[status(thm)],[c_14899])).

cnf(c_14906,plain,
    ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4)) = iProver_top
    | v1_relat_1(k1_wellord2(sK4)) != iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top
    | v3_ordinal1(sK2(sK3,k1_wellord2(sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_14900,c_3908])).

cnf(c_17136,plain,
    ( v3_ordinal1(sK2(sK3,k1_wellord2(sK4))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14906,c_31,c_32,c_29,c_80,c_112,c_1588,c_3373,c_4215,c_4433,c_9072])).

cnf(c_3899,plain,
    ( v3_ordinal1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_3920,plain,
    ( r1_ordinal1(X0,X1) = iProver_top
    | r1_ordinal1(X1,X0) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3909,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_ordinal1(X0,X1) != iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_5123,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_ordinal1(X1,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3920,c_3909])).

cnf(c_6743,plain,
    ( k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
    | r1_ordinal1(X0,X1) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5123,c_3903])).

cnf(c_6827,plain,
    ( k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
    | r1_tarski(X0,X1) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6743,c_3909])).

cnf(c_6843,plain,
    ( k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
    | k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0)
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_6827,c_3903])).

cnf(c_7995,plain,
    ( k2_wellord1(k1_wellord2(X0),sK4) = k1_wellord2(sK4)
    | k2_wellord1(k1_wellord2(sK4),X0) = k1_wellord2(X0)
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3899,c_6843])).

cnf(c_17142,plain,
    ( k2_wellord1(k1_wellord2(sK2(sK3,k1_wellord2(sK4))),sK4) = k1_wellord2(sK4)
    | k2_wellord1(k1_wellord2(sK4),sK2(sK3,k1_wellord2(sK4))) = k1_wellord2(sK2(sK3,k1_wellord2(sK4))) ),
    inference(superposition,[status(thm)],[c_17136,c_7995])).

cnf(c_0,plain,
    ( ~ v3_ordinal1(X0)
    | v1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v1_ordinal1(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_437,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v3_ordinal1(X2)
    | X1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_10])).

cnf(c_438,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v3_ordinal1(X1) ),
    inference(unflattening,[status(thm)],[c_437])).

cnf(c_3896,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_438])).

cnf(c_14485,plain,
    ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top
    | r1_tarski(sK2(sK3,k1_wellord2(sK4)),sK4) = iProver_top
    | v3_ordinal1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_14476,c_3896])).

cnf(c_15173,plain,
    ( r1_tarski(sK2(sK3,k1_wellord2(sK4)),sK4) = iProver_top
    | r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14485,c_32])).

cnf(c_15174,plain,
    ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top
    | r1_tarski(sK2(sK3,k1_wellord2(sK4)),sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_15173])).

cnf(c_15181,plain,
    ( k2_wellord1(k1_wellord2(sK4),sK2(sK3,k1_wellord2(sK4))) = k1_wellord2(sK2(sK3,k1_wellord2(sK4)))
    | r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_15174,c_3903])).

cnf(c_15483,plain,
    ( k2_wellord1(k1_wellord2(sK4),sK2(sK3,k1_wellord2(sK4))) = k1_wellord2(sK2(sK3,k1_wellord2(sK4)))
    | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4)) = iProver_top
    | v1_relat_1(k1_wellord2(sK4)) != iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_15181,c_3908])).

cnf(c_17820,plain,
    ( k2_wellord1(k1_wellord2(sK4),sK2(sK3,k1_wellord2(sK4))) = k1_wellord2(sK2(sK3,k1_wellord2(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17142,c_31,c_32,c_29,c_80,c_112,c_1588,c_3373,c_4215,c_4433,c_9072,c_15483])).

cnf(c_19525,plain,
    ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top
    | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2(sK3,k1_wellord2(sK4)))) = iProver_top
    | v1_relat_1(k1_wellord2(sK2(sK3,k1_wellord2(sK4)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_19515,c_17820])).

cnf(c_3912,plain,
    ( v1_relat_1(k1_wellord2(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_19768,plain,
    ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top
    | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2(sK3,k1_wellord2(sK4)))) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_19525,c_3912])).

cnf(c_3913,plain,
    ( k2_wellord2(X0) = X1
    | r4_wellord1(X0,k1_wellord2(X1)) != iProver_top
    | v2_wellord1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_19770,plain,
    ( sK2(sK3,k1_wellord2(sK4)) = k2_wellord2(k1_wellord2(sK3))
    | r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top
    | v2_wellord1(k1_wellord2(sK3)) != iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top
    | v3_ordinal1(sK2(sK3,k1_wellord2(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_19768,c_3913])).

cnf(c_21565,plain,
    ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top
    | sK2(sK3,k1_wellord2(sK4)) = k2_wellord2(k1_wellord2(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19770,c_31,c_32,c_29,c_80,c_112,c_1588,c_3373,c_4215,c_4433,c_9072,c_14906])).

cnf(c_21566,plain,
    ( sK2(sK3,k1_wellord2(sK4)) = k2_wellord2(k1_wellord2(sK3))
    | r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_21565])).

cnf(c_21572,plain,
    ( sK2(sK3,k1_wellord2(sK4)) = k2_wellord2(k1_wellord2(sK3))
    | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4)) = iProver_top
    | v1_relat_1(k1_wellord2(sK4)) != iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_21566,c_3908])).

cnf(c_21594,plain,
    ( sK2(sK3,k1_wellord2(sK4)) = k2_wellord2(k1_wellord2(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_21572,c_31,c_32,c_29,c_80,c_112,c_1588,c_3373,c_4215,c_4433,c_9072])).

cnf(c_21617,plain,
    ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top
    | r2_hidden(k2_wellord2(k1_wellord2(sK3)),sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_21594,c_14476])).

cnf(c_34,plain,
    ( r1_ordinal1(k2_wellord2(k1_wellord2(sK3)),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_15,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_ordinal1(X0,X1)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_3910,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_ordinal1(X0,X1) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_15183,plain,
    ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top
    | r1_ordinal1(sK2(sK3,k1_wellord2(sK4)),sK4) = iProver_top
    | v3_ordinal1(sK2(sK3,k1_wellord2(sK4))) != iProver_top
    | v3_ordinal1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_15174,c_3910])).

cnf(c_17427,plain,
    ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top
    | r1_ordinal1(sK2(sK3,k1_wellord2(sK4)),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15183,c_31,c_32,c_29,c_80,c_112,c_1588,c_3373,c_4215,c_4433,c_9072,c_14906])).

cnf(c_21608,plain,
    ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top
    | r1_ordinal1(k2_wellord2(k1_wellord2(sK3)),sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_21594,c_17427])).

cnf(c_22020,plain,
    ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_21617,c_34,c_21608])).

cnf(c_22026,plain,
    ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4)) = iProver_top
    | v1_relat_1(k1_wellord2(sK4)) != iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_22020,c_3908])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_22026,c_9072,c_4433,c_4215,c_3373,c_1588,c_112,c_80,c_29,c_32,c_31])).


%------------------------------------------------------------------------------
