%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0740+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:01 EST 2020

% Result     : Theorem 2.86s
% Output     : CNFRefutation 2.86s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 328 expanded)
%              Number of clauses        :   74 ( 104 expanded)
%              Number of leaves         :   18 (  75 expanded)
%              Depth                    :   15
%              Number of atoms          :  475 (1640 expanded)
%              Number of equality atoms :   80 ( 238 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] :
      ( v2_ordinal1(X0)
    <=> ! [X1,X2] :
          ~ ( ~ r2_hidden(X2,X1)
            & X1 != X2
            & ~ r2_hidden(X1,X2)
            & r2_hidden(X2,X0)
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
    <=> ! [X1,X2] :
          ( r2_hidden(X2,X1)
          | X1 = X2
          | r2_hidden(X1,X2)
          | ~ r2_hidden(X2,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f33,plain,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        | ? [X1,X2] :
            ( ~ r2_hidden(X2,X1)
            & X1 != X2
            & ~ r2_hidden(X1,X2)
            & r2_hidden(X2,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X1,X2] :
            ( r2_hidden(X2,X1)
            | X1 = X2
            | r2_hidden(X1,X2)
            | ~ r2_hidden(X2,X0)
            | ~ r2_hidden(X1,X0) )
        | ~ v2_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f34,plain,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        | ? [X1,X2] :
            ( ~ r2_hidden(X2,X1)
            & X1 != X2
            & ~ r2_hidden(X1,X2)
            & r2_hidden(X2,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X3,X4] :
            ( r2_hidden(X4,X3)
            | X3 = X4
            | r2_hidden(X3,X4)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(X3,X0) )
        | ~ v2_ordinal1(X0) ) ) ),
    inference(rectify,[],[f33])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( ~ r2_hidden(X2,X1)
          & X1 != X2
          & ~ r2_hidden(X1,X2)
          & r2_hidden(X2,X0)
          & r2_hidden(X1,X0) )
     => ( ~ r2_hidden(sK2(X0),sK1(X0))
        & sK1(X0) != sK2(X0)
        & ~ r2_hidden(sK1(X0),sK2(X0))
        & r2_hidden(sK2(X0),X0)
        & r2_hidden(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        | ( ~ r2_hidden(sK2(X0),sK1(X0))
          & sK1(X0) != sK2(X0)
          & ~ r2_hidden(sK1(X0),sK2(X0))
          & r2_hidden(sK2(X0),X0)
          & r2_hidden(sK1(X0),X0) ) )
      & ( ! [X3,X4] :
            ( r2_hidden(X4,X3)
            | X3 = X4
            | r2_hidden(X3,X4)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(X3,X0) )
        | ~ v2_ordinal1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f34,f35])).

fof(f54,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
      | r2_hidden(sK1(X0),X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) ) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X0)
                  & r2_hidden(X2,X4) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ? [X7] :
                  ( r2_hidden(X7,X0)
                  & r2_hidden(X5,X7) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f39])).

fof(f43,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK5(X0,X5),X0)
        & r2_hidden(X5,sK5(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(X2,X4) )
     => ( r2_hidden(sK4(X0,X1),X0)
        & r2_hidden(X2,sK4(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X3) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( r2_hidden(X4,X0)
                & r2_hidden(X2,X4) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(sK3(X0,X1),X3) )
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(X4,X0)
              & r2_hidden(sK3(X0,X1),X4) )
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(sK3(X0,X1),X3) )
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( ( r2_hidden(sK4(X0,X1),X0)
              & r2_hidden(sK3(X0,X1),sK4(X0,X1)) )
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ( r2_hidden(sK5(X0,X5),X0)
                & r2_hidden(X5,sK5(X0,X5)) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f40,f43,f42,f41])).

fof(f62,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,sK5(X0,X5))
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f80,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,sK5(X0,X5))
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f62])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ( r2_hidden(X0,X1)
       => v3_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f55,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
      | r2_hidden(sK2(X0),X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f63,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK5(X0,X5),X0)
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f79,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK5(X0,X5),X0)
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f63])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( r1_tarski(X1,X0)
            | ~ r2_hidden(X1,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X1,X0)
          & r2_hidden(X1,X0) )
     => ( ~ r1_tarski(sK0(X0),X0)
        & r2_hidden(sK0(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ( ~ r1_tarski(sK0(X0),X0)
          & r2_hidden(sK0(X0),X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).

fof(f51,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
    <=> ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ( v3_ordinal1(X0)
        | ~ v2_ordinal1(X0)
        | ~ v1_ordinal1(X0) )
      & ( ( v2_ordinal1(X0)
          & v1_ordinal1(X0) )
        | ~ v3_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f38,plain,(
    ! [X0] :
      ( ( v3_ordinal1(X0)
        | ~ v2_ordinal1(X0)
        | ~ v1_ordinal1(X0) )
      & ( ( v2_ordinal1(X0)
          & v1_ordinal1(X0) )
        | ~ v3_ordinal1(X0) ) ) ),
    inference(flattening,[],[f37])).

fof(f61,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
      | ~ v2_ordinal1(X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f50,plain,(
    ! [X2,X0] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f56,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
      | ~ r2_hidden(sK1(X0),sK2(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f57,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
      | sK1(X0) != sK2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f58,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
      | ~ r2_hidden(sK2(X0),sK1(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f52,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ r1_tarski(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f59,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f13,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k3_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => v3_ordinal1(k3_tarski(X0)) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f28,plain,(
    ? [X0] :
      ( ~ v3_ordinal1(k3_tarski(X0))
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f46,plain,
    ( ? [X0] :
        ( ~ v3_ordinal1(k3_tarski(X0))
        & v3_ordinal1(X0) )
   => ( ~ v3_ordinal1(k3_tarski(sK6))
      & v3_ordinal1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ~ v3_ordinal1(k3_tarski(sK6))
    & v3_ordinal1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f28,f46])).

fof(f77,plain,(
    ~ v3_ordinal1(k3_tarski(sK6)) ),
    inference(cnf_transformation,[],[f47])).

fof(f76,plain,(
    v3_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_9,plain,
    ( r2_hidden(sK1(X0),X0)
    | v2_ordinal1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1884,plain,
    ( r2_hidden(sK1(X0),X0) = iProver_top
    | v2_ordinal1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_19,plain,
    ( r2_hidden(X0,sK5(X1,X0))
    | ~ r2_hidden(X0,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1876,plain,
    ( r2_hidden(X0,sK5(X1,X0)) = iProver_top
    | r2_hidden(X0,k3_tarski(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1)
    | v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1875,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3116,plain,
    ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
    | v3_ordinal1(X0) = iProver_top
    | v3_ordinal1(sK5(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1876,c_1875])).

cnf(c_6862,plain,
    ( v3_ordinal1(sK5(X0,sK1(k3_tarski(X0)))) != iProver_top
    | v3_ordinal1(sK1(k3_tarski(X0))) = iProver_top
    | v2_ordinal1(k3_tarski(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1884,c_3116])).

cnf(c_6941,plain,
    ( ~ v3_ordinal1(sK5(X0,sK1(k3_tarski(X0))))
    | v3_ordinal1(sK1(k3_tarski(X0)))
    | v2_ordinal1(k3_tarski(X0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6862])).

cnf(c_6943,plain,
    ( ~ v3_ordinal1(sK5(sK6,sK1(k3_tarski(sK6))))
    | v3_ordinal1(sK1(k3_tarski(sK6)))
    | v2_ordinal1(k3_tarski(sK6)) ),
    inference(instantiation,[status(thm)],[c_6941])).

cnf(c_8,plain,
    ( r2_hidden(sK2(X0),X0)
    | v2_ordinal1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1885,plain,
    ( r2_hidden(sK2(X0),X0) = iProver_top
    | v2_ordinal1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_6861,plain,
    ( v3_ordinal1(sK5(X0,sK2(k3_tarski(X0)))) != iProver_top
    | v3_ordinal1(sK2(k3_tarski(X0))) = iProver_top
    | v2_ordinal1(k3_tarski(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1885,c_3116])).

cnf(c_6938,plain,
    ( ~ v3_ordinal1(sK5(X0,sK2(k3_tarski(X0))))
    | v3_ordinal1(sK2(k3_tarski(X0)))
    | v2_ordinal1(k3_tarski(X0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6861])).

cnf(c_6940,plain,
    ( ~ v3_ordinal1(sK5(sK6,sK2(k3_tarski(sK6))))
    | v3_ordinal1(sK2(k3_tarski(sK6)))
    | v2_ordinal1(k3_tarski(sK6)) ),
    inference(instantiation,[status(thm)],[c_6938])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,k3_tarski(X1))
    | r2_hidden(sK5(X1,X0),X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1877,plain,
    ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
    | r2_hidden(sK5(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3115,plain,
    ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(sK5(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1877,c_1875])).

cnf(c_6588,plain,
    ( v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK5(X0,sK1(k3_tarski(X0)))) = iProver_top
    | v2_ordinal1(k3_tarski(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1884,c_3115])).

cnf(c_6680,plain,
    ( ~ v3_ordinal1(X0)
    | v3_ordinal1(sK5(X0,sK1(k3_tarski(X0))))
    | v2_ordinal1(k3_tarski(X0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6588])).

cnf(c_6682,plain,
    ( v3_ordinal1(sK5(sK6,sK1(k3_tarski(sK6))))
    | ~ v3_ordinal1(sK6)
    | v2_ordinal1(k3_tarski(sK6)) ),
    inference(instantiation,[status(thm)],[c_6680])).

cnf(c_6587,plain,
    ( v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK5(X0,sK2(k3_tarski(X0)))) = iProver_top
    | v2_ordinal1(k3_tarski(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1885,c_3115])).

cnf(c_6677,plain,
    ( ~ v3_ordinal1(X0)
    | v3_ordinal1(sK5(X0,sK2(k3_tarski(X0))))
    | v2_ordinal1(k3_tarski(X0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6587])).

cnf(c_6679,plain,
    ( v3_ordinal1(sK5(sK6,sK2(k3_tarski(sK6))))
    | ~ v3_ordinal1(sK6)
    | v2_ordinal1(k3_tarski(sK6)) ),
    inference(instantiation,[status(thm)],[c_6677])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1889,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_ordinal1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_26,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1871,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2793,plain,
    ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1877,c_1871])).

cnf(c_2880,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_ordinal1(k3_tarski(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1889,c_2793])).

cnf(c_11,plain,
    ( ~ v1_ordinal1(X0)
    | v3_ordinal1(X0)
    | ~ v2_ordinal1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1882,plain,
    ( v1_ordinal1(X0) != iProver_top
    | v3_ordinal1(X0) = iProver_top
    | v2_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3182,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v3_ordinal1(k3_tarski(X0)) = iProver_top
    | v2_ordinal1(k3_tarski(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2880,c_1882])).

cnf(c_2881,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v2_ordinal1(k3_tarski(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1885,c_2793])).

cnf(c_5123,plain,
    ( v3_ordinal1(k3_tarski(X0)) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3182,c_2881])).

cnf(c_5124,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v3_ordinal1(k3_tarski(X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_5123])).

cnf(c_5125,plain,
    ( ~ v1_xboole_0(X0)
    | v3_ordinal1(k3_tarski(X0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5124])).

cnf(c_5127,plain,
    ( ~ v1_xboole_0(sK6)
    | v3_ordinal1(k3_tarski(sK6)) ),
    inference(instantiation,[status(thm)],[c_5125])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_4623,plain,
    ( ~ m1_subset_1(sK0(k3_tarski(sK6)),X0)
    | r2_hidden(sK0(k3_tarski(sK6)),X0)
    | v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_4625,plain,
    ( ~ m1_subset_1(sK0(k3_tarski(sK6)),sK6)
    | r2_hidden(sK0(k3_tarski(sK6)),sK6)
    | v1_xboole_0(sK6) ),
    inference(instantiation,[status(thm)],[c_4623])).

cnf(c_21,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2874,plain,
    ( r2_hidden(sK1(k3_tarski(sK6)),sK2(k3_tarski(sK6)))
    | r2_hidden(sK2(k3_tarski(sK6)),sK1(k3_tarski(sK6)))
    | ~ v3_ordinal1(sK1(k3_tarski(sK6)))
    | ~ v3_ordinal1(sK2(k3_tarski(sK6)))
    | sK1(k3_tarski(sK6)) = sK2(k3_tarski(sK6)) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v1_ordinal1(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_23,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_241,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_23])).

cnf(c_242,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_241])).

cnf(c_402,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X1)
    | ~ v1_ordinal1(X1) ),
    inference(resolution,[status(thm)],[c_4,c_242])).

cnf(c_2618,plain,
    ( m1_subset_1(sK5(sK6,sK0(k3_tarski(sK6))),k1_zfmisc_1(sK6))
    | ~ r2_hidden(sK5(sK6,sK0(k3_tarski(sK6))),sK6)
    | ~ v1_ordinal1(sK6) ),
    inference(instantiation,[status(thm)],[c_402])).

cnf(c_25,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2611,plain,
    ( ~ m1_subset_1(sK5(sK6,sK0(k3_tarski(sK6))),k1_zfmisc_1(X0))
    | m1_subset_1(sK0(k3_tarski(sK6)),X0)
    | ~ r2_hidden(sK0(k3_tarski(sK6)),sK5(sK6,sK0(k3_tarski(sK6)))) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_2613,plain,
    ( ~ m1_subset_1(sK5(sK6,sK0(k3_tarski(sK6))),k1_zfmisc_1(sK6))
    | m1_subset_1(sK0(k3_tarski(sK6)),sK6)
    | ~ r2_hidden(sK0(k3_tarski(sK6)),sK5(sK6,sK0(k3_tarski(sK6)))) ),
    inference(instantiation,[status(thm)],[c_2611])).

cnf(c_2397,plain,
    ( r2_hidden(sK0(k3_tarski(sK6)),sK5(sK6,sK0(k3_tarski(sK6))))
    | ~ r2_hidden(sK0(k3_tarski(sK6)),k3_tarski(sK6)) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_2398,plain,
    ( r2_hidden(sK5(sK6,sK0(k3_tarski(sK6))),sK6)
    | ~ r2_hidden(sK0(k3_tarski(sK6)),k3_tarski(sK6)) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_7,plain,
    ( ~ r2_hidden(sK1(X0),sK2(X0))
    | v2_ordinal1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2202,plain,
    ( ~ r2_hidden(sK1(k3_tarski(sK6)),sK2(k3_tarski(sK6)))
    | v2_ordinal1(k3_tarski(sK6)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_6,plain,
    ( v2_ordinal1(X0)
    | sK1(X0) != sK2(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2203,plain,
    ( v2_ordinal1(k3_tarski(sK6))
    | sK1(k3_tarski(sK6)) != sK2(k3_tarski(sK6)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_5,plain,
    ( ~ r2_hidden(sK2(X0),sK1(X0))
    | v2_ordinal1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2204,plain,
    ( ~ r2_hidden(sK2(k3_tarski(sK6)),sK1(k3_tarski(sK6)))
    | v2_ordinal1(k3_tarski(sK6)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2120,plain,
    ( r2_hidden(sK0(k3_tarski(sK6)),k3_tarski(sK6))
    | v1_ordinal1(k3_tarski(sK6)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2088,plain,
    ( ~ v1_ordinal1(k3_tarski(sK6))
    | v3_ordinal1(k3_tarski(sK6))
    | ~ v2_ordinal1(k3_tarski(sK6)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2,plain,
    ( ~ r1_tarski(sK0(X0),X0)
    | v1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_27,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(X0,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_430,plain,
    ( ~ r2_hidden(X0,X1)
    | v1_ordinal1(X2)
    | k3_tarski(X1) != X2
    | sK0(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_27])).

cnf(c_431,plain,
    ( ~ r2_hidden(sK0(k3_tarski(X0)),X0)
    | v1_ordinal1(k3_tarski(X0)) ),
    inference(unflattening,[status(thm)],[c_430])).

cnf(c_537,plain,
    ( ~ r2_hidden(sK0(k3_tarski(X0)),X0)
    | v3_ordinal1(X1)
    | ~ v2_ordinal1(X1)
    | k3_tarski(X0) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_431])).

cnf(c_538,plain,
    ( ~ r2_hidden(sK0(k3_tarski(X0)),X0)
    | v3_ordinal1(k3_tarski(X0))
    | ~ v2_ordinal1(k3_tarski(X0)) ),
    inference(unflattening,[status(thm)],[c_537])).

cnf(c_540,plain,
    ( ~ r2_hidden(sK0(k3_tarski(sK6)),sK6)
    | v3_ordinal1(k3_tarski(sK6))
    | ~ v2_ordinal1(k3_tarski(sK6)) ),
    inference(instantiation,[status(thm)],[c_538])).

cnf(c_13,plain,
    ( v1_ordinal1(X0)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_73,plain,
    ( v1_ordinal1(sK6)
    | ~ v3_ordinal1(sK6) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_28,negated_conjecture,
    ( ~ v3_ordinal1(k3_tarski(sK6)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_29,negated_conjecture,
    ( v3_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f76])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6943,c_6940,c_6682,c_6679,c_5127,c_4625,c_2874,c_2618,c_2613,c_2397,c_2398,c_2202,c_2203,c_2204,c_2120,c_2088,c_540,c_73,c_28,c_29])).


%------------------------------------------------------------------------------
