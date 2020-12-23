%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:43:12 EST 2020

% Result     : Theorem 3.97s
% Output     : CNFRefutation 3.97s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 182 expanded)
%              Number of clauses        :   52 (  57 expanded)
%              Number of leaves         :   21 (  48 expanded)
%              Depth                    :   14
%              Number of atoms          :  330 ( 613 expanded)
%              Number of equality atoms :   62 (  74 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f58,f59])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k3_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f13,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
             => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
     => ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(sK6))
        & r1_tarski(X0,sK6)
        & v1_relat_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
            & r1_tarski(X0,X1)
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(sK5),k3_relat_1(X1))
          & r1_tarski(sK5,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ~ r1_tarski(k3_relat_1(sK5),k3_relat_1(sK6))
    & r1_tarski(sK5,sK6)
    & v1_relat_1(sK6)
    & v1_relat_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f27,f45,f44])).

fof(f74,plain,(
    r1_tarski(sK5,sK6) ),
    inference(cnf_transformation,[],[f46])).

fof(f73,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f46])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f38])).

fof(f42,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK3(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK2(X0,X1),X3),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK2(X0,X1),X4),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK2(X0,X1),X3),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f39,f42,f41,f40])).

fof(f63,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f83,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f63])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f67,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f78,plain,(
    ! [X0] :
      ( k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f67,f59])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k2_tarski(X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f56,f59])).

fof(f75,plain,(
    ~ r1_tarski(k3_relat_1(sK5),k3_relat_1(sK6)) ),
    inference(cnf_transformation,[],[f46])).

fof(f72,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_4489,plain,
    ( ~ r1_tarski(k2_relat_1(sK5),X0)
    | ~ r1_tarski(k1_relat_1(sK5),X0)
    | r1_tarski(k3_tarski(k2_tarski(k1_relat_1(sK5),k2_relat_1(sK5))),X0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_14450,plain,
    ( ~ r1_tarski(k2_relat_1(sK5),k3_relat_1(sK6))
    | ~ r1_tarski(k1_relat_1(sK5),k3_relat_1(sK6))
    | r1_tarski(k3_tarski(k2_tarski(k1_relat_1(sK5),k2_relat_1(sK5))),k3_relat_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_4489])).

cnf(c_23,plain,
    ( r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_25,negated_conjecture,
    ( r1_tarski(sK5,sK6) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1271,plain,
    ( r2_hidden(X0,sK6)
    | ~ r2_hidden(X0,sK5) ),
    inference(resolution,[status(thm)],[c_2,c_25])).

cnf(c_3909,plain,
    ( r2_hidden(X0,k3_relat_1(sK6))
    | ~ r2_hidden(k4_tarski(X0,X1),sK5)
    | ~ v1_relat_1(sK6) ),
    inference(resolution,[status(thm)],[c_23,c_1271])).

cnf(c_26,negated_conjecture,
    ( v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_4358,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK5)
    | r2_hidden(X0,k3_relat_1(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3909,c_26])).

cnf(c_4359,plain,
    ( r2_hidden(X0,k3_relat_1(sK6))
    | ~ r2_hidden(k4_tarski(X0,X1),sK5) ),
    inference(renaming,[status(thm)],[c_4358])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,sK4(X1,X0)),X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_4553,plain,
    ( r2_hidden(X0,k3_relat_1(sK6))
    | ~ r2_hidden(X0,k1_relat_1(sK5)) ),
    inference(resolution,[status(thm)],[c_4359,c_18])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_4563,plain,
    ( ~ r2_hidden(sK0(X0,k3_relat_1(sK6)),k1_relat_1(sK5))
    | r1_tarski(X0,k3_relat_1(sK6)) ),
    inference(resolution,[status(thm)],[c_4553,c_0])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_4716,plain,
    ( r1_tarski(k1_relat_1(sK5),k3_relat_1(sK6)) ),
    inference(resolution,[status(thm)],[c_4563,c_1])).

cnf(c_322,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1196,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_relat_1(sK5),k3_relat_1(sK6))
    | k3_relat_1(sK6) != X1
    | k3_relat_1(sK5) != X0 ),
    inference(instantiation,[status(thm)],[c_322])).

cnf(c_2998,plain,
    ( r1_tarski(k3_relat_1(sK5),k3_relat_1(sK6))
    | ~ r1_tarski(k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))),X1)
    | k3_relat_1(sK6) != X1
    | k3_relat_1(sK5) != k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))) ),
    inference(instantiation,[status(thm)],[c_1196])).

cnf(c_3533,plain,
    ( r1_tarski(k3_relat_1(sK5),k3_relat_1(sK6))
    | ~ r1_tarski(k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))),k3_relat_1(sK6))
    | k3_relat_1(sK6) != k3_relat_1(sK6)
    | k3_relat_1(sK5) != k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))) ),
    inference(instantiation,[status(thm)],[c_2998])).

cnf(c_3535,plain,
    ( r1_tarski(k3_relat_1(sK5),k3_relat_1(sK6))
    | ~ r1_tarski(k3_tarski(k2_tarski(k1_relat_1(sK5),k2_relat_1(sK5))),k3_relat_1(sK6))
    | k3_relat_1(sK6) != k3_relat_1(sK6)
    | k3_relat_1(sK5) != k3_tarski(k2_tarski(k1_relat_1(sK5),k2_relat_1(sK5))) ),
    inference(instantiation,[status(thm)],[c_3533])).

cnf(c_20,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_12,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_292,plain,
    ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_20,c_14,c_12])).

cnf(c_293,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(renaming,[status(thm)],[c_292])).

cnf(c_913,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_293])).

cnf(c_917,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_19,plain,
    ( ~ v1_relat_1(X0)
    | k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_922,plain,
    ( k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1885,plain,
    ( k3_tarski(k2_tarski(k1_relat_1(sK6),k2_relat_1(sK6))) = k3_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_917,c_922])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k3_tarski(k2_tarski(X2,X1))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_931,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k3_tarski(k2_tarski(X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2398,plain,
    ( r1_tarski(X0,k3_relat_1(sK6)) = iProver_top
    | r1_tarski(X0,k2_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1885,c_931])).

cnf(c_2761,plain,
    ( r1_tarski(X0,sK6) != iProver_top
    | r1_tarski(k2_relat_1(X0),k3_relat_1(sK6)) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_913,c_2398])).

cnf(c_2771,plain,
    ( ~ r1_tarski(X0,sK6)
    | r1_tarski(k2_relat_1(X0),k3_relat_1(sK6))
    | ~ v1_relat_1(sK6) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2761])).

cnf(c_2773,plain,
    ( r1_tarski(k2_relat_1(sK5),k3_relat_1(sK6))
    | ~ r1_tarski(sK5,sK6)
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_2771])).

cnf(c_321,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1297,plain,
    ( X0 != X1
    | k3_relat_1(sK5) != X1
    | k3_relat_1(sK5) = X0 ),
    inference(instantiation,[status(thm)],[c_321])).

cnf(c_1465,plain,
    ( X0 != k3_relat_1(X1)
    | k3_relat_1(sK5) = X0
    | k3_relat_1(sK5) != k3_relat_1(X1) ),
    inference(instantiation,[status(thm)],[c_1297])).

cnf(c_1725,plain,
    ( k3_relat_1(sK5) != k3_relat_1(X0)
    | k3_relat_1(sK5) = k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0)))
    | k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))) != k3_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_1465])).

cnf(c_1726,plain,
    ( k3_relat_1(sK5) != k3_relat_1(sK5)
    | k3_relat_1(sK5) = k3_tarski(k2_tarski(k1_relat_1(sK5),k2_relat_1(sK5)))
    | k3_tarski(k2_tarski(k1_relat_1(sK5),k2_relat_1(sK5))) != k3_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1725])).

cnf(c_320,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1483,plain,
    ( k3_relat_1(sK6) = k3_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_320])).

cnf(c_339,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_320])).

cnf(c_329,plain,
    ( X0 != X1
    | k3_relat_1(X0) = k3_relat_1(X1) ),
    theory(equality)).

cnf(c_337,plain,
    ( k3_relat_1(sK5) = k3_relat_1(sK5)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_329])).

cnf(c_43,plain,
    ( ~ v1_relat_1(sK5)
    | k3_tarski(k2_tarski(k1_relat_1(sK5),k2_relat_1(sK5))) = k3_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_24,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(sK5),k3_relat_1(sK6)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_27,negated_conjecture,
    ( v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f72])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14450,c_4716,c_3535,c_2773,c_1726,c_1483,c_339,c_337,c_43,c_24,c_25,c_26,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:42:12 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.97/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.97/1.00  
% 3.97/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.97/1.00  
% 3.97/1.00  ------  iProver source info
% 3.97/1.00  
% 3.97/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.97/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.97/1.00  git: non_committed_changes: false
% 3.97/1.00  git: last_make_outside_of_git: false
% 3.97/1.00  
% 3.97/1.00  ------ 
% 3.97/1.00  ------ Parsing...
% 3.97/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.97/1.00  
% 3.97/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.97/1.00  
% 3.97/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.97/1.00  
% 3.97/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.97/1.00  ------ Proving...
% 3.97/1.00  ------ Problem Properties 
% 3.97/1.00  
% 3.97/1.00  
% 3.97/1.00  clauses                                 28
% 3.97/1.00  conjectures                             4
% 3.97/1.00  EPR                                     5
% 3.97/1.00  Horn                                    24
% 3.97/1.00  unary                                   4
% 3.97/1.00  binary                                  11
% 3.97/1.00  lits                                    66
% 3.97/1.00  lits eq                                 7
% 3.97/1.00  fd_pure                                 0
% 3.97/1.00  fd_pseudo                               0
% 3.97/1.00  fd_cond                                 0
% 3.97/1.00  fd_pseudo_cond                          5
% 3.97/1.00  AC symbols                              0
% 3.97/1.00  
% 3.97/1.00  ------ Input Options Time Limit: Unbounded
% 3.97/1.00  
% 3.97/1.00  
% 3.97/1.00  ------ 
% 3.97/1.00  Current options:
% 3.97/1.00  ------ 
% 3.97/1.00  
% 3.97/1.00  
% 3.97/1.00  
% 3.97/1.00  
% 3.97/1.00  ------ Proving...
% 3.97/1.00  
% 3.97/1.00  
% 3.97/1.00  % SZS status Theorem for theBenchmark.p
% 3.97/1.00  
% 3.97/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.97/1.00  
% 3.97/1.00  fof(f5,axiom,(
% 3.97/1.00    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 3.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.97/1.00  
% 3.97/1.00  fof(f18,plain,(
% 3.97/1.00    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 3.97/1.00    inference(ennf_transformation,[],[f5])).
% 3.97/1.00  
% 3.97/1.00  fof(f19,plain,(
% 3.97/1.00    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 3.97/1.00    inference(flattening,[],[f18])).
% 3.97/1.00  
% 3.97/1.00  fof(f58,plain,(
% 3.97/1.00    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 3.97/1.00    inference(cnf_transformation,[],[f19])).
% 3.97/1.00  
% 3.97/1.00  fof(f6,axiom,(
% 3.97/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.97/1.00  
% 3.97/1.00  fof(f59,plain,(
% 3.97/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.97/1.00    inference(cnf_transformation,[],[f6])).
% 3.97/1.00  
% 3.97/1.00  fof(f77,plain,(
% 3.97/1.00    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 3.97/1.00    inference(definition_unfolding,[],[f58,f59])).
% 3.97/1.00  
% 3.97/1.00  fof(f12,axiom,(
% 3.97/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)))))),
% 3.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.97/1.00  
% 3.97/1.00  fof(f24,plain,(
% 3.97/1.00    ! [X0,X1,X2] : (((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 3.97/1.00    inference(ennf_transformation,[],[f12])).
% 3.97/1.00  
% 3.97/1.00  fof(f25,plain,(
% 3.97/1.00    ! [X0,X1,X2] : ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 3.97/1.00    inference(flattening,[],[f24])).
% 3.97/1.00  
% 3.97/1.00  fof(f70,plain,(
% 3.97/1.00    ( ! [X2,X0,X1] : (r2_hidden(X0,k3_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 3.97/1.00    inference(cnf_transformation,[],[f25])).
% 3.97/1.00  
% 3.97/1.00  fof(f1,axiom,(
% 3.97/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.97/1.00  
% 3.97/1.00  fof(f15,plain,(
% 3.97/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.97/1.00    inference(ennf_transformation,[],[f1])).
% 3.97/1.00  
% 3.97/1.00  fof(f28,plain,(
% 3.97/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.97/1.00    inference(nnf_transformation,[],[f15])).
% 3.97/1.00  
% 3.97/1.00  fof(f29,plain,(
% 3.97/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.97/1.00    inference(rectify,[],[f28])).
% 3.97/1.00  
% 3.97/1.00  fof(f30,plain,(
% 3.97/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.97/1.00    introduced(choice_axiom,[])).
% 3.97/1.00  
% 3.97/1.00  fof(f31,plain,(
% 3.97/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.97/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).
% 3.97/1.00  
% 3.97/1.00  fof(f47,plain,(
% 3.97/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.97/1.00    inference(cnf_transformation,[],[f31])).
% 3.97/1.00  
% 3.97/1.00  fof(f13,conjecture,(
% 3.97/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 3.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.97/1.00  
% 3.97/1.00  fof(f14,negated_conjecture,(
% 3.97/1.00    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 3.97/1.00    inference(negated_conjecture,[],[f13])).
% 3.97/1.00  
% 3.97/1.00  fof(f26,plain,(
% 3.97/1.00    ? [X0] : (? [X1] : ((~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 3.97/1.00    inference(ennf_transformation,[],[f14])).
% 3.97/1.00  
% 3.97/1.00  fof(f27,plain,(
% 3.97/1.00    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 3.97/1.00    inference(flattening,[],[f26])).
% 3.97/1.00  
% 3.97/1.00  fof(f45,plain,(
% 3.97/1.00    ( ! [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) => (~r1_tarski(k3_relat_1(X0),k3_relat_1(sK6)) & r1_tarski(X0,sK6) & v1_relat_1(sK6))) )),
% 3.97/1.00    introduced(choice_axiom,[])).
% 3.97/1.00  
% 3.97/1.00  fof(f44,plain,(
% 3.97/1.00    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k3_relat_1(sK5),k3_relat_1(X1)) & r1_tarski(sK5,X1) & v1_relat_1(X1)) & v1_relat_1(sK5))),
% 3.97/1.00    introduced(choice_axiom,[])).
% 3.97/1.00  
% 3.97/1.00  fof(f46,plain,(
% 3.97/1.00    (~r1_tarski(k3_relat_1(sK5),k3_relat_1(sK6)) & r1_tarski(sK5,sK6) & v1_relat_1(sK6)) & v1_relat_1(sK5)),
% 3.97/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f27,f45,f44])).
% 3.97/1.00  
% 3.97/1.00  fof(f74,plain,(
% 3.97/1.00    r1_tarski(sK5,sK6)),
% 3.97/1.00    inference(cnf_transformation,[],[f46])).
% 3.97/1.00  
% 3.97/1.00  fof(f73,plain,(
% 3.97/1.00    v1_relat_1(sK6)),
% 3.97/1.00    inference(cnf_transformation,[],[f46])).
% 3.97/1.00  
% 3.97/1.00  fof(f9,axiom,(
% 3.97/1.00    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 3.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.97/1.00  
% 3.97/1.00  fof(f38,plain,(
% 3.97/1.00    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 3.97/1.00    inference(nnf_transformation,[],[f9])).
% 3.97/1.00  
% 3.97/1.00  fof(f39,plain,(
% 3.97/1.00    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 3.97/1.00    inference(rectify,[],[f38])).
% 3.97/1.00  
% 3.97/1.00  fof(f42,plain,(
% 3.97/1.00    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0))),
% 3.97/1.00    introduced(choice_axiom,[])).
% 3.97/1.00  
% 3.97/1.00  fof(f41,plain,(
% 3.97/1.00    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) => r2_hidden(k4_tarski(X2,sK3(X0,X1)),X0))) )),
% 3.97/1.00    introduced(choice_axiom,[])).
% 3.97/1.00  
% 3.97/1.00  fof(f40,plain,(
% 3.97/1.00    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK2(X0,X1),X3),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK2(X0,X1),X4),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 3.97/1.00    introduced(choice_axiom,[])).
% 3.97/1.00  
% 3.97/1.00  fof(f43,plain,(
% 3.97/1.00    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK2(X0,X1),X3),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 3.97/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f39,f42,f41,f40])).
% 3.97/1.00  
% 3.97/1.00  fof(f63,plain,(
% 3.97/1.00    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 3.97/1.00    inference(cnf_transformation,[],[f43])).
% 3.97/1.00  
% 3.97/1.00  fof(f83,plain,(
% 3.97/1.00    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 3.97/1.00    inference(equality_resolution,[],[f63])).
% 3.97/1.00  
% 3.97/1.00  fof(f49,plain,(
% 3.97/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.97/1.00    inference(cnf_transformation,[],[f31])).
% 3.97/1.00  
% 3.97/1.00  fof(f48,plain,(
% 3.97/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.97/1.00    inference(cnf_transformation,[],[f31])).
% 3.97/1.00  
% 3.97/1.00  fof(f11,axiom,(
% 3.97/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 3.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.97/1.00  
% 3.97/1.00  fof(f22,plain,(
% 3.97/1.00    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.97/1.00    inference(ennf_transformation,[],[f11])).
% 3.97/1.00  
% 3.97/1.00  fof(f23,plain,(
% 3.97/1.00    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.97/1.00    inference(flattening,[],[f22])).
% 3.97/1.00  
% 3.97/1.00  fof(f69,plain,(
% 3.97/1.00    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.97/1.00    inference(cnf_transformation,[],[f23])).
% 3.97/1.00  
% 3.97/1.00  fof(f8,axiom,(
% 3.97/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.97/1.00  
% 3.97/1.00  fof(f20,plain,(
% 3.97/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.97/1.00    inference(ennf_transformation,[],[f8])).
% 3.97/1.00  
% 3.97/1.00  fof(f62,plain,(
% 3.97/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.97/1.00    inference(cnf_transformation,[],[f20])).
% 3.97/1.00  
% 3.97/1.00  fof(f7,axiom,(
% 3.97/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.97/1.00  
% 3.97/1.00  fof(f37,plain,(
% 3.97/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.97/1.00    inference(nnf_transformation,[],[f7])).
% 3.97/1.00  
% 3.97/1.00  fof(f61,plain,(
% 3.97/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.97/1.00    inference(cnf_transformation,[],[f37])).
% 3.97/1.00  
% 3.97/1.00  fof(f10,axiom,(
% 3.97/1.00    ! [X0] : (v1_relat_1(X0) => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0))),
% 3.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.97/1.00  
% 3.97/1.00  fof(f21,plain,(
% 3.97/1.00    ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0))),
% 3.97/1.00    inference(ennf_transformation,[],[f10])).
% 3.97/1.00  
% 3.97/1.00  fof(f67,plain,(
% 3.97/1.00    ( ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.97/1.00    inference(cnf_transformation,[],[f21])).
% 3.97/1.00  
% 3.97/1.00  fof(f78,plain,(
% 3.97/1.00    ( ! [X0] : (k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.97/1.00    inference(definition_unfolding,[],[f67,f59])).
% 3.97/1.00  
% 3.97/1.00  fof(f3,axiom,(
% 3.97/1.00    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 3.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.97/1.00  
% 3.97/1.00  fof(f16,plain,(
% 3.97/1.00    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 3.97/1.00    inference(ennf_transformation,[],[f3])).
% 3.97/1.00  
% 3.97/1.00  fof(f56,plain,(
% 3.97/1.00    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 3.97/1.00    inference(cnf_transformation,[],[f16])).
% 3.97/1.00  
% 3.97/1.00  fof(f76,plain,(
% 3.97/1.00    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X2,X1))) | ~r1_tarski(X0,X1)) )),
% 3.97/1.00    inference(definition_unfolding,[],[f56,f59])).
% 3.97/1.00  
% 3.97/1.00  fof(f75,plain,(
% 3.97/1.00    ~r1_tarski(k3_relat_1(sK5),k3_relat_1(sK6))),
% 3.97/1.00    inference(cnf_transformation,[],[f46])).
% 3.97/1.00  
% 3.97/1.00  fof(f72,plain,(
% 3.97/1.00    v1_relat_1(sK5)),
% 3.97/1.00    inference(cnf_transformation,[],[f46])).
% 3.97/1.00  
% 3.97/1.00  cnf(c_11,plain,
% 3.97/1.00      ( ~ r1_tarski(X0,X1)
% 3.97/1.00      | ~ r1_tarski(X2,X1)
% 3.97/1.00      | r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) ),
% 3.97/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_4489,plain,
% 3.97/1.00      ( ~ r1_tarski(k2_relat_1(sK5),X0)
% 3.97/1.00      | ~ r1_tarski(k1_relat_1(sK5),X0)
% 3.97/1.00      | r1_tarski(k3_tarski(k2_tarski(k1_relat_1(sK5),k2_relat_1(sK5))),X0) ),
% 3.97/1.00      inference(instantiation,[status(thm)],[c_11]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_14450,plain,
% 3.97/1.00      ( ~ r1_tarski(k2_relat_1(sK5),k3_relat_1(sK6))
% 3.97/1.00      | ~ r1_tarski(k1_relat_1(sK5),k3_relat_1(sK6))
% 3.97/1.00      | r1_tarski(k3_tarski(k2_tarski(k1_relat_1(sK5),k2_relat_1(sK5))),k3_relat_1(sK6)) ),
% 3.97/1.00      inference(instantiation,[status(thm)],[c_4489]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_23,plain,
% 3.97/1.00      ( r2_hidden(X0,k3_relat_1(X1))
% 3.97/1.00      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 3.97/1.00      | ~ v1_relat_1(X1) ),
% 3.97/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_2,plain,
% 3.97/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.97/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_25,negated_conjecture,
% 3.97/1.00      ( r1_tarski(sK5,sK6) ),
% 3.97/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_1271,plain,
% 3.97/1.00      ( r2_hidden(X0,sK6) | ~ r2_hidden(X0,sK5) ),
% 3.97/1.00      inference(resolution,[status(thm)],[c_2,c_25]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_3909,plain,
% 3.97/1.00      ( r2_hidden(X0,k3_relat_1(sK6))
% 3.97/1.00      | ~ r2_hidden(k4_tarski(X0,X1),sK5)
% 3.97/1.00      | ~ v1_relat_1(sK6) ),
% 3.97/1.00      inference(resolution,[status(thm)],[c_23,c_1271]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_26,negated_conjecture,
% 3.97/1.00      ( v1_relat_1(sK6) ),
% 3.97/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_4358,plain,
% 3.97/1.00      ( ~ r2_hidden(k4_tarski(X0,X1),sK5)
% 3.97/1.00      | r2_hidden(X0,k3_relat_1(sK6)) ),
% 3.97/1.00      inference(global_propositional_subsumption,
% 3.97/1.00                [status(thm)],
% 3.97/1.00                [c_3909,c_26]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_4359,plain,
% 3.97/1.00      ( r2_hidden(X0,k3_relat_1(sK6))
% 3.97/1.00      | ~ r2_hidden(k4_tarski(X0,X1),sK5) ),
% 3.97/1.00      inference(renaming,[status(thm)],[c_4358]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_18,plain,
% 3.97/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.97/1.00      | r2_hidden(k4_tarski(X0,sK4(X1,X0)),X1) ),
% 3.97/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_4553,plain,
% 3.97/1.00      ( r2_hidden(X0,k3_relat_1(sK6)) | ~ r2_hidden(X0,k1_relat_1(sK5)) ),
% 3.97/1.00      inference(resolution,[status(thm)],[c_4359,c_18]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_0,plain,
% 3.97/1.00      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.97/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_4563,plain,
% 3.97/1.00      ( ~ r2_hidden(sK0(X0,k3_relat_1(sK6)),k1_relat_1(sK5))
% 3.97/1.00      | r1_tarski(X0,k3_relat_1(sK6)) ),
% 3.97/1.00      inference(resolution,[status(thm)],[c_4553,c_0]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_1,plain,
% 3.97/1.00      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.97/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_4716,plain,
% 3.97/1.00      ( r1_tarski(k1_relat_1(sK5),k3_relat_1(sK6)) ),
% 3.97/1.00      inference(resolution,[status(thm)],[c_4563,c_1]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_322,plain,
% 3.97/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.97/1.00      theory(equality) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_1196,plain,
% 3.97/1.00      ( ~ r1_tarski(X0,X1)
% 3.97/1.00      | r1_tarski(k3_relat_1(sK5),k3_relat_1(sK6))
% 3.97/1.00      | k3_relat_1(sK6) != X1
% 3.97/1.00      | k3_relat_1(sK5) != X0 ),
% 3.97/1.00      inference(instantiation,[status(thm)],[c_322]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_2998,plain,
% 3.97/1.00      ( r1_tarski(k3_relat_1(sK5),k3_relat_1(sK6))
% 3.97/1.00      | ~ r1_tarski(k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))),X1)
% 3.97/1.00      | k3_relat_1(sK6) != X1
% 3.97/1.00      | k3_relat_1(sK5) != k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))) ),
% 3.97/1.00      inference(instantiation,[status(thm)],[c_1196]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_3533,plain,
% 3.97/1.00      ( r1_tarski(k3_relat_1(sK5),k3_relat_1(sK6))
% 3.97/1.00      | ~ r1_tarski(k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))),k3_relat_1(sK6))
% 3.97/1.00      | k3_relat_1(sK6) != k3_relat_1(sK6)
% 3.97/1.00      | k3_relat_1(sK5) != k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))) ),
% 3.97/1.00      inference(instantiation,[status(thm)],[c_2998]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_3535,plain,
% 3.97/1.00      ( r1_tarski(k3_relat_1(sK5),k3_relat_1(sK6))
% 3.97/1.00      | ~ r1_tarski(k3_tarski(k2_tarski(k1_relat_1(sK5),k2_relat_1(sK5))),k3_relat_1(sK6))
% 3.97/1.00      | k3_relat_1(sK6) != k3_relat_1(sK6)
% 3.97/1.00      | k3_relat_1(sK5) != k3_tarski(k2_tarski(k1_relat_1(sK5),k2_relat_1(sK5))) ),
% 3.97/1.00      inference(instantiation,[status(thm)],[c_3533]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_20,plain,
% 3.97/1.00      ( ~ r1_tarski(X0,X1)
% 3.97/1.00      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 3.97/1.00      | ~ v1_relat_1(X0)
% 3.97/1.00      | ~ v1_relat_1(X1) ),
% 3.97/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_14,plain,
% 3.97/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.97/1.00      | ~ v1_relat_1(X1)
% 3.97/1.00      | v1_relat_1(X0) ),
% 3.97/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_12,plain,
% 3.97/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.97/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_292,plain,
% 3.97/1.00      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 3.97/1.00      | ~ r1_tarski(X0,X1)
% 3.97/1.00      | ~ v1_relat_1(X1) ),
% 3.97/1.00      inference(global_propositional_subsumption,
% 3.97/1.00                [status(thm)],
% 3.97/1.00                [c_20,c_14,c_12]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_293,plain,
% 3.97/1.00      ( ~ r1_tarski(X0,X1)
% 3.97/1.00      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 3.97/1.00      | ~ v1_relat_1(X1) ),
% 3.97/1.00      inference(renaming,[status(thm)],[c_292]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_913,plain,
% 3.97/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.97/1.00      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
% 3.97/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.97/1.00      inference(predicate_to_equality,[status(thm)],[c_293]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_917,plain,
% 3.97/1.00      ( v1_relat_1(sK6) = iProver_top ),
% 3.97/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_19,plain,
% 3.97/1.00      ( ~ v1_relat_1(X0)
% 3.97/1.00      | k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) ),
% 3.97/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_922,plain,
% 3.97/1.00      ( k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
% 3.97/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.97/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_1885,plain,
% 3.97/1.00      ( k3_tarski(k2_tarski(k1_relat_1(sK6),k2_relat_1(sK6))) = k3_relat_1(sK6) ),
% 3.97/1.00      inference(superposition,[status(thm)],[c_917,c_922]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_9,plain,
% 3.97/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X0,k3_tarski(k2_tarski(X2,X1))) ),
% 3.97/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_931,plain,
% 3.97/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.97/1.00      | r1_tarski(X0,k3_tarski(k2_tarski(X2,X1))) = iProver_top ),
% 3.97/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_2398,plain,
% 3.97/1.00      ( r1_tarski(X0,k3_relat_1(sK6)) = iProver_top
% 3.97/1.00      | r1_tarski(X0,k2_relat_1(sK6)) != iProver_top ),
% 3.97/1.00      inference(superposition,[status(thm)],[c_1885,c_931]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_2761,plain,
% 3.97/1.00      ( r1_tarski(X0,sK6) != iProver_top
% 3.97/1.00      | r1_tarski(k2_relat_1(X0),k3_relat_1(sK6)) = iProver_top
% 3.97/1.00      | v1_relat_1(sK6) != iProver_top ),
% 3.97/1.00      inference(superposition,[status(thm)],[c_913,c_2398]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_2771,plain,
% 3.97/1.00      ( ~ r1_tarski(X0,sK6)
% 3.97/1.00      | r1_tarski(k2_relat_1(X0),k3_relat_1(sK6))
% 3.97/1.00      | ~ v1_relat_1(sK6) ),
% 3.97/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_2761]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_2773,plain,
% 3.97/1.00      ( r1_tarski(k2_relat_1(sK5),k3_relat_1(sK6))
% 3.97/1.00      | ~ r1_tarski(sK5,sK6)
% 3.97/1.00      | ~ v1_relat_1(sK6) ),
% 3.97/1.00      inference(instantiation,[status(thm)],[c_2771]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_321,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_1297,plain,
% 3.97/1.00      ( X0 != X1 | k3_relat_1(sK5) != X1 | k3_relat_1(sK5) = X0 ),
% 3.97/1.00      inference(instantiation,[status(thm)],[c_321]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_1465,plain,
% 3.97/1.00      ( X0 != k3_relat_1(X1)
% 3.97/1.00      | k3_relat_1(sK5) = X0
% 3.97/1.00      | k3_relat_1(sK5) != k3_relat_1(X1) ),
% 3.97/1.00      inference(instantiation,[status(thm)],[c_1297]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_1725,plain,
% 3.97/1.00      ( k3_relat_1(sK5) != k3_relat_1(X0)
% 3.97/1.00      | k3_relat_1(sK5) = k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0)))
% 3.97/1.00      | k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))) != k3_relat_1(X0) ),
% 3.97/1.00      inference(instantiation,[status(thm)],[c_1465]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_1726,plain,
% 3.97/1.00      ( k3_relat_1(sK5) != k3_relat_1(sK5)
% 3.97/1.00      | k3_relat_1(sK5) = k3_tarski(k2_tarski(k1_relat_1(sK5),k2_relat_1(sK5)))
% 3.97/1.00      | k3_tarski(k2_tarski(k1_relat_1(sK5),k2_relat_1(sK5))) != k3_relat_1(sK5) ),
% 3.97/1.00      inference(instantiation,[status(thm)],[c_1725]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_320,plain,( X0 = X0 ),theory(equality) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_1483,plain,
% 3.97/1.00      ( k3_relat_1(sK6) = k3_relat_1(sK6) ),
% 3.97/1.00      inference(instantiation,[status(thm)],[c_320]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_339,plain,
% 3.97/1.00      ( sK5 = sK5 ),
% 3.97/1.00      inference(instantiation,[status(thm)],[c_320]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_329,plain,
% 3.97/1.00      ( X0 != X1 | k3_relat_1(X0) = k3_relat_1(X1) ),
% 3.97/1.00      theory(equality) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_337,plain,
% 3.97/1.00      ( k3_relat_1(sK5) = k3_relat_1(sK5) | sK5 != sK5 ),
% 3.97/1.00      inference(instantiation,[status(thm)],[c_329]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_43,plain,
% 3.97/1.00      ( ~ v1_relat_1(sK5)
% 3.97/1.00      | k3_tarski(k2_tarski(k1_relat_1(sK5),k2_relat_1(sK5))) = k3_relat_1(sK5) ),
% 3.97/1.00      inference(instantiation,[status(thm)],[c_19]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_24,negated_conjecture,
% 3.97/1.00      ( ~ r1_tarski(k3_relat_1(sK5),k3_relat_1(sK6)) ),
% 3.97/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_27,negated_conjecture,
% 3.97/1.00      ( v1_relat_1(sK5) ),
% 3.97/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(contradiction,plain,
% 3.97/1.00      ( $false ),
% 3.97/1.00      inference(minisat,
% 3.97/1.00                [status(thm)],
% 3.97/1.00                [c_14450,c_4716,c_3535,c_2773,c_1726,c_1483,c_339,c_337,
% 3.97/1.00                 c_43,c_24,c_25,c_26,c_27]) ).
% 3.97/1.00  
% 3.97/1.00  
% 3.97/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.97/1.00  
% 3.97/1.00  ------                               Statistics
% 3.97/1.00  
% 3.97/1.00  ------ Selected
% 3.97/1.00  
% 3.97/1.00  total_time:                             0.411
% 3.97/1.00  
%------------------------------------------------------------------------------
