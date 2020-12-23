%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:54:38 EST 2020

% Result     : Theorem 3.23s
% Output     : CNFRefutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 430 expanded)
%              Number of clauses        :   80 ( 156 expanded)
%              Number of leaves         :   21 (  87 expanded)
%              Depth                    :   19
%              Number of atoms          :  427 (1549 expanded)
%              Number of equality atoms :  140 ( 342 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ~ ( ! [X4,X5] :
              ~ ( r2_hidden(X5,X2)
                & r2_hidden(X4,X1)
                & k4_tarski(X4,X5) = X0 )
          & r2_hidden(X0,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
       => ~ ( ! [X4,X5] :
                ~ ( r2_hidden(X5,X2)
                  & r2_hidden(X4,X1)
                  & k4_tarski(X4,X5) = X0 )
            & r2_hidden(X0,X3) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4,X5] :
          ( ~ r2_hidden(X5,X2)
          | ~ r2_hidden(X4,X1)
          | k4_tarski(X4,X5) != X0 )
      & r2_hidden(X0,X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4,X5] :
          ( ~ r2_hidden(X5,X2)
          | ~ r2_hidden(X4,X1)
          | k4_tarski(X4,X5) != X0 )
      & r2_hidden(X0,X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(flattening,[],[f19])).

fof(f41,plain,
    ( ? [X0,X1,X2,X3] :
        ( ! [X4,X5] :
            ( ~ r2_hidden(X5,X2)
            | ~ r2_hidden(X4,X1)
            | k4_tarski(X4,X5) != X0 )
        & r2_hidden(X0,X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
   => ( ! [X5,X4] :
          ( ~ r2_hidden(X5,sK11)
          | ~ r2_hidden(X4,sK10)
          | k4_tarski(X4,X5) != sK9 )
      & r2_hidden(sK9,sK12)
      & m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X5,sK11)
        | ~ r2_hidden(X4,sK10)
        | k4_tarski(X4,X5) != sK9 )
    & r2_hidden(sK9,sK12)
    & m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11,sK12])],[f20,f41])).

fof(f63,plain,(
    m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))) ),
    inference(cnf_transformation,[],[f42])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f21])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f64,plain,(
    r2_hidden(sK9,sK12) ),
    inference(cnf_transformation,[],[f42])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ~ ( ! [X3,X4] : k4_tarski(X3,X4) != X0
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
     => k4_tarski(sK1(X0),sK2(X0)) = X0 ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k4_tarski(sK1(X0),sK2(X0)) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f13,f25])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(sK1(X0),sK2(X0)) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f7])).

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f39,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK8(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK7(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0)
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK6(X0,X1)),X0)
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0)
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0)
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK8(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f36,f39,f38,f37])).

fof(f57,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f68,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f6])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f33,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK4(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK3(X0,X1),X3),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK3(X0,X1),X3),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f30,f33,f32,f31])).

fof(f53,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f66,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f65,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X5,sK11)
      | ~ r2_hidden(X4,sK10)
      | k4_tarski(X4,X5) != sK9 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_18,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_303,plain,
    ( v5_relat_1(X0,X1)
    | k1_zfmisc_1(k2_zfmisc_1(X2,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))
    | sK12 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_22])).

cnf(c_304,plain,
    ( v5_relat_1(sK12,X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)) ),
    inference(unflattening,[status(thm)],[c_303])).

cnf(c_8,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_291,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))
    | sK12 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_22])).

cnf(c_292,plain,
    ( v1_relat_1(sK12)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)) ),
    inference(unflattening,[status(thm)],[c_291])).

cnf(c_350,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))
    | sK12 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_292])).

cnf(c_351,plain,
    ( ~ v5_relat_1(sK12,X0)
    | r1_tarski(k2_relat_1(sK12),X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)) ),
    inference(unflattening,[status(thm)],[c_350])).

cnf(c_387,plain,
    ( r1_tarski(k2_relat_1(sK12),X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))
    | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)) ),
    inference(resolution,[status(thm)],[c_304,c_351])).

cnf(c_666,plain,
    ( r1_tarski(k2_relat_1(sK12),X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_387])).

cnf(c_1002,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))
    | r1_tarski(k2_relat_1(sK12),X1) = iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_666])).

cnf(c_667,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_387])).

cnf(c_687,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_667])).

cnf(c_688,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))
    | r1_tarski(k2_relat_1(sK12),X1) = iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_666])).

cnf(c_665,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_387])).

cnf(c_1003,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_665])).

cnf(c_1243,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1003])).

cnf(c_1355,plain,
    ( r1_tarski(k2_relat_1(sK12),X1) = iProver_top
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1002,c_687,c_688,c_1243])).

cnf(c_1356,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))
    | r1_tarski(k2_relat_1(sK12),X1) = iProver_top ),
    inference(renaming,[status(thm)],[c_1355])).

cnf(c_1361,plain,
    ( r1_tarski(k2_relat_1(sK12),sK11) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1356])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1018,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_264,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)) != k1_zfmisc_1(X2)
    | sK12 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_22])).

cnf(c_265,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,sK12)
    | k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)) != k1_zfmisc_1(X1) ),
    inference(unflattening,[status(thm)],[c_264])).

cnf(c_1005,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)) != k1_zfmisc_1(X0)
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(X1,sK12) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_265])).

cnf(c_1181,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK10,sK11)) = iProver_top
    | r2_hidden(X0,sK12) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1005])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1019,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1490,plain,
    ( r2_hidden(sK0(X0,k2_zfmisc_1(sK10,sK11)),sK12) != iProver_top
    | r1_tarski(X0,k2_zfmisc_1(sK10,sK11)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1181,c_1019])).

cnf(c_1997,plain,
    ( r1_tarski(sK12,k2_zfmisc_1(sK10,sK11)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1018,c_1490])).

cnf(c_21,negated_conjecture,
    ( r2_hidden(sK9,sK12) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1006,plain,
    ( r2_hidden(sK9,sK12) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1017,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2369,plain,
    ( r2_hidden(sK9,X0) = iProver_top
    | r1_tarski(sK12,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1006,c_1017])).

cnf(c_2485,plain,
    ( r2_hidden(sK9,k2_zfmisc_1(sK10,sK11)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1997,c_2369])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | k4_tarski(sK1(X0),sK2(X0)) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1016,plain,
    ( k4_tarski(sK1(X0),sK2(X0)) = X0
    | r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2490,plain,
    ( k4_tarski(sK1(sK9),sK2(sK9)) = sK9 ),
    inference(superposition,[status(thm)],[c_2485,c_1016])).

cnf(c_15,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1009,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2528,plain,
    ( r2_hidden(sK2(sK9),k2_relat_1(X0)) = iProver_top
    | r2_hidden(sK9,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2490,c_1009])).

cnf(c_2985,plain,
    ( r2_hidden(sK2(sK9),X0) = iProver_top
    | r2_hidden(sK9,X1) != iProver_top
    | r1_tarski(k2_relat_1(X1),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2528,c_1017])).

cnf(c_8165,plain,
    ( r2_hidden(sK2(sK9),sK11) = iProver_top
    | r2_hidden(sK9,sK12) != iProver_top ),
    inference(superposition,[status(thm)],[c_1361,c_2985])).

cnf(c_3979,plain,
    ( r2_hidden(sK1(sK9),X0)
    | ~ r2_hidden(sK1(sK9),k1_relat_1(sK12))
    | ~ r1_tarski(k1_relat_1(sK12),X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_3980,plain,
    ( r2_hidden(sK1(sK9),X0) = iProver_top
    | r2_hidden(sK1(sK9),k1_relat_1(sK12)) != iProver_top
    | r1_tarski(k1_relat_1(sK12),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3979])).

cnf(c_3982,plain,
    ( r2_hidden(sK1(sK9),k1_relat_1(sK12)) != iProver_top
    | r2_hidden(sK1(sK9),sK10) = iProver_top
    | r1_tarski(k1_relat_1(sK12),sK10) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3980])).

cnf(c_11,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2600,plain,
    ( ~ r2_hidden(k4_tarski(sK1(sK9),sK2(sK9)),sK12)
    | r2_hidden(sK1(sK9),k1_relat_1(sK12)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2601,plain,
    ( r2_hidden(k4_tarski(sK1(sK9),sK2(sK9)),sK12) != iProver_top
    | r2_hidden(sK1(sK9),k1_relat_1(sK12)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2600])).

cnf(c_20,negated_conjecture,
    ( ~ r2_hidden(X0,sK10)
    | ~ r2_hidden(X1,sK11)
    | k4_tarski(X0,X1) != sK9 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1007,plain,
    ( k4_tarski(X0,X1) != sK9
    | r2_hidden(X0,sK10) != iProver_top
    | r2_hidden(X1,sK11) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2530,plain,
    ( r2_hidden(sK2(sK9),sK11) != iProver_top
    | r2_hidden(sK1(sK9),sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_2490,c_1007])).

cnf(c_672,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1188,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK9,sK12)
    | X1 != sK12
    | X0 != sK9 ),
    inference(instantiation,[status(thm)],[c_672])).

cnf(c_1291,plain,
    ( r2_hidden(X0,sK12)
    | ~ r2_hidden(sK9,sK12)
    | X0 != sK9
    | sK12 != sK12 ),
    inference(instantiation,[status(thm)],[c_1188])).

cnf(c_1961,plain,
    ( r2_hidden(k4_tarski(sK1(sK9),sK2(sK9)),sK12)
    | ~ r2_hidden(sK9,sK12)
    | k4_tarski(sK1(sK9),sK2(sK9)) != sK9
    | sK12 != sK12 ),
    inference(instantiation,[status(thm)],[c_1291])).

cnf(c_1962,plain,
    ( k4_tarski(sK1(sK9),sK2(sK9)) != sK9
    | sK12 != sK12
    | r2_hidden(k4_tarski(sK1(sK9),sK2(sK9)),sK12) = iProver_top
    | r2_hidden(sK9,sK12) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1961])).

cnf(c_1202,plain,
    ( ~ r2_hidden(sK9,k2_zfmisc_1(X0,X1))
    | k4_tarski(sK1(sK9),sK2(sK9)) = sK9 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1698,plain,
    ( ~ r2_hidden(sK9,k2_zfmisc_1(sK10,sK11))
    | k4_tarski(sK1(sK9),sK2(sK9)) = sK9 ),
    inference(instantiation,[status(thm)],[c_1202])).

cnf(c_1150,plain,
    ( r2_hidden(sK9,X0)
    | ~ r2_hidden(sK9,sK12)
    | k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)) != k1_zfmisc_1(X0) ),
    inference(instantiation,[status(thm)],[c_265])).

cnf(c_1201,plain,
    ( r2_hidden(sK9,k2_zfmisc_1(X0,X1))
    | ~ r2_hidden(sK9,sK12)
    | k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_1150])).

cnf(c_1412,plain,
    ( r2_hidden(sK9,k2_zfmisc_1(sK10,sK11))
    | ~ r2_hidden(sK9,sK12)
    | k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)) != k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)) ),
    inference(instantiation,[status(thm)],[c_1201])).

cnf(c_669,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1292,plain,
    ( sK12 = sK12 ),
    inference(instantiation,[status(thm)],[c_669])).

cnf(c_6,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_19,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_279,plain,
    ( v4_relat_1(X0,X1)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))
    | sK12 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_22])).

cnf(c_280,plain,
    ( v4_relat_1(sK12,X0)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)) ),
    inference(unflattening,[status(thm)],[c_279])).

cnf(c_329,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | X2 != X1
    | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))
    | sK12 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_280])).

cnf(c_330,plain,
    ( r1_tarski(k1_relat_1(sK12),X0)
    | ~ v1_relat_1(sK12)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)) ),
    inference(unflattening,[status(thm)],[c_329])).

cnf(c_334,plain,
    ( r1_tarski(k1_relat_1(sK12),X0)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_330,c_292])).

cnf(c_1156,plain,
    ( r1_tarski(k1_relat_1(sK12),sK10)
    | k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)) != k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)) ),
    inference(instantiation,[status(thm)],[c_334])).

cnf(c_1157,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)) != k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))
    | r1_tarski(k1_relat_1(sK12),sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1156])).

cnf(c_1155,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)) = k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)) ),
    inference(instantiation,[status(thm)],[c_669])).

cnf(c_24,plain,
    ( r2_hidden(sK9,sK12) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8165,c_3982,c_2601,c_2530,c_1962,c_1698,c_1412,c_1292,c_1157,c_1155,c_24,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:54:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.23/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/1.00  
% 3.23/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.23/1.00  
% 3.23/1.00  ------  iProver source info
% 3.23/1.00  
% 3.23/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.23/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.23/1.00  git: non_committed_changes: false
% 3.23/1.00  git: last_make_outside_of_git: false
% 3.23/1.00  
% 3.23/1.00  ------ 
% 3.23/1.00  
% 3.23/1.00  ------ Input Options
% 3.23/1.00  
% 3.23/1.00  --out_options                           all
% 3.23/1.00  --tptp_safe_out                         true
% 3.23/1.00  --problem_path                          ""
% 3.23/1.00  --include_path                          ""
% 3.23/1.00  --clausifier                            res/vclausify_rel
% 3.23/1.00  --clausifier_options                    --mode clausify
% 3.23/1.00  --stdin                                 false
% 3.23/1.00  --stats_out                             all
% 3.23/1.00  
% 3.23/1.00  ------ General Options
% 3.23/1.00  
% 3.23/1.00  --fof                                   false
% 3.23/1.00  --time_out_real                         305.
% 3.23/1.00  --time_out_virtual                      -1.
% 3.23/1.00  --symbol_type_check                     false
% 3.23/1.00  --clausify_out                          false
% 3.23/1.00  --sig_cnt_out                           false
% 3.23/1.00  --trig_cnt_out                          false
% 3.23/1.00  --trig_cnt_out_tolerance                1.
% 3.23/1.00  --trig_cnt_out_sk_spl                   false
% 3.23/1.00  --abstr_cl_out                          false
% 3.23/1.00  
% 3.23/1.00  ------ Global Options
% 3.23/1.00  
% 3.23/1.00  --schedule                              default
% 3.23/1.00  --add_important_lit                     false
% 3.23/1.00  --prop_solver_per_cl                    1000
% 3.23/1.00  --min_unsat_core                        false
% 3.23/1.00  --soft_assumptions                      false
% 3.23/1.00  --soft_lemma_size                       3
% 3.23/1.00  --prop_impl_unit_size                   0
% 3.23/1.00  --prop_impl_unit                        []
% 3.23/1.00  --share_sel_clauses                     true
% 3.23/1.00  --reset_solvers                         false
% 3.23/1.00  --bc_imp_inh                            [conj_cone]
% 3.23/1.00  --conj_cone_tolerance                   3.
% 3.23/1.00  --extra_neg_conj                        none
% 3.23/1.00  --large_theory_mode                     true
% 3.23/1.00  --prolific_symb_bound                   200
% 3.23/1.00  --lt_threshold                          2000
% 3.23/1.00  --clause_weak_htbl                      true
% 3.23/1.00  --gc_record_bc_elim                     false
% 3.23/1.00  
% 3.23/1.00  ------ Preprocessing Options
% 3.23/1.00  
% 3.23/1.00  --preprocessing_flag                    true
% 3.23/1.00  --time_out_prep_mult                    0.1
% 3.23/1.00  --splitting_mode                        input
% 3.23/1.00  --splitting_grd                         true
% 3.23/1.00  --splitting_cvd                         false
% 3.23/1.00  --splitting_cvd_svl                     false
% 3.23/1.00  --splitting_nvd                         32
% 3.23/1.00  --sub_typing                            true
% 3.23/1.00  --prep_gs_sim                           true
% 3.23/1.00  --prep_unflatten                        true
% 3.23/1.00  --prep_res_sim                          true
% 3.23/1.00  --prep_upred                            true
% 3.23/1.00  --prep_sem_filter                       exhaustive
% 3.23/1.00  --prep_sem_filter_out                   false
% 3.23/1.00  --pred_elim                             true
% 3.23/1.00  --res_sim_input                         true
% 3.23/1.00  --eq_ax_congr_red                       true
% 3.23/1.00  --pure_diseq_elim                       true
% 3.23/1.00  --brand_transform                       false
% 3.23/1.00  --non_eq_to_eq                          false
% 3.23/1.00  --prep_def_merge                        true
% 3.23/1.00  --prep_def_merge_prop_impl              false
% 3.23/1.00  --prep_def_merge_mbd                    true
% 3.23/1.00  --prep_def_merge_tr_red                 false
% 3.23/1.00  --prep_def_merge_tr_cl                  false
% 3.23/1.00  --smt_preprocessing                     true
% 3.23/1.00  --smt_ac_axioms                         fast
% 3.23/1.00  --preprocessed_out                      false
% 3.23/1.00  --preprocessed_stats                    false
% 3.23/1.00  
% 3.23/1.00  ------ Abstraction refinement Options
% 3.23/1.00  
% 3.23/1.00  --abstr_ref                             []
% 3.23/1.00  --abstr_ref_prep                        false
% 3.23/1.00  --abstr_ref_until_sat                   false
% 3.23/1.00  --abstr_ref_sig_restrict                funpre
% 3.23/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.23/1.00  --abstr_ref_under                       []
% 3.23/1.00  
% 3.23/1.00  ------ SAT Options
% 3.23/1.00  
% 3.23/1.00  --sat_mode                              false
% 3.23/1.00  --sat_fm_restart_options                ""
% 3.23/1.00  --sat_gr_def                            false
% 3.23/1.00  --sat_epr_types                         true
% 3.23/1.00  --sat_non_cyclic_types                  false
% 3.23/1.00  --sat_finite_models                     false
% 3.23/1.00  --sat_fm_lemmas                         false
% 3.23/1.00  --sat_fm_prep                           false
% 3.23/1.00  --sat_fm_uc_incr                        true
% 3.23/1.00  --sat_out_model                         small
% 3.23/1.00  --sat_out_clauses                       false
% 3.23/1.00  
% 3.23/1.00  ------ QBF Options
% 3.23/1.00  
% 3.23/1.00  --qbf_mode                              false
% 3.23/1.00  --qbf_elim_univ                         false
% 3.23/1.00  --qbf_dom_inst                          none
% 3.23/1.00  --qbf_dom_pre_inst                      false
% 3.23/1.00  --qbf_sk_in                             false
% 3.23/1.00  --qbf_pred_elim                         true
% 3.23/1.00  --qbf_split                             512
% 3.23/1.00  
% 3.23/1.00  ------ BMC1 Options
% 3.23/1.00  
% 3.23/1.00  --bmc1_incremental                      false
% 3.23/1.00  --bmc1_axioms                           reachable_all
% 3.23/1.00  --bmc1_min_bound                        0
% 3.23/1.00  --bmc1_max_bound                        -1
% 3.23/1.00  --bmc1_max_bound_default                -1
% 3.23/1.00  --bmc1_symbol_reachability              true
% 3.23/1.00  --bmc1_property_lemmas                  false
% 3.23/1.00  --bmc1_k_induction                      false
% 3.23/1.00  --bmc1_non_equiv_states                 false
% 3.23/1.00  --bmc1_deadlock                         false
% 3.23/1.00  --bmc1_ucm                              false
% 3.23/1.00  --bmc1_add_unsat_core                   none
% 3.23/1.00  --bmc1_unsat_core_children              false
% 3.23/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.23/1.00  --bmc1_out_stat                         full
% 3.23/1.00  --bmc1_ground_init                      false
% 3.23/1.00  --bmc1_pre_inst_next_state              false
% 3.23/1.00  --bmc1_pre_inst_state                   false
% 3.23/1.00  --bmc1_pre_inst_reach_state             false
% 3.23/1.00  --bmc1_out_unsat_core                   false
% 3.23/1.00  --bmc1_aig_witness_out                  false
% 3.23/1.00  --bmc1_verbose                          false
% 3.23/1.00  --bmc1_dump_clauses_tptp                false
% 3.23/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.23/1.00  --bmc1_dump_file                        -
% 3.23/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.23/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.23/1.00  --bmc1_ucm_extend_mode                  1
% 3.23/1.00  --bmc1_ucm_init_mode                    2
% 3.23/1.00  --bmc1_ucm_cone_mode                    none
% 3.23/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.23/1.00  --bmc1_ucm_relax_model                  4
% 3.23/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.23/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.23/1.00  --bmc1_ucm_layered_model                none
% 3.23/1.00  --bmc1_ucm_max_lemma_size               10
% 3.23/1.00  
% 3.23/1.00  ------ AIG Options
% 3.23/1.00  
% 3.23/1.00  --aig_mode                              false
% 3.23/1.00  
% 3.23/1.00  ------ Instantiation Options
% 3.23/1.00  
% 3.23/1.00  --instantiation_flag                    true
% 3.23/1.00  --inst_sos_flag                         false
% 3.23/1.00  --inst_sos_phase                        true
% 3.23/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.23/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.23/1.00  --inst_lit_sel_side                     num_symb
% 3.23/1.00  --inst_solver_per_active                1400
% 3.23/1.00  --inst_solver_calls_frac                1.
% 3.23/1.00  --inst_passive_queue_type               priority_queues
% 3.23/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.23/1.00  --inst_passive_queues_freq              [25;2]
% 3.23/1.00  --inst_dismatching                      true
% 3.23/1.00  --inst_eager_unprocessed_to_passive     true
% 3.23/1.00  --inst_prop_sim_given                   true
% 3.23/1.00  --inst_prop_sim_new                     false
% 3.23/1.00  --inst_subs_new                         false
% 3.23/1.00  --inst_eq_res_simp                      false
% 3.23/1.00  --inst_subs_given                       false
% 3.23/1.00  --inst_orphan_elimination               true
% 3.23/1.00  --inst_learning_loop_flag               true
% 3.23/1.00  --inst_learning_start                   3000
% 3.23/1.00  --inst_learning_factor                  2
% 3.23/1.00  --inst_start_prop_sim_after_learn       3
% 3.23/1.00  --inst_sel_renew                        solver
% 3.23/1.00  --inst_lit_activity_flag                true
% 3.23/1.00  --inst_restr_to_given                   false
% 3.23/1.00  --inst_activity_threshold               500
% 3.23/1.00  --inst_out_proof                        true
% 3.23/1.00  
% 3.23/1.00  ------ Resolution Options
% 3.23/1.00  
% 3.23/1.00  --resolution_flag                       true
% 3.23/1.00  --res_lit_sel                           adaptive
% 3.23/1.00  --res_lit_sel_side                      none
% 3.23/1.00  --res_ordering                          kbo
% 3.23/1.00  --res_to_prop_solver                    active
% 3.23/1.00  --res_prop_simpl_new                    false
% 3.23/1.00  --res_prop_simpl_given                  true
% 3.23/1.00  --res_passive_queue_type                priority_queues
% 3.23/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.23/1.00  --res_passive_queues_freq               [15;5]
% 3.23/1.00  --res_forward_subs                      full
% 3.23/1.00  --res_backward_subs                     full
% 3.23/1.00  --res_forward_subs_resolution           true
% 3.23/1.00  --res_backward_subs_resolution          true
% 3.23/1.00  --res_orphan_elimination                true
% 3.23/1.00  --res_time_limit                        2.
% 3.23/1.00  --res_out_proof                         true
% 3.23/1.00  
% 3.23/1.00  ------ Superposition Options
% 3.23/1.00  
% 3.23/1.00  --superposition_flag                    true
% 3.23/1.00  --sup_passive_queue_type                priority_queues
% 3.23/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.23/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.23/1.00  --demod_completeness_check              fast
% 3.23/1.00  --demod_use_ground                      true
% 3.23/1.00  --sup_to_prop_solver                    passive
% 3.23/1.00  --sup_prop_simpl_new                    true
% 3.23/1.00  --sup_prop_simpl_given                  true
% 3.23/1.00  --sup_fun_splitting                     false
% 3.23/1.00  --sup_smt_interval                      50000
% 3.23/1.00  
% 3.23/1.00  ------ Superposition Simplification Setup
% 3.23/1.00  
% 3.23/1.00  --sup_indices_passive                   []
% 3.23/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.23/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/1.00  --sup_full_bw                           [BwDemod]
% 3.23/1.00  --sup_immed_triv                        [TrivRules]
% 3.23/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.23/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/1.00  --sup_immed_bw_main                     []
% 3.23/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.23/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.23/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.23/1.00  
% 3.23/1.00  ------ Combination Options
% 3.23/1.00  
% 3.23/1.00  --comb_res_mult                         3
% 3.23/1.00  --comb_sup_mult                         2
% 3.23/1.00  --comb_inst_mult                        10
% 3.23/1.00  
% 3.23/1.00  ------ Debug Options
% 3.23/1.00  
% 3.23/1.00  --dbg_backtrace                         false
% 3.23/1.00  --dbg_dump_prop_clauses                 false
% 3.23/1.00  --dbg_dump_prop_clauses_file            -
% 3.23/1.00  --dbg_out_stat                          false
% 3.23/1.00  ------ Parsing...
% 3.23/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.23/1.00  
% 3.23/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.23/1.00  
% 3.23/1.00  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.23/1.00  
% 3.23/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.23/1.00  ------ Proving...
% 3.23/1.00  ------ Problem Properties 
% 3.23/1.00  
% 3.23/1.00  
% 3.23/1.00  clauses                                 19
% 3.23/1.00  conjectures                             2
% 3.23/1.00  EPR                                     3
% 3.23/1.00  Horn                                    15
% 3.23/1.00  unary                                   1
% 3.23/1.00  binary                                  10
% 3.23/1.00  lits                                    45
% 3.23/1.00  lits eq                                 10
% 3.23/1.00  fd_pure                                 0
% 3.23/1.00  fd_pseudo                               0
% 3.23/1.00  fd_cond                                 0
% 3.23/1.00  fd_pseudo_cond                          4
% 3.23/1.00  AC symbols                              0
% 3.23/1.00  
% 3.23/1.00  ------ Schedule dynamic 5 is on 
% 3.23/1.00  
% 3.23/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.23/1.00  
% 3.23/1.00  
% 3.23/1.00  ------ 
% 3.23/1.00  Current options:
% 3.23/1.00  ------ 
% 3.23/1.00  
% 3.23/1.00  ------ Input Options
% 3.23/1.00  
% 3.23/1.00  --out_options                           all
% 3.23/1.00  --tptp_safe_out                         true
% 3.23/1.00  --problem_path                          ""
% 3.23/1.00  --include_path                          ""
% 3.23/1.00  --clausifier                            res/vclausify_rel
% 3.23/1.00  --clausifier_options                    --mode clausify
% 3.23/1.00  --stdin                                 false
% 3.23/1.00  --stats_out                             all
% 3.23/1.00  
% 3.23/1.00  ------ General Options
% 3.23/1.00  
% 3.23/1.00  --fof                                   false
% 3.23/1.00  --time_out_real                         305.
% 3.23/1.00  --time_out_virtual                      -1.
% 3.23/1.00  --symbol_type_check                     false
% 3.23/1.00  --clausify_out                          false
% 3.23/1.00  --sig_cnt_out                           false
% 3.23/1.00  --trig_cnt_out                          false
% 3.23/1.00  --trig_cnt_out_tolerance                1.
% 3.23/1.00  --trig_cnt_out_sk_spl                   false
% 3.23/1.00  --abstr_cl_out                          false
% 3.23/1.00  
% 3.23/1.00  ------ Global Options
% 3.23/1.00  
% 3.23/1.00  --schedule                              default
% 3.23/1.00  --add_important_lit                     false
% 3.23/1.00  --prop_solver_per_cl                    1000
% 3.23/1.00  --min_unsat_core                        false
% 3.23/1.00  --soft_assumptions                      false
% 3.23/1.00  --soft_lemma_size                       3
% 3.23/1.00  --prop_impl_unit_size                   0
% 3.23/1.00  --prop_impl_unit                        []
% 3.23/1.00  --share_sel_clauses                     true
% 3.23/1.00  --reset_solvers                         false
% 3.23/1.00  --bc_imp_inh                            [conj_cone]
% 3.23/1.00  --conj_cone_tolerance                   3.
% 3.23/1.00  --extra_neg_conj                        none
% 3.23/1.00  --large_theory_mode                     true
% 3.23/1.00  --prolific_symb_bound                   200
% 3.23/1.00  --lt_threshold                          2000
% 3.23/1.00  --clause_weak_htbl                      true
% 3.23/1.00  --gc_record_bc_elim                     false
% 3.23/1.00  
% 3.23/1.00  ------ Preprocessing Options
% 3.23/1.00  
% 3.23/1.00  --preprocessing_flag                    true
% 3.23/1.00  --time_out_prep_mult                    0.1
% 3.23/1.00  --splitting_mode                        input
% 3.23/1.00  --splitting_grd                         true
% 3.23/1.00  --splitting_cvd                         false
% 3.23/1.00  --splitting_cvd_svl                     false
% 3.23/1.00  --splitting_nvd                         32
% 3.23/1.00  --sub_typing                            true
% 3.23/1.00  --prep_gs_sim                           true
% 3.23/1.00  --prep_unflatten                        true
% 3.23/1.00  --prep_res_sim                          true
% 3.23/1.00  --prep_upred                            true
% 3.23/1.00  --prep_sem_filter                       exhaustive
% 3.23/1.00  --prep_sem_filter_out                   false
% 3.23/1.00  --pred_elim                             true
% 3.23/1.00  --res_sim_input                         true
% 3.23/1.00  --eq_ax_congr_red                       true
% 3.23/1.00  --pure_diseq_elim                       true
% 3.23/1.00  --brand_transform                       false
% 3.23/1.00  --non_eq_to_eq                          false
% 3.23/1.00  --prep_def_merge                        true
% 3.23/1.00  --prep_def_merge_prop_impl              false
% 3.23/1.00  --prep_def_merge_mbd                    true
% 3.23/1.00  --prep_def_merge_tr_red                 false
% 3.23/1.00  --prep_def_merge_tr_cl                  false
% 3.23/1.00  --smt_preprocessing                     true
% 3.23/1.00  --smt_ac_axioms                         fast
% 3.23/1.00  --preprocessed_out                      false
% 3.23/1.00  --preprocessed_stats                    false
% 3.23/1.00  
% 3.23/1.00  ------ Abstraction refinement Options
% 3.23/1.00  
% 3.23/1.00  --abstr_ref                             []
% 3.23/1.00  --abstr_ref_prep                        false
% 3.23/1.00  --abstr_ref_until_sat                   false
% 3.23/1.00  --abstr_ref_sig_restrict                funpre
% 3.23/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.23/1.00  --abstr_ref_under                       []
% 3.23/1.00  
% 3.23/1.00  ------ SAT Options
% 3.23/1.00  
% 3.23/1.00  --sat_mode                              false
% 3.23/1.00  --sat_fm_restart_options                ""
% 3.23/1.00  --sat_gr_def                            false
% 3.23/1.00  --sat_epr_types                         true
% 3.23/1.00  --sat_non_cyclic_types                  false
% 3.23/1.00  --sat_finite_models                     false
% 3.23/1.00  --sat_fm_lemmas                         false
% 3.23/1.00  --sat_fm_prep                           false
% 3.23/1.00  --sat_fm_uc_incr                        true
% 3.23/1.00  --sat_out_model                         small
% 3.23/1.00  --sat_out_clauses                       false
% 3.23/1.00  
% 3.23/1.00  ------ QBF Options
% 3.23/1.00  
% 3.23/1.00  --qbf_mode                              false
% 3.23/1.00  --qbf_elim_univ                         false
% 3.23/1.00  --qbf_dom_inst                          none
% 3.23/1.00  --qbf_dom_pre_inst                      false
% 3.23/1.00  --qbf_sk_in                             false
% 3.23/1.00  --qbf_pred_elim                         true
% 3.23/1.00  --qbf_split                             512
% 3.23/1.00  
% 3.23/1.00  ------ BMC1 Options
% 3.23/1.00  
% 3.23/1.00  --bmc1_incremental                      false
% 3.23/1.00  --bmc1_axioms                           reachable_all
% 3.23/1.00  --bmc1_min_bound                        0
% 3.23/1.00  --bmc1_max_bound                        -1
% 3.23/1.00  --bmc1_max_bound_default                -1
% 3.23/1.00  --bmc1_symbol_reachability              true
% 3.23/1.00  --bmc1_property_lemmas                  false
% 3.23/1.00  --bmc1_k_induction                      false
% 3.23/1.00  --bmc1_non_equiv_states                 false
% 3.23/1.00  --bmc1_deadlock                         false
% 3.23/1.00  --bmc1_ucm                              false
% 3.23/1.00  --bmc1_add_unsat_core                   none
% 3.23/1.00  --bmc1_unsat_core_children              false
% 3.23/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.23/1.00  --bmc1_out_stat                         full
% 3.23/1.00  --bmc1_ground_init                      false
% 3.23/1.00  --bmc1_pre_inst_next_state              false
% 3.23/1.00  --bmc1_pre_inst_state                   false
% 3.23/1.00  --bmc1_pre_inst_reach_state             false
% 3.23/1.00  --bmc1_out_unsat_core                   false
% 3.23/1.00  --bmc1_aig_witness_out                  false
% 3.23/1.00  --bmc1_verbose                          false
% 3.23/1.00  --bmc1_dump_clauses_tptp                false
% 3.23/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.23/1.00  --bmc1_dump_file                        -
% 3.23/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.23/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.23/1.00  --bmc1_ucm_extend_mode                  1
% 3.23/1.00  --bmc1_ucm_init_mode                    2
% 3.23/1.00  --bmc1_ucm_cone_mode                    none
% 3.23/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.23/1.00  --bmc1_ucm_relax_model                  4
% 3.23/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.23/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.23/1.00  --bmc1_ucm_layered_model                none
% 3.23/1.00  --bmc1_ucm_max_lemma_size               10
% 3.23/1.00  
% 3.23/1.00  ------ AIG Options
% 3.23/1.00  
% 3.23/1.00  --aig_mode                              false
% 3.23/1.00  
% 3.23/1.00  ------ Instantiation Options
% 3.23/1.00  
% 3.23/1.00  --instantiation_flag                    true
% 3.23/1.00  --inst_sos_flag                         false
% 3.23/1.00  --inst_sos_phase                        true
% 3.23/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.23/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.23/1.00  --inst_lit_sel_side                     none
% 3.23/1.00  --inst_solver_per_active                1400
% 3.23/1.00  --inst_solver_calls_frac                1.
% 3.23/1.00  --inst_passive_queue_type               priority_queues
% 3.23/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.23/1.00  --inst_passive_queues_freq              [25;2]
% 3.23/1.00  --inst_dismatching                      true
% 3.23/1.00  --inst_eager_unprocessed_to_passive     true
% 3.23/1.00  --inst_prop_sim_given                   true
% 3.23/1.00  --inst_prop_sim_new                     false
% 3.23/1.00  --inst_subs_new                         false
% 3.23/1.00  --inst_eq_res_simp                      false
% 3.23/1.00  --inst_subs_given                       false
% 3.23/1.00  --inst_orphan_elimination               true
% 3.23/1.00  --inst_learning_loop_flag               true
% 3.23/1.00  --inst_learning_start                   3000
% 3.23/1.00  --inst_learning_factor                  2
% 3.23/1.00  --inst_start_prop_sim_after_learn       3
% 3.23/1.00  --inst_sel_renew                        solver
% 3.23/1.00  --inst_lit_activity_flag                true
% 3.23/1.00  --inst_restr_to_given                   false
% 3.23/1.00  --inst_activity_threshold               500
% 3.23/1.00  --inst_out_proof                        true
% 3.23/1.00  
% 3.23/1.00  ------ Resolution Options
% 3.23/1.00  
% 3.23/1.00  --resolution_flag                       false
% 3.23/1.00  --res_lit_sel                           adaptive
% 3.23/1.00  --res_lit_sel_side                      none
% 3.23/1.00  --res_ordering                          kbo
% 3.23/1.00  --res_to_prop_solver                    active
% 3.23/1.00  --res_prop_simpl_new                    false
% 3.23/1.00  --res_prop_simpl_given                  true
% 3.23/1.00  --res_passive_queue_type                priority_queues
% 3.23/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.23/1.00  --res_passive_queues_freq               [15;5]
% 3.23/1.00  --res_forward_subs                      full
% 3.23/1.00  --res_backward_subs                     full
% 3.23/1.00  --res_forward_subs_resolution           true
% 3.23/1.00  --res_backward_subs_resolution          true
% 3.23/1.00  --res_orphan_elimination                true
% 3.23/1.00  --res_time_limit                        2.
% 3.23/1.00  --res_out_proof                         true
% 3.23/1.00  
% 3.23/1.00  ------ Superposition Options
% 3.23/1.00  
% 3.23/1.00  --superposition_flag                    true
% 3.23/1.00  --sup_passive_queue_type                priority_queues
% 3.23/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.23/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.23/1.00  --demod_completeness_check              fast
% 3.23/1.00  --demod_use_ground                      true
% 3.23/1.00  --sup_to_prop_solver                    passive
% 3.23/1.00  --sup_prop_simpl_new                    true
% 3.23/1.00  --sup_prop_simpl_given                  true
% 3.23/1.00  --sup_fun_splitting                     false
% 3.23/1.00  --sup_smt_interval                      50000
% 3.23/1.00  
% 3.23/1.00  ------ Superposition Simplification Setup
% 3.23/1.00  
% 3.23/1.00  --sup_indices_passive                   []
% 3.23/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.23/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/1.00  --sup_full_bw                           [BwDemod]
% 3.23/1.00  --sup_immed_triv                        [TrivRules]
% 3.23/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.23/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/1.00  --sup_immed_bw_main                     []
% 3.23/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.23/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.23/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.23/1.00  
% 3.23/1.00  ------ Combination Options
% 3.23/1.00  
% 3.23/1.00  --comb_res_mult                         3
% 3.23/1.00  --comb_sup_mult                         2
% 3.23/1.00  --comb_inst_mult                        10
% 3.23/1.00  
% 3.23/1.00  ------ Debug Options
% 3.23/1.00  
% 3.23/1.00  --dbg_backtrace                         false
% 3.23/1.00  --dbg_dump_prop_clauses                 false
% 3.23/1.00  --dbg_dump_prop_clauses_file            -
% 3.23/1.00  --dbg_out_stat                          false
% 3.23/1.00  
% 3.23/1.00  
% 3.23/1.00  
% 3.23/1.00  
% 3.23/1.00  ------ Proving...
% 3.23/1.00  
% 3.23/1.00  
% 3.23/1.00  % SZS status Theorem for theBenchmark.p
% 3.23/1.00  
% 3.23/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.23/1.00  
% 3.23/1.00  fof(f9,axiom,(
% 3.23/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.23/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/1.00  
% 3.23/1.00  fof(f18,plain,(
% 3.23/1.00    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.23/1.00    inference(ennf_transformation,[],[f9])).
% 3.23/1.00  
% 3.23/1.00  fof(f62,plain,(
% 3.23/1.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.23/1.00    inference(cnf_transformation,[],[f18])).
% 3.23/1.00  
% 3.23/1.00  fof(f10,conjecture,(
% 3.23/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => ~(! [X4,X5] : ~(r2_hidden(X5,X2) & r2_hidden(X4,X1) & k4_tarski(X4,X5) = X0) & r2_hidden(X0,X3)))),
% 3.23/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/1.00  
% 3.23/1.00  fof(f11,negated_conjecture,(
% 3.23/1.00    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => ~(! [X4,X5] : ~(r2_hidden(X5,X2) & r2_hidden(X4,X1) & k4_tarski(X4,X5) = X0) & r2_hidden(X0,X3)))),
% 3.23/1.00    inference(negated_conjecture,[],[f10])).
% 3.23/1.00  
% 3.23/1.00  fof(f19,plain,(
% 3.23/1.00    ? [X0,X1,X2,X3] : ((! [X4,X5] : (~r2_hidden(X5,X2) | ~r2_hidden(X4,X1) | k4_tarski(X4,X5) != X0) & r2_hidden(X0,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 3.23/1.00    inference(ennf_transformation,[],[f11])).
% 3.23/1.00  
% 3.23/1.00  fof(f20,plain,(
% 3.23/1.00    ? [X0,X1,X2,X3] : (! [X4,X5] : (~r2_hidden(X5,X2) | ~r2_hidden(X4,X1) | k4_tarski(X4,X5) != X0) & r2_hidden(X0,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 3.23/1.00    inference(flattening,[],[f19])).
% 3.23/1.00  
% 3.23/1.00  fof(f41,plain,(
% 3.23/1.00    ? [X0,X1,X2,X3] : (! [X4,X5] : (~r2_hidden(X5,X2) | ~r2_hidden(X4,X1) | k4_tarski(X4,X5) != X0) & r2_hidden(X0,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) => (! [X5,X4] : (~r2_hidden(X5,sK11) | ~r2_hidden(X4,sK10) | k4_tarski(X4,X5) != sK9) & r2_hidden(sK9,sK12) & m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))))),
% 3.23/1.00    introduced(choice_axiom,[])).
% 3.23/1.00  
% 3.23/1.00  fof(f42,plain,(
% 3.23/1.00    ! [X4,X5] : (~r2_hidden(X5,sK11) | ~r2_hidden(X4,sK10) | k4_tarski(X4,X5) != sK9) & r2_hidden(sK9,sK12) & m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)))),
% 3.23/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11,sK12])],[f20,f41])).
% 3.23/1.00  
% 3.23/1.00  fof(f63,plain,(
% 3.23/1.00    m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)))),
% 3.23/1.00    inference(cnf_transformation,[],[f42])).
% 3.23/1.00  
% 3.23/1.00  fof(f5,axiom,(
% 3.23/1.00    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.23/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/1.00  
% 3.23/1.00  fof(f16,plain,(
% 3.23/1.00    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.23/1.00    inference(ennf_transformation,[],[f5])).
% 3.23/1.00  
% 3.23/1.00  fof(f28,plain,(
% 3.23/1.00    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.23/1.00    inference(nnf_transformation,[],[f16])).
% 3.23/1.00  
% 3.23/1.00  fof(f50,plain,(
% 3.23/1.00    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.23/1.00    inference(cnf_transformation,[],[f28])).
% 3.23/1.00  
% 3.23/1.00  fof(f8,axiom,(
% 3.23/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.23/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/1.00  
% 3.23/1.00  fof(f17,plain,(
% 3.23/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.23/1.00    inference(ennf_transformation,[],[f8])).
% 3.23/1.00  
% 3.23/1.00  fof(f60,plain,(
% 3.23/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.23/1.00    inference(cnf_transformation,[],[f17])).
% 3.23/1.00  
% 3.23/1.00  fof(f1,axiom,(
% 3.23/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.23/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/1.00  
% 3.23/1.00  fof(f12,plain,(
% 3.23/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.23/1.00    inference(ennf_transformation,[],[f1])).
% 3.23/1.00  
% 3.23/1.00  fof(f21,plain,(
% 3.23/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.23/1.00    inference(nnf_transformation,[],[f12])).
% 3.23/1.00  
% 3.23/1.00  fof(f22,plain,(
% 3.23/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.23/1.00    inference(rectify,[],[f21])).
% 3.23/1.00  
% 3.23/1.00  fof(f23,plain,(
% 3.23/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.23/1.00    introduced(choice_axiom,[])).
% 3.23/1.00  
% 3.23/1.00  fof(f24,plain,(
% 3.23/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.23/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).
% 3.23/1.00  
% 3.23/1.00  fof(f44,plain,(
% 3.23/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.23/1.00    inference(cnf_transformation,[],[f24])).
% 3.23/1.00  
% 3.23/1.00  fof(f3,axiom,(
% 3.23/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 3.23/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/1.00  
% 3.23/1.00  fof(f14,plain,(
% 3.23/1.00    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.23/1.00    inference(ennf_transformation,[],[f3])).
% 3.23/1.00  
% 3.23/1.00  fof(f47,plain,(
% 3.23/1.00    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.23/1.00    inference(cnf_transformation,[],[f14])).
% 3.23/1.00  
% 3.23/1.00  fof(f45,plain,(
% 3.23/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.23/1.00    inference(cnf_transformation,[],[f24])).
% 3.23/1.00  
% 3.23/1.00  fof(f64,plain,(
% 3.23/1.00    r2_hidden(sK9,sK12)),
% 3.23/1.00    inference(cnf_transformation,[],[f42])).
% 3.23/1.00  
% 3.23/1.00  fof(f43,plain,(
% 3.23/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.23/1.00    inference(cnf_transformation,[],[f24])).
% 3.23/1.00  
% 3.23/1.00  fof(f2,axiom,(
% 3.23/1.00    ! [X0,X1,X2] : ~(! [X3,X4] : k4_tarski(X3,X4) != X0 & r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 3.23/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/1.00  
% 3.23/1.00  fof(f13,plain,(
% 3.23/1.00    ! [X0,X1,X2] : (? [X3,X4] : k4_tarski(X3,X4) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 3.23/1.00    inference(ennf_transformation,[],[f2])).
% 3.23/1.00  
% 3.23/1.00  fof(f25,plain,(
% 3.23/1.00    ! [X0] : (? [X3,X4] : k4_tarski(X3,X4) = X0 => k4_tarski(sK1(X0),sK2(X0)) = X0)),
% 3.23/1.00    introduced(choice_axiom,[])).
% 3.23/1.00  
% 3.23/1.00  fof(f26,plain,(
% 3.23/1.00    ! [X0,X1,X2] : (k4_tarski(sK1(X0),sK2(X0)) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 3.23/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f13,f25])).
% 3.23/1.00  
% 3.23/1.00  fof(f46,plain,(
% 3.23/1.00    ( ! [X2,X0,X1] : (k4_tarski(sK1(X0),sK2(X0)) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 3.23/1.00    inference(cnf_transformation,[],[f26])).
% 3.23/1.00  
% 3.23/1.00  fof(f7,axiom,(
% 3.23/1.00    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 3.23/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/1.00  
% 3.23/1.00  fof(f35,plain,(
% 3.23/1.00    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 3.23/1.00    inference(nnf_transformation,[],[f7])).
% 3.23/1.00  
% 3.23/1.00  fof(f36,plain,(
% 3.23/1.00    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 3.23/1.00    inference(rectify,[],[f35])).
% 3.23/1.00  
% 3.23/1.00  fof(f39,plain,(
% 3.23/1.00    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK8(X0,X5),X5),X0))),
% 3.23/1.00    introduced(choice_axiom,[])).
% 3.23/1.00  
% 3.23/1.00  fof(f38,plain,(
% 3.23/1.00    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) => r2_hidden(k4_tarski(sK7(X0,X1),X2),X0))) )),
% 3.23/1.00    introduced(choice_axiom,[])).
% 3.23/1.00  
% 3.23/1.00  fof(f37,plain,(
% 3.23/1.00    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK6(X0,X1)),X0) | r2_hidden(sK6(X0,X1),X1))))),
% 3.23/1.00    introduced(choice_axiom,[])).
% 3.23/1.00  
% 3.23/1.00  fof(f40,plain,(
% 3.23/1.00    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0) | r2_hidden(sK6(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK8(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 3.23/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f36,f39,f38,f37])).
% 3.23/1.00  
% 3.23/1.00  fof(f57,plain,(
% 3.23/1.00    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 3.23/1.00    inference(cnf_transformation,[],[f40])).
% 3.23/1.00  
% 3.23/1.00  fof(f68,plain,(
% 3.23/1.00    ( ! [X6,X0,X5] : (r2_hidden(X5,k2_relat_1(X0)) | ~r2_hidden(k4_tarski(X6,X5),X0)) )),
% 3.23/1.00    inference(equality_resolution,[],[f57])).
% 3.23/1.00  
% 3.23/1.00  fof(f6,axiom,(
% 3.23/1.00    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 3.23/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/1.00  
% 3.23/1.00  fof(f29,plain,(
% 3.23/1.00    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 3.23/1.00    inference(nnf_transformation,[],[f6])).
% 3.23/1.00  
% 3.23/1.00  fof(f30,plain,(
% 3.23/1.00    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 3.23/1.00    inference(rectify,[],[f29])).
% 3.23/1.00  
% 3.23/1.00  fof(f33,plain,(
% 3.23/1.00    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0))),
% 3.23/1.00    introduced(choice_axiom,[])).
% 3.23/1.00  
% 3.23/1.00  fof(f32,plain,(
% 3.23/1.00    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) => r2_hidden(k4_tarski(X2,sK4(X0,X1)),X0))) )),
% 3.23/1.00    introduced(choice_axiom,[])).
% 3.23/1.00  
% 3.23/1.00  fof(f31,plain,(
% 3.23/1.00    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK3(X0,X1),X3),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 3.23/1.00    introduced(choice_axiom,[])).
% 3.23/1.00  
% 3.23/1.00  fof(f34,plain,(
% 3.23/1.00    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK3(X0,X1),X3),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 3.23/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f30,f33,f32,f31])).
% 3.23/1.00  
% 3.23/1.00  fof(f53,plain,(
% 3.23/1.00    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 3.23/1.00    inference(cnf_transformation,[],[f34])).
% 3.23/1.00  
% 3.23/1.00  fof(f66,plain,(
% 3.23/1.00    ( ! [X6,X0,X5] : (r2_hidden(X5,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X5,X6),X0)) )),
% 3.23/1.00    inference(equality_resolution,[],[f53])).
% 3.23/1.00  
% 3.23/1.00  fof(f65,plain,(
% 3.23/1.00    ( ! [X4,X5] : (~r2_hidden(X5,sK11) | ~r2_hidden(X4,sK10) | k4_tarski(X4,X5) != sK9) )),
% 3.23/1.00    inference(cnf_transformation,[],[f42])).
% 3.23/1.00  
% 3.23/1.00  fof(f4,axiom,(
% 3.23/1.00    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.23/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/1.00  
% 3.23/1.00  fof(f15,plain,(
% 3.23/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.23/1.00    inference(ennf_transformation,[],[f4])).
% 3.23/1.00  
% 3.23/1.00  fof(f27,plain,(
% 3.23/1.00    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.23/1.00    inference(nnf_transformation,[],[f15])).
% 3.23/1.00  
% 3.23/1.00  fof(f48,plain,(
% 3.23/1.00    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.23/1.00    inference(cnf_transformation,[],[f27])).
% 3.23/1.00  
% 3.23/1.00  fof(f61,plain,(
% 3.23/1.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.23/1.00    inference(cnf_transformation,[],[f18])).
% 3.23/1.00  
% 3.23/1.00  cnf(c_18,plain,
% 3.23/1.00      ( v5_relat_1(X0,X1)
% 3.23/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.23/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_22,negated_conjecture,
% 3.23/1.00      ( m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))) ),
% 3.23/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_303,plain,
% 3.23/1.00      ( v5_relat_1(X0,X1)
% 3.23/1.00      | k1_zfmisc_1(k2_zfmisc_1(X2,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))
% 3.23/1.00      | sK12 != X0 ),
% 3.23/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_22]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_304,plain,
% 3.23/1.00      ( v5_relat_1(sK12,X0)
% 3.23/1.00      | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)) ),
% 3.23/1.00      inference(unflattening,[status(thm)],[c_303]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_8,plain,
% 3.23/1.00      ( ~ v5_relat_1(X0,X1)
% 3.23/1.00      | r1_tarski(k2_relat_1(X0),X1)
% 3.23/1.00      | ~ v1_relat_1(X0) ),
% 3.23/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_17,plain,
% 3.23/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.23/1.00      | v1_relat_1(X0) ),
% 3.23/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_291,plain,
% 3.23/1.00      ( v1_relat_1(X0)
% 3.23/1.00      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))
% 3.23/1.00      | sK12 != X0 ),
% 3.23/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_22]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_292,plain,
% 3.23/1.00      ( v1_relat_1(sK12)
% 3.23/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)) ),
% 3.23/1.00      inference(unflattening,[status(thm)],[c_291]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_350,plain,
% 3.23/1.00      ( ~ v5_relat_1(X0,X1)
% 3.23/1.00      | r1_tarski(k2_relat_1(X0),X1)
% 3.23/1.00      | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))
% 3.23/1.00      | sK12 != X0 ),
% 3.23/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_292]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_351,plain,
% 3.23/1.00      ( ~ v5_relat_1(sK12,X0)
% 3.23/1.00      | r1_tarski(k2_relat_1(sK12),X0)
% 3.23/1.00      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)) ),
% 3.23/1.00      inference(unflattening,[status(thm)],[c_350]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_387,plain,
% 3.23/1.00      ( r1_tarski(k2_relat_1(sK12),X0)
% 3.23/1.00      | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))
% 3.23/1.00      | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)) ),
% 3.23/1.00      inference(resolution,[status(thm)],[c_304,c_351]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_666,plain,
% 3.23/1.00      ( r1_tarski(k2_relat_1(sK12),X0)
% 3.23/1.00      | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))
% 3.23/1.00      | ~ sP1_iProver_split ),
% 3.23/1.00      inference(splitting,
% 3.23/1.00                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 3.23/1.00                [c_387]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1002,plain,
% 3.23/1.00      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))
% 3.23/1.00      | r1_tarski(k2_relat_1(sK12),X1) = iProver_top
% 3.23/1.00      | sP1_iProver_split != iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_666]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_667,plain,
% 3.23/1.00      ( sP1_iProver_split | sP0_iProver_split ),
% 3.23/1.00      inference(splitting,
% 3.23/1.00                [splitting(split),new_symbols(definition,[])],
% 3.23/1.00                [c_387]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_687,plain,
% 3.23/1.00      ( sP1_iProver_split = iProver_top
% 3.23/1.00      | sP0_iProver_split = iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_667]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_688,plain,
% 3.23/1.00      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))
% 3.23/1.00      | r1_tarski(k2_relat_1(sK12),X1) = iProver_top
% 3.23/1.00      | sP1_iProver_split != iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_666]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_665,plain,
% 3.23/1.00      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))
% 3.23/1.00      | ~ sP0_iProver_split ),
% 3.23/1.00      inference(splitting,
% 3.23/1.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.23/1.00                [c_387]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1003,plain,
% 3.23/1.00      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))
% 3.23/1.00      | sP0_iProver_split != iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_665]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1243,plain,
% 3.23/1.00      ( sP0_iProver_split != iProver_top ),
% 3.23/1.00      inference(equality_resolution,[status(thm)],[c_1003]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1355,plain,
% 3.23/1.00      ( r1_tarski(k2_relat_1(sK12),X1) = iProver_top
% 3.23/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)) ),
% 3.23/1.00      inference(global_propositional_subsumption,
% 3.23/1.00                [status(thm)],
% 3.23/1.00                [c_1002,c_687,c_688,c_1243]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1356,plain,
% 3.23/1.00      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))
% 3.23/1.00      | r1_tarski(k2_relat_1(sK12),X1) = iProver_top ),
% 3.23/1.00      inference(renaming,[status(thm)],[c_1355]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1361,plain,
% 3.23/1.00      ( r1_tarski(k2_relat_1(sK12),sK11) = iProver_top ),
% 3.23/1.00      inference(equality_resolution,[status(thm)],[c_1356]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1,plain,
% 3.23/1.00      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.23/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1018,plain,
% 3.23/1.00      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.23/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_4,plain,
% 3.23/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.23/1.00      | ~ r2_hidden(X2,X0)
% 3.23/1.00      | r2_hidden(X2,X1) ),
% 3.23/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_264,plain,
% 3.23/1.00      ( ~ r2_hidden(X0,X1)
% 3.23/1.00      | r2_hidden(X0,X2)
% 3.23/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)) != k1_zfmisc_1(X2)
% 3.23/1.00      | sK12 != X1 ),
% 3.23/1.00      inference(resolution_lifted,[status(thm)],[c_4,c_22]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_265,plain,
% 3.23/1.00      ( r2_hidden(X0,X1)
% 3.23/1.00      | ~ r2_hidden(X0,sK12)
% 3.23/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)) != k1_zfmisc_1(X1) ),
% 3.23/1.00      inference(unflattening,[status(thm)],[c_264]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1005,plain,
% 3.23/1.00      ( k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)) != k1_zfmisc_1(X0)
% 3.23/1.00      | r2_hidden(X1,X0) = iProver_top
% 3.23/1.00      | r2_hidden(X1,sK12) != iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_265]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1181,plain,
% 3.23/1.00      ( r2_hidden(X0,k2_zfmisc_1(sK10,sK11)) = iProver_top
% 3.23/1.00      | r2_hidden(X0,sK12) != iProver_top ),
% 3.23/1.00      inference(equality_resolution,[status(thm)],[c_1005]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_0,plain,
% 3.23/1.00      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.23/1.00      inference(cnf_transformation,[],[f45]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1019,plain,
% 3.23/1.00      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 3.23/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1490,plain,
% 3.23/1.00      ( r2_hidden(sK0(X0,k2_zfmisc_1(sK10,sK11)),sK12) != iProver_top
% 3.23/1.00      | r1_tarski(X0,k2_zfmisc_1(sK10,sK11)) = iProver_top ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_1181,c_1019]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1997,plain,
% 3.23/1.00      ( r1_tarski(sK12,k2_zfmisc_1(sK10,sK11)) = iProver_top ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_1018,c_1490]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_21,negated_conjecture,
% 3.23/1.00      ( r2_hidden(sK9,sK12) ),
% 3.23/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1006,plain,
% 3.23/1.00      ( r2_hidden(sK9,sK12) = iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2,plain,
% 3.23/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.23/1.00      inference(cnf_transformation,[],[f43]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1017,plain,
% 3.23/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.23/1.00      | r2_hidden(X0,X2) = iProver_top
% 3.23/1.00      | r1_tarski(X1,X2) != iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2369,plain,
% 3.23/1.00      ( r2_hidden(sK9,X0) = iProver_top
% 3.23/1.00      | r1_tarski(sK12,X0) != iProver_top ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_1006,c_1017]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2485,plain,
% 3.23/1.00      ( r2_hidden(sK9,k2_zfmisc_1(sK10,sK11)) = iProver_top ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_1997,c_2369]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_3,plain,
% 3.23/1.00      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 3.23/1.00      | k4_tarski(sK1(X0),sK2(X0)) = X0 ),
% 3.23/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1016,plain,
% 3.23/1.00      ( k4_tarski(sK1(X0),sK2(X0)) = X0
% 3.23/1.00      | r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2490,plain,
% 3.23/1.00      ( k4_tarski(sK1(sK9),sK2(sK9)) = sK9 ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_2485,c_1016]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_15,plain,
% 3.23/1.00      ( r2_hidden(X0,k2_relat_1(X1)) | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
% 3.23/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1009,plain,
% 3.23/1.00      ( r2_hidden(X0,k2_relat_1(X1)) = iProver_top
% 3.23/1.00      | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2528,plain,
% 3.23/1.00      ( r2_hidden(sK2(sK9),k2_relat_1(X0)) = iProver_top
% 3.23/1.00      | r2_hidden(sK9,X0) != iProver_top ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_2490,c_1009]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2985,plain,
% 3.23/1.00      ( r2_hidden(sK2(sK9),X0) = iProver_top
% 3.23/1.00      | r2_hidden(sK9,X1) != iProver_top
% 3.23/1.00      | r1_tarski(k2_relat_1(X1),X0) != iProver_top ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_2528,c_1017]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_8165,plain,
% 3.23/1.00      ( r2_hidden(sK2(sK9),sK11) = iProver_top
% 3.23/1.00      | r2_hidden(sK9,sK12) != iProver_top ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_1361,c_2985]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_3979,plain,
% 3.23/1.00      ( r2_hidden(sK1(sK9),X0)
% 3.23/1.00      | ~ r2_hidden(sK1(sK9),k1_relat_1(sK12))
% 3.23/1.00      | ~ r1_tarski(k1_relat_1(sK12),X0) ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_3980,plain,
% 3.23/1.00      ( r2_hidden(sK1(sK9),X0) = iProver_top
% 3.23/1.00      | r2_hidden(sK1(sK9),k1_relat_1(sK12)) != iProver_top
% 3.23/1.00      | r1_tarski(k1_relat_1(sK12),X0) != iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_3979]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_3982,plain,
% 3.23/1.00      ( r2_hidden(sK1(sK9),k1_relat_1(sK12)) != iProver_top
% 3.23/1.00      | r2_hidden(sK1(sK9),sK10) = iProver_top
% 3.23/1.00      | r1_tarski(k1_relat_1(sK12),sK10) != iProver_top ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_3980]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_11,plain,
% 3.23/1.00      ( r2_hidden(X0,k1_relat_1(X1)) | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
% 3.23/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2600,plain,
% 3.23/1.00      ( ~ r2_hidden(k4_tarski(sK1(sK9),sK2(sK9)),sK12)
% 3.23/1.00      | r2_hidden(sK1(sK9),k1_relat_1(sK12)) ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_11]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2601,plain,
% 3.23/1.00      ( r2_hidden(k4_tarski(sK1(sK9),sK2(sK9)),sK12) != iProver_top
% 3.23/1.00      | r2_hidden(sK1(sK9),k1_relat_1(sK12)) = iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_2600]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_20,negated_conjecture,
% 3.23/1.00      ( ~ r2_hidden(X0,sK10)
% 3.23/1.00      | ~ r2_hidden(X1,sK11)
% 3.23/1.00      | k4_tarski(X0,X1) != sK9 ),
% 3.23/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1007,plain,
% 3.23/1.00      ( k4_tarski(X0,X1) != sK9
% 3.23/1.00      | r2_hidden(X0,sK10) != iProver_top
% 3.23/1.00      | r2_hidden(X1,sK11) != iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2530,plain,
% 3.23/1.00      ( r2_hidden(sK2(sK9),sK11) != iProver_top
% 3.23/1.00      | r2_hidden(sK1(sK9),sK10) != iProver_top ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_2490,c_1007]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_672,plain,
% 3.23/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.23/1.00      theory(equality) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1188,plain,
% 3.23/1.00      ( r2_hidden(X0,X1)
% 3.23/1.00      | ~ r2_hidden(sK9,sK12)
% 3.23/1.00      | X1 != sK12
% 3.23/1.00      | X0 != sK9 ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_672]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1291,plain,
% 3.23/1.00      ( r2_hidden(X0,sK12)
% 3.23/1.00      | ~ r2_hidden(sK9,sK12)
% 3.23/1.00      | X0 != sK9
% 3.23/1.00      | sK12 != sK12 ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_1188]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1961,plain,
% 3.23/1.00      ( r2_hidden(k4_tarski(sK1(sK9),sK2(sK9)),sK12)
% 3.23/1.00      | ~ r2_hidden(sK9,sK12)
% 3.23/1.00      | k4_tarski(sK1(sK9),sK2(sK9)) != sK9
% 3.23/1.00      | sK12 != sK12 ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_1291]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1962,plain,
% 3.23/1.00      ( k4_tarski(sK1(sK9),sK2(sK9)) != sK9
% 3.23/1.00      | sK12 != sK12
% 3.23/1.00      | r2_hidden(k4_tarski(sK1(sK9),sK2(sK9)),sK12) = iProver_top
% 3.23/1.00      | r2_hidden(sK9,sK12) != iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_1961]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1202,plain,
% 3.23/1.00      ( ~ r2_hidden(sK9,k2_zfmisc_1(X0,X1))
% 3.23/1.00      | k4_tarski(sK1(sK9),sK2(sK9)) = sK9 ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1698,plain,
% 3.23/1.00      ( ~ r2_hidden(sK9,k2_zfmisc_1(sK10,sK11))
% 3.23/1.00      | k4_tarski(sK1(sK9),sK2(sK9)) = sK9 ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_1202]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1150,plain,
% 3.23/1.00      ( r2_hidden(sK9,X0)
% 3.23/1.00      | ~ r2_hidden(sK9,sK12)
% 3.23/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)) != k1_zfmisc_1(X0) ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_265]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1201,plain,
% 3.23/1.00      ( r2_hidden(sK9,k2_zfmisc_1(X0,X1))
% 3.23/1.00      | ~ r2_hidden(sK9,sK12)
% 3.23/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_1150]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1412,plain,
% 3.23/1.00      ( r2_hidden(sK9,k2_zfmisc_1(sK10,sK11))
% 3.23/1.00      | ~ r2_hidden(sK9,sK12)
% 3.23/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)) != k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)) ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_1201]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_669,plain,( X0 = X0 ),theory(equality) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1292,plain,
% 3.23/1.00      ( sK12 = sK12 ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_669]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_6,plain,
% 3.23/1.00      ( ~ v4_relat_1(X0,X1)
% 3.23/1.00      | r1_tarski(k1_relat_1(X0),X1)
% 3.23/1.00      | ~ v1_relat_1(X0) ),
% 3.23/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_19,plain,
% 3.23/1.00      ( v4_relat_1(X0,X1)
% 3.23/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.23/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_279,plain,
% 3.23/1.00      ( v4_relat_1(X0,X1)
% 3.23/1.00      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))
% 3.23/1.00      | sK12 != X0 ),
% 3.23/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_22]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_280,plain,
% 3.23/1.00      ( v4_relat_1(sK12,X0)
% 3.23/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)) ),
% 3.23/1.00      inference(unflattening,[status(thm)],[c_279]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_329,plain,
% 3.23/1.00      ( r1_tarski(k1_relat_1(X0),X1)
% 3.23/1.00      | ~ v1_relat_1(X0)
% 3.23/1.00      | X2 != X1
% 3.23/1.00      | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))
% 3.23/1.00      | sK12 != X0 ),
% 3.23/1.00      inference(resolution_lifted,[status(thm)],[c_6,c_280]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_330,plain,
% 3.23/1.00      ( r1_tarski(k1_relat_1(sK12),X0)
% 3.23/1.00      | ~ v1_relat_1(sK12)
% 3.23/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)) ),
% 3.23/1.00      inference(unflattening,[status(thm)],[c_329]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_334,plain,
% 3.23/1.00      ( r1_tarski(k1_relat_1(sK12),X0)
% 3.23/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)) ),
% 3.23/1.00      inference(global_propositional_subsumption,
% 3.23/1.00                [status(thm)],
% 3.23/1.00                [c_330,c_292]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1156,plain,
% 3.23/1.00      ( r1_tarski(k1_relat_1(sK12),sK10)
% 3.23/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)) != k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)) ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_334]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1157,plain,
% 3.23/1.00      ( k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)) != k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))
% 3.23/1.00      | r1_tarski(k1_relat_1(sK12),sK10) = iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_1156]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1155,plain,
% 3.23/1.00      ( k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)) = k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)) ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_669]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_24,plain,
% 3.23/1.00      ( r2_hidden(sK9,sK12) = iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(contradiction,plain,
% 3.23/1.00      ( $false ),
% 3.23/1.00      inference(minisat,
% 3.23/1.00                [status(thm)],
% 3.23/1.00                [c_8165,c_3982,c_2601,c_2530,c_1962,c_1698,c_1412,c_1292,
% 3.23/1.00                 c_1157,c_1155,c_24,c_21]) ).
% 3.23/1.00  
% 3.23/1.00  
% 3.23/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.23/1.00  
% 3.23/1.00  ------                               Statistics
% 3.23/1.00  
% 3.23/1.00  ------ General
% 3.23/1.00  
% 3.23/1.00  abstr_ref_over_cycles:                  0
% 3.23/1.00  abstr_ref_under_cycles:                 0
% 3.23/1.00  gc_basic_clause_elim:                   0
% 3.23/1.00  forced_gc_time:                         0
% 3.23/1.00  parsing_time:                           0.011
% 3.23/1.00  unif_index_cands_time:                  0.
% 3.23/1.00  unif_index_add_time:                    0.
% 3.23/1.00  orderings_time:                         0.
% 3.23/1.00  out_proof_time:                         0.021
% 3.23/1.00  total_time:                             0.339
% 3.23/1.00  num_of_symbols:                         57
% 3.23/1.00  num_of_terms:                           8389
% 3.23/1.00  
% 3.23/1.00  ------ Preprocessing
% 3.23/1.00  
% 3.23/1.00  num_of_splits:                          2
% 3.23/1.00  num_of_split_atoms:                     2
% 3.23/1.00  num_of_reused_defs:                     0
% 3.23/1.00  num_eq_ax_congr_red:                    58
% 3.23/1.00  num_of_sem_filtered_clauses:            1
% 3.23/1.00  num_of_subtypes:                        0
% 3.23/1.00  monotx_restored_types:                  0
% 3.23/1.00  sat_num_of_epr_types:                   0
% 3.23/1.00  sat_num_of_non_cyclic_types:            0
% 3.23/1.00  sat_guarded_non_collapsed_types:        0
% 3.23/1.00  num_pure_diseq_elim:                    0
% 3.23/1.00  simp_replaced_by:                       0
% 3.23/1.00  res_preprocessed:                       97
% 3.23/1.00  prep_upred:                             0
% 3.23/1.00  prep_unflattend:                        24
% 3.23/1.00  smt_new_axioms:                         0
% 3.23/1.00  pred_elim_cands:                        2
% 3.23/1.00  pred_elim:                              4
% 3.23/1.00  pred_elim_cl:                           6
% 3.23/1.00  pred_elim_cycles:                       6
% 3.23/1.00  merged_defs:                            0
% 3.23/1.00  merged_defs_ncl:                        0
% 3.23/1.00  bin_hyper_res:                          0
% 3.23/1.00  prep_cycles:                            4
% 3.23/1.00  pred_elim_time:                         0.005
% 3.23/1.00  splitting_time:                         0.
% 3.23/1.00  sem_filter_time:                        0.
% 3.23/1.00  monotx_time:                            0.
% 3.23/1.00  subtype_inf_time:                       0.
% 3.23/1.00  
% 3.23/1.00  ------ Problem properties
% 3.23/1.00  
% 3.23/1.00  clauses:                                19
% 3.23/1.00  conjectures:                            2
% 3.23/1.00  epr:                                    3
% 3.23/1.00  horn:                                   15
% 3.23/1.00  ground:                                 2
% 3.23/1.00  unary:                                  1
% 3.23/1.00  binary:                                 10
% 3.23/1.00  lits:                                   45
% 3.23/1.00  lits_eq:                                10
% 3.23/1.00  fd_pure:                                0
% 3.23/1.00  fd_pseudo:                              0
% 3.23/1.00  fd_cond:                                0
% 3.23/1.00  fd_pseudo_cond:                         4
% 3.23/1.00  ac_symbols:                             0
% 3.23/1.00  
% 3.23/1.00  ------ Propositional Solver
% 3.23/1.00  
% 3.23/1.00  prop_solver_calls:                      30
% 3.23/1.00  prop_fast_solver_calls:                 758
% 3.23/1.00  smt_solver_calls:                       0
% 3.23/1.00  smt_fast_solver_calls:                  0
% 3.23/1.00  prop_num_of_clauses:                    3233
% 3.23/1.00  prop_preprocess_simplified:             6477
% 3.23/1.00  prop_fo_subsumed:                       6
% 3.23/1.00  prop_solver_time:                       0.
% 3.23/1.00  smt_solver_time:                        0.
% 3.23/1.00  smt_fast_solver_time:                   0.
% 3.23/1.00  prop_fast_solver_time:                  0.
% 3.23/1.00  prop_unsat_core_time:                   0.
% 3.23/1.00  
% 3.23/1.00  ------ QBF
% 3.23/1.00  
% 3.23/1.00  qbf_q_res:                              0
% 3.23/1.00  qbf_num_tautologies:                    0
% 3.23/1.00  qbf_prep_cycles:                        0
% 3.23/1.00  
% 3.23/1.00  ------ BMC1
% 3.23/1.00  
% 3.23/1.00  bmc1_current_bound:                     -1
% 3.23/1.00  bmc1_last_solved_bound:                 -1
% 3.23/1.00  bmc1_unsat_core_size:                   -1
% 3.23/1.00  bmc1_unsat_core_parents_size:           -1
% 3.23/1.00  bmc1_merge_next_fun:                    0
% 3.23/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.23/1.00  
% 3.23/1.00  ------ Instantiation
% 3.23/1.00  
% 3.23/1.00  inst_num_of_clauses:                    716
% 3.23/1.00  inst_num_in_passive:                    118
% 3.23/1.00  inst_num_in_active:                     381
% 3.23/1.00  inst_num_in_unprocessed:                217
% 3.23/1.00  inst_num_of_loops:                      520
% 3.23/1.00  inst_num_of_learning_restarts:          0
% 3.23/1.00  inst_num_moves_active_passive:          135
% 3.23/1.00  inst_lit_activity:                      0
% 3.23/1.00  inst_lit_activity_moves:                0
% 3.23/1.00  inst_num_tautologies:                   0
% 3.23/1.00  inst_num_prop_implied:                  0
% 3.23/1.00  inst_num_existing_simplified:           0
% 3.23/1.00  inst_num_eq_res_simplified:             0
% 3.23/1.00  inst_num_child_elim:                    0
% 3.23/1.00  inst_num_of_dismatching_blockings:      424
% 3.23/1.00  inst_num_of_non_proper_insts:           806
% 3.23/1.00  inst_num_of_duplicates:                 0
% 3.23/1.00  inst_inst_num_from_inst_to_res:         0
% 3.23/1.00  inst_dismatching_checking_time:         0.
% 3.23/1.00  
% 3.23/1.00  ------ Resolution
% 3.23/1.00  
% 3.23/1.00  res_num_of_clauses:                     0
% 3.23/1.00  res_num_in_passive:                     0
% 3.23/1.00  res_num_in_active:                      0
% 3.23/1.00  res_num_of_loops:                       101
% 3.23/1.00  res_forward_subset_subsumed:            48
% 3.23/1.00  res_backward_subset_subsumed:           0
% 3.23/1.00  res_forward_subsumed:                   0
% 3.23/1.00  res_backward_subsumed:                  0
% 3.23/1.00  res_forward_subsumption_resolution:     0
% 3.23/1.00  res_backward_subsumption_resolution:    0
% 3.23/1.00  res_clause_to_clause_subsumption:       636
% 3.23/1.00  res_orphan_elimination:                 0
% 3.23/1.00  res_tautology_del:                      48
% 3.23/1.00  res_num_eq_res_simplified:              0
% 3.23/1.00  res_num_sel_changes:                    0
% 3.23/1.00  res_moves_from_active_to_pass:          0
% 3.23/1.00  
% 3.23/1.00  ------ Superposition
% 3.23/1.00  
% 3.23/1.00  sup_time_total:                         0.
% 3.23/1.00  sup_time_generating:                    0.
% 3.23/1.00  sup_time_sim_full:                      0.
% 3.23/1.00  sup_time_sim_immed:                     0.
% 3.23/1.00  
% 3.23/1.00  sup_num_of_clauses:                     278
% 3.23/1.00  sup_num_in_active:                      103
% 3.23/1.00  sup_num_in_passive:                     175
% 3.23/1.00  sup_num_of_loops:                       103
% 3.23/1.00  sup_fw_superposition:                   98
% 3.23/1.00  sup_bw_superposition:                   190
% 3.23/1.00  sup_immediate_simplified:               15
% 3.23/1.00  sup_given_eliminated:                   0
% 3.23/1.00  comparisons_done:                       0
% 3.23/1.00  comparisons_avoided:                    30
% 3.23/1.00  
% 3.23/1.00  ------ Simplifications
% 3.23/1.00  
% 3.23/1.00  
% 3.23/1.00  sim_fw_subset_subsumed:                 8
% 3.23/1.00  sim_bw_subset_subsumed:                 1
% 3.23/1.00  sim_fw_subsumed:                        3
% 3.23/1.00  sim_bw_subsumed:                        0
% 3.23/1.00  sim_fw_subsumption_res:                 4
% 3.23/1.00  sim_bw_subsumption_res:                 0
% 3.23/1.00  sim_tautology_del:                      5
% 3.23/1.00  sim_eq_tautology_del:                   6
% 3.23/1.00  sim_eq_res_simp:                        2
% 3.23/1.00  sim_fw_demodulated:                     0
% 3.23/1.00  sim_bw_demodulated:                     0
% 3.23/1.00  sim_light_normalised:                   0
% 3.23/1.00  sim_joinable_taut:                      0
% 3.23/1.00  sim_joinable_simp:                      0
% 3.23/1.00  sim_ac_normalised:                      0
% 3.23/1.00  sim_smt_subsumption:                    0
% 3.23/1.00  
%------------------------------------------------------------------------------
