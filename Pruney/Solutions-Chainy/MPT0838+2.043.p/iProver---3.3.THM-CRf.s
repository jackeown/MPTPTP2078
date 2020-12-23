%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:56:34 EST 2020

% Result     : Theorem 1.37s
% Output     : CNFRefutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 343 expanded)
%              Number of clauses        :   66 ( 127 expanded)
%              Number of leaves         :   27 (  87 expanded)
%              Depth                    :   22
%              Number of atoms          :  426 (1232 expanded)
%              Number of equality atoms :  130 ( 298 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f40,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK2(X0,X1),X1)
          | ~ r2_hidden(sK2(X0,X1),X0) )
        & ( r2_hidden(sK2(X0,X1),X1)
          | r2_hidden(sK2(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK2(X0,X1),X1)
          | ~ r2_hidden(sK2(X0,X1),X0) )
        & ( r2_hidden(sK2(X0,X1),X1)
          | r2_hidden(sK2(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f40,f41])).

fof(f66,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK2(X0,X1),X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f12,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f45,plain,(
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
    inference(rectify,[],[f44])).

fof(f48,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK4(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
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

fof(f49,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f45,f48,f47,f46])).

fof(f73,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f93,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f73])).

fof(f16,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
             => ~ ( ! [X3] :
                      ( m1_subset_1(X3,X1)
                     => ~ r2_hidden(X3,k2_relset_1(X0,X1,X2)) )
                  & k1_xboole_0 != k1_relset_1(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,X1)
                       => ~ r2_hidden(X3,k2_relset_1(X0,X1,X2)) )
                    & k1_xboole_0 != k1_relset_1(X0,X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k1_relset_1(X0,X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k1_relset_1(X0,X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
              | ~ m1_subset_1(X3,X1) )
          & k1_xboole_0 != k1_relset_1(X0,X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,k2_relset_1(X0,X1,sK13))
            | ~ m1_subset_1(X3,X1) )
        & k1_xboole_0 != k1_relset_1(X0,X1,sK13)
        & m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k1_relset_1(X0,X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X1) )
     => ( ? [X2] :
            ( ! [X3] :
                ( ~ r2_hidden(X3,k2_relset_1(X0,sK12,X2))
                | ~ m1_subset_1(X3,sK12) )
            & k1_xboole_0 != k1_relset_1(X0,sK12,X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK12))) )
        & ~ v1_xboole_0(sK12) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ! [X3] :
                    ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
                    | ~ m1_subset_1(X3,X1) )
                & k1_xboole_0 != k1_relset_1(X0,X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k2_relset_1(sK11,X1,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k1_relset_1(sK11,X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK11,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK11) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k2_relset_1(sK11,sK12,sK13))
        | ~ m1_subset_1(X3,sK12) )
    & k1_xboole_0 != k1_relset_1(sK11,sK12,sK13)
    & m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12)))
    & ~ v1_xboole_0(sK12)
    & ~ v1_xboole_0(sK11) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11,sK12,sK13])],[f33,f60,f59,f58])).

fof(f89,plain,(
    m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12))) ),
    inference(cnf_transformation,[],[f61])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f37,f38])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f81,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f69,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f91,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k2_relset_1(sK11,sK12,sK13))
      | ~ m1_subset_1(X3,sK12) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f56,plain,(
    ! [X0] :
      ( ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
     => r2_hidden(k4_tarski(sK9(X0),sK10(X0)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(k4_tarski(sK9(X0),sK10(X0)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10])],[f27,f56])).

fof(f82,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(k4_tarski(sK9(X0),sK10(X0)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f51,plain,(
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
    inference(rectify,[],[f50])).

fof(f54,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK8(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK7(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
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

fof(f55,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f51,f54,f53,f52])).

fof(f78,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f94,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f78])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f90,plain,(
    k1_xboole_0 != k1_relset_1(sK11,sK12,sK13) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_5,plain,
    ( r2_hidden(sK2(X0,X1),X1)
    | r2_hidden(sK2(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1521,plain,
    ( X0 = X1
    | r2_hidden(sK2(X1,X0),X0) = iProver_top
    | r2_hidden(sK2(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_6,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1520,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_21,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1507,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1935,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1520,c_1507])).

cnf(c_4021,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(k1_xboole_0,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1521,c_1935])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,sK5(X1,X0)),X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1514,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK5(X1,X0)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3177,plain,
    ( r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1514,c_1935])).

cnf(c_6180,plain,
    ( r2_hidden(X0,k1_relat_1(k1_relat_1(k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1514,c_3177])).

cnf(c_13543,plain,
    ( k1_relat_1(k1_relat_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4021,c_6180])).

cnf(c_7927,plain,
    ( r2_hidden(X0,k1_relat_1(k1_relat_1(k1_relat_1(k1_xboole_0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1514,c_6180])).

cnf(c_13549,plain,
    ( k1_relat_1(k1_relat_1(k1_relat_1(k1_xboole_0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4021,c_7927])).

cnf(c_13566,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_13543,c_13549])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1503,plain,
    ( m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_22,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_10,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_354,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_22,c_10])).

cnf(c_1500,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_354])).

cnf(c_1930,plain,
    ( r1_tarski(k2_relat_1(sK13),sK12) = iProver_top
    | v1_relat_1(sK13) != iProver_top ),
    inference(superposition,[status(thm)],[c_1503,c_1500])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1523,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4079,plain,
    ( r2_hidden(X0,k2_relat_1(sK13)) != iProver_top
    | r2_hidden(X0,sK12) = iProver_top
    | v1_relat_1(sK13) != iProver_top ),
    inference(superposition,[status(thm)],[c_1930,c_1523])).

cnf(c_32,plain,
    ( m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1704,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1963,plain,
    ( ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12)))
    | ~ v1_relat_1(k2_zfmisc_1(sK11,sK12))
    | v1_relat_1(sK13) ),
    inference(instantiation,[status(thm)],[c_1704])).

cnf(c_1964,plain,
    ( m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK11,sK12)) != iProver_top
    | v1_relat_1(sK13) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1963])).

cnf(c_19,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2430,plain,
    ( v1_relat_1(k2_zfmisc_1(sK11,sK12)) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_2431,plain,
    ( v1_relat_1(k2_zfmisc_1(sK11,sK12)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2430])).

cnf(c_4183,plain,
    ( r2_hidden(X0,sK12) = iProver_top
    | r2_hidden(X0,k2_relat_1(sK13)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4079,c_32,c_1964,c_2431])).

cnf(c_4184,plain,
    ( r2_hidden(X0,k2_relat_1(sK13)) != iProver_top
    | r2_hidden(X0,sK12) = iProver_top ),
    inference(renaming,[status(thm)],[c_4183])).

cnf(c_4193,plain,
    ( k2_relat_1(sK13) = X0
    | r2_hidden(sK2(X0,k2_relat_1(sK13)),X0) = iProver_top
    | r2_hidden(sK2(X0,k2_relat_1(sK13)),sK12) = iProver_top ),
    inference(superposition,[status(thm)],[c_1521,c_4184])).

cnf(c_5416,plain,
    ( k2_relat_1(sK13) = k1_xboole_0
    | r2_hidden(sK2(k1_xboole_0,k2_relat_1(sK13)),sK12) = iProver_top ),
    inference(superposition,[status(thm)],[c_4193,c_1935])).

cnf(c_7,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1519,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_6832,plain,
    ( k2_relat_1(sK13) = k1_xboole_0
    | m1_subset_1(sK2(k1_xboole_0,k2_relat_1(sK13)),sK12) = iProver_top ),
    inference(superposition,[status(thm)],[c_5416,c_1519])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1505,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2996,plain,
    ( k2_relset_1(sK11,sK12,sK13) = k2_relat_1(sK13) ),
    inference(superposition,[status(thm)],[c_1503,c_1505])).

cnf(c_25,negated_conjecture,
    ( ~ m1_subset_1(X0,sK12)
    | ~ r2_hidden(X0,k2_relset_1(sK11,sK12,sK13)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1504,plain,
    ( m1_subset_1(X0,sK12) != iProver_top
    | r2_hidden(X0,k2_relset_1(sK11,sK12,sK13)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3370,plain,
    ( m1_subset_1(X0,sK12) != iProver_top
    | r2_hidden(X0,k2_relat_1(sK13)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2996,c_1504])).

cnf(c_4025,plain,
    ( k2_relat_1(sK13) = X0
    | m1_subset_1(sK2(X0,k2_relat_1(sK13)),sK12) != iProver_top
    | r2_hidden(sK2(X0,k2_relat_1(sK13)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1521,c_3370])).

cnf(c_9665,plain,
    ( k2_relat_1(sK13) = k1_xboole_0
    | r2_hidden(sK2(k1_xboole_0,k2_relat_1(sK13)),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6832,c_4025])).

cnf(c_10354,plain,
    ( k2_relat_1(sK13) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_9665,c_1935])).

cnf(c_20,plain,
    ( r2_hidden(k4_tarski(sK9(X0),sK10(X0)),X0)
    | ~ v1_relat_1(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1508,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(k4_tarski(sK9(X0),sK10(X0)),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_17,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1511,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3833,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK10(X0),k2_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1508,c_1511])).

cnf(c_11647,plain,
    ( sK13 = k1_xboole_0
    | r2_hidden(sK10(sK13),k1_xboole_0) = iProver_top
    | v1_relat_1(sK13) != iProver_top ),
    inference(superposition,[status(thm)],[c_10354,c_3833])).

cnf(c_12495,plain,
    ( r2_hidden(sK10(sK13),k1_xboole_0) = iProver_top
    | sK13 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11647,c_32,c_1964,c_2431])).

cnf(c_12496,plain,
    ( sK13 = k1_xboole_0
    | r2_hidden(sK10(sK13),k1_xboole_0) = iProver_top ),
    inference(renaming,[status(thm)],[c_12495])).

cnf(c_12501,plain,
    ( sK13 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_12496,c_1935])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1506,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3073,plain,
    ( k1_relset_1(sK11,sK12,sK13) = k1_relat_1(sK13) ),
    inference(superposition,[status(thm)],[c_1503,c_1506])).

cnf(c_26,negated_conjecture,
    ( k1_xboole_0 != k1_relset_1(sK11,sK12,sK13) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_3384,plain,
    ( k1_relat_1(sK13) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3073,c_26])).

cnf(c_12505,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_12501,c_3384])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13566,c_12505])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 12:29:44 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.37/1.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.37/1.03  
% 1.37/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.37/1.03  
% 1.37/1.03  ------  iProver source info
% 1.37/1.03  
% 1.37/1.03  git: date: 2020-06-30 10:37:57 +0100
% 1.37/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.37/1.03  git: non_committed_changes: false
% 1.37/1.03  git: last_make_outside_of_git: false
% 1.37/1.03  
% 1.37/1.03  ------ 
% 1.37/1.03  
% 1.37/1.03  ------ Input Options
% 1.37/1.03  
% 1.37/1.03  --out_options                           all
% 1.37/1.03  --tptp_safe_out                         true
% 1.37/1.03  --problem_path                          ""
% 1.37/1.03  --include_path                          ""
% 1.37/1.03  --clausifier                            res/vclausify_rel
% 1.37/1.03  --clausifier_options                    --mode clausify
% 1.37/1.03  --stdin                                 false
% 1.37/1.03  --stats_out                             all
% 1.37/1.03  
% 1.37/1.03  ------ General Options
% 1.37/1.03  
% 1.37/1.03  --fof                                   false
% 1.37/1.03  --time_out_real                         305.
% 1.37/1.03  --time_out_virtual                      -1.
% 1.37/1.03  --symbol_type_check                     false
% 1.37/1.03  --clausify_out                          false
% 1.37/1.03  --sig_cnt_out                           false
% 1.37/1.03  --trig_cnt_out                          false
% 1.37/1.03  --trig_cnt_out_tolerance                1.
% 1.37/1.03  --trig_cnt_out_sk_spl                   false
% 1.37/1.03  --abstr_cl_out                          false
% 1.37/1.03  
% 1.37/1.03  ------ Global Options
% 1.37/1.03  
% 1.37/1.03  --schedule                              default
% 1.37/1.03  --add_important_lit                     false
% 1.37/1.03  --prop_solver_per_cl                    1000
% 1.37/1.03  --min_unsat_core                        false
% 1.37/1.03  --soft_assumptions                      false
% 1.37/1.03  --soft_lemma_size                       3
% 1.37/1.03  --prop_impl_unit_size                   0
% 1.37/1.03  --prop_impl_unit                        []
% 1.37/1.03  --share_sel_clauses                     true
% 1.37/1.03  --reset_solvers                         false
% 1.37/1.03  --bc_imp_inh                            [conj_cone]
% 1.37/1.03  --conj_cone_tolerance                   3.
% 1.37/1.03  --extra_neg_conj                        none
% 1.37/1.03  --large_theory_mode                     true
% 1.37/1.03  --prolific_symb_bound                   200
% 1.37/1.03  --lt_threshold                          2000
% 1.37/1.03  --clause_weak_htbl                      true
% 1.37/1.03  --gc_record_bc_elim                     false
% 1.37/1.03  
% 1.37/1.03  ------ Preprocessing Options
% 1.37/1.03  
% 1.37/1.03  --preprocessing_flag                    true
% 1.37/1.03  --time_out_prep_mult                    0.1
% 1.37/1.03  --splitting_mode                        input
% 1.37/1.03  --splitting_grd                         true
% 1.37/1.03  --splitting_cvd                         false
% 1.37/1.03  --splitting_cvd_svl                     false
% 1.37/1.03  --splitting_nvd                         32
% 1.37/1.03  --sub_typing                            true
% 1.37/1.03  --prep_gs_sim                           true
% 1.37/1.03  --prep_unflatten                        true
% 1.37/1.03  --prep_res_sim                          true
% 1.37/1.03  --prep_upred                            true
% 1.37/1.03  --prep_sem_filter                       exhaustive
% 1.37/1.03  --prep_sem_filter_out                   false
% 1.37/1.03  --pred_elim                             true
% 1.37/1.03  --res_sim_input                         true
% 1.37/1.03  --eq_ax_congr_red                       true
% 1.37/1.03  --pure_diseq_elim                       true
% 1.37/1.03  --brand_transform                       false
% 1.37/1.03  --non_eq_to_eq                          false
% 1.37/1.03  --prep_def_merge                        true
% 1.37/1.03  --prep_def_merge_prop_impl              false
% 1.37/1.03  --prep_def_merge_mbd                    true
% 1.37/1.03  --prep_def_merge_tr_red                 false
% 1.37/1.03  --prep_def_merge_tr_cl                  false
% 1.37/1.03  --smt_preprocessing                     true
% 1.37/1.03  --smt_ac_axioms                         fast
% 1.37/1.03  --preprocessed_out                      false
% 1.37/1.03  --preprocessed_stats                    false
% 1.37/1.03  
% 1.37/1.03  ------ Abstraction refinement Options
% 1.37/1.03  
% 1.37/1.03  --abstr_ref                             []
% 1.37/1.03  --abstr_ref_prep                        false
% 1.37/1.03  --abstr_ref_until_sat                   false
% 1.37/1.03  --abstr_ref_sig_restrict                funpre
% 1.37/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 1.37/1.03  --abstr_ref_under                       []
% 1.37/1.03  
% 1.37/1.03  ------ SAT Options
% 1.37/1.03  
% 1.37/1.03  --sat_mode                              false
% 1.37/1.03  --sat_fm_restart_options                ""
% 1.37/1.03  --sat_gr_def                            false
% 1.37/1.03  --sat_epr_types                         true
% 1.37/1.03  --sat_non_cyclic_types                  false
% 1.37/1.03  --sat_finite_models                     false
% 1.37/1.03  --sat_fm_lemmas                         false
% 1.37/1.03  --sat_fm_prep                           false
% 1.37/1.03  --sat_fm_uc_incr                        true
% 1.37/1.03  --sat_out_model                         small
% 1.37/1.03  --sat_out_clauses                       false
% 1.37/1.03  
% 1.37/1.03  ------ QBF Options
% 1.37/1.03  
% 1.37/1.03  --qbf_mode                              false
% 1.37/1.03  --qbf_elim_univ                         false
% 1.37/1.03  --qbf_dom_inst                          none
% 1.37/1.03  --qbf_dom_pre_inst                      false
% 1.37/1.03  --qbf_sk_in                             false
% 1.37/1.03  --qbf_pred_elim                         true
% 1.37/1.03  --qbf_split                             512
% 1.37/1.03  
% 1.37/1.03  ------ BMC1 Options
% 1.37/1.03  
% 1.37/1.03  --bmc1_incremental                      false
% 1.37/1.03  --bmc1_axioms                           reachable_all
% 1.37/1.03  --bmc1_min_bound                        0
% 1.37/1.03  --bmc1_max_bound                        -1
% 1.37/1.03  --bmc1_max_bound_default                -1
% 1.37/1.03  --bmc1_symbol_reachability              true
% 1.37/1.03  --bmc1_property_lemmas                  false
% 1.37/1.03  --bmc1_k_induction                      false
% 1.37/1.03  --bmc1_non_equiv_states                 false
% 1.37/1.03  --bmc1_deadlock                         false
% 1.37/1.03  --bmc1_ucm                              false
% 1.37/1.03  --bmc1_add_unsat_core                   none
% 1.37/1.03  --bmc1_unsat_core_children              false
% 1.37/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 1.37/1.03  --bmc1_out_stat                         full
% 1.37/1.03  --bmc1_ground_init                      false
% 1.37/1.03  --bmc1_pre_inst_next_state              false
% 1.37/1.03  --bmc1_pre_inst_state                   false
% 1.37/1.03  --bmc1_pre_inst_reach_state             false
% 1.37/1.03  --bmc1_out_unsat_core                   false
% 1.37/1.03  --bmc1_aig_witness_out                  false
% 1.37/1.03  --bmc1_verbose                          false
% 1.37/1.03  --bmc1_dump_clauses_tptp                false
% 1.37/1.03  --bmc1_dump_unsat_core_tptp             false
% 1.37/1.03  --bmc1_dump_file                        -
% 1.37/1.03  --bmc1_ucm_expand_uc_limit              128
% 1.37/1.03  --bmc1_ucm_n_expand_iterations          6
% 1.37/1.03  --bmc1_ucm_extend_mode                  1
% 1.37/1.03  --bmc1_ucm_init_mode                    2
% 1.37/1.03  --bmc1_ucm_cone_mode                    none
% 1.37/1.03  --bmc1_ucm_reduced_relation_type        0
% 1.37/1.03  --bmc1_ucm_relax_model                  4
% 1.37/1.03  --bmc1_ucm_full_tr_after_sat            true
% 1.37/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 1.37/1.03  --bmc1_ucm_layered_model                none
% 1.37/1.03  --bmc1_ucm_max_lemma_size               10
% 1.37/1.03  
% 1.37/1.03  ------ AIG Options
% 1.37/1.03  
% 1.37/1.03  --aig_mode                              false
% 1.37/1.03  
% 1.37/1.03  ------ Instantiation Options
% 1.37/1.03  
% 1.37/1.03  --instantiation_flag                    true
% 1.37/1.03  --inst_sos_flag                         false
% 1.37/1.03  --inst_sos_phase                        true
% 1.37/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.37/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.37/1.03  --inst_lit_sel_side                     num_symb
% 1.37/1.03  --inst_solver_per_active                1400
% 1.37/1.03  --inst_solver_calls_frac                1.
% 1.37/1.03  --inst_passive_queue_type               priority_queues
% 1.37/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.37/1.03  --inst_passive_queues_freq              [25;2]
% 1.37/1.03  --inst_dismatching                      true
% 1.37/1.03  --inst_eager_unprocessed_to_passive     true
% 1.37/1.03  --inst_prop_sim_given                   true
% 1.37/1.03  --inst_prop_sim_new                     false
% 1.37/1.03  --inst_subs_new                         false
% 1.37/1.03  --inst_eq_res_simp                      false
% 1.37/1.03  --inst_subs_given                       false
% 1.37/1.03  --inst_orphan_elimination               true
% 1.37/1.03  --inst_learning_loop_flag               true
% 1.37/1.03  --inst_learning_start                   3000
% 1.37/1.03  --inst_learning_factor                  2
% 1.37/1.03  --inst_start_prop_sim_after_learn       3
% 1.37/1.03  --inst_sel_renew                        solver
% 1.37/1.03  --inst_lit_activity_flag                true
% 1.37/1.03  --inst_restr_to_given                   false
% 1.37/1.03  --inst_activity_threshold               500
% 1.37/1.03  --inst_out_proof                        true
% 1.37/1.03  
% 1.37/1.03  ------ Resolution Options
% 1.37/1.03  
% 1.37/1.03  --resolution_flag                       true
% 1.37/1.03  --res_lit_sel                           adaptive
% 1.37/1.03  --res_lit_sel_side                      none
% 1.37/1.03  --res_ordering                          kbo
% 1.37/1.03  --res_to_prop_solver                    active
% 1.37/1.03  --res_prop_simpl_new                    false
% 1.37/1.03  --res_prop_simpl_given                  true
% 1.37/1.03  --res_passive_queue_type                priority_queues
% 1.37/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.37/1.03  --res_passive_queues_freq               [15;5]
% 1.37/1.03  --res_forward_subs                      full
% 1.37/1.03  --res_backward_subs                     full
% 1.37/1.03  --res_forward_subs_resolution           true
% 1.37/1.03  --res_backward_subs_resolution          true
% 1.37/1.03  --res_orphan_elimination                true
% 1.37/1.03  --res_time_limit                        2.
% 1.37/1.03  --res_out_proof                         true
% 1.37/1.03  
% 1.37/1.03  ------ Superposition Options
% 1.37/1.03  
% 1.37/1.03  --superposition_flag                    true
% 1.37/1.03  --sup_passive_queue_type                priority_queues
% 1.37/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.37/1.03  --sup_passive_queues_freq               [8;1;4]
% 1.37/1.03  --demod_completeness_check              fast
% 1.37/1.03  --demod_use_ground                      true
% 1.37/1.03  --sup_to_prop_solver                    passive
% 1.37/1.03  --sup_prop_simpl_new                    true
% 1.37/1.03  --sup_prop_simpl_given                  true
% 1.37/1.03  --sup_fun_splitting                     false
% 1.37/1.03  --sup_smt_interval                      50000
% 1.37/1.03  
% 1.37/1.03  ------ Superposition Simplification Setup
% 1.37/1.03  
% 1.37/1.03  --sup_indices_passive                   []
% 1.37/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.37/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.37/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.37/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 1.37/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.37/1.03  --sup_full_bw                           [BwDemod]
% 1.37/1.03  --sup_immed_triv                        [TrivRules]
% 1.37/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.37/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.37/1.03  --sup_immed_bw_main                     []
% 1.37/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.37/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 1.37/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.37/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.37/1.03  
% 1.37/1.03  ------ Combination Options
% 1.37/1.03  
% 1.37/1.03  --comb_res_mult                         3
% 1.37/1.03  --comb_sup_mult                         2
% 1.37/1.03  --comb_inst_mult                        10
% 1.37/1.03  
% 1.37/1.03  ------ Debug Options
% 1.37/1.03  
% 1.37/1.03  --dbg_backtrace                         false
% 1.37/1.03  --dbg_dump_prop_clauses                 false
% 1.37/1.03  --dbg_dump_prop_clauses_file            -
% 1.37/1.03  --dbg_out_stat                          false
% 1.37/1.03  ------ Parsing...
% 1.37/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.37/1.03  
% 1.37/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 1.37/1.03  
% 1.37/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.37/1.03  
% 1.37/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.37/1.03  ------ Proving...
% 1.37/1.03  ------ Problem Properties 
% 1.37/1.03  
% 1.37/1.03  
% 1.37/1.03  clauses                                 27
% 1.37/1.03  conjectures                             3
% 1.37/1.03  EPR                                     4
% 1.37/1.03  Horn                                    22
% 1.37/1.03  unary                                   6
% 1.37/1.03  binary                                  11
% 1.37/1.03  lits                                    58
% 1.37/1.03  lits eq                                 10
% 1.37/1.03  fd_pure                                 0
% 1.37/1.03  fd_pseudo                               0
% 1.37/1.03  fd_cond                                 1
% 1.37/1.03  fd_pseudo_cond                          6
% 1.37/1.03  AC symbols                              0
% 1.37/1.03  
% 1.37/1.03  ------ Schedule dynamic 5 is on 
% 1.37/1.03  
% 1.37/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.37/1.03  
% 1.37/1.03  
% 1.37/1.03  ------ 
% 1.37/1.03  Current options:
% 1.37/1.03  ------ 
% 1.37/1.03  
% 1.37/1.03  ------ Input Options
% 1.37/1.03  
% 1.37/1.03  --out_options                           all
% 1.37/1.03  --tptp_safe_out                         true
% 1.37/1.03  --problem_path                          ""
% 1.37/1.03  --include_path                          ""
% 1.37/1.03  --clausifier                            res/vclausify_rel
% 1.37/1.03  --clausifier_options                    --mode clausify
% 1.37/1.03  --stdin                                 false
% 1.37/1.03  --stats_out                             all
% 1.37/1.03  
% 1.37/1.03  ------ General Options
% 1.37/1.03  
% 1.37/1.03  --fof                                   false
% 1.37/1.03  --time_out_real                         305.
% 1.37/1.03  --time_out_virtual                      -1.
% 1.37/1.03  --symbol_type_check                     false
% 1.37/1.03  --clausify_out                          false
% 1.37/1.03  --sig_cnt_out                           false
% 1.37/1.03  --trig_cnt_out                          false
% 1.37/1.03  --trig_cnt_out_tolerance                1.
% 1.37/1.03  --trig_cnt_out_sk_spl                   false
% 1.37/1.03  --abstr_cl_out                          false
% 1.37/1.03  
% 1.37/1.03  ------ Global Options
% 1.37/1.03  
% 1.37/1.03  --schedule                              default
% 1.37/1.03  --add_important_lit                     false
% 1.37/1.03  --prop_solver_per_cl                    1000
% 1.37/1.03  --min_unsat_core                        false
% 1.37/1.03  --soft_assumptions                      false
% 1.37/1.03  --soft_lemma_size                       3
% 1.37/1.03  --prop_impl_unit_size                   0
% 1.37/1.03  --prop_impl_unit                        []
% 1.37/1.03  --share_sel_clauses                     true
% 1.37/1.03  --reset_solvers                         false
% 1.37/1.03  --bc_imp_inh                            [conj_cone]
% 1.37/1.03  --conj_cone_tolerance                   3.
% 1.37/1.03  --extra_neg_conj                        none
% 1.37/1.03  --large_theory_mode                     true
% 1.37/1.03  --prolific_symb_bound                   200
% 1.37/1.03  --lt_threshold                          2000
% 1.37/1.03  --clause_weak_htbl                      true
% 1.37/1.03  --gc_record_bc_elim                     false
% 1.37/1.03  
% 1.37/1.03  ------ Preprocessing Options
% 1.37/1.03  
% 1.37/1.03  --preprocessing_flag                    true
% 1.37/1.03  --time_out_prep_mult                    0.1
% 1.37/1.03  --splitting_mode                        input
% 1.37/1.03  --splitting_grd                         true
% 1.37/1.03  --splitting_cvd                         false
% 1.37/1.03  --splitting_cvd_svl                     false
% 1.37/1.03  --splitting_nvd                         32
% 1.37/1.03  --sub_typing                            true
% 1.37/1.03  --prep_gs_sim                           true
% 1.37/1.03  --prep_unflatten                        true
% 1.37/1.03  --prep_res_sim                          true
% 1.37/1.03  --prep_upred                            true
% 1.37/1.03  --prep_sem_filter                       exhaustive
% 1.37/1.03  --prep_sem_filter_out                   false
% 1.37/1.03  --pred_elim                             true
% 1.37/1.03  --res_sim_input                         true
% 1.37/1.03  --eq_ax_congr_red                       true
% 1.37/1.03  --pure_diseq_elim                       true
% 1.37/1.03  --brand_transform                       false
% 1.37/1.03  --non_eq_to_eq                          false
% 1.37/1.03  --prep_def_merge                        true
% 1.37/1.03  --prep_def_merge_prop_impl              false
% 1.37/1.03  --prep_def_merge_mbd                    true
% 1.37/1.03  --prep_def_merge_tr_red                 false
% 1.37/1.03  --prep_def_merge_tr_cl                  false
% 1.37/1.03  --smt_preprocessing                     true
% 1.37/1.03  --smt_ac_axioms                         fast
% 1.37/1.03  --preprocessed_out                      false
% 1.37/1.03  --preprocessed_stats                    false
% 1.37/1.03  
% 1.37/1.03  ------ Abstraction refinement Options
% 1.37/1.03  
% 1.37/1.03  --abstr_ref                             []
% 1.37/1.03  --abstr_ref_prep                        false
% 1.37/1.03  --abstr_ref_until_sat                   false
% 1.37/1.03  --abstr_ref_sig_restrict                funpre
% 1.37/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 1.37/1.03  --abstr_ref_under                       []
% 1.37/1.03  
% 1.37/1.03  ------ SAT Options
% 1.37/1.03  
% 1.37/1.03  --sat_mode                              false
% 1.37/1.03  --sat_fm_restart_options                ""
% 1.37/1.03  --sat_gr_def                            false
% 1.37/1.03  --sat_epr_types                         true
% 1.37/1.03  --sat_non_cyclic_types                  false
% 1.37/1.03  --sat_finite_models                     false
% 1.37/1.03  --sat_fm_lemmas                         false
% 1.37/1.03  --sat_fm_prep                           false
% 1.37/1.03  --sat_fm_uc_incr                        true
% 1.37/1.03  --sat_out_model                         small
% 1.37/1.03  --sat_out_clauses                       false
% 1.37/1.03  
% 1.37/1.03  ------ QBF Options
% 1.37/1.03  
% 1.37/1.03  --qbf_mode                              false
% 1.37/1.03  --qbf_elim_univ                         false
% 1.37/1.03  --qbf_dom_inst                          none
% 1.37/1.03  --qbf_dom_pre_inst                      false
% 1.37/1.03  --qbf_sk_in                             false
% 1.37/1.03  --qbf_pred_elim                         true
% 1.37/1.03  --qbf_split                             512
% 1.37/1.03  
% 1.37/1.03  ------ BMC1 Options
% 1.37/1.03  
% 1.37/1.03  --bmc1_incremental                      false
% 1.37/1.03  --bmc1_axioms                           reachable_all
% 1.37/1.03  --bmc1_min_bound                        0
% 1.37/1.03  --bmc1_max_bound                        -1
% 1.37/1.03  --bmc1_max_bound_default                -1
% 1.37/1.03  --bmc1_symbol_reachability              true
% 1.37/1.03  --bmc1_property_lemmas                  false
% 1.37/1.03  --bmc1_k_induction                      false
% 1.37/1.03  --bmc1_non_equiv_states                 false
% 1.37/1.03  --bmc1_deadlock                         false
% 1.37/1.03  --bmc1_ucm                              false
% 1.37/1.03  --bmc1_add_unsat_core                   none
% 1.37/1.03  --bmc1_unsat_core_children              false
% 1.37/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 1.37/1.03  --bmc1_out_stat                         full
% 1.37/1.03  --bmc1_ground_init                      false
% 1.37/1.03  --bmc1_pre_inst_next_state              false
% 1.37/1.03  --bmc1_pre_inst_state                   false
% 1.37/1.03  --bmc1_pre_inst_reach_state             false
% 1.37/1.03  --bmc1_out_unsat_core                   false
% 1.37/1.03  --bmc1_aig_witness_out                  false
% 1.37/1.03  --bmc1_verbose                          false
% 1.37/1.03  --bmc1_dump_clauses_tptp                false
% 1.37/1.03  --bmc1_dump_unsat_core_tptp             false
% 1.37/1.03  --bmc1_dump_file                        -
% 1.37/1.03  --bmc1_ucm_expand_uc_limit              128
% 1.37/1.03  --bmc1_ucm_n_expand_iterations          6
% 1.37/1.03  --bmc1_ucm_extend_mode                  1
% 1.37/1.03  --bmc1_ucm_init_mode                    2
% 1.37/1.03  --bmc1_ucm_cone_mode                    none
% 1.37/1.03  --bmc1_ucm_reduced_relation_type        0
% 1.37/1.03  --bmc1_ucm_relax_model                  4
% 1.37/1.03  --bmc1_ucm_full_tr_after_sat            true
% 1.37/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 1.37/1.03  --bmc1_ucm_layered_model                none
% 1.37/1.03  --bmc1_ucm_max_lemma_size               10
% 1.37/1.03  
% 1.37/1.03  ------ AIG Options
% 1.37/1.03  
% 1.37/1.03  --aig_mode                              false
% 1.37/1.03  
% 1.37/1.03  ------ Instantiation Options
% 1.37/1.03  
% 1.37/1.03  --instantiation_flag                    true
% 1.37/1.03  --inst_sos_flag                         false
% 1.37/1.03  --inst_sos_phase                        true
% 1.37/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.37/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.37/1.03  --inst_lit_sel_side                     none
% 1.37/1.03  --inst_solver_per_active                1400
% 1.37/1.03  --inst_solver_calls_frac                1.
% 1.37/1.03  --inst_passive_queue_type               priority_queues
% 1.37/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.37/1.03  --inst_passive_queues_freq              [25;2]
% 1.37/1.03  --inst_dismatching                      true
% 1.37/1.03  --inst_eager_unprocessed_to_passive     true
% 1.37/1.03  --inst_prop_sim_given                   true
% 1.37/1.03  --inst_prop_sim_new                     false
% 1.37/1.03  --inst_subs_new                         false
% 1.37/1.03  --inst_eq_res_simp                      false
% 1.37/1.03  --inst_subs_given                       false
% 1.37/1.03  --inst_orphan_elimination               true
% 1.37/1.03  --inst_learning_loop_flag               true
% 1.37/1.03  --inst_learning_start                   3000
% 1.37/1.03  --inst_learning_factor                  2
% 1.37/1.03  --inst_start_prop_sim_after_learn       3
% 1.37/1.03  --inst_sel_renew                        solver
% 1.37/1.03  --inst_lit_activity_flag                true
% 1.37/1.03  --inst_restr_to_given                   false
% 1.37/1.03  --inst_activity_threshold               500
% 1.37/1.03  --inst_out_proof                        true
% 1.37/1.03  
% 1.37/1.03  ------ Resolution Options
% 1.37/1.03  
% 1.37/1.03  --resolution_flag                       false
% 1.37/1.03  --res_lit_sel                           adaptive
% 1.37/1.03  --res_lit_sel_side                      none
% 1.37/1.03  --res_ordering                          kbo
% 1.37/1.03  --res_to_prop_solver                    active
% 1.37/1.03  --res_prop_simpl_new                    false
% 1.37/1.03  --res_prop_simpl_given                  true
% 1.37/1.03  --res_passive_queue_type                priority_queues
% 1.37/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.37/1.03  --res_passive_queues_freq               [15;5]
% 1.37/1.03  --res_forward_subs                      full
% 1.37/1.03  --res_backward_subs                     full
% 1.37/1.03  --res_forward_subs_resolution           true
% 1.37/1.03  --res_backward_subs_resolution          true
% 1.37/1.03  --res_orphan_elimination                true
% 1.37/1.03  --res_time_limit                        2.
% 1.37/1.03  --res_out_proof                         true
% 1.37/1.03  
% 1.37/1.03  ------ Superposition Options
% 1.37/1.03  
% 1.37/1.03  --superposition_flag                    true
% 1.37/1.03  --sup_passive_queue_type                priority_queues
% 1.37/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.37/1.03  --sup_passive_queues_freq               [8;1;4]
% 1.37/1.03  --demod_completeness_check              fast
% 1.37/1.03  --demod_use_ground                      true
% 1.37/1.03  --sup_to_prop_solver                    passive
% 1.37/1.03  --sup_prop_simpl_new                    true
% 1.37/1.03  --sup_prop_simpl_given                  true
% 1.37/1.03  --sup_fun_splitting                     false
% 1.37/1.03  --sup_smt_interval                      50000
% 1.37/1.03  
% 1.37/1.03  ------ Superposition Simplification Setup
% 1.37/1.03  
% 1.37/1.03  --sup_indices_passive                   []
% 1.37/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.37/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.37/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.37/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 1.37/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.37/1.03  --sup_full_bw                           [BwDemod]
% 1.37/1.03  --sup_immed_triv                        [TrivRules]
% 1.37/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.37/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.37/1.03  --sup_immed_bw_main                     []
% 1.37/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.37/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 1.37/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.37/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.37/1.03  
% 1.37/1.03  ------ Combination Options
% 1.37/1.03  
% 1.37/1.03  --comb_res_mult                         3
% 1.37/1.03  --comb_sup_mult                         2
% 1.37/1.03  --comb_inst_mult                        10
% 1.37/1.03  
% 1.37/1.03  ------ Debug Options
% 1.37/1.03  
% 1.37/1.03  --dbg_backtrace                         false
% 1.37/1.03  --dbg_dump_prop_clauses                 false
% 1.37/1.03  --dbg_dump_prop_clauses_file            -
% 1.37/1.03  --dbg_out_stat                          false
% 1.37/1.03  
% 1.37/1.03  
% 1.37/1.03  
% 1.37/1.03  
% 1.37/1.03  ------ Proving...
% 1.37/1.03  
% 1.37/1.03  
% 1.37/1.03  % SZS status Theorem for theBenchmark.p
% 1.37/1.03  
% 1.37/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 1.37/1.03  
% 1.37/1.03  fof(f3,axiom,(
% 1.37/1.03    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 1.37/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.37/1.03  
% 1.37/1.03  fof(f22,plain,(
% 1.37/1.03    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 1.37/1.03    inference(ennf_transformation,[],[f3])).
% 1.37/1.03  
% 1.37/1.03  fof(f40,plain,(
% 1.37/1.03    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 1.37/1.03    inference(nnf_transformation,[],[f22])).
% 1.37/1.03  
% 1.37/1.03  fof(f41,plain,(
% 1.37/1.03    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK2(X0,X1),X1) | ~r2_hidden(sK2(X0,X1),X0)) & (r2_hidden(sK2(X0,X1),X1) | r2_hidden(sK2(X0,X1),X0))))),
% 1.37/1.03    introduced(choice_axiom,[])).
% 1.37/1.03  
% 1.37/1.03  fof(f42,plain,(
% 1.37/1.03    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK2(X0,X1),X1) | ~r2_hidden(sK2(X0,X1),X0)) & (r2_hidden(sK2(X0,X1),X1) | r2_hidden(sK2(X0,X1),X0))))),
% 1.37/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f40,f41])).
% 1.37/1.03  
% 1.37/1.03  fof(f66,plain,(
% 1.37/1.03    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK2(X0,X1),X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 1.37/1.03    inference(cnf_transformation,[],[f42])).
% 1.37/1.03  
% 1.37/1.03  fof(f4,axiom,(
% 1.37/1.03    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.37/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.37/1.03  
% 1.37/1.03  fof(f68,plain,(
% 1.37/1.03    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.37/1.03    inference(cnf_transformation,[],[f4])).
% 1.37/1.03  
% 1.37/1.03  fof(f12,axiom,(
% 1.37/1.03    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.37/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.37/1.03  
% 1.37/1.03  fof(f28,plain,(
% 1.37/1.03    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.37/1.03    inference(ennf_transformation,[],[f12])).
% 1.37/1.03  
% 1.37/1.03  fof(f83,plain,(
% 1.37/1.03    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.37/1.03    inference(cnf_transformation,[],[f28])).
% 1.37/1.03  
% 1.37/1.03  fof(f8,axiom,(
% 1.37/1.03    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 1.37/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.37/1.03  
% 1.37/1.03  fof(f44,plain,(
% 1.37/1.03    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 1.37/1.03    inference(nnf_transformation,[],[f8])).
% 1.37/1.03  
% 1.37/1.03  fof(f45,plain,(
% 1.37/1.03    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 1.37/1.03    inference(rectify,[],[f44])).
% 1.37/1.03  
% 1.37/1.03  fof(f48,plain,(
% 1.37/1.03    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0))),
% 1.37/1.03    introduced(choice_axiom,[])).
% 1.37/1.03  
% 1.37/1.03  fof(f47,plain,(
% 1.37/1.03    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) => r2_hidden(k4_tarski(X2,sK4(X0,X1)),X0))) )),
% 1.37/1.03    introduced(choice_axiom,[])).
% 1.37/1.03  
% 1.37/1.03  fof(f46,plain,(
% 1.37/1.03    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK3(X0,X1),X3),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 1.37/1.03    introduced(choice_axiom,[])).
% 1.37/1.03  
% 1.37/1.03  fof(f49,plain,(
% 1.37/1.03    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK3(X0,X1),X3),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 1.37/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f45,f48,f47,f46])).
% 1.37/1.03  
% 1.37/1.03  fof(f73,plain,(
% 1.37/1.03    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 1.37/1.03    inference(cnf_transformation,[],[f49])).
% 1.37/1.03  
% 1.37/1.03  fof(f93,plain,(
% 1.37/1.03    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 1.37/1.03    inference(equality_resolution,[],[f73])).
% 1.37/1.03  
% 1.37/1.03  fof(f16,conjecture,(
% 1.37/1.03    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k2_relset_1(X0,X1,X2))) & k1_xboole_0 != k1_relset_1(X0,X1,X2)))))),
% 1.37/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.37/1.03  
% 1.37/1.03  fof(f17,negated_conjecture,(
% 1.37/1.03    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k2_relset_1(X0,X1,X2))) & k1_xboole_0 != k1_relset_1(X0,X1,X2)))))),
% 1.37/1.03    inference(negated_conjecture,[],[f16])).
% 1.37/1.03  
% 1.37/1.03  fof(f32,plain,(
% 1.37/1.03    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.37/1.03    inference(ennf_transformation,[],[f17])).
% 1.37/1.03  
% 1.37/1.03  fof(f33,plain,(
% 1.37/1.03    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.37/1.03    inference(flattening,[],[f32])).
% 1.37/1.03  
% 1.37/1.03  fof(f60,plain,(
% 1.37/1.03    ( ! [X0,X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,sK13)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,sK13) & m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))) )),
% 1.37/1.03    introduced(choice_axiom,[])).
% 1.37/1.03  
% 1.37/1.03  fof(f59,plain,(
% 1.37/1.03    ( ! [X0] : (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) => (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(X0,sK12,X2)) | ~m1_subset_1(X3,sK12)) & k1_xboole_0 != k1_relset_1(X0,sK12,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK12)))) & ~v1_xboole_0(sK12))) )),
% 1.37/1.03    introduced(choice_axiom,[])).
% 1.37/1.03  
% 1.37/1.03  fof(f58,plain,(
% 1.37/1.03    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(sK11,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(sK11,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK11,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK11))),
% 1.37/1.03    introduced(choice_axiom,[])).
% 1.37/1.03  
% 1.37/1.03  fof(f61,plain,(
% 1.37/1.03    ((! [X3] : (~r2_hidden(X3,k2_relset_1(sK11,sK12,sK13)) | ~m1_subset_1(X3,sK12)) & k1_xboole_0 != k1_relset_1(sK11,sK12,sK13) & m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12)))) & ~v1_xboole_0(sK12)) & ~v1_xboole_0(sK11)),
% 1.37/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11,sK12,sK13])],[f33,f60,f59,f58])).
% 1.37/1.03  
% 1.37/1.03  fof(f89,plain,(
% 1.37/1.03    m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12)))),
% 1.37/1.03    inference(cnf_transformation,[],[f61])).
% 1.37/1.03  
% 1.37/1.03  fof(f13,axiom,(
% 1.37/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.37/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.37/1.03  
% 1.37/1.03  fof(f19,plain,(
% 1.37/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.37/1.03    inference(pure_predicate_removal,[],[f13])).
% 1.37/1.03  
% 1.37/1.03  fof(f29,plain,(
% 1.37/1.03    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.37/1.03    inference(ennf_transformation,[],[f19])).
% 1.37/1.03  
% 1.37/1.03  fof(f84,plain,(
% 1.37/1.03    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.37/1.03    inference(cnf_transformation,[],[f29])).
% 1.37/1.03  
% 1.37/1.03  fof(f7,axiom,(
% 1.37/1.03    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.37/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.37/1.03  
% 1.37/1.03  fof(f25,plain,(
% 1.37/1.03    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.37/1.03    inference(ennf_transformation,[],[f7])).
% 1.37/1.03  
% 1.37/1.03  fof(f43,plain,(
% 1.37/1.03    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.37/1.03    inference(nnf_transformation,[],[f25])).
% 1.37/1.03  
% 1.37/1.03  fof(f71,plain,(
% 1.37/1.03    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.37/1.03    inference(cnf_transformation,[],[f43])).
% 1.37/1.03  
% 1.37/1.03  fof(f2,axiom,(
% 1.37/1.03    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.37/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.37/1.03  
% 1.37/1.03  fof(f21,plain,(
% 1.37/1.03    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.37/1.03    inference(ennf_transformation,[],[f2])).
% 1.37/1.03  
% 1.37/1.03  fof(f36,plain,(
% 1.37/1.03    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.37/1.03    inference(nnf_transformation,[],[f21])).
% 1.37/1.03  
% 1.37/1.03  fof(f37,plain,(
% 1.37/1.03    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.37/1.03    inference(rectify,[],[f36])).
% 1.37/1.03  
% 1.37/1.03  fof(f38,plain,(
% 1.37/1.03    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 1.37/1.03    introduced(choice_axiom,[])).
% 1.37/1.03  
% 1.37/1.03  fof(f39,plain,(
% 1.37/1.03    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.37/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f37,f38])).
% 1.37/1.03  
% 1.37/1.03  fof(f63,plain,(
% 1.37/1.03    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.37/1.03    inference(cnf_transformation,[],[f39])).
% 1.37/1.03  
% 1.37/1.03  fof(f6,axiom,(
% 1.37/1.03    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.37/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.37/1.03  
% 1.37/1.03  fof(f24,plain,(
% 1.37/1.03    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.37/1.03    inference(ennf_transformation,[],[f6])).
% 1.37/1.03  
% 1.37/1.03  fof(f70,plain,(
% 1.37/1.03    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.37/1.03    inference(cnf_transformation,[],[f24])).
% 1.37/1.03  
% 1.37/1.03  fof(f10,axiom,(
% 1.37/1.03    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.37/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.37/1.03  
% 1.37/1.03  fof(f81,plain,(
% 1.37/1.03    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.37/1.03    inference(cnf_transformation,[],[f10])).
% 1.37/1.03  
% 1.37/1.03  fof(f5,axiom,(
% 1.37/1.03    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.37/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.37/1.03  
% 1.37/1.03  fof(f23,plain,(
% 1.37/1.03    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.37/1.03    inference(ennf_transformation,[],[f5])).
% 1.37/1.03  
% 1.37/1.03  fof(f69,plain,(
% 1.37/1.03    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.37/1.03    inference(cnf_transformation,[],[f23])).
% 1.37/1.03  
% 1.37/1.03  fof(f15,axiom,(
% 1.37/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 1.37/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.37/1.03  
% 1.37/1.03  fof(f31,plain,(
% 1.37/1.03    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.37/1.03    inference(ennf_transformation,[],[f15])).
% 1.37/1.03  
% 1.37/1.03  fof(f86,plain,(
% 1.37/1.03    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.37/1.03    inference(cnf_transformation,[],[f31])).
% 1.37/1.03  
% 1.37/1.03  fof(f91,plain,(
% 1.37/1.03    ( ! [X3] : (~r2_hidden(X3,k2_relset_1(sK11,sK12,sK13)) | ~m1_subset_1(X3,sK12)) )),
% 1.37/1.03    inference(cnf_transformation,[],[f61])).
% 1.37/1.03  
% 1.37/1.03  fof(f11,axiom,(
% 1.37/1.03    ! [X0] : (v1_relat_1(X0) => (! [X1,X2] : ~r2_hidden(k4_tarski(X1,X2),X0) => k1_xboole_0 = X0))),
% 1.37/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.37/1.03  
% 1.37/1.03  fof(f26,plain,(
% 1.37/1.03    ! [X0] : ((k1_xboole_0 = X0 | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)) | ~v1_relat_1(X0))),
% 1.37/1.03    inference(ennf_transformation,[],[f11])).
% 1.37/1.03  
% 1.37/1.03  fof(f27,plain,(
% 1.37/1.03    ! [X0] : (k1_xboole_0 = X0 | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0) | ~v1_relat_1(X0))),
% 1.37/1.03    inference(flattening,[],[f26])).
% 1.37/1.03  
% 1.37/1.03  fof(f56,plain,(
% 1.37/1.03    ! [X0] : (? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0) => r2_hidden(k4_tarski(sK9(X0),sK10(X0)),X0))),
% 1.37/1.03    introduced(choice_axiom,[])).
% 1.37/1.03  
% 1.37/1.03  fof(f57,plain,(
% 1.37/1.03    ! [X0] : (k1_xboole_0 = X0 | r2_hidden(k4_tarski(sK9(X0),sK10(X0)),X0) | ~v1_relat_1(X0))),
% 1.37/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10])],[f27,f56])).
% 1.37/1.03  
% 1.37/1.03  fof(f82,plain,(
% 1.37/1.03    ( ! [X0] : (k1_xboole_0 = X0 | r2_hidden(k4_tarski(sK9(X0),sK10(X0)),X0) | ~v1_relat_1(X0)) )),
% 1.37/1.03    inference(cnf_transformation,[],[f57])).
% 1.37/1.03  
% 1.37/1.03  fof(f9,axiom,(
% 1.37/1.03    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 1.37/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.37/1.03  
% 1.37/1.03  fof(f50,plain,(
% 1.37/1.03    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 1.37/1.03    inference(nnf_transformation,[],[f9])).
% 1.37/1.03  
% 1.37/1.03  fof(f51,plain,(
% 1.37/1.03    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 1.37/1.03    inference(rectify,[],[f50])).
% 1.37/1.03  
% 1.37/1.03  fof(f54,plain,(
% 1.37/1.03    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK8(X0,X5),X5),X0))),
% 1.37/1.03    introduced(choice_axiom,[])).
% 1.37/1.03  
% 1.37/1.03  fof(f53,plain,(
% 1.37/1.03    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) => r2_hidden(k4_tarski(sK7(X0,X1),X2),X0))) )),
% 1.37/1.03    introduced(choice_axiom,[])).
% 1.37/1.03  
% 1.37/1.03  fof(f52,plain,(
% 1.37/1.03    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK6(X0,X1)),X0) | r2_hidden(sK6(X0,X1),X1))))),
% 1.37/1.03    introduced(choice_axiom,[])).
% 1.37/1.03  
% 1.37/1.03  fof(f55,plain,(
% 1.37/1.03    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0) | r2_hidden(sK6(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK8(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 1.37/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f51,f54,f53,f52])).
% 1.37/1.03  
% 1.37/1.03  fof(f78,plain,(
% 1.37/1.03    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 1.37/1.03    inference(cnf_transformation,[],[f55])).
% 1.37/1.03  
% 1.37/1.03  fof(f94,plain,(
% 1.37/1.03    ( ! [X6,X0,X5] : (r2_hidden(X5,k2_relat_1(X0)) | ~r2_hidden(k4_tarski(X6,X5),X0)) )),
% 1.37/1.03    inference(equality_resolution,[],[f78])).
% 1.37/1.03  
% 1.37/1.03  fof(f14,axiom,(
% 1.37/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.37/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.37/1.03  
% 1.37/1.03  fof(f30,plain,(
% 1.37/1.03    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.37/1.03    inference(ennf_transformation,[],[f14])).
% 1.37/1.03  
% 1.37/1.03  fof(f85,plain,(
% 1.37/1.03    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.37/1.03    inference(cnf_transformation,[],[f30])).
% 1.37/1.03  
% 1.37/1.03  fof(f90,plain,(
% 1.37/1.03    k1_xboole_0 != k1_relset_1(sK11,sK12,sK13)),
% 1.37/1.03    inference(cnf_transformation,[],[f61])).
% 1.37/1.03  
% 1.37/1.03  cnf(c_5,plain,
% 1.37/1.03      ( r2_hidden(sK2(X0,X1),X1) | r2_hidden(sK2(X0,X1),X0) | X1 = X0 ),
% 1.37/1.03      inference(cnf_transformation,[],[f66]) ).
% 1.37/1.03  
% 1.37/1.03  cnf(c_1521,plain,
% 1.37/1.03      ( X0 = X1
% 1.37/1.03      | r2_hidden(sK2(X1,X0),X0) = iProver_top
% 1.37/1.03      | r2_hidden(sK2(X1,X0),X1) = iProver_top ),
% 1.37/1.03      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 1.37/1.03  
% 1.37/1.03  cnf(c_6,plain,
% 1.37/1.03      ( r1_tarski(k1_xboole_0,X0) ),
% 1.37/1.03      inference(cnf_transformation,[],[f68]) ).
% 1.37/1.03  
% 1.37/1.03  cnf(c_1520,plain,
% 1.37/1.03      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 1.37/1.03      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 1.37/1.03  
% 1.37/1.03  cnf(c_21,plain,
% 1.37/1.03      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 1.37/1.03      inference(cnf_transformation,[],[f83]) ).
% 1.37/1.03  
% 1.37/1.03  cnf(c_1507,plain,
% 1.37/1.03      ( r1_tarski(X0,X1) != iProver_top
% 1.37/1.03      | r2_hidden(X1,X0) != iProver_top ),
% 1.37/1.03      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 1.37/1.03  
% 1.37/1.03  cnf(c_1935,plain,
% 1.37/1.03      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 1.37/1.03      inference(superposition,[status(thm)],[c_1520,c_1507]) ).
% 1.37/1.03  
% 1.37/1.03  cnf(c_4021,plain,
% 1.37/1.03      ( k1_xboole_0 = X0
% 1.37/1.03      | r2_hidden(sK2(k1_xboole_0,X0),X0) = iProver_top ),
% 1.37/1.03      inference(superposition,[status(thm)],[c_1521,c_1935]) ).
% 1.37/1.03  
% 1.37/1.03  cnf(c_14,plain,
% 1.37/1.03      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 1.37/1.03      | r2_hidden(k4_tarski(X0,sK5(X1,X0)),X1) ),
% 1.37/1.03      inference(cnf_transformation,[],[f93]) ).
% 1.37/1.03  
% 1.37/1.03  cnf(c_1514,plain,
% 1.37/1.03      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 1.37/1.03      | r2_hidden(k4_tarski(X0,sK5(X1,X0)),X1) = iProver_top ),
% 1.37/1.03      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 1.37/1.03  
% 1.37/1.03  cnf(c_3177,plain,
% 1.37/1.03      ( r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top ),
% 1.37/1.03      inference(superposition,[status(thm)],[c_1514,c_1935]) ).
% 1.37/1.03  
% 1.37/1.03  cnf(c_6180,plain,
% 1.37/1.03      ( r2_hidden(X0,k1_relat_1(k1_relat_1(k1_xboole_0))) != iProver_top ),
% 1.37/1.03      inference(superposition,[status(thm)],[c_1514,c_3177]) ).
% 1.37/1.03  
% 1.37/1.03  cnf(c_13543,plain,
% 1.37/1.03      ( k1_relat_1(k1_relat_1(k1_xboole_0)) = k1_xboole_0 ),
% 1.37/1.03      inference(superposition,[status(thm)],[c_4021,c_6180]) ).
% 1.37/1.03  
% 1.37/1.03  cnf(c_7927,plain,
% 1.37/1.03      ( r2_hidden(X0,k1_relat_1(k1_relat_1(k1_relat_1(k1_xboole_0)))) != iProver_top ),
% 1.37/1.03      inference(superposition,[status(thm)],[c_1514,c_6180]) ).
% 1.37/1.03  
% 1.37/1.03  cnf(c_13549,plain,
% 1.37/1.03      ( k1_relat_1(k1_relat_1(k1_relat_1(k1_xboole_0))) = k1_xboole_0 ),
% 1.37/1.03      inference(superposition,[status(thm)],[c_4021,c_7927]) ).
% 1.37/1.03  
% 1.37/1.03  cnf(c_13566,plain,
% 1.37/1.03      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 1.37/1.03      inference(demodulation,[status(thm)],[c_13543,c_13549]) ).
% 1.37/1.03  
% 1.37/1.03  cnf(c_27,negated_conjecture,
% 1.37/1.03      ( m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12))) ),
% 1.37/1.03      inference(cnf_transformation,[],[f89]) ).
% 1.37/1.03  
% 1.37/1.03  cnf(c_1503,plain,
% 1.37/1.03      ( m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12))) = iProver_top ),
% 1.37/1.03      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 1.37/1.03  
% 1.37/1.03  cnf(c_22,plain,
% 1.37/1.03      ( v5_relat_1(X0,X1)
% 1.37/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 1.37/1.03      inference(cnf_transformation,[],[f84]) ).
% 1.37/1.03  
% 1.37/1.03  cnf(c_10,plain,
% 1.37/1.03      ( ~ v5_relat_1(X0,X1)
% 1.37/1.03      | r1_tarski(k2_relat_1(X0),X1)
% 1.37/1.03      | ~ v1_relat_1(X0) ),
% 1.37/1.03      inference(cnf_transformation,[],[f71]) ).
% 1.37/1.03  
% 1.37/1.03  cnf(c_354,plain,
% 1.37/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.37/1.03      | r1_tarski(k2_relat_1(X0),X2)
% 1.37/1.03      | ~ v1_relat_1(X0) ),
% 1.37/1.03      inference(resolution,[status(thm)],[c_22,c_10]) ).
% 1.37/1.03  
% 1.37/1.03  cnf(c_1500,plain,
% 1.37/1.03      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 1.37/1.03      | r1_tarski(k2_relat_1(X0),X2) = iProver_top
% 1.37/1.03      | v1_relat_1(X0) != iProver_top ),
% 1.37/1.03      inference(predicate_to_equality,[status(thm)],[c_354]) ).
% 1.37/1.03  
% 1.37/1.03  cnf(c_1930,plain,
% 1.37/1.03      ( r1_tarski(k2_relat_1(sK13),sK12) = iProver_top
% 1.37/1.03      | v1_relat_1(sK13) != iProver_top ),
% 1.37/1.03      inference(superposition,[status(thm)],[c_1503,c_1500]) ).
% 1.37/1.03  
% 1.37/1.03  cnf(c_3,plain,
% 1.37/1.03      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 1.37/1.03      inference(cnf_transformation,[],[f63]) ).
% 1.37/1.03  
% 1.37/1.03  cnf(c_1523,plain,
% 1.37/1.03      ( r1_tarski(X0,X1) != iProver_top
% 1.37/1.03      | r2_hidden(X2,X0) != iProver_top
% 1.37/1.03      | r2_hidden(X2,X1) = iProver_top ),
% 1.37/1.03      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 1.37/1.03  
% 1.37/1.03  cnf(c_4079,plain,
% 1.37/1.03      ( r2_hidden(X0,k2_relat_1(sK13)) != iProver_top
% 1.37/1.03      | r2_hidden(X0,sK12) = iProver_top
% 1.37/1.03      | v1_relat_1(sK13) != iProver_top ),
% 1.37/1.03      inference(superposition,[status(thm)],[c_1930,c_1523]) ).
% 1.37/1.03  
% 1.37/1.03  cnf(c_32,plain,
% 1.37/1.03      ( m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12))) = iProver_top ),
% 1.37/1.03      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 1.37/1.03  
% 1.37/1.03  cnf(c_8,plain,
% 1.37/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.37/1.03      | ~ v1_relat_1(X1)
% 1.37/1.03      | v1_relat_1(X0) ),
% 1.37/1.03      inference(cnf_transformation,[],[f70]) ).
% 1.37/1.03  
% 1.37/1.03  cnf(c_1704,plain,
% 1.37/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.37/1.03      | v1_relat_1(X0)
% 1.37/1.03      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 1.37/1.03      inference(instantiation,[status(thm)],[c_8]) ).
% 1.37/1.03  
% 1.37/1.03  cnf(c_1963,plain,
% 1.37/1.03      ( ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12)))
% 1.37/1.03      | ~ v1_relat_1(k2_zfmisc_1(sK11,sK12))
% 1.37/1.03      | v1_relat_1(sK13) ),
% 1.37/1.03      inference(instantiation,[status(thm)],[c_1704]) ).
% 1.37/1.03  
% 1.37/1.03  cnf(c_1964,plain,
% 1.37/1.03      ( m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12))) != iProver_top
% 1.37/1.03      | v1_relat_1(k2_zfmisc_1(sK11,sK12)) != iProver_top
% 1.37/1.03      | v1_relat_1(sK13) = iProver_top ),
% 1.37/1.03      inference(predicate_to_equality,[status(thm)],[c_1963]) ).
% 1.37/1.03  
% 1.37/1.03  cnf(c_19,plain,
% 1.37/1.03      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 1.37/1.03      inference(cnf_transformation,[],[f81]) ).
% 1.37/1.03  
% 1.37/1.03  cnf(c_2430,plain,
% 1.37/1.03      ( v1_relat_1(k2_zfmisc_1(sK11,sK12)) ),
% 1.37/1.03      inference(instantiation,[status(thm)],[c_19]) ).
% 1.37/1.03  
% 1.37/1.03  cnf(c_2431,plain,
% 1.37/1.03      ( v1_relat_1(k2_zfmisc_1(sK11,sK12)) = iProver_top ),
% 1.37/1.03      inference(predicate_to_equality,[status(thm)],[c_2430]) ).
% 1.37/1.03  
% 1.37/1.03  cnf(c_4183,plain,
% 1.37/1.03      ( r2_hidden(X0,sK12) = iProver_top
% 1.37/1.03      | r2_hidden(X0,k2_relat_1(sK13)) != iProver_top ),
% 1.37/1.03      inference(global_propositional_subsumption,
% 1.37/1.03                [status(thm)],
% 1.37/1.03                [c_4079,c_32,c_1964,c_2431]) ).
% 1.37/1.03  
% 1.37/1.03  cnf(c_4184,plain,
% 1.37/1.03      ( r2_hidden(X0,k2_relat_1(sK13)) != iProver_top
% 1.37/1.03      | r2_hidden(X0,sK12) = iProver_top ),
% 1.37/1.03      inference(renaming,[status(thm)],[c_4183]) ).
% 1.37/1.03  
% 1.37/1.03  cnf(c_4193,plain,
% 1.37/1.03      ( k2_relat_1(sK13) = X0
% 1.37/1.03      | r2_hidden(sK2(X0,k2_relat_1(sK13)),X0) = iProver_top
% 1.37/1.03      | r2_hidden(sK2(X0,k2_relat_1(sK13)),sK12) = iProver_top ),
% 1.37/1.03      inference(superposition,[status(thm)],[c_1521,c_4184]) ).
% 1.37/1.03  
% 1.37/1.03  cnf(c_5416,plain,
% 1.37/1.03      ( k2_relat_1(sK13) = k1_xboole_0
% 1.37/1.03      | r2_hidden(sK2(k1_xboole_0,k2_relat_1(sK13)),sK12) = iProver_top ),
% 1.37/1.03      inference(superposition,[status(thm)],[c_4193,c_1935]) ).
% 1.37/1.03  
% 1.37/1.03  cnf(c_7,plain,
% 1.37/1.03      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 1.37/1.03      inference(cnf_transformation,[],[f69]) ).
% 1.37/1.03  
% 1.37/1.03  cnf(c_1519,plain,
% 1.37/1.03      ( m1_subset_1(X0,X1) = iProver_top
% 1.37/1.03      | r2_hidden(X0,X1) != iProver_top ),
% 1.37/1.03      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 1.37/1.03  
% 1.37/1.03  cnf(c_6832,plain,
% 1.37/1.03      ( k2_relat_1(sK13) = k1_xboole_0
% 1.37/1.03      | m1_subset_1(sK2(k1_xboole_0,k2_relat_1(sK13)),sK12) = iProver_top ),
% 1.37/1.03      inference(superposition,[status(thm)],[c_5416,c_1519]) ).
% 1.37/1.03  
% 1.37/1.03  cnf(c_24,plain,
% 1.37/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.37/1.03      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 1.37/1.03      inference(cnf_transformation,[],[f86]) ).
% 1.37/1.03  
% 1.37/1.03  cnf(c_1505,plain,
% 1.37/1.03      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 1.37/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 1.37/1.03      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 1.37/1.03  
% 1.37/1.03  cnf(c_2996,plain,
% 1.37/1.03      ( k2_relset_1(sK11,sK12,sK13) = k2_relat_1(sK13) ),
% 1.37/1.03      inference(superposition,[status(thm)],[c_1503,c_1505]) ).
% 1.37/1.03  
% 1.37/1.03  cnf(c_25,negated_conjecture,
% 1.37/1.03      ( ~ m1_subset_1(X0,sK12)
% 1.37/1.03      | ~ r2_hidden(X0,k2_relset_1(sK11,sK12,sK13)) ),
% 1.37/1.03      inference(cnf_transformation,[],[f91]) ).
% 1.37/1.03  
% 1.37/1.03  cnf(c_1504,plain,
% 1.37/1.03      ( m1_subset_1(X0,sK12) != iProver_top
% 1.37/1.03      | r2_hidden(X0,k2_relset_1(sK11,sK12,sK13)) != iProver_top ),
% 1.37/1.03      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 1.37/1.03  
% 1.37/1.03  cnf(c_3370,plain,
% 1.37/1.03      ( m1_subset_1(X0,sK12) != iProver_top
% 1.37/1.03      | r2_hidden(X0,k2_relat_1(sK13)) != iProver_top ),
% 1.37/1.03      inference(demodulation,[status(thm)],[c_2996,c_1504]) ).
% 1.37/1.03  
% 1.37/1.03  cnf(c_4025,plain,
% 1.37/1.03      ( k2_relat_1(sK13) = X0
% 1.37/1.03      | m1_subset_1(sK2(X0,k2_relat_1(sK13)),sK12) != iProver_top
% 1.37/1.03      | r2_hidden(sK2(X0,k2_relat_1(sK13)),X0) = iProver_top ),
% 1.37/1.03      inference(superposition,[status(thm)],[c_1521,c_3370]) ).
% 1.37/1.03  
% 1.37/1.03  cnf(c_9665,plain,
% 1.37/1.03      ( k2_relat_1(sK13) = k1_xboole_0
% 1.37/1.03      | r2_hidden(sK2(k1_xboole_0,k2_relat_1(sK13)),k1_xboole_0) = iProver_top ),
% 1.37/1.03      inference(superposition,[status(thm)],[c_6832,c_4025]) ).
% 1.37/1.03  
% 1.37/1.03  cnf(c_10354,plain,
% 1.37/1.03      ( k2_relat_1(sK13) = k1_xboole_0 ),
% 1.37/1.03      inference(forward_subsumption_resolution,
% 1.37/1.03                [status(thm)],
% 1.37/1.03                [c_9665,c_1935]) ).
% 1.37/1.03  
% 1.37/1.03  cnf(c_20,plain,
% 1.37/1.03      ( r2_hidden(k4_tarski(sK9(X0),sK10(X0)),X0)
% 1.37/1.03      | ~ v1_relat_1(X0)
% 1.37/1.03      | k1_xboole_0 = X0 ),
% 1.37/1.03      inference(cnf_transformation,[],[f82]) ).
% 1.37/1.03  
% 1.37/1.03  cnf(c_1508,plain,
% 1.37/1.03      ( k1_xboole_0 = X0
% 1.37/1.03      | r2_hidden(k4_tarski(sK9(X0),sK10(X0)),X0) = iProver_top
% 1.37/1.03      | v1_relat_1(X0) != iProver_top ),
% 1.37/1.03      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 1.37/1.03  
% 1.37/1.03  cnf(c_17,plain,
% 1.37/1.03      ( r2_hidden(X0,k2_relat_1(X1)) | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
% 1.37/1.03      inference(cnf_transformation,[],[f94]) ).
% 1.37/1.03  
% 1.37/1.03  cnf(c_1511,plain,
% 1.37/1.03      ( r2_hidden(X0,k2_relat_1(X1)) = iProver_top
% 1.37/1.03      | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top ),
% 1.37/1.03      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 1.37/1.03  
% 1.37/1.03  cnf(c_3833,plain,
% 1.37/1.03      ( k1_xboole_0 = X0
% 1.37/1.03      | r2_hidden(sK10(X0),k2_relat_1(X0)) = iProver_top
% 1.37/1.03      | v1_relat_1(X0) != iProver_top ),
% 1.37/1.03      inference(superposition,[status(thm)],[c_1508,c_1511]) ).
% 1.37/1.03  
% 1.37/1.03  cnf(c_11647,plain,
% 1.37/1.03      ( sK13 = k1_xboole_0
% 1.37/1.03      | r2_hidden(sK10(sK13),k1_xboole_0) = iProver_top
% 1.37/1.03      | v1_relat_1(sK13) != iProver_top ),
% 1.37/1.03      inference(superposition,[status(thm)],[c_10354,c_3833]) ).
% 1.37/1.03  
% 1.37/1.03  cnf(c_12495,plain,
% 1.37/1.03      ( r2_hidden(sK10(sK13),k1_xboole_0) = iProver_top
% 1.37/1.03      | sK13 = k1_xboole_0 ),
% 1.37/1.03      inference(global_propositional_subsumption,
% 1.37/1.03                [status(thm)],
% 1.37/1.03                [c_11647,c_32,c_1964,c_2431]) ).
% 1.37/1.03  
% 1.37/1.03  cnf(c_12496,plain,
% 1.37/1.03      ( sK13 = k1_xboole_0
% 1.37/1.03      | r2_hidden(sK10(sK13),k1_xboole_0) = iProver_top ),
% 1.37/1.03      inference(renaming,[status(thm)],[c_12495]) ).
% 1.37/1.03  
% 1.37/1.03  cnf(c_12501,plain,
% 1.37/1.03      ( sK13 = k1_xboole_0 ),
% 1.37/1.03      inference(forward_subsumption_resolution,
% 1.37/1.03                [status(thm)],
% 1.37/1.03                [c_12496,c_1935]) ).
% 1.37/1.03  
% 1.37/1.03  cnf(c_23,plain,
% 1.37/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.37/1.03      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 1.37/1.03      inference(cnf_transformation,[],[f85]) ).
% 1.37/1.03  
% 1.37/1.03  cnf(c_1506,plain,
% 1.37/1.03      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 1.37/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 1.37/1.03      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 1.37/1.03  
% 1.37/1.03  cnf(c_3073,plain,
% 1.37/1.03      ( k1_relset_1(sK11,sK12,sK13) = k1_relat_1(sK13) ),
% 1.37/1.03      inference(superposition,[status(thm)],[c_1503,c_1506]) ).
% 1.37/1.03  
% 1.37/1.03  cnf(c_26,negated_conjecture,
% 1.37/1.03      ( k1_xboole_0 != k1_relset_1(sK11,sK12,sK13) ),
% 1.37/1.03      inference(cnf_transformation,[],[f90]) ).
% 1.37/1.03  
% 1.37/1.03  cnf(c_3384,plain,
% 1.37/1.03      ( k1_relat_1(sK13) != k1_xboole_0 ),
% 1.37/1.03      inference(demodulation,[status(thm)],[c_3073,c_26]) ).
% 1.37/1.03  
% 1.37/1.03  cnf(c_12505,plain,
% 1.37/1.03      ( k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
% 1.37/1.03      inference(demodulation,[status(thm)],[c_12501,c_3384]) ).
% 1.37/1.03  
% 1.37/1.03  cnf(contradiction,plain,
% 1.37/1.03      ( $false ),
% 1.37/1.03      inference(minisat,[status(thm)],[c_13566,c_12505]) ).
% 1.37/1.03  
% 1.37/1.03  
% 1.37/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 1.37/1.03  
% 1.37/1.03  ------                               Statistics
% 1.37/1.03  
% 1.37/1.03  ------ General
% 1.37/1.03  
% 1.37/1.03  abstr_ref_over_cycles:                  0
% 1.37/1.03  abstr_ref_under_cycles:                 0
% 1.37/1.03  gc_basic_clause_elim:                   0
% 1.37/1.03  forced_gc_time:                         0
% 1.37/1.03  parsing_time:                           0.009
% 1.37/1.03  unif_index_cands_time:                  0.
% 1.37/1.03  unif_index_add_time:                    0.
% 1.37/1.03  orderings_time:                         0.
% 1.37/1.03  out_proof_time:                         0.01
% 1.37/1.03  total_time:                             0.355
% 1.37/1.03  num_of_symbols:                         59
% 1.37/1.03  num_of_terms:                           13596
% 1.37/1.03  
% 1.37/1.03  ------ Preprocessing
% 1.37/1.03  
% 1.37/1.03  num_of_splits:                          0
% 1.37/1.03  num_of_split_atoms:                     0
% 1.37/1.03  num_of_reused_defs:                     0
% 1.37/1.03  num_eq_ax_congr_red:                    66
% 1.37/1.03  num_of_sem_filtered_clauses:            1
% 1.37/1.03  num_of_subtypes:                        0
% 1.37/1.03  monotx_restored_types:                  0
% 1.37/1.03  sat_num_of_epr_types:                   0
% 1.37/1.03  sat_num_of_non_cyclic_types:            0
% 1.37/1.03  sat_guarded_non_collapsed_types:        0
% 1.37/1.03  num_pure_diseq_elim:                    0
% 1.37/1.03  simp_replaced_by:                       0
% 1.37/1.03  res_preprocessed:                       136
% 1.37/1.03  prep_upred:                             0
% 1.37/1.03  prep_unflattend:                        48
% 1.37/1.03  smt_new_axioms:                         0
% 1.37/1.03  pred_elim_cands:                        4
% 1.37/1.03  pred_elim:                              2
% 1.37/1.03  pred_elim_cl:                           3
% 1.37/1.03  pred_elim_cycles:                       6
% 1.37/1.03  merged_defs:                            0
% 1.37/1.03  merged_defs_ncl:                        0
% 1.37/1.03  bin_hyper_res:                          0
% 1.37/1.03  prep_cycles:                            4
% 1.37/1.03  pred_elim_time:                         0.009
% 1.37/1.03  splitting_time:                         0.
% 1.37/1.03  sem_filter_time:                        0.
% 1.37/1.03  monotx_time:                            0.
% 1.37/1.03  subtype_inf_time:                       0.
% 1.37/1.03  
% 1.37/1.03  ------ Problem properties
% 1.37/1.03  
% 1.37/1.03  clauses:                                27
% 1.37/1.03  conjectures:                            3
% 1.37/1.03  epr:                                    4
% 1.37/1.03  horn:                                   22
% 1.37/1.03  ground:                                 4
% 1.37/1.03  unary:                                  6
% 1.37/1.03  binary:                                 11
% 1.37/1.03  lits:                                   58
% 1.37/1.03  lits_eq:                                10
% 1.37/1.03  fd_pure:                                0
% 1.37/1.03  fd_pseudo:                              0
% 1.37/1.03  fd_cond:                                1
% 1.37/1.03  fd_pseudo_cond:                         6
% 1.37/1.03  ac_symbols:                             0
% 1.37/1.03  
% 1.37/1.03  ------ Propositional Solver
% 1.37/1.03  
% 1.37/1.03  prop_solver_calls:                      28
% 1.37/1.03  prop_fast_solver_calls:                 1090
% 1.37/1.03  smt_solver_calls:                       0
% 1.37/1.03  smt_fast_solver_calls:                  0
% 1.37/1.03  prop_num_of_clauses:                    5506
% 1.37/1.03  prop_preprocess_simplified:             13588
% 1.37/1.03  prop_fo_subsumed:                       25
% 1.37/1.03  prop_solver_time:                       0.
% 1.37/1.03  smt_solver_time:                        0.
% 1.37/1.03  smt_fast_solver_time:                   0.
% 1.37/1.03  prop_fast_solver_time:                  0.
% 1.37/1.03  prop_unsat_core_time:                   0.
% 1.37/1.03  
% 1.37/1.03  ------ QBF
% 1.37/1.03  
% 1.37/1.03  qbf_q_res:                              0
% 1.37/1.03  qbf_num_tautologies:                    0
% 1.37/1.03  qbf_prep_cycles:                        0
% 1.37/1.03  
% 1.37/1.03  ------ BMC1
% 1.37/1.03  
% 1.37/1.03  bmc1_current_bound:                     -1
% 1.37/1.03  bmc1_last_solved_bound:                 -1
% 1.37/1.03  bmc1_unsat_core_size:                   -1
% 1.37/1.03  bmc1_unsat_core_parents_size:           -1
% 1.37/1.03  bmc1_merge_next_fun:                    0
% 1.37/1.03  bmc1_unsat_core_clauses_time:           0.
% 1.37/1.03  
% 1.37/1.03  ------ Instantiation
% 1.37/1.03  
% 1.37/1.03  inst_num_of_clauses:                    1440
% 1.37/1.03  inst_num_in_passive:                    901
% 1.37/1.03  inst_num_in_active:                     536
% 1.37/1.03  inst_num_in_unprocessed:                3
% 1.37/1.03  inst_num_of_loops:                      710
% 1.37/1.03  inst_num_of_learning_restarts:          0
% 1.37/1.03  inst_num_moves_active_passive:          173
% 1.37/1.03  inst_lit_activity:                      0
% 1.37/1.03  inst_lit_activity_moves:                0
% 1.37/1.03  inst_num_tautologies:                   0
% 1.37/1.03  inst_num_prop_implied:                  0
% 1.37/1.03  inst_num_existing_simplified:           0
% 1.37/1.03  inst_num_eq_res_simplified:             0
% 1.37/1.03  inst_num_child_elim:                    0
% 1.37/1.03  inst_num_of_dismatching_blockings:      373
% 1.37/1.03  inst_num_of_non_proper_insts:           1305
% 1.37/1.03  inst_num_of_duplicates:                 0
% 1.37/1.03  inst_inst_num_from_inst_to_res:         0
% 1.37/1.03  inst_dismatching_checking_time:         0.
% 1.37/1.03  
% 1.37/1.03  ------ Resolution
% 1.37/1.03  
% 1.37/1.03  res_num_of_clauses:                     0
% 1.37/1.03  res_num_in_passive:                     0
% 1.37/1.03  res_num_in_active:                      0
% 1.37/1.03  res_num_of_loops:                       140
% 1.37/1.03  res_forward_subset_subsumed:            93
% 1.37/1.03  res_backward_subset_subsumed:           4
% 1.37/1.03  res_forward_subsumed:                   0
% 1.37/1.03  res_backward_subsumed:                  0
% 1.37/1.03  res_forward_subsumption_resolution:     0
% 1.37/1.03  res_backward_subsumption_resolution:    0
% 1.37/1.03  res_clause_to_clause_subsumption:       868
% 1.37/1.03  res_orphan_elimination:                 0
% 1.37/1.03  res_tautology_del:                      49
% 1.37/1.03  res_num_eq_res_simplified:              0
% 1.37/1.03  res_num_sel_changes:                    0
% 1.37/1.03  res_moves_from_active_to_pass:          0
% 1.37/1.03  
% 1.37/1.03  ------ Superposition
% 1.37/1.03  
% 1.37/1.03  sup_time_total:                         0.
% 1.37/1.03  sup_time_generating:                    0.
% 1.37/1.03  sup_time_sim_full:                      0.
% 1.37/1.03  sup_time_sim_immed:                     0.
% 1.37/1.03  
% 1.37/1.03  sup_num_of_clauses:                     268
% 1.37/1.03  sup_num_in_active:                      73
% 1.37/1.03  sup_num_in_passive:                     195
% 1.37/1.03  sup_num_of_loops:                       140
% 1.37/1.03  sup_fw_superposition:                   209
% 1.37/1.03  sup_bw_superposition:                   218
% 1.37/1.03  sup_immediate_simplified:               36
% 1.37/1.03  sup_given_eliminated:                   0
% 1.37/1.03  comparisons_done:                       0
% 1.37/1.03  comparisons_avoided:                    0
% 1.37/1.03  
% 1.37/1.03  ------ Simplifications
% 1.37/1.03  
% 1.37/1.03  
% 1.37/1.03  sim_fw_subset_subsumed:                 26
% 1.37/1.03  sim_bw_subset_subsumed:                 31
% 1.37/1.03  sim_fw_subsumed:                        11
% 1.37/1.03  sim_bw_subsumed:                        1
% 1.37/1.03  sim_fw_subsumption_res:                 2
% 1.37/1.03  sim_bw_subsumption_res:                 0
% 1.37/1.03  sim_tautology_del:                      7
% 1.37/1.03  sim_eq_tautology_del:                   11
% 1.37/1.03  sim_eq_res_simp:                        2
% 1.37/1.03  sim_fw_demodulated:                     0
% 1.37/1.03  sim_bw_demodulated:                     59
% 1.37/1.03  sim_light_normalised:                   14
% 1.37/1.03  sim_joinable_taut:                      0
% 1.37/1.03  sim_joinable_simp:                      0
% 1.37/1.03  sim_ac_normalised:                      0
% 1.37/1.03  sim_smt_subsumption:                    0
% 1.37/1.03  
%------------------------------------------------------------------------------
