%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:55:05 EST 2020

% Result     : Theorem 31.76s
% Output     : CNFRefutation 31.76s
% Verified   : 
% Statistics : Number of formulae       :  169 ( 690 expanded)
%              Number of clauses        :  116 ( 217 expanded)
%              Number of leaves         :   19 ( 203 expanded)
%              Depth                    :   21
%              Number of atoms          :  509 (2919 expanded)
%              Number of equality atoms :  156 ( 705 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k2_relat_1(X1))
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,k2_relat_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,k2_relat_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,k2_relat_1(X1))
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
              & r2_hidden(X3,X1) )
      <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( ! [X3] :
              ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
                & r2_hidden(X3,X1) )
        <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
            | ~ r2_hidden(X3,X1) )
      <~> k2_relset_1(X0,X1,X2) = X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ? [X3] :
            ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
            & r2_hidden(X3,X1) ) )
      & ( k2_relset_1(X0,X1,X2) = X1
        | ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
            | ~ r2_hidden(X3,X1) ) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ? [X3] :
            ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
            & r2_hidden(X3,X1) ) )
      & ( k2_relset_1(X0,X1,X2) = X1
        | ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
            | ~ r2_hidden(X3,X1) ) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f28])).

fof(f30,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ? [X3] :
            ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
            & r2_hidden(X3,X1) ) )
      & ( k2_relset_1(X0,X1,X2) = X1
        | ! [X5] :
            ( ? [X6] : r2_hidden(k4_tarski(X6,X5),X2)
            | ~ r2_hidden(X5,X1) ) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(rectify,[],[f29])).

fof(f33,plain,(
    ! [X2,X5] :
      ( ? [X6] : r2_hidden(k4_tarski(X6,X5),X2)
     => r2_hidden(k4_tarski(sK8(X5),X5),X2) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
          & r2_hidden(X3,X1) )
     => ( ! [X4] : ~ r2_hidden(k4_tarski(X4,sK7),X2)
        & r2_hidden(sK7,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X0,X1,X2] :
        ( ( k2_relset_1(X0,X1,X2) != X1
          | ? [X3] :
              ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
              & r2_hidden(X3,X1) ) )
        & ( k2_relset_1(X0,X1,X2) = X1
          | ! [X5] :
              ( ? [X6] : r2_hidden(k4_tarski(X6,X5),X2)
              | ~ r2_hidden(X5,X1) ) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ( k2_relset_1(sK4,sK5,sK6) != sK5
        | ? [X3] :
            ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),sK6)
            & r2_hidden(X3,sK5) ) )
      & ( k2_relset_1(sK4,sK5,sK6) = sK5
        | ! [X5] :
            ( ? [X6] : r2_hidden(k4_tarski(X6,X5),sK6)
            | ~ r2_hidden(X5,sK5) ) )
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ( k2_relset_1(sK4,sK5,sK6) != sK5
      | ( ! [X4] : ~ r2_hidden(k4_tarski(X4,sK7),sK6)
        & r2_hidden(sK7,sK5) ) )
    & ( k2_relset_1(sK4,sK5,sK6) = sK5
      | ! [X5] :
          ( r2_hidden(k4_tarski(sK8(X5),X5),sK6)
          | ~ r2_hidden(X5,sK5) ) )
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f30,f33,f32,f31])).

fof(f48,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f34])).

fof(f49,plain,(
    ! [X5] :
      ( k2_relset_1(sK4,sK5,sK6) = sK5
      | r2_hidden(k4_tarski(sK8(X5),X5),sK6)
      | ~ r2_hidden(X5,sK5) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f26,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK3(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK2(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0)
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK1(X0,X1)),X0)
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0)
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0)
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK3(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f23,f26,f25,f24])).

fof(f41,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f52,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f17])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f51,plain,(
    ! [X4] :
      ( k2_relset_1(sK4,sK5,sK6) != sK5
      | ~ r2_hidden(k4_tarski(X4,sK7),sK6) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f50,plain,
    ( k2_relset_1(sK4,sK5,sK6) != sK5
    | r2_hidden(sK7,sK5) ),
    inference(cnf_transformation,[],[f34])).

fof(f40,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f53,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK3(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f35,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( k2_relat_1(X0) = X1
      | ~ r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0)
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0)
      | r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_3,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_117087,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_120747,plain,
    ( m1_subset_1(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_117087])).

cnf(c_153055,plain,
    ( m1_subset_1(k2_zfmisc_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | ~ r1_tarski(k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_120747])).

cnf(c_11,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_10,plain,
    ( ~ v5_relat_1(X0,X1)
    | r2_hidden(X2,X1)
    | ~ r2_hidden(X2,k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_260,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r2_hidden(X3,X2)
    | ~ r2_hidden(X3,k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_11,c_10])).

cnf(c_118554,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r2_hidden(sK1(X3,X4),X2)
    | ~ r2_hidden(sK1(X3,X4),k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_260])).

cnf(c_120743,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | r2_hidden(sK1(X4,X5),X3)
    | ~ r2_hidden(sK1(X4,X5),k2_relat_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_118554])).

cnf(c_125956,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | r2_hidden(sK1(sK6,sK5),X1)
    | ~ r2_hidden(sK1(sK6,sK5),k2_relat_1(k2_zfmisc_1(sK4,sK5)))
    | ~ v1_relat_1(k2_zfmisc_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_120743])).

cnf(c_153054,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | ~ r2_hidden(sK1(sK6,sK5),k2_relat_1(k2_zfmisc_1(sK4,sK5)))
    | r2_hidden(sK1(sK6,sK5),sK5)
    | ~ v1_relat_1(k2_zfmisc_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_125956])).

cnf(c_9,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_130353,plain,
    ( v1_relat_1(k2_zfmisc_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_792,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2748,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 != k2_relat_1(X0)
    | k2_relset_1(X1,X2,X0) = X3 ),
    inference(resolution,[status(thm)],[c_12,c_792])).

cnf(c_791,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2592,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_792,c_791])).

cnf(c_10658,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = k2_relset_1(X1,X2,X0)
    | X3 != k2_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_2748,c_2592])).

cnf(c_793,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_16186,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r2_hidden(X3,X4)
    | ~ r2_hidden(X5,k2_relset_1(X1,X2,X0))
    | X3 != X5
    | X4 != k2_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_10658,c_793])).

cnf(c_3493,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_793,c_791])).

cnf(c_6499,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r2_hidden(k2_relset_1(X1,X2,X0),X3)
    | ~ r2_hidden(k2_relat_1(X0),X3) ),
    inference(resolution,[status(thm)],[c_3493,c_12])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_16097,plain,
    ( r2_hidden(k2_relset_1(sK4,sK5,sK6),X0)
    | ~ r2_hidden(k2_relat_1(sK6),X0) ),
    inference(resolution,[status(thm)],[c_6499,c_16])).

cnf(c_83293,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r2_hidden(X3,X4)
    | ~ r2_hidden(k2_relat_1(sK6),k2_relset_1(X1,X2,X0))
    | X3 != k2_relset_1(sK4,sK5,sK6)
    | X4 != k2_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_16186,c_16097])).

cnf(c_88806,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r2_hidden(k2_relset_1(sK4,sK5,sK6),X3)
    | ~ r2_hidden(k2_relat_1(sK6),k2_relset_1(X1,X2,X0))
    | X3 != k2_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_83293,c_791])).

cnf(c_3477,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r2_hidden(X3,k2_relset_1(X1,X2,X0))
    | ~ r2_hidden(X4,k2_relat_1(X0))
    | X3 != X4 ),
    inference(resolution,[status(thm)],[c_793,c_12])).

cnf(c_10741,plain,
    ( r2_hidden(X0,k2_relset_1(sK4,sK5,sK6))
    | ~ r2_hidden(X1,k2_relat_1(sK6))
    | X0 != X1 ),
    inference(resolution,[status(thm)],[c_3477,c_16])).

cnf(c_11218,plain,
    ( r2_hidden(X0,k2_relset_1(sK4,sK5,sK6))
    | ~ r2_hidden(X0,k2_relat_1(sK6)) ),
    inference(resolution,[status(thm)],[c_10741,c_791])).

cnf(c_108763,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | r2_hidden(k2_relset_1(sK4,sK5,sK6),X0)
    | ~ r2_hidden(k2_relat_1(sK6),k2_relat_1(sK6))
    | X0 != k2_relat_1(sK6) ),
    inference(resolution,[status(thm)],[c_88806,c_11218])).

cnf(c_108784,plain,
    ( r2_hidden(k2_relset_1(sK4,sK5,sK6),X0)
    | ~ r2_hidden(k2_relat_1(sK6),k2_relat_1(sK6))
    | X0 != k2_relat_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_108763,c_16])).

cnf(c_795,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3527,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_795,c_791])).

cnf(c_15,negated_conjecture,
    ( ~ r2_hidden(X0,sK5)
    | r2_hidden(k4_tarski(sK8(X0),X0),sK6)
    | k2_relset_1(sK4,sK5,sK6) = sK5 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_6564,plain,
    ( m1_subset_1(k2_relset_1(sK4,sK5,sK6),X0)
    | ~ m1_subset_1(sK5,X0)
    | ~ r2_hidden(X1,sK5)
    | r2_hidden(k4_tarski(sK8(X1),X1),sK6) ),
    inference(resolution,[status(thm)],[c_3527,c_15])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_7099,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(X0))
    | ~ r2_hidden(X1,sK5)
    | r2_hidden(k4_tarski(sK8(X1),X1),sK6)
    | r1_tarski(k2_relset_1(sK4,sK5,sK6),X0) ),
    inference(resolution,[status(thm)],[c_6564,c_4])).

cnf(c_7,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1667,plain,
    ( r2_hidden(X0,k2_relat_1(sK6))
    | ~ r2_hidden(X0,sK5)
    | k2_relset_1(sK4,sK5,sK6) = sK5 ),
    inference(resolution,[status(thm)],[c_7,c_15])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1866,plain,
    ( ~ r2_hidden(sK0(X0,k2_relat_1(sK6)),sK5)
    | r1_tarski(X0,k2_relat_1(sK6))
    | k2_relset_1(sK4,sK5,sK6) = sK5 ),
    inference(resolution,[status(thm)],[c_1667,c_0])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_2141,plain,
    ( r1_tarski(sK5,k2_relat_1(sK6))
    | k2_relset_1(sK4,sK5,sK6) = sK5 ),
    inference(resolution,[status(thm)],[c_1866,c_1])).

cnf(c_13,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(X0,sK7),sK6)
    | k2_relset_1(sK4,sK5,sK6) != sK5 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2158,plain,
    ( ~ r2_hidden(k4_tarski(X0,sK7),sK6)
    | r1_tarski(sK5,k2_relat_1(sK6)) ),
    inference(resolution,[status(thm)],[c_2141,c_13])).

cnf(c_10154,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(X0))
    | ~ r2_hidden(sK7,sK5)
    | r1_tarski(k2_relset_1(sK4,sK5,sK6),X0)
    | r1_tarski(sK5,k2_relat_1(sK6)) ),
    inference(resolution,[status(thm)],[c_7099,c_2158])).

cnf(c_2018,plain,
    ( sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_791])).

cnf(c_14,negated_conjecture,
    ( r2_hidden(sK7,sK5)
    | k2_relset_1(sK4,sK5,sK6) != sK5 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2157,plain,
    ( r2_hidden(sK7,sK5)
    | r1_tarski(sK5,k2_relat_1(sK6)) ),
    inference(resolution,[status(thm)],[c_2141,c_14])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(k4_tarski(sK3(X1,X0),X0),X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2568,plain,
    ( ~ r2_hidden(sK7,k2_relat_1(sK6))
    | r1_tarski(sK5,k2_relat_1(sK6)) ),
    inference(resolution,[status(thm)],[c_8,c_2158])).

cnf(c_1234,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1222,plain,
    ( k2_relset_1(sK4,sK5,sK6) = sK5
    | r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(k4_tarski(sK8(X0),X0),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1228,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1728,plain,
    ( k2_relset_1(sK4,sK5,sK6) = sK5
    | r2_hidden(X0,k2_relat_1(sK6)) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1222,c_1228])).

cnf(c_1221,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1225,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1814,plain,
    ( k2_relset_1(sK4,sK5,sK6) = k2_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_1221,c_1225])).

cnf(c_2105,plain,
    ( k2_relat_1(sK6) = sK5
    | r2_hidden(X0,k2_relat_1(sK6)) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1728,c_1814])).

cnf(c_1235,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2112,plain,
    ( k2_relat_1(sK6) = sK5
    | r2_hidden(sK0(X0,k2_relat_1(sK6)),sK5) != iProver_top
    | r1_tarski(X0,k2_relat_1(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2105,c_1235])).

cnf(c_3628,plain,
    ( k2_relat_1(sK6) = sK5
    | r1_tarski(sK5,k2_relat_1(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1234,c_2112])).

cnf(c_3644,plain,
    ( r1_tarski(sK5,k2_relat_1(sK6))
    | k2_relat_1(sK6) = sK5 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3628])).

cnf(c_1799,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK7,sK5)
    | X0 != sK7
    | X1 != sK5 ),
    inference(instantiation,[status(thm)],[c_793])).

cnf(c_2017,plain,
    ( r2_hidden(sK7,X0)
    | ~ r2_hidden(sK7,sK5)
    | X0 != sK5
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_1799])).

cnf(c_7185,plain,
    ( r2_hidden(sK7,k2_relat_1(X0))
    | ~ r2_hidden(sK7,sK5)
    | k2_relat_1(X0) != sK5
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_2017])).

cnf(c_10182,plain,
    ( r2_hidden(sK7,k2_relat_1(sK6))
    | ~ r2_hidden(sK7,sK5)
    | k2_relat_1(sK6) != sK5
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_7185])).

cnf(c_10417,plain,
    ( r1_tarski(sK5,k2_relat_1(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10154,c_2018,c_2157,c_2568,c_3644,c_10182])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_10429,plain,
    ( r2_hidden(X0,k2_relat_1(sK6))
    | ~ r2_hidden(X0,sK5) ),
    inference(resolution,[status(thm)],[c_10417,c_2])).

cnf(c_16158,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r2_hidden(X3,k2_relset_1(sK4,sK5,sK6))
    | ~ r2_hidden(k2_relset_1(X1,X2,X0),k2_relat_1(sK6))
    | X3 != k2_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_10658,c_10741])).

cnf(c_29737,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r2_hidden(X3,k2_relset_1(sK4,sK5,sK6))
    | ~ r2_hidden(k2_relset_1(X1,X2,X0),sK5)
    | X3 != k2_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_10429,c_16158])).

cnf(c_72798,plain,
    ( r2_hidden(X0,k2_relset_1(sK4,sK5,sK6))
    | ~ r2_hidden(k2_relset_1(sK4,sK5,sK6),sK5)
    | X0 != k2_relat_1(sK6) ),
    inference(resolution,[status(thm)],[c_29737,c_16])).

cnf(c_109128,plain,
    ( r2_hidden(X0,k2_relset_1(sK4,sK5,sK6))
    | ~ r2_hidden(k2_relat_1(sK6),k2_relat_1(sK6))
    | X0 != k2_relat_1(sK6)
    | sK5 != k2_relat_1(sK6) ),
    inference(resolution,[status(thm)],[c_108784,c_72798])).

cnf(c_10651,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | r2_hidden(sK7,sK5)
    | sK5 != k2_relat_1(sK6) ),
    inference(resolution,[status(thm)],[c_2748,c_14])).

cnf(c_11022,plain,
    ( r2_hidden(sK7,sK5)
    | sK5 != k2_relat_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10651,c_16])).

cnf(c_1583,plain,
    ( X0 != X1
    | k2_relat_1(sK6) != X1
    | k2_relat_1(sK6) = X0 ),
    inference(instantiation,[status(thm)],[c_792])).

cnf(c_5100,plain,
    ( X0 != k2_relat_1(X1)
    | k2_relat_1(sK6) = X0
    | k2_relat_1(sK6) != k2_relat_1(X1) ),
    inference(instantiation,[status(thm)],[c_1583])).

cnf(c_12934,plain,
    ( k2_relat_1(sK6) != k2_relat_1(sK6)
    | k2_relat_1(sK6) = sK5
    | sK5 != k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_5100])).

cnf(c_2815,plain,
    ( r2_hidden(k4_tarski(sK3(X0,sK7),sK7),X0)
    | ~ r2_hidden(sK7,k2_relat_1(X0)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_21278,plain,
    ( r2_hidden(k4_tarski(sK3(sK6,sK7),sK7),sK6)
    | ~ r2_hidden(sK7,k2_relat_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_2815])).

cnf(c_21279,plain,
    ( ~ r2_hidden(k4_tarski(sK3(sK6,sK7),sK7),sK6)
    | k2_relset_1(sK4,sK5,sK6) != sK5 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2649,plain,
    ( k2_relat_1(X0) = k2_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_791])).

cnf(c_22770,plain,
    ( k2_relat_1(sK6) = k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_2649])).

cnf(c_5,plain,
    ( ~ r2_hidden(k4_tarski(X0,sK1(X1,X2)),X1)
    | ~ r2_hidden(sK1(X1,X2),X2)
    | k2_relat_1(X1) = X2 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_3670,plain,
    ( ~ r2_hidden(sK1(sK6,X0),X0)
    | ~ r2_hidden(sK1(sK6,X0),sK5)
    | k2_relset_1(sK4,sK5,sK6) = sK5
    | k2_relat_1(sK6) = X0 ),
    inference(resolution,[status(thm)],[c_5,c_15])).

cnf(c_11798,plain,
    ( ~ r2_hidden(sK1(sK6,k2_relset_1(sK4,sK5,sK6)),k2_relat_1(sK6))
    | ~ r2_hidden(sK1(sK6,k2_relset_1(sK4,sK5,sK6)),sK5)
    | k2_relset_1(sK4,sK5,sK6) = sK5
    | k2_relat_1(sK6) = k2_relset_1(sK4,sK5,sK6) ),
    inference(resolution,[status(thm)],[c_11218,c_3670])).

cnf(c_1389,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | k2_relset_1(sK4,sK5,sK6) = k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_12933,plain,
    ( k2_relset_1(sK4,sK5,sK6) != k2_relat_1(sK6)
    | k2_relat_1(sK6) = k2_relset_1(sK4,sK5,sK6)
    | k2_relat_1(sK6) != k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_5100])).

cnf(c_26519,plain,
    ( k2_relat_1(sK6) = k2_relset_1(sK4,sK5,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11798,c_16,c_1389,c_12933,c_22770])).

cnf(c_26896,plain,
    ( k2_relset_1(sK4,sK5,sK6) = k2_relat_1(sK6) ),
    inference(resolution,[status(thm)],[c_26519,c_2592])).

cnf(c_30048,plain,
    ( X0 != k2_relat_1(sK6)
    | k2_relset_1(sK4,sK5,sK6) = X0 ),
    inference(resolution,[status(thm)],[c_26896,c_792])).

cnf(c_30051,plain,
    ( k2_relset_1(sK4,sK5,sK6) = sK5
    | sK5 != k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_30048])).

cnf(c_110129,plain,
    ( sK5 != k2_relat_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_109128,c_2018,c_10182,c_11022,c_12934,c_21278,c_21279,c_22770,c_30051])).

cnf(c_5674,plain,
    ( ~ r2_hidden(sK0(X0,k2_zfmisc_1(X1,X2)),k2_zfmisc_1(X1,X2))
    | r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_6621,plain,
    ( ~ r2_hidden(sK0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1))
    | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_5674])).

cnf(c_103811,plain,
    ( ~ r2_hidden(sK0(k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(sK4,sK5)),k2_zfmisc_1(sK4,sK5))
    | r1_tarski(k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_6621])).

cnf(c_9586,plain,
    ( r2_hidden(sK0(k2_zfmisc_1(X0,X1),X2),k2_zfmisc_1(X0,X1))
    | r1_tarski(k2_zfmisc_1(X0,X1),X2) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_48472,plain,
    ( r2_hidden(sK0(k2_zfmisc_1(sK4,sK5),X0),k2_zfmisc_1(sK4,sK5))
    | r1_tarski(k2_zfmisc_1(sK4,sK5),X0) ),
    inference(instantiation,[status(thm)],[c_9586])).

cnf(c_103810,plain,
    ( r2_hidden(sK0(k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(sK4,sK5)),k2_zfmisc_1(sK4,sK5))
    | r1_tarski(k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_48472])).

cnf(c_6,plain,
    ( r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0)
    | r2_hidden(sK1(X0,X1),X1)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1575,plain,
    ( r1_tarski(sK6,k2_zfmisc_1(sK4,sK5)) ),
    inference(resolution,[status(thm)],[c_4,c_16])).

cnf(c_2556,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK4,sK5))
    | ~ r2_hidden(X0,sK6) ),
    inference(resolution,[status(thm)],[c_2,c_1575])).

cnf(c_2790,plain,
    ( r2_hidden(X0,k2_relat_1(k2_zfmisc_1(sK4,sK5)))
    | ~ r2_hidden(k4_tarski(X1,X0),sK6) ),
    inference(resolution,[status(thm)],[c_2556,c_7])).

cnf(c_4699,plain,
    ( r2_hidden(sK1(sK6,X0),X0)
    | r2_hidden(sK1(sK6,X0),k2_relat_1(k2_zfmisc_1(sK4,sK5)))
    | k2_relat_1(sK6) = X0 ),
    inference(resolution,[status(thm)],[c_6,c_2790])).

cnf(c_4701,plain,
    ( r2_hidden(sK1(sK6,sK5),k2_relat_1(k2_zfmisc_1(sK4,sK5)))
    | r2_hidden(sK1(sK6,sK5),sK5)
    | k2_relat_1(sK6) = sK5 ),
    inference(instantiation,[status(thm)],[c_4699])).

cnf(c_1825,plain,
    ( k2_relat_1(sK6) = sK5
    | r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(k4_tarski(sK8(X0),X0),sK6) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1814,c_1222])).

cnf(c_1230,plain,
    ( k2_relat_1(X0) = X1
    | r2_hidden(k4_tarski(X2,sK1(X0,X1)),X0) != iProver_top
    | r2_hidden(sK1(X0,X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2707,plain,
    ( k2_relat_1(sK6) = X0
    | k2_relat_1(sK6) = sK5
    | r2_hidden(sK1(sK6,X0),X0) != iProver_top
    | r2_hidden(sK1(sK6,X0),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1825,c_1230])).

cnf(c_2734,plain,
    ( ~ r2_hidden(sK1(sK6,X0),X0)
    | ~ r2_hidden(sK1(sK6,X0),sK5)
    | k2_relat_1(sK6) = X0
    | k2_relat_1(sK6) = sK5 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2707])).

cnf(c_2736,plain,
    ( ~ r2_hidden(sK1(sK6,sK5),sK5)
    | k2_relat_1(sK6) = sK5 ),
    inference(instantiation,[status(thm)],[c_2734])).

cnf(c_1520,plain,
    ( k2_relat_1(sK6) != X0
    | sK5 != X0
    | sK5 = k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_792])).

cnf(c_1521,plain,
    ( k2_relat_1(sK6) != sK5
    | sK5 = k2_relat_1(sK6)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_1520])).

cnf(c_808,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_791])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_153055,c_153054,c_130353,c_110129,c_103811,c_103810,c_4701,c_2736,c_1521,c_808])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:19:42 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 31.76/4.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 31.76/4.49  
% 31.76/4.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 31.76/4.49  
% 31.76/4.49  ------  iProver source info
% 31.76/4.49  
% 31.76/4.49  git: date: 2020-06-30 10:37:57 +0100
% 31.76/4.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 31.76/4.49  git: non_committed_changes: false
% 31.76/4.49  git: last_make_outside_of_git: false
% 31.76/4.49  
% 31.76/4.49  ------ 
% 31.76/4.49  ------ Parsing...
% 31.76/4.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 31.76/4.49  
% 31.76/4.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 31.76/4.49  
% 31.76/4.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 31.76/4.49  
% 31.76/4.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.76/4.49  ------ Proving...
% 31.76/4.49  ------ Problem Properties 
% 31.76/4.49  
% 31.76/4.49  
% 31.76/4.49  clauses                                 16
% 31.76/4.49  conjectures                             4
% 31.76/4.49  EPR                                     1
% 31.76/4.49  Horn                                    13
% 31.76/4.49  unary                                   2
% 31.76/4.49  binary                                  9
% 31.76/4.49  lits                                    36
% 31.76/4.49  lits eq                                 6
% 31.76/4.49  fd_pure                                 0
% 31.76/4.49  fd_pseudo                               0
% 31.76/4.49  fd_cond                                 0
% 31.76/4.49  fd_pseudo_cond                          2
% 31.76/4.49  AC symbols                              0
% 31.76/4.49  
% 31.76/4.49  ------ Input Options Time Limit: Unbounded
% 31.76/4.49  
% 31.76/4.49  
% 31.76/4.49  ------ 
% 31.76/4.49  Current options:
% 31.76/4.49  ------ 
% 31.76/4.49  
% 31.76/4.49  
% 31.76/4.49  
% 31.76/4.49  
% 31.76/4.49  ------ Proving...
% 31.76/4.49  
% 31.76/4.49  
% 31.76/4.49  % SZS status Theorem for theBenchmark.p
% 31.76/4.49  
% 31.76/4.49  % SZS output start CNFRefutation for theBenchmark.p
% 31.76/4.49  
% 31.76/4.49  fof(f2,axiom,(
% 31.76/4.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 31.76/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.76/4.49  
% 31.76/4.49  fof(f21,plain,(
% 31.76/4.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 31.76/4.49    inference(nnf_transformation,[],[f2])).
% 31.76/4.49  
% 31.76/4.49  fof(f39,plain,(
% 31.76/4.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 31.76/4.49    inference(cnf_transformation,[],[f21])).
% 31.76/4.49  
% 31.76/4.49  fof(f6,axiom,(
% 31.76/4.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 31.76/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.76/4.49  
% 31.76/4.49  fof(f10,plain,(
% 31.76/4.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 31.76/4.49    inference(pure_predicate_removal,[],[f6])).
% 31.76/4.49  
% 31.76/4.49  fof(f14,plain,(
% 31.76/4.49    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.76/4.49    inference(ennf_transformation,[],[f10])).
% 31.76/4.49  
% 31.76/4.49  fof(f46,plain,(
% 31.76/4.49    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 31.76/4.49    inference(cnf_transformation,[],[f14])).
% 31.76/4.49  
% 31.76/4.49  fof(f5,axiom,(
% 31.76/4.49    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k2_relat_1(X1)) => r2_hidden(X2,X0)))),
% 31.76/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.76/4.49  
% 31.76/4.49  fof(f12,plain,(
% 31.76/4.49    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,k2_relat_1(X1))) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 31.76/4.49    inference(ennf_transformation,[],[f5])).
% 31.76/4.49  
% 31.76/4.49  fof(f13,plain,(
% 31.76/4.49    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,k2_relat_1(X1))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 31.76/4.49    inference(flattening,[],[f12])).
% 31.76/4.49  
% 31.76/4.49  fof(f45,plain,(
% 31.76/4.49    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,k2_relat_1(X1)) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 31.76/4.49    inference(cnf_transformation,[],[f13])).
% 31.76/4.49  
% 31.76/4.49  fof(f4,axiom,(
% 31.76/4.49    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 31.76/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.76/4.49  
% 31.76/4.49  fof(f44,plain,(
% 31.76/4.49    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 31.76/4.49    inference(cnf_transformation,[],[f4])).
% 31.76/4.49  
% 31.76/4.49  fof(f7,axiom,(
% 31.76/4.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 31.76/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.76/4.49  
% 31.76/4.49  fof(f15,plain,(
% 31.76/4.49    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.76/4.49    inference(ennf_transformation,[],[f7])).
% 31.76/4.49  
% 31.76/4.49  fof(f47,plain,(
% 31.76/4.49    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 31.76/4.49    inference(cnf_transformation,[],[f15])).
% 31.76/4.49  
% 31.76/4.49  fof(f8,conjecture,(
% 31.76/4.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1))),
% 31.76/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.76/4.49  
% 31.76/4.49  fof(f9,negated_conjecture,(
% 31.76/4.49    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1))),
% 31.76/4.49    inference(negated_conjecture,[],[f8])).
% 31.76/4.49  
% 31.76/4.49  fof(f16,plain,(
% 31.76/4.49    ? [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) | ~r2_hidden(X3,X1)) <~> k2_relset_1(X0,X1,X2) = X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.76/4.49    inference(ennf_transformation,[],[f9])).
% 31.76/4.49  
% 31.76/4.49  fof(f28,plain,(
% 31.76/4.49    ? [X0,X1,X2] : (((k2_relset_1(X0,X1,X2) != X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1))) & (k2_relset_1(X0,X1,X2) = X1 | ! [X3] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) | ~r2_hidden(X3,X1)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.76/4.49    inference(nnf_transformation,[],[f16])).
% 31.76/4.49  
% 31.76/4.49  fof(f29,plain,(
% 31.76/4.49    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1))) & (k2_relset_1(X0,X1,X2) = X1 | ! [X3] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) | ~r2_hidden(X3,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.76/4.49    inference(flattening,[],[f28])).
% 31.76/4.49  
% 31.76/4.49  fof(f30,plain,(
% 31.76/4.49    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1))) & (k2_relset_1(X0,X1,X2) = X1 | ! [X5] : (? [X6] : r2_hidden(k4_tarski(X6,X5),X2) | ~r2_hidden(X5,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.76/4.49    inference(rectify,[],[f29])).
% 31.76/4.49  
% 31.76/4.49  fof(f33,plain,(
% 31.76/4.49    ( ! [X2] : (! [X5] : (? [X6] : r2_hidden(k4_tarski(X6,X5),X2) => r2_hidden(k4_tarski(sK8(X5),X5),X2))) )),
% 31.76/4.49    introduced(choice_axiom,[])).
% 31.76/4.49  
% 31.76/4.49  fof(f32,plain,(
% 31.76/4.49    ( ! [X2,X1] : (? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1)) => (! [X4] : ~r2_hidden(k4_tarski(X4,sK7),X2) & r2_hidden(sK7,X1))) )),
% 31.76/4.49    introduced(choice_axiom,[])).
% 31.76/4.49  
% 31.76/4.49  fof(f31,plain,(
% 31.76/4.49    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1))) & (k2_relset_1(X0,X1,X2) = X1 | ! [X5] : (? [X6] : r2_hidden(k4_tarski(X6,X5),X2) | ~r2_hidden(X5,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => ((k2_relset_1(sK4,sK5,sK6) != sK5 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X4,X3),sK6) & r2_hidden(X3,sK5))) & (k2_relset_1(sK4,sK5,sK6) = sK5 | ! [X5] : (? [X6] : r2_hidden(k4_tarski(X6,X5),sK6) | ~r2_hidden(X5,sK5))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))))),
% 31.76/4.49    introduced(choice_axiom,[])).
% 31.76/4.49  
% 31.76/4.49  fof(f34,plain,(
% 31.76/4.49    (k2_relset_1(sK4,sK5,sK6) != sK5 | (! [X4] : ~r2_hidden(k4_tarski(X4,sK7),sK6) & r2_hidden(sK7,sK5))) & (k2_relset_1(sK4,sK5,sK6) = sK5 | ! [X5] : (r2_hidden(k4_tarski(sK8(X5),X5),sK6) | ~r2_hidden(X5,sK5))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 31.76/4.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f30,f33,f32,f31])).
% 31.76/4.49  
% 31.76/4.49  fof(f48,plain,(
% 31.76/4.49    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 31.76/4.49    inference(cnf_transformation,[],[f34])).
% 31.76/4.49  
% 31.76/4.49  fof(f49,plain,(
% 31.76/4.49    ( ! [X5] : (k2_relset_1(sK4,sK5,sK6) = sK5 | r2_hidden(k4_tarski(sK8(X5),X5),sK6) | ~r2_hidden(X5,sK5)) )),
% 31.76/4.49    inference(cnf_transformation,[],[f34])).
% 31.76/4.49  
% 31.76/4.49  fof(f38,plain,(
% 31.76/4.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 31.76/4.49    inference(cnf_transformation,[],[f21])).
% 31.76/4.49  
% 31.76/4.49  fof(f3,axiom,(
% 31.76/4.49    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 31.76/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.76/4.49  
% 31.76/4.49  fof(f22,plain,(
% 31.76/4.49    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 31.76/4.49    inference(nnf_transformation,[],[f3])).
% 31.76/4.49  
% 31.76/4.49  fof(f23,plain,(
% 31.76/4.49    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 31.76/4.49    inference(rectify,[],[f22])).
% 31.76/4.49  
% 31.76/4.49  fof(f26,plain,(
% 31.76/4.49    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK3(X0,X5),X5),X0))),
% 31.76/4.49    introduced(choice_axiom,[])).
% 31.76/4.49  
% 31.76/4.49  fof(f25,plain,(
% 31.76/4.49    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) => r2_hidden(k4_tarski(sK2(X0,X1),X2),X0))) )),
% 31.76/4.49    introduced(choice_axiom,[])).
% 31.76/4.49  
% 31.76/4.49  fof(f24,plain,(
% 31.76/4.49    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK1(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 31.76/4.49    introduced(choice_axiom,[])).
% 31.76/4.49  
% 31.76/4.49  fof(f27,plain,(
% 31.76/4.49    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK3(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 31.76/4.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f23,f26,f25,f24])).
% 31.76/4.49  
% 31.76/4.49  fof(f41,plain,(
% 31.76/4.49    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 31.76/4.49    inference(cnf_transformation,[],[f27])).
% 31.76/4.49  
% 31.76/4.49  fof(f52,plain,(
% 31.76/4.49    ( ! [X6,X0,X5] : (r2_hidden(X5,k2_relat_1(X0)) | ~r2_hidden(k4_tarski(X6,X5),X0)) )),
% 31.76/4.49    inference(equality_resolution,[],[f41])).
% 31.76/4.49  
% 31.76/4.49  fof(f1,axiom,(
% 31.76/4.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 31.76/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.76/4.49  
% 31.76/4.49  fof(f11,plain,(
% 31.76/4.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 31.76/4.49    inference(ennf_transformation,[],[f1])).
% 31.76/4.49  
% 31.76/4.49  fof(f17,plain,(
% 31.76/4.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 31.76/4.49    inference(nnf_transformation,[],[f11])).
% 31.76/4.49  
% 31.76/4.49  fof(f18,plain,(
% 31.76/4.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 31.76/4.49    inference(rectify,[],[f17])).
% 31.76/4.49  
% 31.76/4.49  fof(f19,plain,(
% 31.76/4.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 31.76/4.49    introduced(choice_axiom,[])).
% 31.76/4.49  
% 31.76/4.49  fof(f20,plain,(
% 31.76/4.49    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 31.76/4.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).
% 31.76/4.49  
% 31.76/4.49  fof(f37,plain,(
% 31.76/4.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 31.76/4.49    inference(cnf_transformation,[],[f20])).
% 31.76/4.49  
% 31.76/4.49  fof(f36,plain,(
% 31.76/4.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 31.76/4.49    inference(cnf_transformation,[],[f20])).
% 31.76/4.49  
% 31.76/4.49  fof(f51,plain,(
% 31.76/4.49    ( ! [X4] : (k2_relset_1(sK4,sK5,sK6) != sK5 | ~r2_hidden(k4_tarski(X4,sK7),sK6)) )),
% 31.76/4.49    inference(cnf_transformation,[],[f34])).
% 31.76/4.49  
% 31.76/4.49  fof(f50,plain,(
% 31.76/4.49    k2_relset_1(sK4,sK5,sK6) != sK5 | r2_hidden(sK7,sK5)),
% 31.76/4.49    inference(cnf_transformation,[],[f34])).
% 31.76/4.49  
% 31.76/4.49  fof(f40,plain,(
% 31.76/4.49    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK3(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 31.76/4.49    inference(cnf_transformation,[],[f27])).
% 31.76/4.49  
% 31.76/4.49  fof(f53,plain,(
% 31.76/4.49    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK3(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 31.76/4.49    inference(equality_resolution,[],[f40])).
% 31.76/4.49  
% 31.76/4.49  fof(f35,plain,(
% 31.76/4.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 31.76/4.49    inference(cnf_transformation,[],[f20])).
% 31.76/4.49  
% 31.76/4.49  fof(f43,plain,(
% 31.76/4.49    ( ! [X0,X3,X1] : (k2_relat_1(X0) = X1 | ~r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0) | ~r2_hidden(sK1(X0,X1),X1)) )),
% 31.76/4.49    inference(cnf_transformation,[],[f27])).
% 31.76/4.49  
% 31.76/4.49  fof(f42,plain,(
% 31.76/4.49    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1)) )),
% 31.76/4.49    inference(cnf_transformation,[],[f27])).
% 31.76/4.49  
% 31.76/4.49  cnf(c_3,plain,
% 31.76/4.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 31.76/4.49      inference(cnf_transformation,[],[f39]) ).
% 31.76/4.49  
% 31.76/4.49  cnf(c_117087,plain,
% 31.76/4.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.76/4.49      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
% 31.76/4.49      inference(instantiation,[status(thm)],[c_3]) ).
% 31.76/4.49  
% 31.76/4.49  cnf(c_120747,plain,
% 31.76/4.49      ( m1_subset_1(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 31.76/4.49      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)) ),
% 31.76/4.49      inference(instantiation,[status(thm)],[c_117087]) ).
% 31.76/4.49  
% 31.76/4.49  cnf(c_153055,plain,
% 31.76/4.49      ( m1_subset_1(k2_zfmisc_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 31.76/4.49      | ~ r1_tarski(k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(sK4,sK5)) ),
% 31.76/4.49      inference(instantiation,[status(thm)],[c_120747]) ).
% 31.76/4.49  
% 31.76/4.49  cnf(c_11,plain,
% 31.76/4.49      ( v5_relat_1(X0,X1)
% 31.76/4.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 31.76/4.49      inference(cnf_transformation,[],[f46]) ).
% 31.76/4.49  
% 31.76/4.49  cnf(c_10,plain,
% 31.76/4.49      ( ~ v5_relat_1(X0,X1)
% 31.76/4.49      | r2_hidden(X2,X1)
% 31.76/4.49      | ~ r2_hidden(X2,k2_relat_1(X0))
% 31.76/4.49      | ~ v1_relat_1(X0) ),
% 31.76/4.49      inference(cnf_transformation,[],[f45]) ).
% 31.76/4.49  
% 31.76/4.49  cnf(c_260,plain,
% 31.76/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.76/4.49      | r2_hidden(X3,X2)
% 31.76/4.49      | ~ r2_hidden(X3,k2_relat_1(X0))
% 31.76/4.49      | ~ v1_relat_1(X0) ),
% 31.76/4.49      inference(resolution,[status(thm)],[c_11,c_10]) ).
% 31.76/4.49  
% 31.76/4.49  cnf(c_118554,plain,
% 31.76/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.76/4.49      | r2_hidden(sK1(X3,X4),X2)
% 31.76/4.49      | ~ r2_hidden(sK1(X3,X4),k2_relat_1(X0))
% 31.76/4.49      | ~ v1_relat_1(X0) ),
% 31.76/4.49      inference(instantiation,[status(thm)],[c_260]) ).
% 31.76/4.49  
% 31.76/4.49  cnf(c_120743,plain,
% 31.76/4.49      ( ~ m1_subset_1(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 31.76/4.49      | r2_hidden(sK1(X4,X5),X3)
% 31.76/4.49      | ~ r2_hidden(sK1(X4,X5),k2_relat_1(k2_zfmisc_1(X0,X1)))
% 31.76/4.49      | ~ v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 31.76/4.49      inference(instantiation,[status(thm)],[c_118554]) ).
% 31.76/4.49  
% 31.76/4.49  cnf(c_125956,plain,
% 31.76/4.49      ( ~ m1_subset_1(k2_zfmisc_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 31.76/4.49      | r2_hidden(sK1(sK6,sK5),X1)
% 31.76/4.49      | ~ r2_hidden(sK1(sK6,sK5),k2_relat_1(k2_zfmisc_1(sK4,sK5)))
% 31.76/4.49      | ~ v1_relat_1(k2_zfmisc_1(sK4,sK5)) ),
% 31.76/4.49      inference(instantiation,[status(thm)],[c_120743]) ).
% 31.76/4.49  
% 31.76/4.49  cnf(c_153054,plain,
% 31.76/4.49      ( ~ m1_subset_1(k2_zfmisc_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 31.76/4.49      | ~ r2_hidden(sK1(sK6,sK5),k2_relat_1(k2_zfmisc_1(sK4,sK5)))
% 31.76/4.49      | r2_hidden(sK1(sK6,sK5),sK5)
% 31.76/4.49      | ~ v1_relat_1(k2_zfmisc_1(sK4,sK5)) ),
% 31.76/4.49      inference(instantiation,[status(thm)],[c_125956]) ).
% 31.76/4.49  
% 31.76/4.49  cnf(c_9,plain,
% 31.76/4.49      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 31.76/4.49      inference(cnf_transformation,[],[f44]) ).
% 31.76/4.49  
% 31.76/4.49  cnf(c_130353,plain,
% 31.76/4.49      ( v1_relat_1(k2_zfmisc_1(sK4,sK5)) ),
% 31.76/4.49      inference(instantiation,[status(thm)],[c_9]) ).
% 31.76/4.49  
% 31.76/4.49  cnf(c_12,plain,
% 31.76/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.76/4.49      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 31.76/4.49      inference(cnf_transformation,[],[f47]) ).
% 31.76/4.49  
% 31.76/4.49  cnf(c_792,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 31.76/4.49  
% 31.76/4.49  cnf(c_2748,plain,
% 31.76/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.76/4.49      | X3 != k2_relat_1(X0)
% 31.76/4.49      | k2_relset_1(X1,X2,X0) = X3 ),
% 31.76/4.49      inference(resolution,[status(thm)],[c_12,c_792]) ).
% 31.76/4.49  
% 31.76/4.49  cnf(c_791,plain,( X0 = X0 ),theory(equality) ).
% 31.76/4.49  
% 31.76/4.49  cnf(c_2592,plain,
% 31.76/4.49      ( X0 != X1 | X1 = X0 ),
% 31.76/4.49      inference(resolution,[status(thm)],[c_792,c_791]) ).
% 31.76/4.49  
% 31.76/4.49  cnf(c_10658,plain,
% 31.76/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.76/4.49      | X3 = k2_relset_1(X1,X2,X0)
% 31.76/4.49      | X3 != k2_relat_1(X0) ),
% 31.76/4.49      inference(resolution,[status(thm)],[c_2748,c_2592]) ).
% 31.76/4.49  
% 31.76/4.49  cnf(c_793,plain,
% 31.76/4.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 31.76/4.49      theory(equality) ).
% 31.76/4.49  
% 31.76/4.49  cnf(c_16186,plain,
% 31.76/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.76/4.49      | r2_hidden(X3,X4)
% 31.76/4.49      | ~ r2_hidden(X5,k2_relset_1(X1,X2,X0))
% 31.76/4.49      | X3 != X5
% 31.76/4.49      | X4 != k2_relat_1(X0) ),
% 31.76/4.49      inference(resolution,[status(thm)],[c_10658,c_793]) ).
% 31.76/4.49  
% 31.76/4.49  cnf(c_3493,plain,
% 31.76/4.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X1) | X2 != X0 ),
% 31.76/4.49      inference(resolution,[status(thm)],[c_793,c_791]) ).
% 31.76/4.49  
% 31.76/4.49  cnf(c_6499,plain,
% 31.76/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.76/4.49      | r2_hidden(k2_relset_1(X1,X2,X0),X3)
% 31.76/4.49      | ~ r2_hidden(k2_relat_1(X0),X3) ),
% 31.76/4.49      inference(resolution,[status(thm)],[c_3493,c_12]) ).
% 31.76/4.49  
% 31.76/4.49  cnf(c_16,negated_conjecture,
% 31.76/4.49      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
% 31.76/4.49      inference(cnf_transformation,[],[f48]) ).
% 31.76/4.49  
% 31.76/4.49  cnf(c_16097,plain,
% 31.76/4.49      ( r2_hidden(k2_relset_1(sK4,sK5,sK6),X0)
% 31.76/4.49      | ~ r2_hidden(k2_relat_1(sK6),X0) ),
% 31.76/4.49      inference(resolution,[status(thm)],[c_6499,c_16]) ).
% 31.76/4.49  
% 31.76/4.49  cnf(c_83293,plain,
% 31.76/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.76/4.49      | r2_hidden(X3,X4)
% 31.76/4.49      | ~ r2_hidden(k2_relat_1(sK6),k2_relset_1(X1,X2,X0))
% 31.76/4.49      | X3 != k2_relset_1(sK4,sK5,sK6)
% 31.76/4.49      | X4 != k2_relat_1(X0) ),
% 31.76/4.49      inference(resolution,[status(thm)],[c_16186,c_16097]) ).
% 31.76/4.49  
% 31.76/4.49  cnf(c_88806,plain,
% 31.76/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.76/4.49      | r2_hidden(k2_relset_1(sK4,sK5,sK6),X3)
% 31.76/4.49      | ~ r2_hidden(k2_relat_1(sK6),k2_relset_1(X1,X2,X0))
% 31.76/4.49      | X3 != k2_relat_1(X0) ),
% 31.76/4.49      inference(resolution,[status(thm)],[c_83293,c_791]) ).
% 31.76/4.49  
% 31.76/4.49  cnf(c_3477,plain,
% 31.76/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.76/4.49      | r2_hidden(X3,k2_relset_1(X1,X2,X0))
% 31.76/4.49      | ~ r2_hidden(X4,k2_relat_1(X0))
% 31.76/4.49      | X3 != X4 ),
% 31.76/4.49      inference(resolution,[status(thm)],[c_793,c_12]) ).
% 31.76/4.49  
% 31.76/4.49  cnf(c_10741,plain,
% 31.76/4.49      ( r2_hidden(X0,k2_relset_1(sK4,sK5,sK6))
% 31.76/4.49      | ~ r2_hidden(X1,k2_relat_1(sK6))
% 31.76/4.49      | X0 != X1 ),
% 31.76/4.49      inference(resolution,[status(thm)],[c_3477,c_16]) ).
% 31.76/4.49  
% 31.76/4.49  cnf(c_11218,plain,
% 31.76/4.49      ( r2_hidden(X0,k2_relset_1(sK4,sK5,sK6))
% 31.76/4.49      | ~ r2_hidden(X0,k2_relat_1(sK6)) ),
% 31.76/4.49      inference(resolution,[status(thm)],[c_10741,c_791]) ).
% 31.76/4.49  
% 31.76/4.49  cnf(c_108763,plain,
% 31.76/4.49      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 31.76/4.49      | r2_hidden(k2_relset_1(sK4,sK5,sK6),X0)
% 31.76/4.49      | ~ r2_hidden(k2_relat_1(sK6),k2_relat_1(sK6))
% 31.76/4.49      | X0 != k2_relat_1(sK6) ),
% 31.76/4.49      inference(resolution,[status(thm)],[c_88806,c_11218]) ).
% 31.76/4.49  
% 31.76/4.49  cnf(c_108784,plain,
% 31.76/4.49      ( r2_hidden(k2_relset_1(sK4,sK5,sK6),X0)
% 31.76/4.49      | ~ r2_hidden(k2_relat_1(sK6),k2_relat_1(sK6))
% 31.76/4.49      | X0 != k2_relat_1(sK6) ),
% 31.76/4.49      inference(global_propositional_subsumption,
% 31.76/4.49                [status(thm)],
% 31.76/4.49                [c_108763,c_16]) ).
% 31.76/4.49  
% 31.76/4.49  cnf(c_795,plain,
% 31.76/4.49      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 31.76/4.49      theory(equality) ).
% 31.76/4.49  
% 31.76/4.49  cnf(c_3527,plain,
% 31.76/4.49      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X1) | X2 != X0 ),
% 31.76/4.49      inference(resolution,[status(thm)],[c_795,c_791]) ).
% 31.76/4.49  
% 31.76/4.49  cnf(c_15,negated_conjecture,
% 31.76/4.49      ( ~ r2_hidden(X0,sK5)
% 31.76/4.49      | r2_hidden(k4_tarski(sK8(X0),X0),sK6)
% 31.76/4.49      | k2_relset_1(sK4,sK5,sK6) = sK5 ),
% 31.76/4.49      inference(cnf_transformation,[],[f49]) ).
% 31.76/4.49  
% 31.76/4.49  cnf(c_6564,plain,
% 31.76/4.49      ( m1_subset_1(k2_relset_1(sK4,sK5,sK6),X0)
% 31.76/4.49      | ~ m1_subset_1(sK5,X0)
% 31.76/4.49      | ~ r2_hidden(X1,sK5)
% 31.76/4.49      | r2_hidden(k4_tarski(sK8(X1),X1),sK6) ),
% 31.76/4.49      inference(resolution,[status(thm)],[c_3527,c_15]) ).
% 31.76/4.49  
% 31.76/4.49  cnf(c_4,plain,
% 31.76/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 31.76/4.49      inference(cnf_transformation,[],[f38]) ).
% 31.76/4.49  
% 31.76/4.49  cnf(c_7099,plain,
% 31.76/4.49      ( ~ m1_subset_1(sK5,k1_zfmisc_1(X0))
% 31.76/4.49      | ~ r2_hidden(X1,sK5)
% 31.76/4.49      | r2_hidden(k4_tarski(sK8(X1),X1),sK6)
% 31.76/4.49      | r1_tarski(k2_relset_1(sK4,sK5,sK6),X0) ),
% 31.76/4.49      inference(resolution,[status(thm)],[c_6564,c_4]) ).
% 31.76/4.49  
% 31.76/4.49  cnf(c_7,plain,
% 31.76/4.49      ( r2_hidden(X0,k2_relat_1(X1)) | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
% 31.76/4.49      inference(cnf_transformation,[],[f52]) ).
% 31.76/4.49  
% 31.76/4.49  cnf(c_1667,plain,
% 31.76/4.49      ( r2_hidden(X0,k2_relat_1(sK6))
% 31.76/4.49      | ~ r2_hidden(X0,sK5)
% 31.76/4.49      | k2_relset_1(sK4,sK5,sK6) = sK5 ),
% 31.76/4.49      inference(resolution,[status(thm)],[c_7,c_15]) ).
% 31.76/4.49  
% 31.76/4.49  cnf(c_0,plain,
% 31.76/4.49      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 31.76/4.49      inference(cnf_transformation,[],[f37]) ).
% 31.76/4.49  
% 31.76/4.49  cnf(c_1866,plain,
% 31.76/4.49      ( ~ r2_hidden(sK0(X0,k2_relat_1(sK6)),sK5)
% 31.76/4.49      | r1_tarski(X0,k2_relat_1(sK6))
% 31.76/4.49      | k2_relset_1(sK4,sK5,sK6) = sK5 ),
% 31.76/4.49      inference(resolution,[status(thm)],[c_1667,c_0]) ).
% 31.76/4.49  
% 31.76/4.49  cnf(c_1,plain,
% 31.76/4.49      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 31.76/4.49      inference(cnf_transformation,[],[f36]) ).
% 31.76/4.49  
% 31.76/4.49  cnf(c_2141,plain,
% 31.76/4.49      ( r1_tarski(sK5,k2_relat_1(sK6)) | k2_relset_1(sK4,sK5,sK6) = sK5 ),
% 31.76/4.49      inference(resolution,[status(thm)],[c_1866,c_1]) ).
% 31.76/4.49  
% 31.76/4.49  cnf(c_13,negated_conjecture,
% 31.76/4.49      ( ~ r2_hidden(k4_tarski(X0,sK7),sK6)
% 31.76/4.49      | k2_relset_1(sK4,sK5,sK6) != sK5 ),
% 31.76/4.49      inference(cnf_transformation,[],[f51]) ).
% 31.76/4.49  
% 31.76/4.49  cnf(c_2158,plain,
% 31.76/4.49      ( ~ r2_hidden(k4_tarski(X0,sK7),sK6)
% 31.76/4.49      | r1_tarski(sK5,k2_relat_1(sK6)) ),
% 31.76/4.49      inference(resolution,[status(thm)],[c_2141,c_13]) ).
% 31.76/4.49  
% 31.76/4.49  cnf(c_10154,plain,
% 31.76/4.49      ( ~ m1_subset_1(sK5,k1_zfmisc_1(X0))
% 31.76/4.49      | ~ r2_hidden(sK7,sK5)
% 31.76/4.49      | r1_tarski(k2_relset_1(sK4,sK5,sK6),X0)
% 31.76/4.49      | r1_tarski(sK5,k2_relat_1(sK6)) ),
% 31.76/4.49      inference(resolution,[status(thm)],[c_7099,c_2158]) ).
% 31.76/4.49  
% 31.76/4.49  cnf(c_2018,plain,
% 31.76/4.49      ( sK7 = sK7 ),
% 31.76/4.49      inference(instantiation,[status(thm)],[c_791]) ).
% 31.76/4.49  
% 31.76/4.49  cnf(c_14,negated_conjecture,
% 31.76/4.49      ( r2_hidden(sK7,sK5) | k2_relset_1(sK4,sK5,sK6) != sK5 ),
% 31.76/4.49      inference(cnf_transformation,[],[f50]) ).
% 31.76/4.49  
% 31.76/4.49  cnf(c_2157,plain,
% 31.76/4.49      ( r2_hidden(sK7,sK5) | r1_tarski(sK5,k2_relat_1(sK6)) ),
% 31.76/4.49      inference(resolution,[status(thm)],[c_2141,c_14]) ).
% 31.76/4.49  
% 31.76/4.49  cnf(c_8,plain,
% 31.76/4.49      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 31.76/4.49      | r2_hidden(k4_tarski(sK3(X1,X0),X0),X1) ),
% 31.76/4.50      inference(cnf_transformation,[],[f53]) ).
% 31.76/4.50  
% 31.76/4.50  cnf(c_2568,plain,
% 31.76/4.50      ( ~ r2_hidden(sK7,k2_relat_1(sK6))
% 31.76/4.50      | r1_tarski(sK5,k2_relat_1(sK6)) ),
% 31.76/4.50      inference(resolution,[status(thm)],[c_8,c_2158]) ).
% 31.76/4.50  
% 31.76/4.50  cnf(c_1234,plain,
% 31.76/4.50      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 31.76/4.50      | r1_tarski(X0,X1) = iProver_top ),
% 31.76/4.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 31.76/4.50  
% 31.76/4.50  cnf(c_1222,plain,
% 31.76/4.50      ( k2_relset_1(sK4,sK5,sK6) = sK5
% 31.76/4.50      | r2_hidden(X0,sK5) != iProver_top
% 31.76/4.50      | r2_hidden(k4_tarski(sK8(X0),X0),sK6) = iProver_top ),
% 31.76/4.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 31.76/4.50  
% 31.76/4.50  cnf(c_1228,plain,
% 31.76/4.50      ( r2_hidden(X0,k2_relat_1(X1)) = iProver_top
% 31.76/4.50      | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top ),
% 31.76/4.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 31.76/4.50  
% 31.76/4.50  cnf(c_1728,plain,
% 31.76/4.50      ( k2_relset_1(sK4,sK5,sK6) = sK5
% 31.76/4.50      | r2_hidden(X0,k2_relat_1(sK6)) = iProver_top
% 31.76/4.50      | r2_hidden(X0,sK5) != iProver_top ),
% 31.76/4.50      inference(superposition,[status(thm)],[c_1222,c_1228]) ).
% 31.76/4.50  
% 31.76/4.50  cnf(c_1221,plain,
% 31.76/4.50      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 31.76/4.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 31.76/4.50  
% 31.76/4.50  cnf(c_1225,plain,
% 31.76/4.50      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 31.76/4.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 31.76/4.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 31.76/4.50  
% 31.76/4.50  cnf(c_1814,plain,
% 31.76/4.50      ( k2_relset_1(sK4,sK5,sK6) = k2_relat_1(sK6) ),
% 31.76/4.50      inference(superposition,[status(thm)],[c_1221,c_1225]) ).
% 31.76/4.50  
% 31.76/4.50  cnf(c_2105,plain,
% 31.76/4.50      ( k2_relat_1(sK6) = sK5
% 31.76/4.50      | r2_hidden(X0,k2_relat_1(sK6)) = iProver_top
% 31.76/4.50      | r2_hidden(X0,sK5) != iProver_top ),
% 31.76/4.50      inference(demodulation,[status(thm)],[c_1728,c_1814]) ).
% 31.76/4.50  
% 31.76/4.50  cnf(c_1235,plain,
% 31.76/4.50      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 31.76/4.50      | r1_tarski(X0,X1) = iProver_top ),
% 31.76/4.50      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 31.76/4.50  
% 31.76/4.50  cnf(c_2112,plain,
% 31.76/4.50      ( k2_relat_1(sK6) = sK5
% 31.76/4.50      | r2_hidden(sK0(X0,k2_relat_1(sK6)),sK5) != iProver_top
% 31.76/4.50      | r1_tarski(X0,k2_relat_1(sK6)) = iProver_top ),
% 31.76/4.50      inference(superposition,[status(thm)],[c_2105,c_1235]) ).
% 31.76/4.50  
% 31.76/4.50  cnf(c_3628,plain,
% 31.76/4.50      ( k2_relat_1(sK6) = sK5
% 31.76/4.50      | r1_tarski(sK5,k2_relat_1(sK6)) = iProver_top ),
% 31.76/4.50      inference(superposition,[status(thm)],[c_1234,c_2112]) ).
% 31.76/4.50  
% 31.76/4.50  cnf(c_3644,plain,
% 31.76/4.50      ( r1_tarski(sK5,k2_relat_1(sK6)) | k2_relat_1(sK6) = sK5 ),
% 31.76/4.50      inference(predicate_to_equality_rev,[status(thm)],[c_3628]) ).
% 31.76/4.50  
% 31.76/4.50  cnf(c_1799,plain,
% 31.76/4.50      ( r2_hidden(X0,X1) | ~ r2_hidden(sK7,sK5) | X0 != sK7 | X1 != sK5 ),
% 31.76/4.50      inference(instantiation,[status(thm)],[c_793]) ).
% 31.76/4.50  
% 31.76/4.50  cnf(c_2017,plain,
% 31.76/4.50      ( r2_hidden(sK7,X0)
% 31.76/4.50      | ~ r2_hidden(sK7,sK5)
% 31.76/4.50      | X0 != sK5
% 31.76/4.50      | sK7 != sK7 ),
% 31.76/4.50      inference(instantiation,[status(thm)],[c_1799]) ).
% 31.76/4.50  
% 31.76/4.50  cnf(c_7185,plain,
% 31.76/4.50      ( r2_hidden(sK7,k2_relat_1(X0))
% 31.76/4.50      | ~ r2_hidden(sK7,sK5)
% 31.76/4.50      | k2_relat_1(X0) != sK5
% 31.76/4.50      | sK7 != sK7 ),
% 31.76/4.50      inference(instantiation,[status(thm)],[c_2017]) ).
% 31.76/4.50  
% 31.76/4.50  cnf(c_10182,plain,
% 31.76/4.50      ( r2_hidden(sK7,k2_relat_1(sK6))
% 31.76/4.50      | ~ r2_hidden(sK7,sK5)
% 31.76/4.50      | k2_relat_1(sK6) != sK5
% 31.76/4.50      | sK7 != sK7 ),
% 31.76/4.50      inference(instantiation,[status(thm)],[c_7185]) ).
% 31.76/4.50  
% 31.76/4.50  cnf(c_10417,plain,
% 31.76/4.50      ( r1_tarski(sK5,k2_relat_1(sK6)) ),
% 31.76/4.50      inference(global_propositional_subsumption,
% 31.76/4.50                [status(thm)],
% 31.76/4.50                [c_10154,c_2018,c_2157,c_2568,c_3644,c_10182]) ).
% 31.76/4.50  
% 31.76/4.50  cnf(c_2,plain,
% 31.76/4.50      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 31.76/4.50      inference(cnf_transformation,[],[f35]) ).
% 31.76/4.50  
% 31.76/4.50  cnf(c_10429,plain,
% 31.76/4.50      ( r2_hidden(X0,k2_relat_1(sK6)) | ~ r2_hidden(X0,sK5) ),
% 31.76/4.50      inference(resolution,[status(thm)],[c_10417,c_2]) ).
% 31.76/4.50  
% 31.76/4.50  cnf(c_16158,plain,
% 31.76/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.76/4.50      | r2_hidden(X3,k2_relset_1(sK4,sK5,sK6))
% 31.76/4.50      | ~ r2_hidden(k2_relset_1(X1,X2,X0),k2_relat_1(sK6))
% 31.76/4.50      | X3 != k2_relat_1(X0) ),
% 31.76/4.50      inference(resolution,[status(thm)],[c_10658,c_10741]) ).
% 31.76/4.50  
% 31.76/4.50  cnf(c_29737,plain,
% 31.76/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.76/4.50      | r2_hidden(X3,k2_relset_1(sK4,sK5,sK6))
% 31.76/4.50      | ~ r2_hidden(k2_relset_1(X1,X2,X0),sK5)
% 31.76/4.50      | X3 != k2_relat_1(X0) ),
% 31.76/4.50      inference(resolution,[status(thm)],[c_10429,c_16158]) ).
% 31.76/4.50  
% 31.76/4.50  cnf(c_72798,plain,
% 31.76/4.50      ( r2_hidden(X0,k2_relset_1(sK4,sK5,sK6))
% 31.76/4.50      | ~ r2_hidden(k2_relset_1(sK4,sK5,sK6),sK5)
% 31.76/4.50      | X0 != k2_relat_1(sK6) ),
% 31.76/4.50      inference(resolution,[status(thm)],[c_29737,c_16]) ).
% 31.76/4.50  
% 31.76/4.50  cnf(c_109128,plain,
% 31.76/4.50      ( r2_hidden(X0,k2_relset_1(sK4,sK5,sK6))
% 31.76/4.50      | ~ r2_hidden(k2_relat_1(sK6),k2_relat_1(sK6))
% 31.76/4.50      | X0 != k2_relat_1(sK6)
% 31.76/4.50      | sK5 != k2_relat_1(sK6) ),
% 31.76/4.50      inference(resolution,[status(thm)],[c_108784,c_72798]) ).
% 31.76/4.50  
% 31.76/4.50  cnf(c_10651,plain,
% 31.76/4.50      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 31.76/4.50      | r2_hidden(sK7,sK5)
% 31.76/4.50      | sK5 != k2_relat_1(sK6) ),
% 31.76/4.50      inference(resolution,[status(thm)],[c_2748,c_14]) ).
% 31.76/4.50  
% 31.76/4.50  cnf(c_11022,plain,
% 31.76/4.50      ( r2_hidden(sK7,sK5) | sK5 != k2_relat_1(sK6) ),
% 31.76/4.50      inference(global_propositional_subsumption,
% 31.76/4.50                [status(thm)],
% 31.76/4.50                [c_10651,c_16]) ).
% 31.76/4.50  
% 31.76/4.50  cnf(c_1583,plain,
% 31.76/4.50      ( X0 != X1 | k2_relat_1(sK6) != X1 | k2_relat_1(sK6) = X0 ),
% 31.76/4.50      inference(instantiation,[status(thm)],[c_792]) ).
% 31.76/4.50  
% 31.76/4.50  cnf(c_5100,plain,
% 31.76/4.50      ( X0 != k2_relat_1(X1)
% 31.76/4.50      | k2_relat_1(sK6) = X0
% 31.76/4.50      | k2_relat_1(sK6) != k2_relat_1(X1) ),
% 31.76/4.50      inference(instantiation,[status(thm)],[c_1583]) ).
% 31.76/4.50  
% 31.76/4.50  cnf(c_12934,plain,
% 31.76/4.50      ( k2_relat_1(sK6) != k2_relat_1(sK6)
% 31.76/4.50      | k2_relat_1(sK6) = sK5
% 31.76/4.50      | sK5 != k2_relat_1(sK6) ),
% 31.76/4.50      inference(instantiation,[status(thm)],[c_5100]) ).
% 31.76/4.50  
% 31.76/4.50  cnf(c_2815,plain,
% 31.76/4.50      ( r2_hidden(k4_tarski(sK3(X0,sK7),sK7),X0)
% 31.76/4.50      | ~ r2_hidden(sK7,k2_relat_1(X0)) ),
% 31.76/4.50      inference(instantiation,[status(thm)],[c_8]) ).
% 31.76/4.50  
% 31.76/4.50  cnf(c_21278,plain,
% 31.76/4.50      ( r2_hidden(k4_tarski(sK3(sK6,sK7),sK7),sK6)
% 31.76/4.50      | ~ r2_hidden(sK7,k2_relat_1(sK6)) ),
% 31.76/4.50      inference(instantiation,[status(thm)],[c_2815]) ).
% 31.76/4.50  
% 31.76/4.50  cnf(c_21279,plain,
% 31.76/4.50      ( ~ r2_hidden(k4_tarski(sK3(sK6,sK7),sK7),sK6)
% 31.76/4.50      | k2_relset_1(sK4,sK5,sK6) != sK5 ),
% 31.76/4.50      inference(instantiation,[status(thm)],[c_13]) ).
% 31.76/4.50  
% 31.76/4.50  cnf(c_2649,plain,
% 31.76/4.50      ( k2_relat_1(X0) = k2_relat_1(X0) ),
% 31.76/4.50      inference(instantiation,[status(thm)],[c_791]) ).
% 31.76/4.50  
% 31.76/4.50  cnf(c_22770,plain,
% 31.76/4.50      ( k2_relat_1(sK6) = k2_relat_1(sK6) ),
% 31.76/4.50      inference(instantiation,[status(thm)],[c_2649]) ).
% 31.76/4.50  
% 31.76/4.50  cnf(c_5,plain,
% 31.76/4.50      ( ~ r2_hidden(k4_tarski(X0,sK1(X1,X2)),X1)
% 31.76/4.50      | ~ r2_hidden(sK1(X1,X2),X2)
% 31.76/4.50      | k2_relat_1(X1) = X2 ),
% 31.76/4.50      inference(cnf_transformation,[],[f43]) ).
% 31.76/4.50  
% 31.76/4.50  cnf(c_3670,plain,
% 31.76/4.50      ( ~ r2_hidden(sK1(sK6,X0),X0)
% 31.76/4.50      | ~ r2_hidden(sK1(sK6,X0),sK5)
% 31.76/4.50      | k2_relset_1(sK4,sK5,sK6) = sK5
% 31.76/4.50      | k2_relat_1(sK6) = X0 ),
% 31.76/4.50      inference(resolution,[status(thm)],[c_5,c_15]) ).
% 31.76/4.50  
% 31.76/4.50  cnf(c_11798,plain,
% 31.76/4.50      ( ~ r2_hidden(sK1(sK6,k2_relset_1(sK4,sK5,sK6)),k2_relat_1(sK6))
% 31.76/4.50      | ~ r2_hidden(sK1(sK6,k2_relset_1(sK4,sK5,sK6)),sK5)
% 31.76/4.50      | k2_relset_1(sK4,sK5,sK6) = sK5
% 31.76/4.50      | k2_relat_1(sK6) = k2_relset_1(sK4,sK5,sK6) ),
% 31.76/4.50      inference(resolution,[status(thm)],[c_11218,c_3670]) ).
% 31.76/4.50  
% 31.76/4.50  cnf(c_1389,plain,
% 31.76/4.50      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 31.76/4.50      | k2_relset_1(sK4,sK5,sK6) = k2_relat_1(sK6) ),
% 31.76/4.50      inference(instantiation,[status(thm)],[c_12]) ).
% 31.76/4.50  
% 31.76/4.50  cnf(c_12933,plain,
% 31.76/4.50      ( k2_relset_1(sK4,sK5,sK6) != k2_relat_1(sK6)
% 31.76/4.50      | k2_relat_1(sK6) = k2_relset_1(sK4,sK5,sK6)
% 31.76/4.50      | k2_relat_1(sK6) != k2_relat_1(sK6) ),
% 31.76/4.50      inference(instantiation,[status(thm)],[c_5100]) ).
% 31.76/4.50  
% 31.76/4.50  cnf(c_26519,plain,
% 31.76/4.50      ( k2_relat_1(sK6) = k2_relset_1(sK4,sK5,sK6) ),
% 31.76/4.50      inference(global_propositional_subsumption,
% 31.76/4.50                [status(thm)],
% 31.76/4.50                [c_11798,c_16,c_1389,c_12933,c_22770]) ).
% 31.76/4.50  
% 31.76/4.50  cnf(c_26896,plain,
% 31.76/4.50      ( k2_relset_1(sK4,sK5,sK6) = k2_relat_1(sK6) ),
% 31.76/4.50      inference(resolution,[status(thm)],[c_26519,c_2592]) ).
% 31.76/4.50  
% 31.76/4.50  cnf(c_30048,plain,
% 31.76/4.50      ( X0 != k2_relat_1(sK6) | k2_relset_1(sK4,sK5,sK6) = X0 ),
% 31.76/4.50      inference(resolution,[status(thm)],[c_26896,c_792]) ).
% 31.76/4.50  
% 31.76/4.50  cnf(c_30051,plain,
% 31.76/4.50      ( k2_relset_1(sK4,sK5,sK6) = sK5 | sK5 != k2_relat_1(sK6) ),
% 31.76/4.50      inference(instantiation,[status(thm)],[c_30048]) ).
% 31.76/4.50  
% 31.76/4.50  cnf(c_110129,plain,
% 31.76/4.50      ( sK5 != k2_relat_1(sK6) ),
% 31.76/4.50      inference(global_propositional_subsumption,
% 31.76/4.50                [status(thm)],
% 31.76/4.50                [c_109128,c_2018,c_10182,c_11022,c_12934,c_21278,c_21279,
% 31.76/4.50                 c_22770,c_30051]) ).
% 31.76/4.50  
% 31.76/4.50  cnf(c_5674,plain,
% 31.76/4.50      ( ~ r2_hidden(sK0(X0,k2_zfmisc_1(X1,X2)),k2_zfmisc_1(X1,X2))
% 31.76/4.50      | r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
% 31.76/4.50      inference(instantiation,[status(thm)],[c_0]) ).
% 31.76/4.50  
% 31.76/4.50  cnf(c_6621,plain,
% 31.76/4.50      ( ~ r2_hidden(sK0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1))
% 31.76/4.50      | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)) ),
% 31.76/4.50      inference(instantiation,[status(thm)],[c_5674]) ).
% 31.76/4.50  
% 31.76/4.50  cnf(c_103811,plain,
% 31.76/4.50      ( ~ r2_hidden(sK0(k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(sK4,sK5)),k2_zfmisc_1(sK4,sK5))
% 31.76/4.50      | r1_tarski(k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(sK4,sK5)) ),
% 31.76/4.50      inference(instantiation,[status(thm)],[c_6621]) ).
% 31.76/4.50  
% 31.76/4.50  cnf(c_9586,plain,
% 31.76/4.50      ( r2_hidden(sK0(k2_zfmisc_1(X0,X1),X2),k2_zfmisc_1(X0,X1))
% 31.76/4.50      | r1_tarski(k2_zfmisc_1(X0,X1),X2) ),
% 31.76/4.50      inference(instantiation,[status(thm)],[c_1]) ).
% 31.76/4.50  
% 31.76/4.50  cnf(c_48472,plain,
% 31.76/4.50      ( r2_hidden(sK0(k2_zfmisc_1(sK4,sK5),X0),k2_zfmisc_1(sK4,sK5))
% 31.76/4.50      | r1_tarski(k2_zfmisc_1(sK4,sK5),X0) ),
% 31.76/4.50      inference(instantiation,[status(thm)],[c_9586]) ).
% 31.76/4.50  
% 31.76/4.50  cnf(c_103810,plain,
% 31.76/4.50      ( r2_hidden(sK0(k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(sK4,sK5)),k2_zfmisc_1(sK4,sK5))
% 31.76/4.50      | r1_tarski(k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(sK4,sK5)) ),
% 31.76/4.50      inference(instantiation,[status(thm)],[c_48472]) ).
% 31.76/4.50  
% 31.76/4.50  cnf(c_6,plain,
% 31.76/4.50      ( r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0)
% 31.76/4.50      | r2_hidden(sK1(X0,X1),X1)
% 31.76/4.50      | k2_relat_1(X0) = X1 ),
% 31.76/4.50      inference(cnf_transformation,[],[f42]) ).
% 31.76/4.50  
% 31.76/4.50  cnf(c_1575,plain,
% 31.76/4.50      ( r1_tarski(sK6,k2_zfmisc_1(sK4,sK5)) ),
% 31.76/4.50      inference(resolution,[status(thm)],[c_4,c_16]) ).
% 31.76/4.50  
% 31.76/4.50  cnf(c_2556,plain,
% 31.76/4.50      ( r2_hidden(X0,k2_zfmisc_1(sK4,sK5)) | ~ r2_hidden(X0,sK6) ),
% 31.76/4.50      inference(resolution,[status(thm)],[c_2,c_1575]) ).
% 31.76/4.50  
% 31.76/4.50  cnf(c_2790,plain,
% 31.76/4.50      ( r2_hidden(X0,k2_relat_1(k2_zfmisc_1(sK4,sK5)))
% 31.76/4.50      | ~ r2_hidden(k4_tarski(X1,X0),sK6) ),
% 31.76/4.50      inference(resolution,[status(thm)],[c_2556,c_7]) ).
% 31.76/4.50  
% 31.76/4.50  cnf(c_4699,plain,
% 31.76/4.50      ( r2_hidden(sK1(sK6,X0),X0)
% 31.76/4.50      | r2_hidden(sK1(sK6,X0),k2_relat_1(k2_zfmisc_1(sK4,sK5)))
% 31.76/4.50      | k2_relat_1(sK6) = X0 ),
% 31.76/4.50      inference(resolution,[status(thm)],[c_6,c_2790]) ).
% 31.76/4.50  
% 31.76/4.50  cnf(c_4701,plain,
% 31.76/4.50      ( r2_hidden(sK1(sK6,sK5),k2_relat_1(k2_zfmisc_1(sK4,sK5)))
% 31.76/4.50      | r2_hidden(sK1(sK6,sK5),sK5)
% 31.76/4.50      | k2_relat_1(sK6) = sK5 ),
% 31.76/4.50      inference(instantiation,[status(thm)],[c_4699]) ).
% 31.76/4.50  
% 31.76/4.50  cnf(c_1825,plain,
% 31.76/4.50      ( k2_relat_1(sK6) = sK5
% 31.76/4.50      | r2_hidden(X0,sK5) != iProver_top
% 31.76/4.50      | r2_hidden(k4_tarski(sK8(X0),X0),sK6) = iProver_top ),
% 31.76/4.50      inference(demodulation,[status(thm)],[c_1814,c_1222]) ).
% 31.76/4.50  
% 31.76/4.50  cnf(c_1230,plain,
% 31.76/4.50      ( k2_relat_1(X0) = X1
% 31.76/4.50      | r2_hidden(k4_tarski(X2,sK1(X0,X1)),X0) != iProver_top
% 31.76/4.50      | r2_hidden(sK1(X0,X1),X1) != iProver_top ),
% 31.76/4.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 31.76/4.50  
% 31.76/4.50  cnf(c_2707,plain,
% 31.76/4.50      ( k2_relat_1(sK6) = X0
% 31.76/4.50      | k2_relat_1(sK6) = sK5
% 31.76/4.50      | r2_hidden(sK1(sK6,X0),X0) != iProver_top
% 31.76/4.50      | r2_hidden(sK1(sK6,X0),sK5) != iProver_top ),
% 31.76/4.50      inference(superposition,[status(thm)],[c_1825,c_1230]) ).
% 31.76/4.50  
% 31.76/4.50  cnf(c_2734,plain,
% 31.76/4.50      ( ~ r2_hidden(sK1(sK6,X0),X0)
% 31.76/4.50      | ~ r2_hidden(sK1(sK6,X0),sK5)
% 31.76/4.50      | k2_relat_1(sK6) = X0
% 31.76/4.50      | k2_relat_1(sK6) = sK5 ),
% 31.76/4.50      inference(predicate_to_equality_rev,[status(thm)],[c_2707]) ).
% 31.76/4.50  
% 31.76/4.50  cnf(c_2736,plain,
% 31.76/4.50      ( ~ r2_hidden(sK1(sK6,sK5),sK5) | k2_relat_1(sK6) = sK5 ),
% 31.76/4.50      inference(instantiation,[status(thm)],[c_2734]) ).
% 31.76/4.50  
% 31.76/4.50  cnf(c_1520,plain,
% 31.76/4.50      ( k2_relat_1(sK6) != X0 | sK5 != X0 | sK5 = k2_relat_1(sK6) ),
% 31.76/4.50      inference(instantiation,[status(thm)],[c_792]) ).
% 31.76/4.50  
% 31.76/4.50  cnf(c_1521,plain,
% 31.76/4.50      ( k2_relat_1(sK6) != sK5 | sK5 = k2_relat_1(sK6) | sK5 != sK5 ),
% 31.76/4.50      inference(instantiation,[status(thm)],[c_1520]) ).
% 31.76/4.50  
% 31.76/4.50  cnf(c_808,plain,
% 31.76/4.50      ( sK5 = sK5 ),
% 31.76/4.50      inference(instantiation,[status(thm)],[c_791]) ).
% 31.76/4.50  
% 31.76/4.50  cnf(contradiction,plain,
% 31.76/4.50      ( $false ),
% 31.76/4.50      inference(minisat,
% 31.76/4.50                [status(thm)],
% 31.76/4.50                [c_153055,c_153054,c_130353,c_110129,c_103811,c_103810,
% 31.76/4.50                 c_4701,c_2736,c_1521,c_808]) ).
% 31.76/4.50  
% 31.76/4.50  
% 31.76/4.50  % SZS output end CNFRefutation for theBenchmark.p
% 31.76/4.50  
% 31.76/4.50  ------                               Statistics
% 31.76/4.50  
% 31.76/4.50  ------ Selected
% 31.76/4.50  
% 31.76/4.50  total_time:                             3.908
% 31.76/4.50  
%------------------------------------------------------------------------------
