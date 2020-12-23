%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:55:04 EST 2020

% Result     : Theorem 3.24s
% Output     : CNFRefutation 3.24s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 412 expanded)
%              Number of clauses        :   74 ( 125 expanded)
%              Number of leaves         :   17 ( 112 expanded)
%              Depth                    :   22
%              Number of atoms          :  381 (1738 expanded)
%              Number of equality atoms :  133 ( 441 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
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

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f25,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK3(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK2(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
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

fof(f26,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f22,f25,f24,f23])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0)
      | r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f40,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f50,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f16])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f18])).

fof(f34,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
              & r2_hidden(X3,X1) )
      <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( ! [X3] :
              ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
                & r2_hidden(X3,X1) )
        <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
            | ~ r2_hidden(X3,X1) )
      <~> k2_relset_1(X0,X1,X2) = X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f15])).

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
    inference(flattening,[],[f27])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f32,plain,(
    ! [X2,X5] :
      ( ? [X6] : r2_hidden(k4_tarski(X6,X5),X2)
     => r2_hidden(k4_tarski(sK8(X5),X5),X2) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
          & r2_hidden(X3,X1) )
     => ( ! [X4] : ~ r2_hidden(k4_tarski(X4,sK7),X2)
        & r2_hidden(sK7,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
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

fof(f33,plain,
    ( ( k2_relset_1(sK4,sK5,sK6) != sK5
      | ( ! [X4] : ~ r2_hidden(k4_tarski(X4,sK7),sK6)
        & r2_hidden(sK7,sK5) ) )
    & ( k2_relset_1(sK4,sK5,sK6) = sK5
      | ! [X5] :
          ( r2_hidden(k4_tarski(sK8(X5),X5),sK6)
          | ~ r2_hidden(X5,sK5) ) )
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f29,f32,f31,f30])).

fof(f46,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f49,plain,(
    ! [X4] :
      ( k2_relset_1(sK4,sK5,sK6) != sK5
      | ~ r2_hidden(k4_tarski(X4,sK7),sK6) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f39,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f51,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK3(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f47,plain,(
    ! [X5] :
      ( k2_relset_1(sK4,sK5,sK6) = sK5
      | r2_hidden(k4_tarski(sK8(X5),X5),sK6)
      | ~ r2_hidden(X5,sK5) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( k2_relat_1(X0) = X1
      | ~ r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0)
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f48,plain,
    ( k2_relset_1(sK4,sK5,sK6) != sK5
    | r2_hidden(sK7,sK5) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_6,plain,
    ( r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0)
    | r2_hidden(sK1(X0,X1),X1)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_7,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_3244,plain,
    ( r2_hidden(sK1(X0,X1),X1)
    | r2_hidden(sK1(X0,X1),k2_relat_1(X0))
    | k2_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_6,c_7])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v5_relat_1(X0,X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_198,plain,
    ( v5_relat_1(X0,X1)
    | k1_zfmisc_1(k2_zfmisc_1(X2,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_15])).

cnf(c_199,plain,
    ( v5_relat_1(sK6,X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
    inference(unflattening,[status(thm)],[c_198])).

cnf(c_4,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_210,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_15])).

cnf(c_211,plain,
    ( v1_relat_1(sK6)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
    inference(unflattening,[status(thm)],[c_210])).

cnf(c_230,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_211])).

cnf(c_231,plain,
    ( ~ v5_relat_1(sK6,X0)
    | r1_tarski(k2_relat_1(sK6),X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
    inference(unflattening,[status(thm)],[c_230])).

cnf(c_267,plain,
    ( r1_tarski(k2_relat_1(sK6),X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
    inference(resolution,[status(thm)],[c_199,c_231])).

cnf(c_474,plain,
    ( r1_tarski(k2_relat_1(sK6),X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_267])).

cnf(c_475,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_267])).

cnf(c_473,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_267])).

cnf(c_477,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_981,plain,
    ( ~ sP0_iProver_split ),
    inference(resolution,[status(thm)],[c_473,c_477])).

cnf(c_1022,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | r1_tarski(k2_relat_1(sK6),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_474,c_475,c_981])).

cnf(c_1023,plain,
    ( r1_tarski(k2_relat_1(sK6),X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
    inference(renaming,[status(thm)],[c_1022])).

cnf(c_1038,plain,
    ( r1_tarski(k2_relat_1(sK6),sK5) ),
    inference(resolution,[status(thm)],[c_1023,c_477])).

cnf(c_1211,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK6))
    | r2_hidden(X0,sK5) ),
    inference(resolution,[status(thm)],[c_2,c_1038])).

cnf(c_5942,plain,
    ( r2_hidden(sK1(sK6,X0),X0)
    | r2_hidden(sK1(sK6,X0),sK5)
    | k2_relat_1(sK6) = X0 ),
    inference(resolution,[status(thm)],[c_3244,c_1211])).

cnf(c_5944,plain,
    ( r2_hidden(sK1(sK6,sK5),sK5)
    | k2_relat_1(sK6) = sK5 ),
    inference(instantiation,[status(thm)],[c_5942])).

cnf(c_1231,plain,
    ( r2_hidden(sK7,X0)
    | ~ r2_hidden(sK7,sK5)
    | ~ r1_tarski(sK5,X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1339,plain,
    ( r2_hidden(sK7,k2_relat_1(X0))
    | ~ r2_hidden(sK7,sK5)
    | ~ r1_tarski(sK5,k2_relat_1(X0)) ),
    inference(instantiation,[status(thm)],[c_1231])).

cnf(c_5686,plain,
    ( r2_hidden(sK7,k2_relat_1(sK6))
    | ~ r2_hidden(sK7,sK5)
    | ~ r1_tarski(sK5,k2_relat_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_1339])).

cnf(c_5687,plain,
    ( r2_hidden(sK7,k2_relat_1(sK6)) = iProver_top
    | r2_hidden(sK7,sK5) != iProver_top
    | r1_tarski(sK5,k2_relat_1(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5686])).

cnf(c_480,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1230,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK7,sK5)
    | X0 != sK7
    | X1 != sK5 ),
    inference(instantiation,[status(thm)],[c_480])).

cnf(c_1350,plain,
    ( r2_hidden(sK7,X0)
    | ~ r2_hidden(sK7,sK5)
    | X0 != sK5
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_1230])).

cnf(c_2458,plain,
    ( r2_hidden(sK7,k2_relat_1(X0))
    | ~ r2_hidden(sK7,sK5)
    | k2_relat_1(X0) != sK5
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_1350])).

cnf(c_5230,plain,
    ( r2_hidden(sK7,k2_relat_1(sK6))
    | ~ r2_hidden(sK7,sK5)
    | k2_relat_1(sK6) != sK5
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_2458])).

cnf(c_12,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(X0,sK7),sK6)
    | k2_relset_1(sK4,sK5,sK6) != sK5 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_5182,plain,
    ( ~ r2_hidden(k4_tarski(sK3(sK6,sK7),sK7),sK6)
    | k2_relset_1(sK4,sK5,sK6) != sK5 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_5185,plain,
    ( k2_relset_1(sK4,sK5,sK6) != sK5
    | r2_hidden(k4_tarski(sK3(sK6,sK7),sK7),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5182])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(k4_tarski(sK3(X1,X0),X0),X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1340,plain,
    ( r2_hidden(k4_tarski(sK3(X0,sK7),sK7),X0)
    | ~ r2_hidden(sK7,k2_relat_1(X0)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_5181,plain,
    ( r2_hidden(k4_tarski(sK3(sK6,sK7),sK7),sK6)
    | ~ r2_hidden(sK7,k2_relat_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_1340])).

cnf(c_5183,plain,
    ( r2_hidden(k4_tarski(sK3(sK6,sK7),sK7),sK6) = iProver_top
    | r2_hidden(sK7,k2_relat_1(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5181])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_189,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | sK6 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_15])).

cnf(c_190,plain,
    ( k2_relset_1(X0,X1,sK6) = k2_relat_1(sK6)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
    inference(unflattening,[status(thm)],[c_189])).

cnf(c_899,plain,
    ( k2_relset_1(sK4,sK5,sK6) = k2_relat_1(sK6) ),
    inference(equality_resolution,[status(thm)],[c_190])).

cnf(c_14,negated_conjecture,
    ( ~ r2_hidden(X0,sK5)
    | r2_hidden(k4_tarski(sK8(X0),X0),sK6)
    | k2_relset_1(sK4,sK5,sK6) = sK5 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_739,plain,
    ( k2_relset_1(sK4,sK5,sK6) = sK5
    | r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(k4_tarski(sK8(X0),X0),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_942,plain,
    ( k2_relat_1(sK6) = sK5
    | r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(k4_tarski(sK8(X0),X0),sK6) = iProver_top ),
    inference(demodulation,[status(thm)],[c_899,c_739])).

cnf(c_5,plain,
    ( ~ r2_hidden(k4_tarski(X0,sK1(X1,X2)),X1)
    | ~ r2_hidden(sK1(X1,X2),X2)
    | k2_relat_1(X1) = X2 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_745,plain,
    ( k2_relat_1(X0) = X1
    | r2_hidden(k4_tarski(X2,sK1(X0,X1)),X0) != iProver_top
    | r2_hidden(sK1(X0,X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1982,plain,
    ( k2_relat_1(sK6) = X0
    | k2_relat_1(sK6) = sK5
    | r2_hidden(sK1(sK6,X0),X0) != iProver_top
    | r2_hidden(sK1(sK6,X0),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_942,c_745])).

cnf(c_2018,plain,
    ( ~ r2_hidden(sK1(sK6,X0),X0)
    | ~ r2_hidden(sK1(sK6,X0),sK5)
    | k2_relat_1(sK6) = X0
    | k2_relat_1(sK6) = sK5 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1982])).

cnf(c_2020,plain,
    ( ~ r2_hidden(sK1(sK6,sK5),sK5)
    | k2_relat_1(sK6) = sK5 ),
    inference(instantiation,[status(thm)],[c_2018])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_747,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_743,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1199,plain,
    ( k2_relat_1(sK6) = sK5
    | r2_hidden(X0,k2_relat_1(sK6)) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_942,c_743])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_748,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1387,plain,
    ( k2_relat_1(sK6) = sK5
    | r2_hidden(sK0(X0,k2_relat_1(sK6)),sK5) != iProver_top
    | r1_tarski(X0,k2_relat_1(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1199,c_748])).

cnf(c_1515,plain,
    ( k2_relat_1(sK6) = sK5
    | r1_tarski(sK5,k2_relat_1(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_747,c_1387])).

cnf(c_1351,plain,
    ( sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_477])).

cnf(c_478,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_986,plain,
    ( k2_relat_1(sK6) != X0
    | sK5 != X0
    | sK5 = k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_478])).

cnf(c_987,plain,
    ( k2_relat_1(sK6) != sK5
    | sK5 = k2_relat_1(sK6)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_986])).

cnf(c_893,plain,
    ( k2_relset_1(sK4,sK5,sK6) != X0
    | k2_relset_1(sK4,sK5,sK6) = sK5
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_478])).

cnf(c_928,plain,
    ( k2_relset_1(sK4,sK5,sK6) != k2_relat_1(sK6)
    | k2_relset_1(sK4,sK5,sK6) = sK5
    | sK5 != k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_893])).

cnf(c_864,plain,
    ( k2_relset_1(sK4,sK5,sK6) = k2_relat_1(sK6)
    | k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_190])).

cnf(c_863,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) = k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_477])).

cnf(c_494,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_477])).

cnf(c_13,negated_conjecture,
    ( r2_hidden(sK7,sK5)
    | k2_relset_1(sK4,sK5,sK6) != sK5 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_20,plain,
    ( k2_relset_1(sK4,sK5,sK6) != sK5
    | r2_hidden(sK7,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5944,c_5687,c_5230,c_5185,c_5182,c_5183,c_5181,c_2020,c_1515,c_1351,c_987,c_928,c_864,c_863,c_494,c_20,c_13])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:01:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.24/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.24/1.00  
% 3.24/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.24/1.00  
% 3.24/1.00  ------  iProver source info
% 3.24/1.00  
% 3.24/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.24/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.24/1.00  git: non_committed_changes: false
% 3.24/1.00  git: last_make_outside_of_git: false
% 3.24/1.00  
% 3.24/1.00  ------ 
% 3.24/1.00  ------ Parsing...
% 3.24/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.24/1.00  
% 3.24/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.24/1.00  
% 3.24/1.00  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.24/1.00  
% 3.24/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.24/1.00  ------ Proving...
% 3.24/1.00  ------ Problem Properties 
% 3.24/1.00  
% 3.24/1.00  
% 3.24/1.00  clauses                                 14
% 3.24/1.00  conjectures                             3
% 3.24/1.00  EPR                                     2
% 3.24/1.00  Horn                                    10
% 3.24/1.00  unary                                   0
% 3.24/1.00  binary                                  9
% 3.24/1.00  lits                                    33
% 3.24/1.00  lits eq                                 9
% 3.24/1.00  fd_pure                                 0
% 3.24/1.00  fd_pseudo                               0
% 3.24/1.00  fd_cond                                 0
% 3.24/1.00  fd_pseudo_cond                          2
% 3.24/1.00  AC symbols                              0
% 3.24/1.00  
% 3.24/1.00  ------ Input Options Time Limit: Unbounded
% 3.24/1.00  
% 3.24/1.00  
% 3.24/1.00  ------ 
% 3.24/1.00  Current options:
% 3.24/1.00  ------ 
% 3.24/1.00  
% 3.24/1.00  
% 3.24/1.00  
% 3.24/1.00  
% 3.24/1.00  ------ Proving...
% 3.24/1.00  
% 3.24/1.00  
% 3.24/1.00  % SZS status Theorem for theBenchmark.p
% 3.24/1.00  
% 3.24/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.24/1.00  
% 3.24/1.00  fof(f3,axiom,(
% 3.24/1.00    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 3.24/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.24/1.00  
% 3.24/1.00  fof(f21,plain,(
% 3.24/1.00    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 3.24/1.00    inference(nnf_transformation,[],[f3])).
% 3.24/1.00  
% 3.24/1.00  fof(f22,plain,(
% 3.24/1.00    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 3.24/1.00    inference(rectify,[],[f21])).
% 3.24/1.00  
% 3.24/1.00  fof(f25,plain,(
% 3.24/1.00    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK3(X0,X5),X5),X0))),
% 3.24/1.00    introduced(choice_axiom,[])).
% 3.24/1.00  
% 3.24/1.00  fof(f24,plain,(
% 3.24/1.00    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) => r2_hidden(k4_tarski(sK2(X0,X1),X2),X0))) )),
% 3.24/1.00    introduced(choice_axiom,[])).
% 3.24/1.00  
% 3.24/1.00  fof(f23,plain,(
% 3.24/1.00    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK1(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 3.24/1.00    introduced(choice_axiom,[])).
% 3.24/1.00  
% 3.24/1.00  fof(f26,plain,(
% 3.24/1.00    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK3(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 3.24/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f22,f25,f24,f23])).
% 3.24/1.00  
% 3.24/1.00  fof(f41,plain,(
% 3.24/1.00    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1)) )),
% 3.24/1.00    inference(cnf_transformation,[],[f26])).
% 3.24/1.00  
% 3.24/1.00  fof(f40,plain,(
% 3.24/1.00    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 3.24/1.00    inference(cnf_transformation,[],[f26])).
% 3.24/1.00  
% 3.24/1.00  fof(f50,plain,(
% 3.24/1.00    ( ! [X6,X0,X5] : (r2_hidden(X5,k2_relat_1(X0)) | ~r2_hidden(k4_tarski(X6,X5),X0)) )),
% 3.24/1.00    inference(equality_resolution,[],[f40])).
% 3.24/1.00  
% 3.24/1.00  fof(f1,axiom,(
% 3.24/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.24/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.24/1.00  
% 3.24/1.00  fof(f10,plain,(
% 3.24/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.24/1.00    inference(ennf_transformation,[],[f1])).
% 3.24/1.00  
% 3.24/1.00  fof(f16,plain,(
% 3.24/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.24/1.00    inference(nnf_transformation,[],[f10])).
% 3.24/1.00  
% 3.24/1.00  fof(f17,plain,(
% 3.24/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.24/1.00    inference(rectify,[],[f16])).
% 3.24/1.00  
% 3.24/1.00  fof(f18,plain,(
% 3.24/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.24/1.00    introduced(choice_axiom,[])).
% 3.24/1.00  
% 3.24/1.00  fof(f19,plain,(
% 3.24/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.24/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f18])).
% 3.24/1.00  
% 3.24/1.00  fof(f34,plain,(
% 3.24/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.24/1.00    inference(cnf_transformation,[],[f19])).
% 3.24/1.00  
% 3.24/1.00  fof(f5,axiom,(
% 3.24/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.24/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.24/1.00  
% 3.24/1.00  fof(f9,plain,(
% 3.24/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.24/1.00    inference(pure_predicate_removal,[],[f5])).
% 3.24/1.00  
% 3.24/1.00  fof(f13,plain,(
% 3.24/1.00    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.24/1.00    inference(ennf_transformation,[],[f9])).
% 3.24/1.00  
% 3.24/1.00  fof(f44,plain,(
% 3.24/1.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.24/1.00    inference(cnf_transformation,[],[f13])).
% 3.24/1.00  
% 3.24/1.00  fof(f7,conjecture,(
% 3.24/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1))),
% 3.24/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.24/1.00  
% 3.24/1.00  fof(f8,negated_conjecture,(
% 3.24/1.00    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1))),
% 3.24/1.00    inference(negated_conjecture,[],[f7])).
% 3.24/1.00  
% 3.24/1.00  fof(f15,plain,(
% 3.24/1.00    ? [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) | ~r2_hidden(X3,X1)) <~> k2_relset_1(X0,X1,X2) = X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.24/1.00    inference(ennf_transformation,[],[f8])).
% 3.24/1.00  
% 3.24/1.00  fof(f27,plain,(
% 3.24/1.00    ? [X0,X1,X2] : (((k2_relset_1(X0,X1,X2) != X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1))) & (k2_relset_1(X0,X1,X2) = X1 | ! [X3] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) | ~r2_hidden(X3,X1)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.24/1.00    inference(nnf_transformation,[],[f15])).
% 3.24/1.00  
% 3.24/1.00  fof(f28,plain,(
% 3.24/1.00    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1))) & (k2_relset_1(X0,X1,X2) = X1 | ! [X3] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) | ~r2_hidden(X3,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.24/1.00    inference(flattening,[],[f27])).
% 3.24/1.00  
% 3.24/1.00  fof(f29,plain,(
% 3.24/1.00    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1))) & (k2_relset_1(X0,X1,X2) = X1 | ! [X5] : (? [X6] : r2_hidden(k4_tarski(X6,X5),X2) | ~r2_hidden(X5,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.24/1.00    inference(rectify,[],[f28])).
% 3.24/1.00  
% 3.24/1.00  fof(f32,plain,(
% 3.24/1.00    ( ! [X2] : (! [X5] : (? [X6] : r2_hidden(k4_tarski(X6,X5),X2) => r2_hidden(k4_tarski(sK8(X5),X5),X2))) )),
% 3.24/1.00    introduced(choice_axiom,[])).
% 3.24/1.00  
% 3.24/1.00  fof(f31,plain,(
% 3.24/1.00    ( ! [X2,X1] : (? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1)) => (! [X4] : ~r2_hidden(k4_tarski(X4,sK7),X2) & r2_hidden(sK7,X1))) )),
% 3.24/1.00    introduced(choice_axiom,[])).
% 3.24/1.00  
% 3.24/1.00  fof(f30,plain,(
% 3.24/1.00    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1))) & (k2_relset_1(X0,X1,X2) = X1 | ! [X5] : (? [X6] : r2_hidden(k4_tarski(X6,X5),X2) | ~r2_hidden(X5,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => ((k2_relset_1(sK4,sK5,sK6) != sK5 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X4,X3),sK6) & r2_hidden(X3,sK5))) & (k2_relset_1(sK4,sK5,sK6) = sK5 | ! [X5] : (? [X6] : r2_hidden(k4_tarski(X6,X5),sK6) | ~r2_hidden(X5,sK5))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))))),
% 3.24/1.00    introduced(choice_axiom,[])).
% 3.24/1.00  
% 3.24/1.00  fof(f33,plain,(
% 3.24/1.00    (k2_relset_1(sK4,sK5,sK6) != sK5 | (! [X4] : ~r2_hidden(k4_tarski(X4,sK7),sK6) & r2_hidden(sK7,sK5))) & (k2_relset_1(sK4,sK5,sK6) = sK5 | ! [X5] : (r2_hidden(k4_tarski(sK8(X5),X5),sK6) | ~r2_hidden(X5,sK5))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 3.24/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f29,f32,f31,f30])).
% 3.24/1.00  
% 3.24/1.00  fof(f46,plain,(
% 3.24/1.00    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 3.24/1.00    inference(cnf_transformation,[],[f33])).
% 3.24/1.00  
% 3.24/1.00  fof(f2,axiom,(
% 3.24/1.00    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.24/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.24/1.00  
% 3.24/1.00  fof(f11,plain,(
% 3.24/1.00    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.24/1.00    inference(ennf_transformation,[],[f2])).
% 3.24/1.00  
% 3.24/1.00  fof(f20,plain,(
% 3.24/1.00    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.24/1.00    inference(nnf_transformation,[],[f11])).
% 3.24/1.00  
% 3.24/1.00  fof(f37,plain,(
% 3.24/1.00    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.24/1.00    inference(cnf_transformation,[],[f20])).
% 3.24/1.00  
% 3.24/1.00  fof(f4,axiom,(
% 3.24/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.24/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.24/1.00  
% 3.24/1.00  fof(f12,plain,(
% 3.24/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.24/1.00    inference(ennf_transformation,[],[f4])).
% 3.24/1.00  
% 3.24/1.00  fof(f43,plain,(
% 3.24/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.24/1.00    inference(cnf_transformation,[],[f12])).
% 3.24/1.00  
% 3.24/1.00  fof(f49,plain,(
% 3.24/1.00    ( ! [X4] : (k2_relset_1(sK4,sK5,sK6) != sK5 | ~r2_hidden(k4_tarski(X4,sK7),sK6)) )),
% 3.24/1.00    inference(cnf_transformation,[],[f33])).
% 3.24/1.00  
% 3.24/1.00  fof(f39,plain,(
% 3.24/1.00    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK3(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 3.24/1.00    inference(cnf_transformation,[],[f26])).
% 3.24/1.00  
% 3.24/1.00  fof(f51,plain,(
% 3.24/1.00    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK3(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 3.24/1.00    inference(equality_resolution,[],[f39])).
% 3.24/1.00  
% 3.24/1.00  fof(f6,axiom,(
% 3.24/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.24/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.24/1.00  
% 3.24/1.00  fof(f14,plain,(
% 3.24/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.24/1.00    inference(ennf_transformation,[],[f6])).
% 3.24/1.00  
% 3.24/1.00  fof(f45,plain,(
% 3.24/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.24/1.00    inference(cnf_transformation,[],[f14])).
% 3.24/1.00  
% 3.24/1.00  fof(f47,plain,(
% 3.24/1.00    ( ! [X5] : (k2_relset_1(sK4,sK5,sK6) = sK5 | r2_hidden(k4_tarski(sK8(X5),X5),sK6) | ~r2_hidden(X5,sK5)) )),
% 3.24/1.00    inference(cnf_transformation,[],[f33])).
% 3.24/1.00  
% 3.24/1.00  fof(f42,plain,(
% 3.24/1.00    ( ! [X0,X3,X1] : (k2_relat_1(X0) = X1 | ~r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0) | ~r2_hidden(sK1(X0,X1),X1)) )),
% 3.24/1.00    inference(cnf_transformation,[],[f26])).
% 3.24/1.00  
% 3.24/1.00  fof(f35,plain,(
% 3.24/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.24/1.00    inference(cnf_transformation,[],[f19])).
% 3.24/1.00  
% 3.24/1.00  fof(f36,plain,(
% 3.24/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.24/1.00    inference(cnf_transformation,[],[f19])).
% 3.24/1.00  
% 3.24/1.00  fof(f48,plain,(
% 3.24/1.00    k2_relset_1(sK4,sK5,sK6) != sK5 | r2_hidden(sK7,sK5)),
% 3.24/1.00    inference(cnf_transformation,[],[f33])).
% 3.24/1.00  
% 3.24/1.00  cnf(c_6,plain,
% 3.24/1.00      ( r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0)
% 3.24/1.00      | r2_hidden(sK1(X0,X1),X1)
% 3.24/1.00      | k2_relat_1(X0) = X1 ),
% 3.24/1.00      inference(cnf_transformation,[],[f41]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_7,plain,
% 3.24/1.00      ( r2_hidden(X0,k2_relat_1(X1)) | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
% 3.24/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_3244,plain,
% 3.24/1.00      ( r2_hidden(sK1(X0,X1),X1)
% 3.24/1.00      | r2_hidden(sK1(X0,X1),k2_relat_1(X0))
% 3.24/1.00      | k2_relat_1(X0) = X1 ),
% 3.24/1.00      inference(resolution,[status(thm)],[c_6,c_7]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_2,plain,
% 3.24/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.24/1.00      inference(cnf_transformation,[],[f34]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_10,plain,
% 3.24/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.24/1.00      | v5_relat_1(X0,X2) ),
% 3.24/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_15,negated_conjecture,
% 3.24/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
% 3.24/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_198,plain,
% 3.24/1.00      ( v5_relat_1(X0,X1)
% 3.24/1.00      | k1_zfmisc_1(k2_zfmisc_1(X2,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 3.24/1.00      | sK6 != X0 ),
% 3.24/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_15]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_199,plain,
% 3.24/1.00      ( v5_relat_1(sK6,X0)
% 3.24/1.00      | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
% 3.24/1.00      inference(unflattening,[status(thm)],[c_198]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_4,plain,
% 3.24/1.00      ( ~ v5_relat_1(X0,X1)
% 3.24/1.00      | r1_tarski(k2_relat_1(X0),X1)
% 3.24/1.00      | ~ v1_relat_1(X0) ),
% 3.24/1.00      inference(cnf_transformation,[],[f37]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_9,plain,
% 3.24/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.24/1.00      | v1_relat_1(X0) ),
% 3.24/1.00      inference(cnf_transformation,[],[f43]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_210,plain,
% 3.24/1.00      ( v1_relat_1(X0)
% 3.24/1.00      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 3.24/1.00      | sK6 != X0 ),
% 3.24/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_15]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_211,plain,
% 3.24/1.00      ( v1_relat_1(sK6)
% 3.24/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
% 3.24/1.00      inference(unflattening,[status(thm)],[c_210]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_230,plain,
% 3.24/1.00      ( ~ v5_relat_1(X0,X1)
% 3.24/1.00      | r1_tarski(k2_relat_1(X0),X1)
% 3.24/1.00      | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 3.24/1.00      | sK6 != X0 ),
% 3.24/1.00      inference(resolution_lifted,[status(thm)],[c_4,c_211]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_231,plain,
% 3.24/1.00      ( ~ v5_relat_1(sK6,X0)
% 3.24/1.00      | r1_tarski(k2_relat_1(sK6),X0)
% 3.24/1.00      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
% 3.24/1.00      inference(unflattening,[status(thm)],[c_230]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_267,plain,
% 3.24/1.00      ( r1_tarski(k2_relat_1(sK6),X0)
% 3.24/1.00      | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 3.24/1.00      | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
% 3.24/1.00      inference(resolution,[status(thm)],[c_199,c_231]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_474,plain,
% 3.24/1.00      ( r1_tarski(k2_relat_1(sK6),X0)
% 3.24/1.00      | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 3.24/1.00      | ~ sP1_iProver_split ),
% 3.24/1.00      inference(splitting,
% 3.24/1.00                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 3.24/1.00                [c_267]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_475,plain,
% 3.24/1.00      ( sP1_iProver_split | sP0_iProver_split ),
% 3.24/1.00      inference(splitting,
% 3.24/1.00                [splitting(split),new_symbols(definition,[])],
% 3.24/1.00                [c_267]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_473,plain,
% 3.24/1.00      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 3.24/1.00      | ~ sP0_iProver_split ),
% 3.24/1.00      inference(splitting,
% 3.24/1.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.24/1.00                [c_267]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_477,plain,( X0 = X0 ),theory(equality) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_981,plain,
% 3.24/1.00      ( ~ sP0_iProver_split ),
% 3.24/1.00      inference(resolution,[status(thm)],[c_473,c_477]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1022,plain,
% 3.24/1.00      ( k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 3.24/1.00      | r1_tarski(k2_relat_1(sK6),X0) ),
% 3.24/1.00      inference(global_propositional_subsumption,
% 3.24/1.00                [status(thm)],
% 3.24/1.00                [c_474,c_475,c_981]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1023,plain,
% 3.24/1.00      ( r1_tarski(k2_relat_1(sK6),X0)
% 3.24/1.00      | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
% 3.24/1.00      inference(renaming,[status(thm)],[c_1022]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1038,plain,
% 3.24/1.00      ( r1_tarski(k2_relat_1(sK6),sK5) ),
% 3.24/1.00      inference(resolution,[status(thm)],[c_1023,c_477]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1211,plain,
% 3.24/1.00      ( ~ r2_hidden(X0,k2_relat_1(sK6)) | r2_hidden(X0,sK5) ),
% 3.24/1.00      inference(resolution,[status(thm)],[c_2,c_1038]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_5942,plain,
% 3.24/1.00      ( r2_hidden(sK1(sK6,X0),X0)
% 3.24/1.00      | r2_hidden(sK1(sK6,X0),sK5)
% 3.24/1.00      | k2_relat_1(sK6) = X0 ),
% 3.24/1.00      inference(resolution,[status(thm)],[c_3244,c_1211]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_5944,plain,
% 3.24/1.00      ( r2_hidden(sK1(sK6,sK5),sK5) | k2_relat_1(sK6) = sK5 ),
% 3.24/1.00      inference(instantiation,[status(thm)],[c_5942]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1231,plain,
% 3.24/1.00      ( r2_hidden(sK7,X0) | ~ r2_hidden(sK7,sK5) | ~ r1_tarski(sK5,X0) ),
% 3.24/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1339,plain,
% 3.24/1.00      ( r2_hidden(sK7,k2_relat_1(X0))
% 3.24/1.00      | ~ r2_hidden(sK7,sK5)
% 3.24/1.00      | ~ r1_tarski(sK5,k2_relat_1(X0)) ),
% 3.24/1.00      inference(instantiation,[status(thm)],[c_1231]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_5686,plain,
% 3.24/1.00      ( r2_hidden(sK7,k2_relat_1(sK6))
% 3.24/1.00      | ~ r2_hidden(sK7,sK5)
% 3.24/1.00      | ~ r1_tarski(sK5,k2_relat_1(sK6)) ),
% 3.24/1.00      inference(instantiation,[status(thm)],[c_1339]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_5687,plain,
% 3.24/1.00      ( r2_hidden(sK7,k2_relat_1(sK6)) = iProver_top
% 3.24/1.00      | r2_hidden(sK7,sK5) != iProver_top
% 3.24/1.00      | r1_tarski(sK5,k2_relat_1(sK6)) != iProver_top ),
% 3.24/1.00      inference(predicate_to_equality,[status(thm)],[c_5686]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_480,plain,
% 3.24/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.24/1.00      theory(equality) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1230,plain,
% 3.24/1.00      ( r2_hidden(X0,X1) | ~ r2_hidden(sK7,sK5) | X0 != sK7 | X1 != sK5 ),
% 3.24/1.00      inference(instantiation,[status(thm)],[c_480]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1350,plain,
% 3.24/1.00      ( r2_hidden(sK7,X0)
% 3.24/1.00      | ~ r2_hidden(sK7,sK5)
% 3.24/1.00      | X0 != sK5
% 3.24/1.00      | sK7 != sK7 ),
% 3.24/1.00      inference(instantiation,[status(thm)],[c_1230]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_2458,plain,
% 3.24/1.00      ( r2_hidden(sK7,k2_relat_1(X0))
% 3.24/1.00      | ~ r2_hidden(sK7,sK5)
% 3.24/1.00      | k2_relat_1(X0) != sK5
% 3.24/1.00      | sK7 != sK7 ),
% 3.24/1.00      inference(instantiation,[status(thm)],[c_1350]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_5230,plain,
% 3.24/1.00      ( r2_hidden(sK7,k2_relat_1(sK6))
% 3.24/1.00      | ~ r2_hidden(sK7,sK5)
% 3.24/1.00      | k2_relat_1(sK6) != sK5
% 3.24/1.00      | sK7 != sK7 ),
% 3.24/1.00      inference(instantiation,[status(thm)],[c_2458]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_12,negated_conjecture,
% 3.24/1.00      ( ~ r2_hidden(k4_tarski(X0,sK7),sK6)
% 3.24/1.00      | k2_relset_1(sK4,sK5,sK6) != sK5 ),
% 3.24/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_5182,plain,
% 3.24/1.00      ( ~ r2_hidden(k4_tarski(sK3(sK6,sK7),sK7),sK6)
% 3.24/1.00      | k2_relset_1(sK4,sK5,sK6) != sK5 ),
% 3.24/1.00      inference(instantiation,[status(thm)],[c_12]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_5185,plain,
% 3.24/1.00      ( k2_relset_1(sK4,sK5,sK6) != sK5
% 3.24/1.00      | r2_hidden(k4_tarski(sK3(sK6,sK7),sK7),sK6) != iProver_top ),
% 3.24/1.00      inference(predicate_to_equality,[status(thm)],[c_5182]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_8,plain,
% 3.24/1.00      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 3.24/1.00      | r2_hidden(k4_tarski(sK3(X1,X0),X0),X1) ),
% 3.24/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1340,plain,
% 3.24/1.00      ( r2_hidden(k4_tarski(sK3(X0,sK7),sK7),X0)
% 3.24/1.00      | ~ r2_hidden(sK7,k2_relat_1(X0)) ),
% 3.24/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_5181,plain,
% 3.24/1.00      ( r2_hidden(k4_tarski(sK3(sK6,sK7),sK7),sK6)
% 3.24/1.00      | ~ r2_hidden(sK7,k2_relat_1(sK6)) ),
% 3.24/1.00      inference(instantiation,[status(thm)],[c_1340]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_5183,plain,
% 3.24/1.00      ( r2_hidden(k4_tarski(sK3(sK6,sK7),sK7),sK6) = iProver_top
% 3.24/1.00      | r2_hidden(sK7,k2_relat_1(sK6)) != iProver_top ),
% 3.24/1.00      inference(predicate_to_equality,[status(thm)],[c_5181]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_11,plain,
% 3.24/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.24/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.24/1.00      inference(cnf_transformation,[],[f45]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_189,plain,
% 3.24/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.24/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 3.24/1.00      | sK6 != X2 ),
% 3.24/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_15]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_190,plain,
% 3.24/1.00      ( k2_relset_1(X0,X1,sK6) = k2_relat_1(sK6)
% 3.24/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
% 3.24/1.00      inference(unflattening,[status(thm)],[c_189]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_899,plain,
% 3.24/1.00      ( k2_relset_1(sK4,sK5,sK6) = k2_relat_1(sK6) ),
% 3.24/1.00      inference(equality_resolution,[status(thm)],[c_190]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_14,negated_conjecture,
% 3.24/1.00      ( ~ r2_hidden(X0,sK5)
% 3.24/1.00      | r2_hidden(k4_tarski(sK8(X0),X0),sK6)
% 3.24/1.00      | k2_relset_1(sK4,sK5,sK6) = sK5 ),
% 3.24/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_739,plain,
% 3.24/1.00      ( k2_relset_1(sK4,sK5,sK6) = sK5
% 3.24/1.00      | r2_hidden(X0,sK5) != iProver_top
% 3.24/1.00      | r2_hidden(k4_tarski(sK8(X0),X0),sK6) = iProver_top ),
% 3.24/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_942,plain,
% 3.24/1.00      ( k2_relat_1(sK6) = sK5
% 3.24/1.00      | r2_hidden(X0,sK5) != iProver_top
% 3.24/1.00      | r2_hidden(k4_tarski(sK8(X0),X0),sK6) = iProver_top ),
% 3.24/1.00      inference(demodulation,[status(thm)],[c_899,c_739]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_5,plain,
% 3.24/1.00      ( ~ r2_hidden(k4_tarski(X0,sK1(X1,X2)),X1)
% 3.24/1.00      | ~ r2_hidden(sK1(X1,X2),X2)
% 3.24/1.00      | k2_relat_1(X1) = X2 ),
% 3.24/1.00      inference(cnf_transformation,[],[f42]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_745,plain,
% 3.24/1.00      ( k2_relat_1(X0) = X1
% 3.24/1.00      | r2_hidden(k4_tarski(X2,sK1(X0,X1)),X0) != iProver_top
% 3.24/1.00      | r2_hidden(sK1(X0,X1),X1) != iProver_top ),
% 3.24/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1982,plain,
% 3.24/1.00      ( k2_relat_1(sK6) = X0
% 3.24/1.00      | k2_relat_1(sK6) = sK5
% 3.24/1.00      | r2_hidden(sK1(sK6,X0),X0) != iProver_top
% 3.24/1.00      | r2_hidden(sK1(sK6,X0),sK5) != iProver_top ),
% 3.24/1.00      inference(superposition,[status(thm)],[c_942,c_745]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_2018,plain,
% 3.24/1.00      ( ~ r2_hidden(sK1(sK6,X0),X0)
% 3.24/1.00      | ~ r2_hidden(sK1(sK6,X0),sK5)
% 3.24/1.00      | k2_relat_1(sK6) = X0
% 3.24/1.00      | k2_relat_1(sK6) = sK5 ),
% 3.24/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1982]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_2020,plain,
% 3.24/1.00      ( ~ r2_hidden(sK1(sK6,sK5),sK5) | k2_relat_1(sK6) = sK5 ),
% 3.24/1.00      inference(instantiation,[status(thm)],[c_2018]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1,plain,
% 3.24/1.00      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.24/1.00      inference(cnf_transformation,[],[f35]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_747,plain,
% 3.24/1.00      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.24/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.24/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_743,plain,
% 3.24/1.00      ( r2_hidden(X0,k2_relat_1(X1)) = iProver_top
% 3.24/1.00      | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top ),
% 3.24/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1199,plain,
% 3.24/1.00      ( k2_relat_1(sK6) = sK5
% 3.24/1.00      | r2_hidden(X0,k2_relat_1(sK6)) = iProver_top
% 3.24/1.00      | r2_hidden(X0,sK5) != iProver_top ),
% 3.24/1.00      inference(superposition,[status(thm)],[c_942,c_743]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_0,plain,
% 3.24/1.00      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.24/1.00      inference(cnf_transformation,[],[f36]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_748,plain,
% 3.24/1.00      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 3.24/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.24/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1387,plain,
% 3.24/1.00      ( k2_relat_1(sK6) = sK5
% 3.24/1.00      | r2_hidden(sK0(X0,k2_relat_1(sK6)),sK5) != iProver_top
% 3.24/1.00      | r1_tarski(X0,k2_relat_1(sK6)) = iProver_top ),
% 3.24/1.00      inference(superposition,[status(thm)],[c_1199,c_748]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1515,plain,
% 3.24/1.00      ( k2_relat_1(sK6) = sK5
% 3.24/1.00      | r1_tarski(sK5,k2_relat_1(sK6)) = iProver_top ),
% 3.24/1.00      inference(superposition,[status(thm)],[c_747,c_1387]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1351,plain,
% 3.24/1.00      ( sK7 = sK7 ),
% 3.24/1.00      inference(instantiation,[status(thm)],[c_477]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_478,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_986,plain,
% 3.24/1.00      ( k2_relat_1(sK6) != X0 | sK5 != X0 | sK5 = k2_relat_1(sK6) ),
% 3.24/1.00      inference(instantiation,[status(thm)],[c_478]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_987,plain,
% 3.24/1.00      ( k2_relat_1(sK6) != sK5 | sK5 = k2_relat_1(sK6) | sK5 != sK5 ),
% 3.24/1.00      inference(instantiation,[status(thm)],[c_986]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_893,plain,
% 3.24/1.00      ( k2_relset_1(sK4,sK5,sK6) != X0
% 3.24/1.00      | k2_relset_1(sK4,sK5,sK6) = sK5
% 3.24/1.00      | sK5 != X0 ),
% 3.24/1.00      inference(instantiation,[status(thm)],[c_478]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_928,plain,
% 3.24/1.00      ( k2_relset_1(sK4,sK5,sK6) != k2_relat_1(sK6)
% 3.24/1.00      | k2_relset_1(sK4,sK5,sK6) = sK5
% 3.24/1.00      | sK5 != k2_relat_1(sK6) ),
% 3.24/1.00      inference(instantiation,[status(thm)],[c_893]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_864,plain,
% 3.24/1.00      ( k2_relset_1(sK4,sK5,sK6) = k2_relat_1(sK6)
% 3.24/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
% 3.24/1.00      inference(instantiation,[status(thm)],[c_190]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_863,plain,
% 3.24/1.00      ( k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) = k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
% 3.24/1.00      inference(instantiation,[status(thm)],[c_477]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_494,plain,
% 3.24/1.00      ( sK5 = sK5 ),
% 3.24/1.00      inference(instantiation,[status(thm)],[c_477]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_13,negated_conjecture,
% 3.24/1.00      ( r2_hidden(sK7,sK5) | k2_relset_1(sK4,sK5,sK6) != sK5 ),
% 3.24/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_20,plain,
% 3.24/1.00      ( k2_relset_1(sK4,sK5,sK6) != sK5
% 3.24/1.00      | r2_hidden(sK7,sK5) = iProver_top ),
% 3.24/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(contradiction,plain,
% 3.24/1.00      ( $false ),
% 3.24/1.00      inference(minisat,
% 3.24/1.00                [status(thm)],
% 3.24/1.00                [c_5944,c_5687,c_5230,c_5185,c_5182,c_5183,c_5181,c_2020,
% 3.24/1.00                 c_1515,c_1351,c_987,c_928,c_864,c_863,c_494,c_20,c_13]) ).
% 3.24/1.00  
% 3.24/1.00  
% 3.24/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.24/1.00  
% 3.24/1.00  ------                               Statistics
% 3.24/1.00  
% 3.24/1.00  ------ Selected
% 3.24/1.00  
% 3.24/1.00  total_time:                             0.205
% 3.24/1.00  
%------------------------------------------------------------------------------
