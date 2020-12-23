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
% DateTime   : Thu Dec  3 11:56:25 EST 2020

% Result     : Theorem 2.48s
% Output     : CNFRefutation 2.48s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 443 expanded)
%              Number of clauses        :   41 ( 116 expanded)
%              Number of leaves         :   14 ( 122 expanded)
%              Depth                    :   20
%              Number of atoms          :  279 (2121 expanded)
%              Number of equality atoms :   42 ( 187 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
             => ! [X3] :
                  ( r2_hidden(X3,k2_relset_1(X1,X0,X2))
                <=> ? [X4] :
                      ( r2_hidden(k4_tarski(X4,X3),X2)
                      & m1_subset_1(X4,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
               => ! [X3] :
                    ( r2_hidden(X3,k2_relset_1(X1,X0,X2))
                  <=> ? [X4] :
                        ( r2_hidden(k4_tarski(X4,X3),X2)
                        & m1_subset_1(X4,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f9,plain,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ! [X3] :
            ( r2_hidden(X3,k2_relset_1(X1,X0,X2))
          <=> ? [X4] :
                ( r2_hidden(k4_tarski(X4,X3),X2)
                & m1_subset_1(X4,X1) ) ) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( r2_hidden(X3,k2_relset_1(X1,X0,X2))
        <~> ? [X4] :
              ( r2_hidden(k4_tarski(X4,X3),X2)
              & m1_subset_1(X4,X1) ) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(k4_tarski(X4,X3),X2)
                | ~ m1_subset_1(X4,X1) )
            | ~ r2_hidden(X3,k2_relset_1(X1,X0,X2)) )
          & ( ? [X4] :
                ( r2_hidden(k4_tarski(X4,X3),X2)
                & m1_subset_1(X4,X1) )
            | r2_hidden(X3,k2_relset_1(X1,X0,X2)) ) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(k4_tarski(X4,X3),X2)
                | ~ m1_subset_1(X4,X1) )
            | ~ r2_hidden(X3,k2_relset_1(X1,X0,X2)) )
          & ( ? [X5] :
                ( r2_hidden(k4_tarski(X5,X3),X2)
                & m1_subset_1(X5,X1) )
            | r2_hidden(X3,k2_relset_1(X1,X0,X2)) ) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(rectify,[],[f27])).

fof(f31,plain,(
    ! [X2,X3,X1] :
      ( ? [X5] :
          ( r2_hidden(k4_tarski(X5,X3),X2)
          & m1_subset_1(X5,X1) )
     => ( r2_hidden(k4_tarski(sK8,X3),X2)
        & m1_subset_1(sK8,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(k4_tarski(X4,X3),X2)
                | ~ m1_subset_1(X4,X1) )
            | ~ r2_hidden(X3,k2_relset_1(X1,X0,X2)) )
          & ( ? [X5] :
                ( r2_hidden(k4_tarski(X5,X3),X2)
                & m1_subset_1(X5,X1) )
            | r2_hidden(X3,k2_relset_1(X1,X0,X2)) ) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(k4_tarski(X4,sK7),X2)
              | ~ m1_subset_1(X4,X1) )
          | ~ r2_hidden(sK7,k2_relset_1(X1,X0,X2)) )
        & ( ? [X5] :
              ( r2_hidden(k4_tarski(X5,sK7),X2)
              & m1_subset_1(X5,X1) )
          | r2_hidden(sK7,k2_relset_1(X1,X0,X2)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ( ! [X4] :
                  ( ~ r2_hidden(k4_tarski(X4,X3),X2)
                  | ~ m1_subset_1(X4,X1) )
              | ~ r2_hidden(X3,k2_relset_1(X1,X0,X2)) )
            & ( ? [X5] :
                  ( r2_hidden(k4_tarski(X5,X3),X2)
                  & m1_subset_1(X5,X1) )
              | r2_hidden(X3,k2_relset_1(X1,X0,X2)) ) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
   => ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(k4_tarski(X4,X3),sK6)
                | ~ m1_subset_1(X4,sK5) )
            | ~ r2_hidden(X3,k2_relset_1(sK5,sK4,sK6)) )
          & ( ? [X5] :
                ( r2_hidden(k4_tarski(X5,X3),sK6)
                & m1_subset_1(X5,sK5) )
            | r2_hidden(X3,k2_relset_1(sK5,sK4,sK6)) ) )
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ( ! [X4] :
          ( ~ r2_hidden(k4_tarski(X4,sK7),sK6)
          | ~ m1_subset_1(X4,sK5) )
      | ~ r2_hidden(sK7,k2_relset_1(sK5,sK4,sK6)) )
    & ( ( r2_hidden(k4_tarski(sK8,sK7),sK6)
        & m1_subset_1(sK8,sK5) )
      | r2_hidden(sK7,k2_relset_1(sK5,sK4,sK6)) )
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f28,f31,f30,f29])).

fof(f50,plain,(
    ! [X4] :
      ( ~ r2_hidden(k4_tarski(X4,sK7),sK6)
      | ~ m1_subset_1(X4,sK5)
      | ~ r2_hidden(sK7,k2_relset_1(sK5,sK4,sK6)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f47,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) ),
    inference(cnf_transformation,[],[f32])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f48,plain,
    ( m1_subset_1(sK8,sK5)
    | r2_hidden(sK7,k2_relset_1(sK5,sK4,sK6)) ),
    inference(cnf_transformation,[],[f32])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f5])).

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

fof(f43,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f51,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f43])).

fof(f49,plain,
    ( r2_hidden(k4_tarski(sK8,sK7),sK6)
    | r2_hidden(sK7,k2_relset_1(sK5,sK4,sK6)) ),
    inference(cnf_transformation,[],[f32])).

fof(f42,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f52,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK3(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f42])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f18])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f14,plain,(
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

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f14])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_14,negated_conjecture,
    ( ~ m1_subset_1(X0,sK5)
    | ~ r2_hidden(k4_tarski(X0,sK7),sK6)
    | ~ r2_hidden(sK7,k2_relset_1(sK5,sK4,sK6)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_937,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_941,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1402,plain,
    ( k2_relset_1(sK5,sK4,sK6) = k2_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_937,c_941])).

cnf(c_940,plain,
    ( m1_subset_1(X0,sK5) != iProver_top
    | r2_hidden(k4_tarski(X0,sK7),sK6) != iProver_top
    | r2_hidden(sK7,k2_relset_1(sK5,sK4,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1533,plain,
    ( m1_subset_1(X0,sK5) != iProver_top
    | r2_hidden(k4_tarski(X0,sK7),sK6) != iProver_top
    | r2_hidden(sK7,k2_relat_1(sK6)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1402,c_940])).

cnf(c_1555,plain,
    ( ~ m1_subset_1(X0,sK5)
    | ~ r2_hidden(k4_tarski(X0,sK7),sK6)
    | ~ r2_hidden(sK7,k2_relat_1(sK6)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1533])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK8,sK5)
    | r2_hidden(sK7,k2_relset_1(sK5,sK4,sK6)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_938,plain,
    ( m1_subset_1(sK8,sK5) = iProver_top
    | r2_hidden(sK7,k2_relset_1(sK5,sK4,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1532,plain,
    ( m1_subset_1(sK8,sK5) = iProver_top
    | r2_hidden(sK7,k2_relat_1(sK6)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1402,c_938])).

cnf(c_11,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1212,plain,
    ( ~ r2_hidden(k4_tarski(sK8,sK7),sK6)
    | r2_hidden(sK7,k2_relat_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1213,plain,
    ( r2_hidden(k4_tarski(sK8,sK7),sK6) != iProver_top
    | r2_hidden(sK7,k2_relat_1(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1212])).

cnf(c_15,negated_conjecture,
    ( r2_hidden(k4_tarski(sK8,sK7),sK6)
    | r2_hidden(sK7,k2_relset_1(sK5,sK4,sK6)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_939,plain,
    ( r2_hidden(k4_tarski(sK8,sK7),sK6) = iProver_top
    | r2_hidden(sK7,k2_relset_1(sK5,sK4,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1531,plain,
    ( r2_hidden(k4_tarski(sK8,sK7),sK6) = iProver_top
    | r2_hidden(sK7,k2_relat_1(sK6)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1402,c_939])).

cnf(c_1828,plain,
    ( r2_hidden(sK7,k2_relat_1(sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1532,c_1213,c_1531])).

cnf(c_1830,plain,
    ( r2_hidden(sK7,k2_relat_1(sK6)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1828])).

cnf(c_1877,plain,
    ( ~ r2_hidden(k4_tarski(X0,sK7),sK6)
    | ~ m1_subset_1(X0,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14,c_1555,c_1830])).

cnf(c_1878,negated_conjecture,
    ( ~ m1_subset_1(X0,sK5)
    | ~ r2_hidden(k4_tarski(X0,sK7),sK6) ),
    inference(renaming,[status(thm)],[c_1877])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(k4_tarski(sK3(X1,X0),X0),X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2050,plain,
    ( ~ m1_subset_1(sK3(sK6,sK7),sK5)
    | ~ r2_hidden(sK7,k2_relat_1(sK6)) ),
    inference(resolution,[status(thm)],[c_1878,c_12])).

cnf(c_942,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(sK3(X1,X0),X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1669,plain,
    ( r2_hidden(k4_tarski(X0,sK7),sK6) != iProver_top
    | m1_subset_1(X0,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1533,c_1213,c_1531])).

cnf(c_1670,plain,
    ( m1_subset_1(X0,sK5) != iProver_top
    | r2_hidden(k4_tarski(X0,sK7),sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_1669])).

cnf(c_2019,plain,
    ( m1_subset_1(sK3(sK6,sK7),sK5) != iProver_top
    | r2_hidden(sK7,k2_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_942,c_1670])).

cnf(c_2038,plain,
    ( ~ m1_subset_1(sK3(sK6,sK7),sK5)
    | ~ r2_hidden(sK7,k2_relat_1(sK6)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2019])).

cnf(c_2053,plain,
    ( ~ m1_subset_1(sK3(sK6,sK7),sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2050,c_1830,c_2038])).

cnf(c_6,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_2065,plain,
    ( ~ r2_hidden(sK3(sK6,sK7),sK5) ),
    inference(resolution,[status(thm)],[c_2053,c_6])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1176,plain,
    ( r1_tarski(sK6,k2_zfmisc_1(sK5,sK4)) ),
    inference(resolution,[status(thm)],[c_8,c_17])).

cnf(c_1418,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK5,sK4))
    | ~ r2_hidden(X0,sK6) ),
    inference(resolution,[status(thm)],[c_2,c_1176])).

cnf(c_1697,plain,
    ( r2_hidden(X0,sK5)
    | ~ r2_hidden(k4_tarski(X0,X1),sK6) ),
    inference(resolution,[status(thm)],[c_5,c_1418])).

cnf(c_2541,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK6))
    | r2_hidden(sK3(sK6,X0),sK5) ),
    inference(resolution,[status(thm)],[c_1697,c_12])).

cnf(c_2664,plain,
    ( ~ r2_hidden(sK7,k2_relat_1(sK6)) ),
    inference(resolution,[status(thm)],[c_2065,c_2541])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2664,c_1830])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.33  % Computer   : n022.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 19:06:55 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running in FOF mode
% 2.48/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.48/1.00  
% 2.48/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.48/1.00  
% 2.48/1.00  ------  iProver source info
% 2.48/1.00  
% 2.48/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.48/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.48/1.00  git: non_committed_changes: false
% 2.48/1.00  git: last_make_outside_of_git: false
% 2.48/1.00  
% 2.48/1.00  ------ 
% 2.48/1.00  ------ Parsing...
% 2.48/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.48/1.00  
% 2.48/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.48/1.00  
% 2.48/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.48/1.00  
% 2.48/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.48/1.00  ------ Proving...
% 2.48/1.00  ------ Problem Properties 
% 2.48/1.00  
% 2.48/1.00  
% 2.48/1.00  clauses                                 18
% 2.48/1.00  conjectures                             4
% 2.48/1.00  EPR                                     2
% 2.48/1.00  Horn                                    14
% 2.48/1.00  unary                                   1
% 2.48/1.00  binary                                  12
% 2.48/1.00  lits                                    40
% 2.48/1.00  lits eq                                 3
% 2.48/1.00  fd_pure                                 0
% 2.48/1.00  fd_pseudo                               0
% 2.48/1.00  fd_cond                                 0
% 2.48/1.00  fd_pseudo_cond                          2
% 2.48/1.00  AC symbols                              0
% 2.48/1.00  
% 2.48/1.00  ------ Input Options Time Limit: Unbounded
% 2.48/1.00  
% 2.48/1.00  
% 2.48/1.00  ------ 
% 2.48/1.00  Current options:
% 2.48/1.00  ------ 
% 2.48/1.00  
% 2.48/1.00  
% 2.48/1.00  
% 2.48/1.00  
% 2.48/1.00  ------ Proving...
% 2.48/1.00  
% 2.48/1.00  
% 2.48/1.00  % SZS status Theorem for theBenchmark.p
% 2.48/1.00  
% 2.48/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.48/1.00  
% 2.48/1.00  fof(f7,conjecture,(
% 2.48/1.00    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ! [X3] : (r2_hidden(X3,k2_relset_1(X1,X0,X2)) <=> ? [X4] : (r2_hidden(k4_tarski(X4,X3),X2) & m1_subset_1(X4,X1))))))),
% 2.48/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.48/1.00  
% 2.48/1.00  fof(f8,negated_conjecture,(
% 2.48/1.00    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ! [X3] : (r2_hidden(X3,k2_relset_1(X1,X0,X2)) <=> ? [X4] : (r2_hidden(k4_tarski(X4,X3),X2) & m1_subset_1(X4,X1))))))),
% 2.48/1.00    inference(negated_conjecture,[],[f7])).
% 2.48/1.00  
% 2.48/1.00  fof(f9,plain,(
% 2.48/1.00    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ! [X3] : (r2_hidden(X3,k2_relset_1(X1,X0,X2)) <=> ? [X4] : (r2_hidden(k4_tarski(X4,X3),X2) & m1_subset_1(X4,X1))))),
% 2.48/1.00    inference(pure_predicate_removal,[],[f8])).
% 2.48/1.00  
% 2.48/1.00  fof(f13,plain,(
% 2.48/1.00    ? [X0,X1,X2] : (? [X3] : (r2_hidden(X3,k2_relset_1(X1,X0,X2)) <~> ? [X4] : (r2_hidden(k4_tarski(X4,X3),X2) & m1_subset_1(X4,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 2.48/1.00    inference(ennf_transformation,[],[f9])).
% 2.48/1.00  
% 2.48/1.00  fof(f27,plain,(
% 2.48/1.00    ? [X0,X1,X2] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X4,X3),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k2_relset_1(X1,X0,X2))) & (? [X4] : (r2_hidden(k4_tarski(X4,X3),X2) & m1_subset_1(X4,X1)) | r2_hidden(X3,k2_relset_1(X1,X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 2.48/1.00    inference(nnf_transformation,[],[f13])).
% 2.48/1.00  
% 2.48/1.00  fof(f28,plain,(
% 2.48/1.00    ? [X0,X1,X2] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X4,X3),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k2_relset_1(X1,X0,X2))) & (? [X5] : (r2_hidden(k4_tarski(X5,X3),X2) & m1_subset_1(X5,X1)) | r2_hidden(X3,k2_relset_1(X1,X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 2.48/1.00    inference(rectify,[],[f27])).
% 2.48/1.00  
% 2.48/1.00  fof(f31,plain,(
% 2.48/1.00    ( ! [X2,X3,X1] : (? [X5] : (r2_hidden(k4_tarski(X5,X3),X2) & m1_subset_1(X5,X1)) => (r2_hidden(k4_tarski(sK8,X3),X2) & m1_subset_1(sK8,X1))) )),
% 2.48/1.00    introduced(choice_axiom,[])).
% 2.48/1.00  
% 2.48/1.00  fof(f30,plain,(
% 2.48/1.00    ( ! [X2,X0,X1] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X4,X3),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k2_relset_1(X1,X0,X2))) & (? [X5] : (r2_hidden(k4_tarski(X5,X3),X2) & m1_subset_1(X5,X1)) | r2_hidden(X3,k2_relset_1(X1,X0,X2)))) => ((! [X4] : (~r2_hidden(k4_tarski(X4,sK7),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(sK7,k2_relset_1(X1,X0,X2))) & (? [X5] : (r2_hidden(k4_tarski(X5,sK7),X2) & m1_subset_1(X5,X1)) | r2_hidden(sK7,k2_relset_1(X1,X0,X2))))) )),
% 2.48/1.00    introduced(choice_axiom,[])).
% 2.48/1.00  
% 2.48/1.00  fof(f29,plain,(
% 2.48/1.00    ? [X0,X1,X2] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X4,X3),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k2_relset_1(X1,X0,X2))) & (? [X5] : (r2_hidden(k4_tarski(X5,X3),X2) & m1_subset_1(X5,X1)) | r2_hidden(X3,k2_relset_1(X1,X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) => (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X4,X3),sK6) | ~m1_subset_1(X4,sK5)) | ~r2_hidden(X3,k2_relset_1(sK5,sK4,sK6))) & (? [X5] : (r2_hidden(k4_tarski(X5,X3),sK6) & m1_subset_1(X5,sK5)) | r2_hidden(X3,k2_relset_1(sK5,sK4,sK6)))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))))),
% 2.48/1.00    introduced(choice_axiom,[])).
% 2.48/1.00  
% 2.48/1.00  fof(f32,plain,(
% 2.48/1.00    ((! [X4] : (~r2_hidden(k4_tarski(X4,sK7),sK6) | ~m1_subset_1(X4,sK5)) | ~r2_hidden(sK7,k2_relset_1(sK5,sK4,sK6))) & ((r2_hidden(k4_tarski(sK8,sK7),sK6) & m1_subset_1(sK8,sK5)) | r2_hidden(sK7,k2_relset_1(sK5,sK4,sK6)))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))),
% 2.48/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f28,f31,f30,f29])).
% 2.48/1.00  
% 2.48/1.00  fof(f50,plain,(
% 2.48/1.00    ( ! [X4] : (~r2_hidden(k4_tarski(X4,sK7),sK6) | ~m1_subset_1(X4,sK5) | ~r2_hidden(sK7,k2_relset_1(sK5,sK4,sK6))) )),
% 2.48/1.00    inference(cnf_transformation,[],[f32])).
% 2.48/1.00  
% 2.48/1.00  fof(f47,plain,(
% 2.48/1.00    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))),
% 2.48/1.00    inference(cnf_transformation,[],[f32])).
% 2.48/1.00  
% 2.48/1.00  fof(f6,axiom,(
% 2.48/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.48/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.48/1.00  
% 2.48/1.00  fof(f12,plain,(
% 2.48/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.48/1.00    inference(ennf_transformation,[],[f6])).
% 2.48/1.00  
% 2.48/1.00  fof(f46,plain,(
% 2.48/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.48/1.00    inference(cnf_transformation,[],[f12])).
% 2.48/1.00  
% 2.48/1.00  fof(f48,plain,(
% 2.48/1.00    m1_subset_1(sK8,sK5) | r2_hidden(sK7,k2_relset_1(sK5,sK4,sK6))),
% 2.48/1.00    inference(cnf_transformation,[],[f32])).
% 2.48/1.00  
% 2.48/1.00  fof(f5,axiom,(
% 2.48/1.00    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 2.48/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.48/1.00  
% 2.48/1.00  fof(f21,plain,(
% 2.48/1.00    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 2.48/1.00    inference(nnf_transformation,[],[f5])).
% 2.48/1.00  
% 2.48/1.00  fof(f22,plain,(
% 2.48/1.00    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 2.48/1.00    inference(rectify,[],[f21])).
% 2.48/1.00  
% 2.48/1.00  fof(f25,plain,(
% 2.48/1.00    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK3(X0,X5),X5),X0))),
% 2.48/1.00    introduced(choice_axiom,[])).
% 2.48/1.00  
% 2.48/1.00  fof(f24,plain,(
% 2.48/1.00    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) => r2_hidden(k4_tarski(sK2(X0,X1),X2),X0))) )),
% 2.48/1.00    introduced(choice_axiom,[])).
% 2.48/1.00  
% 2.48/1.00  fof(f23,plain,(
% 2.48/1.00    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK1(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 2.48/1.00    introduced(choice_axiom,[])).
% 2.48/1.00  
% 2.48/1.00  fof(f26,plain,(
% 2.48/1.00    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK3(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 2.48/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f22,f25,f24,f23])).
% 2.48/1.00  
% 2.48/1.00  fof(f43,plain,(
% 2.48/1.00    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 2.48/1.00    inference(cnf_transformation,[],[f26])).
% 2.48/1.00  
% 2.48/1.00  fof(f51,plain,(
% 2.48/1.00    ( ! [X6,X0,X5] : (r2_hidden(X5,k2_relat_1(X0)) | ~r2_hidden(k4_tarski(X6,X5),X0)) )),
% 2.48/1.00    inference(equality_resolution,[],[f43])).
% 2.48/1.00  
% 2.48/1.00  fof(f49,plain,(
% 2.48/1.00    r2_hidden(k4_tarski(sK8,sK7),sK6) | r2_hidden(sK7,k2_relset_1(sK5,sK4,sK6))),
% 2.48/1.00    inference(cnf_transformation,[],[f32])).
% 2.48/1.00  
% 2.48/1.00  fof(f42,plain,(
% 2.48/1.00    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK3(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 2.48/1.00    inference(cnf_transformation,[],[f26])).
% 2.48/1.00  
% 2.48/1.00  fof(f52,plain,(
% 2.48/1.00    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK3(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 2.48/1.00    inference(equality_resolution,[],[f42])).
% 2.48/1.00  
% 2.48/1.00  fof(f3,axiom,(
% 2.48/1.00    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 2.48/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.48/1.00  
% 2.48/1.00  fof(f11,plain,(
% 2.48/1.00    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 2.48/1.00    inference(ennf_transformation,[],[f3])).
% 2.48/1.00  
% 2.48/1.00  fof(f39,plain,(
% 2.48/1.00    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 2.48/1.00    inference(cnf_transformation,[],[f11])).
% 2.48/1.00  
% 2.48/1.00  fof(f2,axiom,(
% 2.48/1.00    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 2.48/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.48/1.00  
% 2.48/1.00  fof(f18,plain,(
% 2.48/1.00    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 2.48/1.00    inference(nnf_transformation,[],[f2])).
% 2.48/1.00  
% 2.48/1.00  fof(f19,plain,(
% 2.48/1.00    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 2.48/1.00    inference(flattening,[],[f18])).
% 2.48/1.00  
% 2.48/1.00  fof(f36,plain,(
% 2.48/1.00    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 2.48/1.00    inference(cnf_transformation,[],[f19])).
% 2.48/1.00  
% 2.48/1.00  fof(f1,axiom,(
% 2.48/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.48/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.48/1.00  
% 2.48/1.00  fof(f10,plain,(
% 2.48/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.48/1.00    inference(ennf_transformation,[],[f1])).
% 2.48/1.00  
% 2.48/1.00  fof(f14,plain,(
% 2.48/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.48/1.00    inference(nnf_transformation,[],[f10])).
% 2.48/1.00  
% 2.48/1.00  fof(f15,plain,(
% 2.48/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.48/1.00    inference(rectify,[],[f14])).
% 2.48/1.00  
% 2.48/1.00  fof(f16,plain,(
% 2.48/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.48/1.00    introduced(choice_axiom,[])).
% 2.48/1.00  
% 2.48/1.00  fof(f17,plain,(
% 2.48/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.48/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).
% 2.48/1.00  
% 2.48/1.00  fof(f33,plain,(
% 2.48/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.48/1.00    inference(cnf_transformation,[],[f17])).
% 2.48/1.00  
% 2.48/1.00  fof(f4,axiom,(
% 2.48/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.48/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.48/1.00  
% 2.48/1.00  fof(f20,plain,(
% 2.48/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.48/1.00    inference(nnf_transformation,[],[f4])).
% 2.48/1.00  
% 2.48/1.00  fof(f40,plain,(
% 2.48/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.48/1.00    inference(cnf_transformation,[],[f20])).
% 2.48/1.00  
% 2.48/1.00  cnf(c_14,negated_conjecture,
% 2.48/1.00      ( ~ m1_subset_1(X0,sK5)
% 2.48/1.00      | ~ r2_hidden(k4_tarski(X0,sK7),sK6)
% 2.48/1.00      | ~ r2_hidden(sK7,k2_relset_1(sK5,sK4,sK6)) ),
% 2.48/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.48/1.00  
% 2.48/1.00  cnf(c_17,negated_conjecture,
% 2.48/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) ),
% 2.48/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.48/1.00  
% 2.48/1.00  cnf(c_937,plain,
% 2.48/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) = iProver_top ),
% 2.48/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.48/1.00  
% 2.48/1.00  cnf(c_13,plain,
% 2.48/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.48/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.48/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.48/1.00  
% 2.48/1.00  cnf(c_941,plain,
% 2.48/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.48/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.48/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.48/1.00  
% 2.48/1.00  cnf(c_1402,plain,
% 2.48/1.00      ( k2_relset_1(sK5,sK4,sK6) = k2_relat_1(sK6) ),
% 2.48/1.00      inference(superposition,[status(thm)],[c_937,c_941]) ).
% 2.48/1.00  
% 2.48/1.00  cnf(c_940,plain,
% 2.48/1.00      ( m1_subset_1(X0,sK5) != iProver_top
% 2.48/1.00      | r2_hidden(k4_tarski(X0,sK7),sK6) != iProver_top
% 2.48/1.00      | r2_hidden(sK7,k2_relset_1(sK5,sK4,sK6)) != iProver_top ),
% 2.48/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.48/1.00  
% 2.48/1.00  cnf(c_1533,plain,
% 2.48/1.00      ( m1_subset_1(X0,sK5) != iProver_top
% 2.48/1.00      | r2_hidden(k4_tarski(X0,sK7),sK6) != iProver_top
% 2.48/1.00      | r2_hidden(sK7,k2_relat_1(sK6)) != iProver_top ),
% 2.48/1.00      inference(demodulation,[status(thm)],[c_1402,c_940]) ).
% 2.48/1.00  
% 2.48/1.00  cnf(c_1555,plain,
% 2.48/1.00      ( ~ m1_subset_1(X0,sK5)
% 2.48/1.00      | ~ r2_hidden(k4_tarski(X0,sK7),sK6)
% 2.48/1.00      | ~ r2_hidden(sK7,k2_relat_1(sK6)) ),
% 2.48/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1533]) ).
% 2.48/1.00  
% 2.48/1.00  cnf(c_16,negated_conjecture,
% 2.48/1.00      ( m1_subset_1(sK8,sK5) | r2_hidden(sK7,k2_relset_1(sK5,sK4,sK6)) ),
% 2.48/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.48/1.00  
% 2.48/1.00  cnf(c_938,plain,
% 2.48/1.00      ( m1_subset_1(sK8,sK5) = iProver_top
% 2.48/1.00      | r2_hidden(sK7,k2_relset_1(sK5,sK4,sK6)) = iProver_top ),
% 2.48/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.48/1.00  
% 2.48/1.00  cnf(c_1532,plain,
% 2.48/1.00      ( m1_subset_1(sK8,sK5) = iProver_top
% 2.48/1.00      | r2_hidden(sK7,k2_relat_1(sK6)) = iProver_top ),
% 2.48/1.00      inference(demodulation,[status(thm)],[c_1402,c_938]) ).
% 2.48/1.00  
% 2.48/1.00  cnf(c_11,plain,
% 2.48/1.00      ( r2_hidden(X0,k2_relat_1(X1)) | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
% 2.48/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.48/1.00  
% 2.48/1.00  cnf(c_1212,plain,
% 2.48/1.00      ( ~ r2_hidden(k4_tarski(sK8,sK7),sK6)
% 2.48/1.00      | r2_hidden(sK7,k2_relat_1(sK6)) ),
% 2.48/1.00      inference(instantiation,[status(thm)],[c_11]) ).
% 2.48/1.00  
% 2.48/1.00  cnf(c_1213,plain,
% 2.48/1.00      ( r2_hidden(k4_tarski(sK8,sK7),sK6) != iProver_top
% 2.48/1.00      | r2_hidden(sK7,k2_relat_1(sK6)) = iProver_top ),
% 2.48/1.00      inference(predicate_to_equality,[status(thm)],[c_1212]) ).
% 2.48/1.00  
% 2.48/1.00  cnf(c_15,negated_conjecture,
% 2.48/1.00      ( r2_hidden(k4_tarski(sK8,sK7),sK6)
% 2.48/1.00      | r2_hidden(sK7,k2_relset_1(sK5,sK4,sK6)) ),
% 2.48/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.48/1.00  
% 2.48/1.00  cnf(c_939,plain,
% 2.48/1.00      ( r2_hidden(k4_tarski(sK8,sK7),sK6) = iProver_top
% 2.48/1.00      | r2_hidden(sK7,k2_relset_1(sK5,sK4,sK6)) = iProver_top ),
% 2.48/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.48/1.00  
% 2.48/1.00  cnf(c_1531,plain,
% 2.48/1.00      ( r2_hidden(k4_tarski(sK8,sK7),sK6) = iProver_top
% 2.48/1.00      | r2_hidden(sK7,k2_relat_1(sK6)) = iProver_top ),
% 2.48/1.00      inference(demodulation,[status(thm)],[c_1402,c_939]) ).
% 2.48/1.00  
% 2.48/1.00  cnf(c_1828,plain,
% 2.48/1.00      ( r2_hidden(sK7,k2_relat_1(sK6)) = iProver_top ),
% 2.48/1.00      inference(global_propositional_subsumption,
% 2.48/1.00                [status(thm)],
% 2.48/1.00                [c_1532,c_1213,c_1531]) ).
% 2.48/1.00  
% 2.48/1.00  cnf(c_1830,plain,
% 2.48/1.00      ( r2_hidden(sK7,k2_relat_1(sK6)) ),
% 2.48/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1828]) ).
% 2.48/1.00  
% 2.48/1.00  cnf(c_1877,plain,
% 2.48/1.00      ( ~ r2_hidden(k4_tarski(X0,sK7),sK6) | ~ m1_subset_1(X0,sK5) ),
% 2.48/1.00      inference(global_propositional_subsumption,
% 2.48/1.00                [status(thm)],
% 2.48/1.00                [c_14,c_1555,c_1830]) ).
% 2.48/1.00  
% 2.48/1.00  cnf(c_1878,negated_conjecture,
% 2.48/1.00      ( ~ m1_subset_1(X0,sK5) | ~ r2_hidden(k4_tarski(X0,sK7),sK6) ),
% 2.48/1.00      inference(renaming,[status(thm)],[c_1877]) ).
% 2.48/1.00  
% 2.48/1.00  cnf(c_12,plain,
% 2.48/1.00      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 2.48/1.00      | r2_hidden(k4_tarski(sK3(X1,X0),X0),X1) ),
% 2.48/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.48/1.00  
% 2.48/1.00  cnf(c_2050,plain,
% 2.48/1.00      ( ~ m1_subset_1(sK3(sK6,sK7),sK5)
% 2.48/1.00      | ~ r2_hidden(sK7,k2_relat_1(sK6)) ),
% 2.48/1.00      inference(resolution,[status(thm)],[c_1878,c_12]) ).
% 2.48/1.00  
% 2.48/1.00  cnf(c_942,plain,
% 2.48/1.00      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 2.48/1.00      | r2_hidden(k4_tarski(sK3(X1,X0),X0),X1) = iProver_top ),
% 2.48/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.48/1.00  
% 2.48/1.00  cnf(c_1669,plain,
% 2.48/1.00      ( r2_hidden(k4_tarski(X0,sK7),sK6) != iProver_top
% 2.48/1.00      | m1_subset_1(X0,sK5) != iProver_top ),
% 2.48/1.00      inference(global_propositional_subsumption,
% 2.48/1.00                [status(thm)],
% 2.48/1.00                [c_1533,c_1213,c_1531]) ).
% 2.48/1.00  
% 2.48/1.00  cnf(c_1670,plain,
% 2.48/1.00      ( m1_subset_1(X0,sK5) != iProver_top
% 2.48/1.00      | r2_hidden(k4_tarski(X0,sK7),sK6) != iProver_top ),
% 2.48/1.00      inference(renaming,[status(thm)],[c_1669]) ).
% 2.48/1.00  
% 2.48/1.00  cnf(c_2019,plain,
% 2.48/1.00      ( m1_subset_1(sK3(sK6,sK7),sK5) != iProver_top
% 2.48/1.00      | r2_hidden(sK7,k2_relat_1(sK6)) != iProver_top ),
% 2.48/1.00      inference(superposition,[status(thm)],[c_942,c_1670]) ).
% 2.48/1.00  
% 2.48/1.00  cnf(c_2038,plain,
% 2.48/1.00      ( ~ m1_subset_1(sK3(sK6,sK7),sK5)
% 2.48/1.00      | ~ r2_hidden(sK7,k2_relat_1(sK6)) ),
% 2.48/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_2019]) ).
% 2.48/1.00  
% 2.48/1.00  cnf(c_2053,plain,
% 2.48/1.00      ( ~ m1_subset_1(sK3(sK6,sK7),sK5) ),
% 2.48/1.00      inference(global_propositional_subsumption,
% 2.48/1.00                [status(thm)],
% 2.48/1.00                [c_2050,c_1830,c_2038]) ).
% 2.48/1.00  
% 2.48/1.00  cnf(c_6,plain,
% 2.48/1.00      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 2.48/1.00      inference(cnf_transformation,[],[f39]) ).
% 2.48/1.00  
% 2.48/1.00  cnf(c_2065,plain,
% 2.48/1.00      ( ~ r2_hidden(sK3(sK6,sK7),sK5) ),
% 2.48/1.00      inference(resolution,[status(thm)],[c_2053,c_6]) ).
% 2.48/1.00  
% 2.48/1.00  cnf(c_5,plain,
% 2.48/1.00      ( r2_hidden(X0,X1)
% 2.48/1.00      | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
% 2.48/1.00      inference(cnf_transformation,[],[f36]) ).
% 2.48/1.00  
% 2.48/1.00  cnf(c_2,plain,
% 2.48/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 2.48/1.00      inference(cnf_transformation,[],[f33]) ).
% 2.48/1.00  
% 2.48/1.00  cnf(c_8,plain,
% 2.48/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.48/1.00      inference(cnf_transformation,[],[f40]) ).
% 2.48/1.00  
% 2.48/1.00  cnf(c_1176,plain,
% 2.48/1.00      ( r1_tarski(sK6,k2_zfmisc_1(sK5,sK4)) ),
% 2.48/1.00      inference(resolution,[status(thm)],[c_8,c_17]) ).
% 2.48/1.00  
% 2.48/1.00  cnf(c_1418,plain,
% 2.48/1.00      ( r2_hidden(X0,k2_zfmisc_1(sK5,sK4)) | ~ r2_hidden(X0,sK6) ),
% 2.48/1.00      inference(resolution,[status(thm)],[c_2,c_1176]) ).
% 2.48/1.00  
% 2.48/1.00  cnf(c_1697,plain,
% 2.48/1.00      ( r2_hidden(X0,sK5) | ~ r2_hidden(k4_tarski(X0,X1),sK6) ),
% 2.48/1.00      inference(resolution,[status(thm)],[c_5,c_1418]) ).
% 2.48/1.00  
% 2.48/1.00  cnf(c_2541,plain,
% 2.48/1.00      ( ~ r2_hidden(X0,k2_relat_1(sK6)) | r2_hidden(sK3(sK6,X0),sK5) ),
% 2.48/1.00      inference(resolution,[status(thm)],[c_1697,c_12]) ).
% 2.48/1.00  
% 2.48/1.00  cnf(c_2664,plain,
% 2.48/1.00      ( ~ r2_hidden(sK7,k2_relat_1(sK6)) ),
% 2.48/1.00      inference(resolution,[status(thm)],[c_2065,c_2541]) ).
% 2.48/1.00  
% 2.48/1.00  cnf(contradiction,plain,
% 2.48/1.00      ( $false ),
% 2.48/1.00      inference(minisat,[status(thm)],[c_2664,c_1830]) ).
% 2.48/1.00  
% 2.48/1.00  
% 2.48/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.48/1.00  
% 2.48/1.00  ------                               Statistics
% 2.48/1.00  
% 2.48/1.00  ------ Selected
% 2.48/1.00  
% 2.48/1.00  total_time:                             0.119
% 2.48/1.00  
%------------------------------------------------------------------------------
