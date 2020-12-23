%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:56:19 EST 2020

% Result     : Theorem 2.62s
% Output     : CNFRefutation 2.62s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 463 expanded)
%              Number of clauses        :   41 ( 116 expanded)
%              Number of leaves         :   14 ( 122 expanded)
%              Depth                    :   21
%              Number of atoms          :  298 (2501 expanded)
%              Number of equality atoms :   42 ( 187 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
             => ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => ( r2_hidden(X3,k1_relset_1(X0,X1,X2))
                  <=> ? [X4] :
                        ( r2_hidden(k4_tarski(X3,X4),X2)
                        & m1_subset_1(X4,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
               => ! [X3] :
                    ( m1_subset_1(X3,X0)
                   => ( r2_hidden(X3,k1_relset_1(X0,X1,X2))
                    <=> ? [X4] :
                          ( r2_hidden(k4_tarski(X3,X4),X2)
                          & m1_subset_1(X4,X1) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f9,plain,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ! [X3] :
            ( m1_subset_1(X3,X0)
           => ( r2_hidden(X3,k1_relset_1(X0,X1,X2))
            <=> ? [X4] :
                  ( r2_hidden(k4_tarski(X3,X4),X2)
                  & m1_subset_1(X4,X1) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( r2_hidden(X3,k1_relset_1(X0,X1,X2))
          <~> ? [X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
                & m1_subset_1(X4,X1) ) )
          & m1_subset_1(X3,X0) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(k4_tarski(X3,X4),X2)
                | ~ m1_subset_1(X4,X1) )
            | ~ r2_hidden(X3,k1_relset_1(X0,X1,X2)) )
          & ( ? [X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
                & m1_subset_1(X4,X1) )
            | r2_hidden(X3,k1_relset_1(X0,X1,X2)) )
          & m1_subset_1(X3,X0) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(k4_tarski(X3,X4),X2)
                | ~ m1_subset_1(X4,X1) )
            | ~ r2_hidden(X3,k1_relset_1(X0,X1,X2)) )
          & ( ? [X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
                & m1_subset_1(X4,X1) )
            | r2_hidden(X3,k1_relset_1(X0,X1,X2)) )
          & m1_subset_1(X3,X0) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f27])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(k4_tarski(X3,X4),X2)
                | ~ m1_subset_1(X4,X1) )
            | ~ r2_hidden(X3,k1_relset_1(X0,X1,X2)) )
          & ( ? [X5] :
                ( r2_hidden(k4_tarski(X3,X5),X2)
                & m1_subset_1(X5,X1) )
            | r2_hidden(X3,k1_relset_1(X0,X1,X2)) )
          & m1_subset_1(X3,X0) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(rectify,[],[f28])).

fof(f32,plain,(
    ! [X2,X3,X1] :
      ( ? [X5] :
          ( r2_hidden(k4_tarski(X3,X5),X2)
          & m1_subset_1(X5,X1) )
     => ( r2_hidden(k4_tarski(X3,sK8),X2)
        & m1_subset_1(sK8,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(k4_tarski(X3,X4),X2)
                | ~ m1_subset_1(X4,X1) )
            | ~ r2_hidden(X3,k1_relset_1(X0,X1,X2)) )
          & ( ? [X5] :
                ( r2_hidden(k4_tarski(X3,X5),X2)
                & m1_subset_1(X5,X1) )
            | r2_hidden(X3,k1_relset_1(X0,X1,X2)) )
          & m1_subset_1(X3,X0) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(k4_tarski(sK7,X4),X2)
              | ~ m1_subset_1(X4,X1) )
          | ~ r2_hidden(sK7,k1_relset_1(X0,X1,X2)) )
        & ( ? [X5] :
              ( r2_hidden(k4_tarski(sK7,X5),X2)
              & m1_subset_1(X5,X1) )
          | r2_hidden(sK7,k1_relset_1(X0,X1,X2)) )
        & m1_subset_1(sK7,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ( ! [X4] :
                  ( ~ r2_hidden(k4_tarski(X3,X4),X2)
                  | ~ m1_subset_1(X4,X1) )
              | ~ r2_hidden(X3,k1_relset_1(X0,X1,X2)) )
            & ( ? [X5] :
                  ( r2_hidden(k4_tarski(X3,X5),X2)
                  & m1_subset_1(X5,X1) )
              | r2_hidden(X3,k1_relset_1(X0,X1,X2)) )
            & m1_subset_1(X3,X0) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(k4_tarski(X3,X4),sK6)
                | ~ m1_subset_1(X4,sK5) )
            | ~ r2_hidden(X3,k1_relset_1(sK4,sK5,sK6)) )
          & ( ? [X5] :
                ( r2_hidden(k4_tarski(X3,X5),sK6)
                & m1_subset_1(X5,sK5) )
            | r2_hidden(X3,k1_relset_1(sK4,sK5,sK6)) )
          & m1_subset_1(X3,sK4) )
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ( ! [X4] :
          ( ~ r2_hidden(k4_tarski(sK7,X4),sK6)
          | ~ m1_subset_1(X4,sK5) )
      | ~ r2_hidden(sK7,k1_relset_1(sK4,sK5,sK6)) )
    & ( ( r2_hidden(k4_tarski(sK7,sK8),sK6)
        & m1_subset_1(sK8,sK5) )
      | r2_hidden(sK7,k1_relset_1(sK4,sK5,sK6)) )
    & m1_subset_1(sK7,sK4)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f29,f32,f31,f30])).

fof(f52,plain,(
    ! [X4] :
      ( ~ r2_hidden(k4_tarski(sK7,X4),sK6)
      | ~ m1_subset_1(X4,sK5)
      | ~ r2_hidden(sK7,k1_relset_1(sK4,sK5,sK6)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f48,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f33])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f50,plain,
    ( m1_subset_1(sK8,sK5)
    | r2_hidden(sK7,k1_relset_1(sK4,sK5,sK6)) ),
    inference(cnf_transformation,[],[f33])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f25,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK2(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK1(X0,X1),X3),X0)
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK1(X0,X1),X4),X0)
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK1(X0,X1),X3),X0)
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f22,f25,f24,f23])).

fof(f44,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f53,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f51,plain,
    ( r2_hidden(k4_tarski(sK7,sK8),sK6)
    | r2_hidden(sK7,k1_relset_1(sK4,sK5,sK6)) ),
    inference(cnf_transformation,[],[f33])).

fof(f43,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f54,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f43])).

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

fof(f40,plain,(
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

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
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

fof(f34,plain,(
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

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_14,negated_conjecture,
    ( ~ m1_subset_1(X0,sK5)
    | ~ r2_hidden(k4_tarski(sK7,X0),sK6)
    | ~ r2_hidden(sK7,k1_relset_1(sK4,sK5,sK6)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1005,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1010,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1480,plain,
    ( k1_relset_1(sK4,sK5,sK6) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_1005,c_1010])).

cnf(c_1009,plain,
    ( m1_subset_1(X0,sK5) != iProver_top
    | r2_hidden(k4_tarski(sK7,X0),sK6) != iProver_top
    | r2_hidden(sK7,k1_relset_1(sK4,sK5,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1634,plain,
    ( m1_subset_1(X0,sK5) != iProver_top
    | r2_hidden(k4_tarski(sK7,X0),sK6) != iProver_top
    | r2_hidden(sK7,k1_relat_1(sK6)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1480,c_1009])).

cnf(c_1651,plain,
    ( ~ m1_subset_1(X0,sK5)
    | ~ r2_hidden(k4_tarski(sK7,X0),sK6)
    | ~ r2_hidden(sK7,k1_relat_1(sK6)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1634])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK8,sK5)
    | r2_hidden(sK7,k1_relset_1(sK4,sK5,sK6)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1007,plain,
    ( m1_subset_1(sK8,sK5) = iProver_top
    | r2_hidden(sK7,k1_relset_1(sK4,sK5,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1633,plain,
    ( m1_subset_1(sK8,sK5) = iProver_top
    | r2_hidden(sK7,k1_relat_1(sK6)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1480,c_1007])).

cnf(c_11,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1415,plain,
    ( ~ r2_hidden(k4_tarski(sK7,sK8),sK6)
    | r2_hidden(sK7,k1_relat_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1416,plain,
    ( r2_hidden(k4_tarski(sK7,sK8),sK6) != iProver_top
    | r2_hidden(sK7,k1_relat_1(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1415])).

cnf(c_15,negated_conjecture,
    ( r2_hidden(k4_tarski(sK7,sK8),sK6)
    | r2_hidden(sK7,k1_relset_1(sK4,sK5,sK6)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1008,plain,
    ( r2_hidden(k4_tarski(sK7,sK8),sK6) = iProver_top
    | r2_hidden(sK7,k1_relset_1(sK4,sK5,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1632,plain,
    ( r2_hidden(k4_tarski(sK7,sK8),sK6) = iProver_top
    | r2_hidden(sK7,k1_relat_1(sK6)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1480,c_1008])).

cnf(c_1916,plain,
    ( r2_hidden(sK7,k1_relat_1(sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1633,c_1416,c_1632])).

cnf(c_1918,plain,
    ( r2_hidden(sK7,k1_relat_1(sK6)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1916])).

cnf(c_2064,plain,
    ( ~ r2_hidden(k4_tarski(sK7,X0),sK6)
    | ~ m1_subset_1(X0,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14,c_1651,c_1918])).

cnf(c_2065,negated_conjecture,
    ( ~ m1_subset_1(X0,sK5)
    | ~ r2_hidden(k4_tarski(sK7,X0),sK6) ),
    inference(renaming,[status(thm)],[c_2064])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,sK3(X1,X0)),X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2080,plain,
    ( ~ m1_subset_1(sK3(sK6,sK7),sK5)
    | ~ r2_hidden(sK7,k1_relat_1(sK6)) ),
    inference(resolution,[status(thm)],[c_2065,c_12])).

cnf(c_1011,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK3(X1,X0)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1761,plain,
    ( r2_hidden(k4_tarski(sK7,X0),sK6) != iProver_top
    | m1_subset_1(X0,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1634,c_1416,c_1632])).

cnf(c_1762,plain,
    ( m1_subset_1(X0,sK5) != iProver_top
    | r2_hidden(k4_tarski(sK7,X0),sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_1761])).

cnf(c_2038,plain,
    ( m1_subset_1(sK3(sK6,sK7),sK5) != iProver_top
    | r2_hidden(sK7,k1_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1011,c_1762])).

cnf(c_2057,plain,
    ( ~ m1_subset_1(sK3(sK6,sK7),sK5)
    | ~ r2_hidden(sK7,k1_relat_1(sK6)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2038])).

cnf(c_2083,plain,
    ( ~ m1_subset_1(sK3(sK6,sK7),sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2080,c_1918,c_2057])).

cnf(c_6,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_2189,plain,
    ( ~ r2_hidden(sK3(sK6,sK7),sK5) ),
    inference(resolution,[status(thm)],[c_2083,c_6])).

cnf(c_4,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1275,plain,
    ( r1_tarski(sK6,k2_zfmisc_1(sK4,sK5)) ),
    inference(resolution,[status(thm)],[c_8,c_18])).

cnf(c_1496,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK4,sK5))
    | ~ r2_hidden(X0,sK6) ),
    inference(resolution,[status(thm)],[c_2,c_1275])).

cnf(c_1784,plain,
    ( r2_hidden(X0,sK5)
    | ~ r2_hidden(k4_tarski(X1,X0),sK6) ),
    inference(resolution,[status(thm)],[c_4,c_1496])).

cnf(c_2425,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK6))
    | r2_hidden(sK3(sK6,X0),sK5) ),
    inference(resolution,[status(thm)],[c_1784,c_12])).

cnf(c_2711,plain,
    ( ~ r2_hidden(sK7,k1_relat_1(sK6)) ),
    inference(resolution,[status(thm)],[c_2189,c_2425])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2711,c_1918])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:21:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.62/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.62/0.98  
% 2.62/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.62/0.98  
% 2.62/0.98  ------  iProver source info
% 2.62/0.98  
% 2.62/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.62/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.62/0.98  git: non_committed_changes: false
% 2.62/0.98  git: last_make_outside_of_git: false
% 2.62/0.98  
% 2.62/0.98  ------ 
% 2.62/0.98  ------ Parsing...
% 2.62/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.62/0.98  
% 2.62/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.62/0.98  
% 2.62/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.62/0.98  
% 2.62/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.62/0.98  ------ Proving...
% 2.62/0.98  ------ Problem Properties 
% 2.62/0.98  
% 2.62/0.98  
% 2.62/0.98  clauses                                 19
% 2.62/0.98  conjectures                             5
% 2.62/0.98  EPR                                     3
% 2.62/0.98  Horn                                    15
% 2.62/0.98  unary                                   2
% 2.62/0.98  binary                                  12
% 2.62/0.98  lits                                    41
% 2.62/0.98  lits eq                                 3
% 2.62/0.98  fd_pure                                 0
% 2.62/0.98  fd_pseudo                               0
% 2.62/0.98  fd_cond                                 0
% 2.62/0.98  fd_pseudo_cond                          2
% 2.62/0.98  AC symbols                              0
% 2.62/0.98  
% 2.62/0.98  ------ Input Options Time Limit: Unbounded
% 2.62/0.98  
% 2.62/0.98  
% 2.62/0.98  ------ 
% 2.62/0.98  Current options:
% 2.62/0.98  ------ 
% 2.62/0.98  
% 2.62/0.98  
% 2.62/0.98  
% 2.62/0.98  
% 2.62/0.98  ------ Proving...
% 2.62/0.98  
% 2.62/0.98  
% 2.62/0.98  % SZS status Theorem for theBenchmark.p
% 2.62/0.98  
% 2.62/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.62/0.98  
% 2.62/0.98  fof(f7,conjecture,(
% 2.62/0.98    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,k1_relset_1(X0,X1,X2)) <=> ? [X4] : (r2_hidden(k4_tarski(X3,X4),X2) & m1_subset_1(X4,X1)))))))),
% 2.62/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.62/0.98  
% 2.62/0.98  fof(f8,negated_conjecture,(
% 2.62/0.98    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,k1_relset_1(X0,X1,X2)) <=> ? [X4] : (r2_hidden(k4_tarski(X3,X4),X2) & m1_subset_1(X4,X1)))))))),
% 2.62/0.98    inference(negated_conjecture,[],[f7])).
% 2.62/0.98  
% 2.62/0.98  fof(f9,plain,(
% 2.62/0.98    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,k1_relset_1(X0,X1,X2)) <=> ? [X4] : (r2_hidden(k4_tarski(X3,X4),X2) & m1_subset_1(X4,X1)))))),
% 2.62/0.98    inference(pure_predicate_removal,[],[f8])).
% 2.62/0.98  
% 2.62/0.98  fof(f13,plain,(
% 2.62/0.98    ? [X0,X1,X2] : (? [X3] : ((r2_hidden(X3,k1_relset_1(X0,X1,X2)) <~> ? [X4] : (r2_hidden(k4_tarski(X3,X4),X2) & m1_subset_1(X4,X1))) & m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.62/0.98    inference(ennf_transformation,[],[f9])).
% 2.62/0.98  
% 2.62/0.98  fof(f27,plain,(
% 2.62/0.98    ? [X0,X1,X2] : (? [X3] : (((! [X4] : (~r2_hidden(k4_tarski(X3,X4),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k1_relset_1(X0,X1,X2))) & (? [X4] : (r2_hidden(k4_tarski(X3,X4),X2) & m1_subset_1(X4,X1)) | r2_hidden(X3,k1_relset_1(X0,X1,X2)))) & m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.62/0.98    inference(nnf_transformation,[],[f13])).
% 2.62/0.98  
% 2.62/0.98  fof(f28,plain,(
% 2.62/0.98    ? [X0,X1,X2] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X3,X4),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k1_relset_1(X0,X1,X2))) & (? [X4] : (r2_hidden(k4_tarski(X3,X4),X2) & m1_subset_1(X4,X1)) | r2_hidden(X3,k1_relset_1(X0,X1,X2))) & m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.62/0.98    inference(flattening,[],[f27])).
% 2.62/0.98  
% 2.62/0.98  fof(f29,plain,(
% 2.62/0.98    ? [X0,X1,X2] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X3,X4),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k1_relset_1(X0,X1,X2))) & (? [X5] : (r2_hidden(k4_tarski(X3,X5),X2) & m1_subset_1(X5,X1)) | r2_hidden(X3,k1_relset_1(X0,X1,X2))) & m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.62/0.98    inference(rectify,[],[f28])).
% 2.62/0.98  
% 2.62/0.98  fof(f32,plain,(
% 2.62/0.98    ( ! [X2,X3,X1] : (? [X5] : (r2_hidden(k4_tarski(X3,X5),X2) & m1_subset_1(X5,X1)) => (r2_hidden(k4_tarski(X3,sK8),X2) & m1_subset_1(sK8,X1))) )),
% 2.62/0.98    introduced(choice_axiom,[])).
% 2.62/0.98  
% 2.62/0.98  fof(f31,plain,(
% 2.62/0.98    ( ! [X2,X0,X1] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X3,X4),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k1_relset_1(X0,X1,X2))) & (? [X5] : (r2_hidden(k4_tarski(X3,X5),X2) & m1_subset_1(X5,X1)) | r2_hidden(X3,k1_relset_1(X0,X1,X2))) & m1_subset_1(X3,X0)) => ((! [X4] : (~r2_hidden(k4_tarski(sK7,X4),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(sK7,k1_relset_1(X0,X1,X2))) & (? [X5] : (r2_hidden(k4_tarski(sK7,X5),X2) & m1_subset_1(X5,X1)) | r2_hidden(sK7,k1_relset_1(X0,X1,X2))) & m1_subset_1(sK7,X0))) )),
% 2.62/0.98    introduced(choice_axiom,[])).
% 2.62/0.98  
% 2.62/0.98  fof(f30,plain,(
% 2.62/0.98    ? [X0,X1,X2] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X3,X4),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k1_relset_1(X0,X1,X2))) & (? [X5] : (r2_hidden(k4_tarski(X3,X5),X2) & m1_subset_1(X5,X1)) | r2_hidden(X3,k1_relset_1(X0,X1,X2))) & m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X3,X4),sK6) | ~m1_subset_1(X4,sK5)) | ~r2_hidden(X3,k1_relset_1(sK4,sK5,sK6))) & (? [X5] : (r2_hidden(k4_tarski(X3,X5),sK6) & m1_subset_1(X5,sK5)) | r2_hidden(X3,k1_relset_1(sK4,sK5,sK6))) & m1_subset_1(X3,sK4)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))))),
% 2.62/0.98    introduced(choice_axiom,[])).
% 2.62/0.98  
% 2.62/0.98  fof(f33,plain,(
% 2.62/0.98    ((! [X4] : (~r2_hidden(k4_tarski(sK7,X4),sK6) | ~m1_subset_1(X4,sK5)) | ~r2_hidden(sK7,k1_relset_1(sK4,sK5,sK6))) & ((r2_hidden(k4_tarski(sK7,sK8),sK6) & m1_subset_1(sK8,sK5)) | r2_hidden(sK7,k1_relset_1(sK4,sK5,sK6))) & m1_subset_1(sK7,sK4)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 2.62/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f29,f32,f31,f30])).
% 2.62/0.98  
% 2.62/0.98  fof(f52,plain,(
% 2.62/0.98    ( ! [X4] : (~r2_hidden(k4_tarski(sK7,X4),sK6) | ~m1_subset_1(X4,sK5) | ~r2_hidden(sK7,k1_relset_1(sK4,sK5,sK6))) )),
% 2.62/0.98    inference(cnf_transformation,[],[f33])).
% 2.62/0.98  
% 2.62/0.98  fof(f48,plain,(
% 2.62/0.98    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 2.62/0.98    inference(cnf_transformation,[],[f33])).
% 2.62/0.98  
% 2.62/0.98  fof(f6,axiom,(
% 2.62/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.62/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.62/0.98  
% 2.62/0.98  fof(f12,plain,(
% 2.62/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.62/0.98    inference(ennf_transformation,[],[f6])).
% 2.62/0.98  
% 2.62/0.98  fof(f47,plain,(
% 2.62/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.62/0.98    inference(cnf_transformation,[],[f12])).
% 2.62/0.98  
% 2.62/0.98  fof(f50,plain,(
% 2.62/0.98    m1_subset_1(sK8,sK5) | r2_hidden(sK7,k1_relset_1(sK4,sK5,sK6))),
% 2.62/0.98    inference(cnf_transformation,[],[f33])).
% 2.62/0.98  
% 2.62/0.98  fof(f5,axiom,(
% 2.62/0.98    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 2.62/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.62/0.98  
% 2.62/0.98  fof(f21,plain,(
% 2.62/0.98    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 2.62/0.98    inference(nnf_transformation,[],[f5])).
% 2.62/0.98  
% 2.62/0.98  fof(f22,plain,(
% 2.62/0.98    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 2.62/0.98    inference(rectify,[],[f21])).
% 2.62/0.98  
% 2.62/0.98  fof(f25,plain,(
% 2.62/0.98    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0))),
% 2.62/0.98    introduced(choice_axiom,[])).
% 2.62/0.98  
% 2.62/0.98  fof(f24,plain,(
% 2.62/0.98    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) => r2_hidden(k4_tarski(X2,sK2(X0,X1)),X0))) )),
% 2.62/0.98    introduced(choice_axiom,[])).
% 2.62/0.98  
% 2.62/0.98  fof(f23,plain,(
% 2.62/0.98    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK1(X0,X1),X3),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK1(X0,X1),X4),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 2.62/0.98    introduced(choice_axiom,[])).
% 2.62/0.98  
% 2.62/0.98  fof(f26,plain,(
% 2.62/0.98    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK1(X0,X1),X3),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 2.62/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f22,f25,f24,f23])).
% 2.62/0.98  
% 2.62/0.98  fof(f44,plain,(
% 2.62/0.98    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 2.62/0.98    inference(cnf_transformation,[],[f26])).
% 2.62/0.98  
% 2.62/0.98  fof(f53,plain,(
% 2.62/0.98    ( ! [X6,X0,X5] : (r2_hidden(X5,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X5,X6),X0)) )),
% 2.62/0.98    inference(equality_resolution,[],[f44])).
% 2.62/0.98  
% 2.62/0.98  fof(f51,plain,(
% 2.62/0.98    r2_hidden(k4_tarski(sK7,sK8),sK6) | r2_hidden(sK7,k1_relset_1(sK4,sK5,sK6))),
% 2.62/0.98    inference(cnf_transformation,[],[f33])).
% 2.62/0.98  
% 2.62/0.98  fof(f43,plain,(
% 2.62/0.98    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 2.62/0.98    inference(cnf_transformation,[],[f26])).
% 2.62/0.98  
% 2.62/0.98  fof(f54,plain,(
% 2.62/0.98    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 2.62/0.98    inference(equality_resolution,[],[f43])).
% 2.62/0.98  
% 2.62/0.98  fof(f3,axiom,(
% 2.62/0.98    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 2.62/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.62/0.98  
% 2.62/0.98  fof(f11,plain,(
% 2.62/0.98    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 2.62/0.98    inference(ennf_transformation,[],[f3])).
% 2.62/0.98  
% 2.62/0.98  fof(f40,plain,(
% 2.62/0.98    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 2.62/0.98    inference(cnf_transformation,[],[f11])).
% 2.62/0.98  
% 2.62/0.98  fof(f2,axiom,(
% 2.62/0.98    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 2.62/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.62/0.98  
% 2.62/0.98  fof(f18,plain,(
% 2.62/0.98    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 2.62/0.98    inference(nnf_transformation,[],[f2])).
% 2.62/0.98  
% 2.62/0.98  fof(f19,plain,(
% 2.62/0.98    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 2.62/0.98    inference(flattening,[],[f18])).
% 2.62/0.98  
% 2.62/0.98  fof(f38,plain,(
% 2.62/0.98    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 2.62/0.98    inference(cnf_transformation,[],[f19])).
% 2.62/0.98  
% 2.62/0.98  fof(f1,axiom,(
% 2.62/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.62/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.62/0.98  
% 2.62/0.98  fof(f10,plain,(
% 2.62/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.62/0.98    inference(ennf_transformation,[],[f1])).
% 2.62/0.98  
% 2.62/0.98  fof(f14,plain,(
% 2.62/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.62/0.98    inference(nnf_transformation,[],[f10])).
% 2.62/0.98  
% 2.62/0.98  fof(f15,plain,(
% 2.62/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.62/0.98    inference(rectify,[],[f14])).
% 2.62/0.98  
% 2.62/0.98  fof(f16,plain,(
% 2.62/0.98    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.62/0.98    introduced(choice_axiom,[])).
% 2.62/0.98  
% 2.62/0.98  fof(f17,plain,(
% 2.62/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.62/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).
% 2.62/0.98  
% 2.62/0.98  fof(f34,plain,(
% 2.62/0.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.62/0.98    inference(cnf_transformation,[],[f17])).
% 2.62/0.98  
% 2.62/0.98  fof(f4,axiom,(
% 2.62/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.62/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.62/0.98  
% 2.62/0.98  fof(f20,plain,(
% 2.62/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.62/0.98    inference(nnf_transformation,[],[f4])).
% 2.62/0.98  
% 2.62/0.98  fof(f41,plain,(
% 2.62/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.62/0.98    inference(cnf_transformation,[],[f20])).
% 2.62/0.98  
% 2.62/0.98  cnf(c_14,negated_conjecture,
% 2.62/0.98      ( ~ m1_subset_1(X0,sK5)
% 2.62/0.98      | ~ r2_hidden(k4_tarski(sK7,X0),sK6)
% 2.62/0.98      | ~ r2_hidden(sK7,k1_relset_1(sK4,sK5,sK6)) ),
% 2.62/0.98      inference(cnf_transformation,[],[f52]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_18,negated_conjecture,
% 2.62/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
% 2.62/0.98      inference(cnf_transformation,[],[f48]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_1005,plain,
% 2.62/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 2.62/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_13,plain,
% 2.62/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.62/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.62/0.98      inference(cnf_transformation,[],[f47]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_1010,plain,
% 2.62/0.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.62/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.62/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_1480,plain,
% 2.62/0.98      ( k1_relset_1(sK4,sK5,sK6) = k1_relat_1(sK6) ),
% 2.62/0.98      inference(superposition,[status(thm)],[c_1005,c_1010]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_1009,plain,
% 2.62/0.98      ( m1_subset_1(X0,sK5) != iProver_top
% 2.62/0.98      | r2_hidden(k4_tarski(sK7,X0),sK6) != iProver_top
% 2.62/0.98      | r2_hidden(sK7,k1_relset_1(sK4,sK5,sK6)) != iProver_top ),
% 2.62/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_1634,plain,
% 2.62/0.98      ( m1_subset_1(X0,sK5) != iProver_top
% 2.62/0.98      | r2_hidden(k4_tarski(sK7,X0),sK6) != iProver_top
% 2.62/0.98      | r2_hidden(sK7,k1_relat_1(sK6)) != iProver_top ),
% 2.62/0.98      inference(demodulation,[status(thm)],[c_1480,c_1009]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_1651,plain,
% 2.62/0.98      ( ~ m1_subset_1(X0,sK5)
% 2.62/0.98      | ~ r2_hidden(k4_tarski(sK7,X0),sK6)
% 2.62/0.98      | ~ r2_hidden(sK7,k1_relat_1(sK6)) ),
% 2.62/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_1634]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_16,negated_conjecture,
% 2.62/0.98      ( m1_subset_1(sK8,sK5) | r2_hidden(sK7,k1_relset_1(sK4,sK5,sK6)) ),
% 2.62/0.98      inference(cnf_transformation,[],[f50]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_1007,plain,
% 2.62/0.98      ( m1_subset_1(sK8,sK5) = iProver_top
% 2.62/0.98      | r2_hidden(sK7,k1_relset_1(sK4,sK5,sK6)) = iProver_top ),
% 2.62/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_1633,plain,
% 2.62/0.98      ( m1_subset_1(sK8,sK5) = iProver_top
% 2.62/0.98      | r2_hidden(sK7,k1_relat_1(sK6)) = iProver_top ),
% 2.62/0.98      inference(demodulation,[status(thm)],[c_1480,c_1007]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_11,plain,
% 2.62/0.98      ( r2_hidden(X0,k1_relat_1(X1)) | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
% 2.62/0.98      inference(cnf_transformation,[],[f53]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_1415,plain,
% 2.62/0.98      ( ~ r2_hidden(k4_tarski(sK7,sK8),sK6)
% 2.62/0.98      | r2_hidden(sK7,k1_relat_1(sK6)) ),
% 2.62/0.98      inference(instantiation,[status(thm)],[c_11]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_1416,plain,
% 2.62/0.98      ( r2_hidden(k4_tarski(sK7,sK8),sK6) != iProver_top
% 2.62/0.98      | r2_hidden(sK7,k1_relat_1(sK6)) = iProver_top ),
% 2.62/0.98      inference(predicate_to_equality,[status(thm)],[c_1415]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_15,negated_conjecture,
% 2.62/0.98      ( r2_hidden(k4_tarski(sK7,sK8),sK6)
% 2.62/0.98      | r2_hidden(sK7,k1_relset_1(sK4,sK5,sK6)) ),
% 2.62/0.98      inference(cnf_transformation,[],[f51]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_1008,plain,
% 2.62/0.98      ( r2_hidden(k4_tarski(sK7,sK8),sK6) = iProver_top
% 2.62/0.98      | r2_hidden(sK7,k1_relset_1(sK4,sK5,sK6)) = iProver_top ),
% 2.62/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_1632,plain,
% 2.62/0.98      ( r2_hidden(k4_tarski(sK7,sK8),sK6) = iProver_top
% 2.62/0.98      | r2_hidden(sK7,k1_relat_1(sK6)) = iProver_top ),
% 2.62/0.98      inference(demodulation,[status(thm)],[c_1480,c_1008]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_1916,plain,
% 2.62/0.98      ( r2_hidden(sK7,k1_relat_1(sK6)) = iProver_top ),
% 2.62/0.98      inference(global_propositional_subsumption,
% 2.62/0.98                [status(thm)],
% 2.62/0.98                [c_1633,c_1416,c_1632]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_1918,plain,
% 2.62/0.98      ( r2_hidden(sK7,k1_relat_1(sK6)) ),
% 2.62/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_1916]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_2064,plain,
% 2.62/0.98      ( ~ r2_hidden(k4_tarski(sK7,X0),sK6) | ~ m1_subset_1(X0,sK5) ),
% 2.62/0.98      inference(global_propositional_subsumption,
% 2.62/0.98                [status(thm)],
% 2.62/0.98                [c_14,c_1651,c_1918]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_2065,negated_conjecture,
% 2.62/0.98      ( ~ m1_subset_1(X0,sK5) | ~ r2_hidden(k4_tarski(sK7,X0),sK6) ),
% 2.62/0.98      inference(renaming,[status(thm)],[c_2064]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_12,plain,
% 2.62/0.98      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.62/0.98      | r2_hidden(k4_tarski(X0,sK3(X1,X0)),X1) ),
% 2.62/0.98      inference(cnf_transformation,[],[f54]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_2080,plain,
% 2.62/0.98      ( ~ m1_subset_1(sK3(sK6,sK7),sK5)
% 2.62/0.98      | ~ r2_hidden(sK7,k1_relat_1(sK6)) ),
% 2.62/0.98      inference(resolution,[status(thm)],[c_2065,c_12]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_1011,plain,
% 2.62/0.98      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 2.62/0.98      | r2_hidden(k4_tarski(X0,sK3(X1,X0)),X1) = iProver_top ),
% 2.62/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_1761,plain,
% 2.62/0.98      ( r2_hidden(k4_tarski(sK7,X0),sK6) != iProver_top
% 2.62/0.98      | m1_subset_1(X0,sK5) != iProver_top ),
% 2.62/0.98      inference(global_propositional_subsumption,
% 2.62/0.98                [status(thm)],
% 2.62/0.98                [c_1634,c_1416,c_1632]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_1762,plain,
% 2.62/0.98      ( m1_subset_1(X0,sK5) != iProver_top
% 2.62/0.98      | r2_hidden(k4_tarski(sK7,X0),sK6) != iProver_top ),
% 2.62/0.98      inference(renaming,[status(thm)],[c_1761]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_2038,plain,
% 2.62/0.98      ( m1_subset_1(sK3(sK6,sK7),sK5) != iProver_top
% 2.62/0.98      | r2_hidden(sK7,k1_relat_1(sK6)) != iProver_top ),
% 2.62/0.98      inference(superposition,[status(thm)],[c_1011,c_1762]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_2057,plain,
% 2.62/0.98      ( ~ m1_subset_1(sK3(sK6,sK7),sK5)
% 2.62/0.98      | ~ r2_hidden(sK7,k1_relat_1(sK6)) ),
% 2.62/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_2038]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_2083,plain,
% 2.62/0.98      ( ~ m1_subset_1(sK3(sK6,sK7),sK5) ),
% 2.62/0.98      inference(global_propositional_subsumption,
% 2.62/0.98                [status(thm)],
% 2.62/0.98                [c_2080,c_1918,c_2057]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_6,plain,
% 2.62/0.98      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 2.62/0.98      inference(cnf_transformation,[],[f40]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_2189,plain,
% 2.62/0.98      ( ~ r2_hidden(sK3(sK6,sK7),sK5) ),
% 2.62/0.98      inference(resolution,[status(thm)],[c_2083,c_6]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_4,plain,
% 2.62/0.98      ( r2_hidden(X0,X1)
% 2.62/0.98      | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 2.62/0.98      inference(cnf_transformation,[],[f38]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_2,plain,
% 2.62/0.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 2.62/0.98      inference(cnf_transformation,[],[f34]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_8,plain,
% 2.62/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.62/0.98      inference(cnf_transformation,[],[f41]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_1275,plain,
% 2.62/0.98      ( r1_tarski(sK6,k2_zfmisc_1(sK4,sK5)) ),
% 2.62/0.98      inference(resolution,[status(thm)],[c_8,c_18]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_1496,plain,
% 2.62/0.98      ( r2_hidden(X0,k2_zfmisc_1(sK4,sK5)) | ~ r2_hidden(X0,sK6) ),
% 2.62/0.98      inference(resolution,[status(thm)],[c_2,c_1275]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_1784,plain,
% 2.62/0.98      ( r2_hidden(X0,sK5) | ~ r2_hidden(k4_tarski(X1,X0),sK6) ),
% 2.62/0.98      inference(resolution,[status(thm)],[c_4,c_1496]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_2425,plain,
% 2.62/0.98      ( ~ r2_hidden(X0,k1_relat_1(sK6)) | r2_hidden(sK3(sK6,X0),sK5) ),
% 2.62/0.98      inference(resolution,[status(thm)],[c_1784,c_12]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_2711,plain,
% 2.62/0.98      ( ~ r2_hidden(sK7,k1_relat_1(sK6)) ),
% 2.62/0.98      inference(resolution,[status(thm)],[c_2189,c_2425]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(contradiction,plain,
% 2.62/0.98      ( $false ),
% 2.62/0.98      inference(minisat,[status(thm)],[c_2711,c_1918]) ).
% 2.62/0.98  
% 2.62/0.98  
% 2.62/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.62/0.98  
% 2.62/0.98  ------                               Statistics
% 2.62/0.98  
% 2.62/0.98  ------ Selected
% 2.62/0.98  
% 2.62/0.98  total_time:                             0.104
% 2.62/0.98  
%------------------------------------------------------------------------------
