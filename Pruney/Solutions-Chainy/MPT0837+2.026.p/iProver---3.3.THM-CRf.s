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
% DateTime   : Thu Dec  3 11:56:25 EST 2020

% Result     : Theorem 6.37s
% Output     : CNFRefutation 6.37s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 467 expanded)
%              Number of clauses        :   47 ( 122 expanded)
%              Number of leaves         :   14 ( 127 expanded)
%              Depth                    :   20
%              Number of atoms          :  304 (2208 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( r2_hidden(X3,k2_relset_1(X1,X0,X2))
        <~> ? [X4] :
              ( r2_hidden(k4_tarski(X4,X3),X2)
              & m1_subset_1(X4,X1) ) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f32,plain,(
    ! [X2,X3,X1] :
      ( ? [X5] :
          ( r2_hidden(k4_tarski(X5,X3),X2)
          & m1_subset_1(X5,X1) )
     => ( r2_hidden(k4_tarski(sK8,X3),X2)
        & m1_subset_1(sK8,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
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

fof(f30,plain,
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

fof(f33,plain,
    ( ( ! [X4] :
          ( ~ r2_hidden(k4_tarski(X4,sK7),sK6)
          | ~ m1_subset_1(X4,sK5) )
      | ~ r2_hidden(sK7,k2_relset_1(sK5,sK4,sK6)) )
    & ( ( r2_hidden(k4_tarski(sK8,sK7),sK6)
        & m1_subset_1(sK8,sK5) )
      | r2_hidden(sK7,k2_relset_1(sK5,sK4,sK6)) )
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f29,f32,f31,f30])).

fof(f51,plain,(
    ! [X4] :
      ( ~ r2_hidden(k4_tarski(X4,sK7),sK6)
      | ~ m1_subset_1(X4,sK5)
      | ~ r2_hidden(sK7,k2_relset_1(sK5,sK4,sK6)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f48,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) ),
    inference(cnf_transformation,[],[f33])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f49,plain,
    ( m1_subset_1(sK8,sK5)
    | r2_hidden(sK7,k2_relset_1(sK5,sK4,sK6)) ),
    inference(cnf_transformation,[],[f33])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f5])).

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

fof(f44,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f52,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f50,plain,
    ( r2_hidden(k4_tarski(sK8,sK7),sK6)
    | r2_hidden(sK7,k2_relset_1(sK5,sK4,sK6)) ),
    inference(cnf_transformation,[],[f33])).

fof(f43,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f53,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK3(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f43])).

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

fof(f15,plain,(
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

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f15])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f17])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f19])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f34,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_14,negated_conjecture,
    ( ~ m1_subset_1(X0,sK5)
    | ~ r2_hidden(k4_tarski(X0,sK7),sK6)
    | ~ r2_hidden(sK7,k2_relset_1(sK5,sK4,sK6)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_774,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_778,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1353,plain,
    ( k2_relset_1(sK5,sK4,sK6) = k2_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_774,c_778])).

cnf(c_777,plain,
    ( m1_subset_1(X0,sK5) != iProver_top
    | r2_hidden(k4_tarski(X0,sK7),sK6) != iProver_top
    | r2_hidden(sK7,k2_relset_1(sK5,sK4,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1560,plain,
    ( m1_subset_1(X0,sK5) != iProver_top
    | r2_hidden(k4_tarski(X0,sK7),sK6) != iProver_top
    | r2_hidden(sK7,k2_relat_1(sK6)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1353,c_777])).

cnf(c_1577,plain,
    ( ~ m1_subset_1(X0,sK5)
    | ~ r2_hidden(k4_tarski(X0,sK7),sK6)
    | ~ r2_hidden(sK7,k2_relat_1(sK6)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1560])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK8,sK5)
    | r2_hidden(sK7,k2_relset_1(sK5,sK4,sK6)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_775,plain,
    ( m1_subset_1(sK8,sK5) = iProver_top
    | r2_hidden(sK7,k2_relset_1(sK5,sK4,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1559,plain,
    ( m1_subset_1(sK8,sK5) = iProver_top
    | r2_hidden(sK7,k2_relat_1(sK6)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1353,c_775])).

cnf(c_11,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1536,plain,
    ( ~ r2_hidden(k4_tarski(sK8,sK7),sK6)
    | r2_hidden(sK7,k2_relat_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1537,plain,
    ( r2_hidden(k4_tarski(sK8,sK7),sK6) != iProver_top
    | r2_hidden(sK7,k2_relat_1(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1536])).

cnf(c_15,negated_conjecture,
    ( r2_hidden(k4_tarski(sK8,sK7),sK6)
    | r2_hidden(sK7,k2_relset_1(sK5,sK4,sK6)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_776,plain,
    ( r2_hidden(k4_tarski(sK8,sK7),sK6) = iProver_top
    | r2_hidden(sK7,k2_relset_1(sK5,sK4,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1558,plain,
    ( r2_hidden(k4_tarski(sK8,sK7),sK6) = iProver_top
    | r2_hidden(sK7,k2_relat_1(sK6)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1353,c_776])).

cnf(c_1658,plain,
    ( r2_hidden(sK7,k2_relat_1(sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1559,c_1537,c_1558])).

cnf(c_1660,plain,
    ( r2_hidden(sK7,k2_relat_1(sK6)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1658])).

cnf(c_17047,plain,
    ( ~ r2_hidden(k4_tarski(X0,sK7),sK6)
    | ~ m1_subset_1(X0,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14,c_1577,c_1660])).

cnf(c_17048,negated_conjecture,
    ( ~ m1_subset_1(X0,sK5)
    | ~ r2_hidden(k4_tarski(X0,sK7),sK6) ),
    inference(renaming,[status(thm)],[c_17047])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(k4_tarski(sK3(X1,X0),X0),X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_17418,plain,
    ( ~ m1_subset_1(sK3(sK6,sK7),sK5)
    | ~ r2_hidden(sK7,k2_relat_1(sK6)) ),
    inference(resolution,[status(thm)],[c_17048,c_12])).

cnf(c_779,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(sK3(X1,X0),X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1649,plain,
    ( r2_hidden(k4_tarski(X0,sK7),sK6) != iProver_top
    | m1_subset_1(X0,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1560,c_1537,c_1558])).

cnf(c_1650,plain,
    ( m1_subset_1(X0,sK5) != iProver_top
    | r2_hidden(k4_tarski(X0,sK7),sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_1649])).

cnf(c_2256,plain,
    ( m1_subset_1(sK3(sK6,sK7),sK5) != iProver_top
    | r2_hidden(sK7,k2_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_779,c_1650])).

cnf(c_2278,plain,
    ( ~ m1_subset_1(sK3(sK6,sK7),sK5)
    | ~ r2_hidden(sK7,k2_relat_1(sK6)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2256])).

cnf(c_17421,plain,
    ( ~ m1_subset_1(sK3(sK6,sK7),sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17418,c_1660,c_2278])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1054,plain,
    ( r1_tarski(X0,X0) ),
    inference(resolution,[status(thm)],[c_0,c_1])).

cnf(c_8,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_6,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1482,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(resolution,[status(thm)],[c_8,c_6])).

cnf(c_4375,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(resolution,[status(thm)],[c_1054,c_1482])).

cnf(c_17745,plain,
    ( ~ r2_hidden(sK3(sK6,sK7),sK5) ),
    inference(resolution,[status(thm)],[c_17421,c_4375])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1002,plain,
    ( r1_tarski(sK6,k2_zfmisc_1(sK5,sK4)) ),
    inference(resolution,[status(thm)],[c_7,c_17])).

cnf(c_1072,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK5,sK4))
    | ~ r2_hidden(X0,sK6) ),
    inference(resolution,[status(thm)],[c_2,c_1002])).

cnf(c_1384,plain,
    ( r2_hidden(X0,sK5)
    | ~ r2_hidden(k4_tarski(X0,X1),sK6) ),
    inference(resolution,[status(thm)],[c_5,c_1072])).

cnf(c_1892,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK6))
    | r2_hidden(sK3(sK6,X0),sK5) ),
    inference(resolution,[status(thm)],[c_1384,c_12])).

cnf(c_18152,plain,
    ( ~ r2_hidden(sK7,k2_relat_1(sK6)) ),
    inference(resolution,[status(thm)],[c_17745,c_1892])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_18152,c_1660])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:50:27 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 6.37/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.37/1.49  
% 6.37/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.37/1.49  
% 6.37/1.49  ------  iProver source info
% 6.37/1.49  
% 6.37/1.49  git: date: 2020-06-30 10:37:57 +0100
% 6.37/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.37/1.49  git: non_committed_changes: false
% 6.37/1.49  git: last_make_outside_of_git: false
% 6.37/1.49  
% 6.37/1.49  ------ 
% 6.37/1.49  ------ Parsing...
% 6.37/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.37/1.49  
% 6.37/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 6.37/1.49  
% 6.37/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.37/1.49  
% 6.37/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.37/1.49  ------ Proving...
% 6.37/1.49  ------ Problem Properties 
% 6.37/1.49  
% 6.37/1.49  
% 6.37/1.49  clauses                                 18
% 6.37/1.49  conjectures                             4
% 6.37/1.49  EPR                                     1
% 6.37/1.49  Horn                                    14
% 6.37/1.49  unary                                   1
% 6.37/1.49  binary                                  11
% 6.37/1.49  lits                                    41
% 6.37/1.49  lits eq                                 3
% 6.37/1.49  fd_pure                                 0
% 6.37/1.49  fd_pseudo                               0
% 6.37/1.49  fd_cond                                 0
% 6.37/1.49  fd_pseudo_cond                          2
% 6.37/1.49  AC symbols                              0
% 6.37/1.49  
% 6.37/1.49  ------ Input Options Time Limit: Unbounded
% 6.37/1.49  
% 6.37/1.49  
% 6.37/1.49  ------ 
% 6.37/1.49  Current options:
% 6.37/1.49  ------ 
% 6.37/1.49  
% 6.37/1.49  
% 6.37/1.49  
% 6.37/1.49  
% 6.37/1.49  ------ Proving...
% 6.37/1.49  
% 6.37/1.49  
% 6.37/1.49  % SZS status Theorem for theBenchmark.p
% 6.37/1.49  
% 6.37/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 6.37/1.49  
% 6.37/1.49  fof(f7,conjecture,(
% 6.37/1.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ! [X3] : (r2_hidden(X3,k2_relset_1(X1,X0,X2)) <=> ? [X4] : (r2_hidden(k4_tarski(X4,X3),X2) & m1_subset_1(X4,X1))))))),
% 6.37/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.37/1.49  
% 6.37/1.49  fof(f8,negated_conjecture,(
% 6.37/1.49    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ! [X3] : (r2_hidden(X3,k2_relset_1(X1,X0,X2)) <=> ? [X4] : (r2_hidden(k4_tarski(X4,X3),X2) & m1_subset_1(X4,X1))))))),
% 6.37/1.49    inference(negated_conjecture,[],[f7])).
% 6.37/1.49  
% 6.37/1.49  fof(f9,plain,(
% 6.37/1.49    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ! [X3] : (r2_hidden(X3,k2_relset_1(X1,X0,X2)) <=> ? [X4] : (r2_hidden(k4_tarski(X4,X3),X2) & m1_subset_1(X4,X1))))),
% 6.37/1.49    inference(pure_predicate_removal,[],[f8])).
% 6.37/1.49  
% 6.37/1.49  fof(f14,plain,(
% 6.37/1.49    ? [X0,X1,X2] : (? [X3] : (r2_hidden(X3,k2_relset_1(X1,X0,X2)) <~> ? [X4] : (r2_hidden(k4_tarski(X4,X3),X2) & m1_subset_1(X4,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 6.37/1.49    inference(ennf_transformation,[],[f9])).
% 6.37/1.49  
% 6.37/1.49  fof(f28,plain,(
% 6.37/1.49    ? [X0,X1,X2] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X4,X3),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k2_relset_1(X1,X0,X2))) & (? [X4] : (r2_hidden(k4_tarski(X4,X3),X2) & m1_subset_1(X4,X1)) | r2_hidden(X3,k2_relset_1(X1,X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 6.37/1.49    inference(nnf_transformation,[],[f14])).
% 6.37/1.49  
% 6.37/1.49  fof(f29,plain,(
% 6.37/1.49    ? [X0,X1,X2] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X4,X3),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k2_relset_1(X1,X0,X2))) & (? [X5] : (r2_hidden(k4_tarski(X5,X3),X2) & m1_subset_1(X5,X1)) | r2_hidden(X3,k2_relset_1(X1,X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 6.37/1.49    inference(rectify,[],[f28])).
% 6.37/1.49  
% 6.37/1.49  fof(f32,plain,(
% 6.37/1.49    ( ! [X2,X3,X1] : (? [X5] : (r2_hidden(k4_tarski(X5,X3),X2) & m1_subset_1(X5,X1)) => (r2_hidden(k4_tarski(sK8,X3),X2) & m1_subset_1(sK8,X1))) )),
% 6.37/1.49    introduced(choice_axiom,[])).
% 6.37/1.49  
% 6.37/1.49  fof(f31,plain,(
% 6.37/1.49    ( ! [X2,X0,X1] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X4,X3),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k2_relset_1(X1,X0,X2))) & (? [X5] : (r2_hidden(k4_tarski(X5,X3),X2) & m1_subset_1(X5,X1)) | r2_hidden(X3,k2_relset_1(X1,X0,X2)))) => ((! [X4] : (~r2_hidden(k4_tarski(X4,sK7),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(sK7,k2_relset_1(X1,X0,X2))) & (? [X5] : (r2_hidden(k4_tarski(X5,sK7),X2) & m1_subset_1(X5,X1)) | r2_hidden(sK7,k2_relset_1(X1,X0,X2))))) )),
% 6.37/1.49    introduced(choice_axiom,[])).
% 6.37/1.49  
% 6.37/1.49  fof(f30,plain,(
% 6.37/1.49    ? [X0,X1,X2] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X4,X3),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k2_relset_1(X1,X0,X2))) & (? [X5] : (r2_hidden(k4_tarski(X5,X3),X2) & m1_subset_1(X5,X1)) | r2_hidden(X3,k2_relset_1(X1,X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) => (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X4,X3),sK6) | ~m1_subset_1(X4,sK5)) | ~r2_hidden(X3,k2_relset_1(sK5,sK4,sK6))) & (? [X5] : (r2_hidden(k4_tarski(X5,X3),sK6) & m1_subset_1(X5,sK5)) | r2_hidden(X3,k2_relset_1(sK5,sK4,sK6)))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))))),
% 6.37/1.49    introduced(choice_axiom,[])).
% 6.37/1.49  
% 6.37/1.49  fof(f33,plain,(
% 6.37/1.49    ((! [X4] : (~r2_hidden(k4_tarski(X4,sK7),sK6) | ~m1_subset_1(X4,sK5)) | ~r2_hidden(sK7,k2_relset_1(sK5,sK4,sK6))) & ((r2_hidden(k4_tarski(sK8,sK7),sK6) & m1_subset_1(sK8,sK5)) | r2_hidden(sK7,k2_relset_1(sK5,sK4,sK6)))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))),
% 6.37/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f29,f32,f31,f30])).
% 6.37/1.49  
% 6.37/1.49  fof(f51,plain,(
% 6.37/1.49    ( ! [X4] : (~r2_hidden(k4_tarski(X4,sK7),sK6) | ~m1_subset_1(X4,sK5) | ~r2_hidden(sK7,k2_relset_1(sK5,sK4,sK6))) )),
% 6.37/1.49    inference(cnf_transformation,[],[f33])).
% 6.37/1.49  
% 6.37/1.49  fof(f48,plain,(
% 6.37/1.49    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))),
% 6.37/1.49    inference(cnf_transformation,[],[f33])).
% 6.37/1.49  
% 6.37/1.49  fof(f6,axiom,(
% 6.37/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 6.37/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.37/1.49  
% 6.37/1.49  fof(f13,plain,(
% 6.37/1.49    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.37/1.49    inference(ennf_transformation,[],[f6])).
% 6.37/1.49  
% 6.37/1.49  fof(f47,plain,(
% 6.37/1.49    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.37/1.49    inference(cnf_transformation,[],[f13])).
% 6.37/1.49  
% 6.37/1.49  fof(f49,plain,(
% 6.37/1.49    m1_subset_1(sK8,sK5) | r2_hidden(sK7,k2_relset_1(sK5,sK4,sK6))),
% 6.37/1.49    inference(cnf_transformation,[],[f33])).
% 6.37/1.49  
% 6.37/1.49  fof(f5,axiom,(
% 6.37/1.49    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 6.37/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.37/1.49  
% 6.37/1.49  fof(f22,plain,(
% 6.37/1.49    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 6.37/1.49    inference(nnf_transformation,[],[f5])).
% 6.37/1.49  
% 6.37/1.49  fof(f23,plain,(
% 6.37/1.49    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 6.37/1.49    inference(rectify,[],[f22])).
% 6.37/1.49  
% 6.37/1.49  fof(f26,plain,(
% 6.37/1.49    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK3(X0,X5),X5),X0))),
% 6.37/1.49    introduced(choice_axiom,[])).
% 6.37/1.49  
% 6.37/1.49  fof(f25,plain,(
% 6.37/1.49    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) => r2_hidden(k4_tarski(sK2(X0,X1),X2),X0))) )),
% 6.37/1.49    introduced(choice_axiom,[])).
% 6.37/1.49  
% 6.37/1.49  fof(f24,plain,(
% 6.37/1.49    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK1(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 6.37/1.49    introduced(choice_axiom,[])).
% 6.37/1.49  
% 6.37/1.49  fof(f27,plain,(
% 6.37/1.49    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK3(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 6.37/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f23,f26,f25,f24])).
% 6.37/1.49  
% 6.37/1.49  fof(f44,plain,(
% 6.37/1.49    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 6.37/1.49    inference(cnf_transformation,[],[f27])).
% 6.37/1.49  
% 6.37/1.49  fof(f52,plain,(
% 6.37/1.49    ( ! [X6,X0,X5] : (r2_hidden(X5,k2_relat_1(X0)) | ~r2_hidden(k4_tarski(X6,X5),X0)) )),
% 6.37/1.49    inference(equality_resolution,[],[f44])).
% 6.37/1.49  
% 6.37/1.49  fof(f50,plain,(
% 6.37/1.49    r2_hidden(k4_tarski(sK8,sK7),sK6) | r2_hidden(sK7,k2_relset_1(sK5,sK4,sK6))),
% 6.37/1.49    inference(cnf_transformation,[],[f33])).
% 6.37/1.49  
% 6.37/1.49  fof(f43,plain,(
% 6.37/1.49    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK3(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 6.37/1.49    inference(cnf_transformation,[],[f27])).
% 6.37/1.49  
% 6.37/1.49  fof(f53,plain,(
% 6.37/1.49    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK3(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 6.37/1.49    inference(equality_resolution,[],[f43])).
% 6.37/1.49  
% 6.37/1.49  fof(f1,axiom,(
% 6.37/1.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 6.37/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.37/1.49  
% 6.37/1.49  fof(f10,plain,(
% 6.37/1.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 6.37/1.49    inference(ennf_transformation,[],[f1])).
% 6.37/1.49  
% 6.37/1.49  fof(f15,plain,(
% 6.37/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 6.37/1.49    inference(nnf_transformation,[],[f10])).
% 6.37/1.49  
% 6.37/1.49  fof(f16,plain,(
% 6.37/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 6.37/1.49    inference(rectify,[],[f15])).
% 6.37/1.49  
% 6.37/1.49  fof(f17,plain,(
% 6.37/1.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 6.37/1.49    introduced(choice_axiom,[])).
% 6.37/1.49  
% 6.37/1.49  fof(f18,plain,(
% 6.37/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 6.37/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f17])).
% 6.37/1.49  
% 6.37/1.49  fof(f36,plain,(
% 6.37/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 6.37/1.49    inference(cnf_transformation,[],[f18])).
% 6.37/1.49  
% 6.37/1.49  fof(f35,plain,(
% 6.37/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 6.37/1.49    inference(cnf_transformation,[],[f18])).
% 6.37/1.49  
% 6.37/1.49  fof(f4,axiom,(
% 6.37/1.49    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 6.37/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.37/1.49  
% 6.37/1.49  fof(f11,plain,(
% 6.37/1.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 6.37/1.49    inference(ennf_transformation,[],[f4])).
% 6.37/1.49  
% 6.37/1.49  fof(f12,plain,(
% 6.37/1.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 6.37/1.49    inference(flattening,[],[f11])).
% 6.37/1.49  
% 6.37/1.49  fof(f42,plain,(
% 6.37/1.49    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 6.37/1.49    inference(cnf_transformation,[],[f12])).
% 6.37/1.49  
% 6.37/1.49  fof(f3,axiom,(
% 6.37/1.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 6.37/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.37/1.49  
% 6.37/1.49  fof(f21,plain,(
% 6.37/1.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 6.37/1.49    inference(nnf_transformation,[],[f3])).
% 6.37/1.49  
% 6.37/1.49  fof(f41,plain,(
% 6.37/1.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 6.37/1.49    inference(cnf_transformation,[],[f21])).
% 6.37/1.49  
% 6.37/1.49  fof(f2,axiom,(
% 6.37/1.49    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 6.37/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.37/1.49  
% 6.37/1.49  fof(f19,plain,(
% 6.37/1.49    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 6.37/1.49    inference(nnf_transformation,[],[f2])).
% 6.37/1.49  
% 6.37/1.49  fof(f20,plain,(
% 6.37/1.49    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 6.37/1.49    inference(flattening,[],[f19])).
% 6.37/1.49  
% 6.37/1.49  fof(f37,plain,(
% 6.37/1.49    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 6.37/1.49    inference(cnf_transformation,[],[f20])).
% 6.37/1.49  
% 6.37/1.49  fof(f34,plain,(
% 6.37/1.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 6.37/1.49    inference(cnf_transformation,[],[f18])).
% 6.37/1.49  
% 6.37/1.49  fof(f40,plain,(
% 6.37/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 6.37/1.49    inference(cnf_transformation,[],[f21])).
% 6.37/1.49  
% 6.37/1.49  cnf(c_14,negated_conjecture,
% 6.37/1.49      ( ~ m1_subset_1(X0,sK5)
% 6.37/1.49      | ~ r2_hidden(k4_tarski(X0,sK7),sK6)
% 6.37/1.49      | ~ r2_hidden(sK7,k2_relset_1(sK5,sK4,sK6)) ),
% 6.37/1.49      inference(cnf_transformation,[],[f51]) ).
% 6.37/1.49  
% 6.37/1.49  cnf(c_17,negated_conjecture,
% 6.37/1.49      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) ),
% 6.37/1.49      inference(cnf_transformation,[],[f48]) ).
% 6.37/1.49  
% 6.37/1.49  cnf(c_774,plain,
% 6.37/1.49      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) = iProver_top ),
% 6.37/1.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 6.37/1.49  
% 6.37/1.49  cnf(c_13,plain,
% 6.37/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.37/1.49      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 6.37/1.49      inference(cnf_transformation,[],[f47]) ).
% 6.37/1.49  
% 6.37/1.49  cnf(c_778,plain,
% 6.37/1.49      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 6.37/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 6.37/1.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 6.37/1.49  
% 6.37/1.49  cnf(c_1353,plain,
% 6.37/1.49      ( k2_relset_1(sK5,sK4,sK6) = k2_relat_1(sK6) ),
% 6.37/1.49      inference(superposition,[status(thm)],[c_774,c_778]) ).
% 6.37/1.49  
% 6.37/1.49  cnf(c_777,plain,
% 6.37/1.49      ( m1_subset_1(X0,sK5) != iProver_top
% 6.37/1.49      | r2_hidden(k4_tarski(X0,sK7),sK6) != iProver_top
% 6.37/1.49      | r2_hidden(sK7,k2_relset_1(sK5,sK4,sK6)) != iProver_top ),
% 6.37/1.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 6.37/1.49  
% 6.37/1.49  cnf(c_1560,plain,
% 6.37/1.49      ( m1_subset_1(X0,sK5) != iProver_top
% 6.37/1.49      | r2_hidden(k4_tarski(X0,sK7),sK6) != iProver_top
% 6.37/1.49      | r2_hidden(sK7,k2_relat_1(sK6)) != iProver_top ),
% 6.37/1.49      inference(demodulation,[status(thm)],[c_1353,c_777]) ).
% 6.37/1.49  
% 6.37/1.49  cnf(c_1577,plain,
% 6.37/1.49      ( ~ m1_subset_1(X0,sK5)
% 6.37/1.49      | ~ r2_hidden(k4_tarski(X0,sK7),sK6)
% 6.37/1.49      | ~ r2_hidden(sK7,k2_relat_1(sK6)) ),
% 6.37/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_1560]) ).
% 6.37/1.49  
% 6.37/1.49  cnf(c_16,negated_conjecture,
% 6.37/1.49      ( m1_subset_1(sK8,sK5) | r2_hidden(sK7,k2_relset_1(sK5,sK4,sK6)) ),
% 6.37/1.49      inference(cnf_transformation,[],[f49]) ).
% 6.37/1.49  
% 6.37/1.49  cnf(c_775,plain,
% 6.37/1.49      ( m1_subset_1(sK8,sK5) = iProver_top
% 6.37/1.49      | r2_hidden(sK7,k2_relset_1(sK5,sK4,sK6)) = iProver_top ),
% 6.37/1.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 6.37/1.49  
% 6.37/1.49  cnf(c_1559,plain,
% 6.37/1.49      ( m1_subset_1(sK8,sK5) = iProver_top
% 6.37/1.49      | r2_hidden(sK7,k2_relat_1(sK6)) = iProver_top ),
% 6.37/1.49      inference(demodulation,[status(thm)],[c_1353,c_775]) ).
% 6.37/1.49  
% 6.37/1.49  cnf(c_11,plain,
% 6.37/1.49      ( r2_hidden(X0,k2_relat_1(X1)) | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
% 6.37/1.49      inference(cnf_transformation,[],[f52]) ).
% 6.37/1.49  
% 6.37/1.49  cnf(c_1536,plain,
% 6.37/1.49      ( ~ r2_hidden(k4_tarski(sK8,sK7),sK6)
% 6.37/1.49      | r2_hidden(sK7,k2_relat_1(sK6)) ),
% 6.37/1.49      inference(instantiation,[status(thm)],[c_11]) ).
% 6.37/1.49  
% 6.37/1.49  cnf(c_1537,plain,
% 6.37/1.49      ( r2_hidden(k4_tarski(sK8,sK7),sK6) != iProver_top
% 6.37/1.49      | r2_hidden(sK7,k2_relat_1(sK6)) = iProver_top ),
% 6.37/1.49      inference(predicate_to_equality,[status(thm)],[c_1536]) ).
% 6.37/1.49  
% 6.37/1.49  cnf(c_15,negated_conjecture,
% 6.37/1.49      ( r2_hidden(k4_tarski(sK8,sK7),sK6)
% 6.37/1.49      | r2_hidden(sK7,k2_relset_1(sK5,sK4,sK6)) ),
% 6.37/1.49      inference(cnf_transformation,[],[f50]) ).
% 6.37/1.49  
% 6.37/1.49  cnf(c_776,plain,
% 6.37/1.49      ( r2_hidden(k4_tarski(sK8,sK7),sK6) = iProver_top
% 6.37/1.49      | r2_hidden(sK7,k2_relset_1(sK5,sK4,sK6)) = iProver_top ),
% 6.37/1.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 6.37/1.49  
% 6.37/1.49  cnf(c_1558,plain,
% 6.37/1.49      ( r2_hidden(k4_tarski(sK8,sK7),sK6) = iProver_top
% 6.37/1.49      | r2_hidden(sK7,k2_relat_1(sK6)) = iProver_top ),
% 6.37/1.49      inference(demodulation,[status(thm)],[c_1353,c_776]) ).
% 6.37/1.49  
% 6.37/1.49  cnf(c_1658,plain,
% 6.37/1.49      ( r2_hidden(sK7,k2_relat_1(sK6)) = iProver_top ),
% 6.37/1.49      inference(global_propositional_subsumption,
% 6.37/1.49                [status(thm)],
% 6.37/1.49                [c_1559,c_1537,c_1558]) ).
% 6.37/1.49  
% 6.37/1.49  cnf(c_1660,plain,
% 6.37/1.49      ( r2_hidden(sK7,k2_relat_1(sK6)) ),
% 6.37/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_1658]) ).
% 6.37/1.49  
% 6.37/1.49  cnf(c_17047,plain,
% 6.37/1.49      ( ~ r2_hidden(k4_tarski(X0,sK7),sK6) | ~ m1_subset_1(X0,sK5) ),
% 6.37/1.49      inference(global_propositional_subsumption,
% 6.37/1.49                [status(thm)],
% 6.37/1.49                [c_14,c_1577,c_1660]) ).
% 6.37/1.49  
% 6.37/1.49  cnf(c_17048,negated_conjecture,
% 6.37/1.49      ( ~ m1_subset_1(X0,sK5) | ~ r2_hidden(k4_tarski(X0,sK7),sK6) ),
% 6.37/1.49      inference(renaming,[status(thm)],[c_17047]) ).
% 6.37/1.49  
% 6.37/1.49  cnf(c_12,plain,
% 6.37/1.49      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 6.37/1.49      | r2_hidden(k4_tarski(sK3(X1,X0),X0),X1) ),
% 6.37/1.49      inference(cnf_transformation,[],[f53]) ).
% 6.37/1.49  
% 6.37/1.49  cnf(c_17418,plain,
% 6.37/1.49      ( ~ m1_subset_1(sK3(sK6,sK7),sK5)
% 6.37/1.49      | ~ r2_hidden(sK7,k2_relat_1(sK6)) ),
% 6.37/1.49      inference(resolution,[status(thm)],[c_17048,c_12]) ).
% 6.37/1.49  
% 6.37/1.49  cnf(c_779,plain,
% 6.37/1.49      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 6.37/1.49      | r2_hidden(k4_tarski(sK3(X1,X0),X0),X1) = iProver_top ),
% 6.37/1.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 6.37/1.49  
% 6.37/1.49  cnf(c_1649,plain,
% 6.37/1.49      ( r2_hidden(k4_tarski(X0,sK7),sK6) != iProver_top
% 6.37/1.49      | m1_subset_1(X0,sK5) != iProver_top ),
% 6.37/1.49      inference(global_propositional_subsumption,
% 6.37/1.49                [status(thm)],
% 6.37/1.49                [c_1560,c_1537,c_1558]) ).
% 6.37/1.49  
% 6.37/1.49  cnf(c_1650,plain,
% 6.37/1.49      ( m1_subset_1(X0,sK5) != iProver_top
% 6.37/1.49      | r2_hidden(k4_tarski(X0,sK7),sK6) != iProver_top ),
% 6.37/1.49      inference(renaming,[status(thm)],[c_1649]) ).
% 6.37/1.49  
% 6.37/1.49  cnf(c_2256,plain,
% 6.37/1.49      ( m1_subset_1(sK3(sK6,sK7),sK5) != iProver_top
% 6.37/1.49      | r2_hidden(sK7,k2_relat_1(sK6)) != iProver_top ),
% 6.37/1.49      inference(superposition,[status(thm)],[c_779,c_1650]) ).
% 6.37/1.49  
% 6.37/1.49  cnf(c_2278,plain,
% 6.37/1.49      ( ~ m1_subset_1(sK3(sK6,sK7),sK5)
% 6.37/1.49      | ~ r2_hidden(sK7,k2_relat_1(sK6)) ),
% 6.37/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_2256]) ).
% 6.37/1.49  
% 6.37/1.49  cnf(c_17421,plain,
% 6.37/1.49      ( ~ m1_subset_1(sK3(sK6,sK7),sK5) ),
% 6.37/1.49      inference(global_propositional_subsumption,
% 6.37/1.49                [status(thm)],
% 6.37/1.49                [c_17418,c_1660,c_2278]) ).
% 6.37/1.49  
% 6.37/1.49  cnf(c_0,plain,
% 6.37/1.49      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 6.37/1.49      inference(cnf_transformation,[],[f36]) ).
% 6.37/1.49  
% 6.37/1.49  cnf(c_1,plain,
% 6.37/1.49      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 6.37/1.49      inference(cnf_transformation,[],[f35]) ).
% 6.37/1.49  
% 6.37/1.49  cnf(c_1054,plain,
% 6.37/1.49      ( r1_tarski(X0,X0) ),
% 6.37/1.49      inference(resolution,[status(thm)],[c_0,c_1]) ).
% 6.37/1.49  
% 6.37/1.49  cnf(c_8,plain,
% 6.37/1.49      ( m1_subset_1(X0,X1)
% 6.37/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 6.37/1.49      | ~ r2_hidden(X0,X2) ),
% 6.37/1.49      inference(cnf_transformation,[],[f42]) ).
% 6.37/1.49  
% 6.37/1.49  cnf(c_6,plain,
% 6.37/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 6.37/1.49      inference(cnf_transformation,[],[f41]) ).
% 6.37/1.49  
% 6.37/1.49  cnf(c_1482,plain,
% 6.37/1.49      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_tarski(X2,X1) ),
% 6.37/1.49      inference(resolution,[status(thm)],[c_8,c_6]) ).
% 6.37/1.49  
% 6.37/1.49  cnf(c_4375,plain,
% 6.37/1.49      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 6.37/1.49      inference(resolution,[status(thm)],[c_1054,c_1482]) ).
% 6.37/1.49  
% 6.37/1.49  cnf(c_17745,plain,
% 6.37/1.49      ( ~ r2_hidden(sK3(sK6,sK7),sK5) ),
% 6.37/1.49      inference(resolution,[status(thm)],[c_17421,c_4375]) ).
% 6.37/1.49  
% 6.37/1.49  cnf(c_5,plain,
% 6.37/1.49      ( r2_hidden(X0,X1)
% 6.37/1.49      | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
% 6.37/1.49      inference(cnf_transformation,[],[f37]) ).
% 6.37/1.49  
% 6.37/1.49  cnf(c_2,plain,
% 6.37/1.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 6.37/1.49      inference(cnf_transformation,[],[f34]) ).
% 6.37/1.49  
% 6.37/1.49  cnf(c_7,plain,
% 6.37/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 6.37/1.49      inference(cnf_transformation,[],[f40]) ).
% 6.37/1.49  
% 6.37/1.49  cnf(c_1002,plain,
% 6.37/1.49      ( r1_tarski(sK6,k2_zfmisc_1(sK5,sK4)) ),
% 6.37/1.49      inference(resolution,[status(thm)],[c_7,c_17]) ).
% 6.37/1.49  
% 6.37/1.49  cnf(c_1072,plain,
% 6.37/1.49      ( r2_hidden(X0,k2_zfmisc_1(sK5,sK4)) | ~ r2_hidden(X0,sK6) ),
% 6.37/1.49      inference(resolution,[status(thm)],[c_2,c_1002]) ).
% 6.37/1.49  
% 6.37/1.49  cnf(c_1384,plain,
% 6.37/1.49      ( r2_hidden(X0,sK5) | ~ r2_hidden(k4_tarski(X0,X1),sK6) ),
% 6.37/1.49      inference(resolution,[status(thm)],[c_5,c_1072]) ).
% 6.37/1.49  
% 6.37/1.49  cnf(c_1892,plain,
% 6.37/1.49      ( ~ r2_hidden(X0,k2_relat_1(sK6)) | r2_hidden(sK3(sK6,X0),sK5) ),
% 6.37/1.49      inference(resolution,[status(thm)],[c_1384,c_12]) ).
% 6.37/1.49  
% 6.37/1.49  cnf(c_18152,plain,
% 6.37/1.49      ( ~ r2_hidden(sK7,k2_relat_1(sK6)) ),
% 6.37/1.49      inference(resolution,[status(thm)],[c_17745,c_1892]) ).
% 6.37/1.49  
% 6.37/1.49  cnf(contradiction,plain,
% 6.37/1.49      ( $false ),
% 6.37/1.49      inference(minisat,[status(thm)],[c_18152,c_1660]) ).
% 6.37/1.49  
% 6.37/1.49  
% 6.37/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 6.37/1.49  
% 6.37/1.49  ------                               Statistics
% 6.37/1.49  
% 6.37/1.49  ------ Selected
% 6.37/1.49  
% 6.37/1.49  total_time:                             0.603
% 6.37/1.49  
%------------------------------------------------------------------------------
