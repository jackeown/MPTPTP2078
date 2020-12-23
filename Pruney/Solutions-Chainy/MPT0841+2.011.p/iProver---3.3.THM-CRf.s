%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:57:00 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 563 expanded)
%              Number of clauses        :   64 ( 184 expanded)
%              Number of leaves         :   17 ( 127 expanded)
%              Depth                    :   20
%              Number of atoms          :  493 (3243 expanded)
%              Number of equality atoms :  127 ( 243 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f31])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK3(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2)
        & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2)
            & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f33])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2))
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f10,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ~ v1_xboole_0(X2)
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                 => ! [X4] :
                      ( m1_subset_1(X4,X0)
                     => ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                      <=> ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X5,X4),X3)
                            & m1_subset_1(X5,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ~ v1_xboole_0(X2)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                   => ! [X4] :
                        ( m1_subset_1(X4,X0)
                       => ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                        <=> ? [X5] :
                              ( r2_hidden(X5,X1)
                              & r2_hidden(k4_tarski(X5,X4),X3)
                              & m1_subset_1(X5,X2) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f12,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
       => ! [X4] :
            ( m1_subset_1(X4,X0)
           => ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
            <=> ? [X5] :
                  ( r2_hidden(X5,X1)
                  & r2_hidden(k4_tarski(X5,X4),X3)
                  & m1_subset_1(X5,X2) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
          <~> ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X5,X4),X3)
                & m1_subset_1(X5,X2) ) )
          & m1_subset_1(X4,X0) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f35,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ! [X5] :
                ( ~ r2_hidden(X5,X1)
                | ~ r2_hidden(k4_tarski(X5,X4),X3)
                | ~ m1_subset_1(X5,X2) )
            | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X5,X4),X3)
                & m1_subset_1(X5,X2) )
            | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
          & m1_subset_1(X4,X0) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f36,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ! [X5] :
                ( ~ r2_hidden(X5,X1)
                | ~ r2_hidden(k4_tarski(X5,X4),X3)
                | ~ m1_subset_1(X5,X2) )
            | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X5,X4),X3)
                & m1_subset_1(X5,X2) )
            | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
          & m1_subset_1(X4,X0) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f35])).

fof(f37,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ! [X5] :
                ( ~ r2_hidden(X5,X1)
                | ~ r2_hidden(k4_tarski(X5,X4),X3)
                | ~ m1_subset_1(X5,X2) )
            | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
          & ( ? [X6] :
                ( r2_hidden(X6,X1)
                & r2_hidden(k4_tarski(X6,X4),X3)
                & m1_subset_1(X6,X2) )
            | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
          & m1_subset_1(X4,X0) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(rectify,[],[f36])).

fof(f40,plain,(
    ! [X4,X2,X3,X1] :
      ( ? [X6] :
          ( r2_hidden(X6,X1)
          & r2_hidden(k4_tarski(X6,X4),X3)
          & m1_subset_1(X6,X2) )
     => ( r2_hidden(sK9,X1)
        & r2_hidden(k4_tarski(sK9,X4),X3)
        & m1_subset_1(sK9,X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ( ! [X5] :
                ( ~ r2_hidden(X5,X1)
                | ~ r2_hidden(k4_tarski(X5,X4),X3)
                | ~ m1_subset_1(X5,X2) )
            | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
          & ( ? [X6] :
                ( r2_hidden(X6,X1)
                & r2_hidden(k4_tarski(X6,X4),X3)
                & m1_subset_1(X6,X2) )
            | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
          & m1_subset_1(X4,X0) )
     => ( ( ! [X5] :
              ( ~ r2_hidden(X5,X1)
              | ~ r2_hidden(k4_tarski(X5,sK8),X3)
              | ~ m1_subset_1(X5,X2) )
          | ~ r2_hidden(sK8,k7_relset_1(X2,X0,X3,X1)) )
        & ( ? [X6] :
              ( r2_hidden(X6,X1)
              & r2_hidden(k4_tarski(X6,sK8),X3)
              & m1_subset_1(X6,X2) )
          | r2_hidden(sK8,k7_relset_1(X2,X0,X3,X1)) )
        & m1_subset_1(sK8,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ( ! [X5] :
                  ( ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(k4_tarski(X5,X4),X3)
                  | ~ m1_subset_1(X5,X2) )
              | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
            & ( ? [X6] :
                  ( r2_hidden(X6,X1)
                  & r2_hidden(k4_tarski(X6,X4),X3)
                  & m1_subset_1(X6,X2) )
              | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
            & m1_subset_1(X4,X0) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
   => ( ? [X4] :
          ( ( ! [X5] :
                ( ~ r2_hidden(X5,sK5)
                | ~ r2_hidden(k4_tarski(X5,X4),sK7)
                | ~ m1_subset_1(X5,sK6) )
            | ~ r2_hidden(X4,k7_relset_1(sK6,sK4,sK7,sK5)) )
          & ( ? [X6] :
                ( r2_hidden(X6,sK5)
                & r2_hidden(k4_tarski(X6,X4),sK7)
                & m1_subset_1(X6,sK6) )
            | r2_hidden(X4,k7_relset_1(sK6,sK4,sK7,sK5)) )
          & m1_subset_1(X4,sK4) )
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ( ! [X5] :
          ( ~ r2_hidden(X5,sK5)
          | ~ r2_hidden(k4_tarski(X5,sK8),sK7)
          | ~ m1_subset_1(X5,sK6) )
      | ~ r2_hidden(sK8,k7_relset_1(sK6,sK4,sK7,sK5)) )
    & ( ( r2_hidden(sK9,sK5)
        & r2_hidden(k4_tarski(sK9,sK8),sK7)
        & m1_subset_1(sK9,sK6) )
      | r2_hidden(sK8,k7_relset_1(sK6,sK4,sK7,sK5)) )
    & m1_subset_1(sK8,sK4)
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9])],[f37,f40,f39,f38])).

fof(f64,plain,
    ( r2_hidden(k4_tarski(sK9,sK8),sK7)
    | r2_hidden(sK8,k7_relset_1(sK6,sK4,sK7,sK5)) ),
    inference(cnf_transformation,[],[f41])).

fof(f66,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK5)
      | ~ r2_hidden(k4_tarski(X5,sK8),sK7)
      | ~ m1_subset_1(X5,sK6)
      | ~ r2_hidden(sK8,k7_relset_1(sK6,sK4,sK7,sK5)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f61,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) ),
    inference(cnf_transformation,[],[f41])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X4,X3),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) ) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( r2_hidden(X5,X1)
                      & r2_hidden(k4_tarski(X5,X3),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X7,X6),X0) ) )
                & ( ? [X8] :
                      ( r2_hidden(X8,X1)
                      & r2_hidden(k4_tarski(X8,X6),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f24])).

fof(f28,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X8,X6),X0) )
     => ( r2_hidden(sK2(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(sK2(X0,X1,X6),X6),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X5,X3),X0) )
     => ( r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK1(X0,X1,X2),X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X1)
                | ~ r2_hidden(k4_tarski(X4,X3),X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X5,X3),X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X1)
              | ~ r2_hidden(k4_tarski(X4,sK0(X0,X1,X2)),X0) )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(X5,sK0(X0,X1,X2)),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(X4,sK0(X0,X1,X2)),X0) )
                | ~ r2_hidden(sK0(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK1(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK1(X0,X1,X2),sK0(X0,X1,X2)),X0) )
                | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X7,X6),X0) ) )
                & ( ( r2_hidden(sK2(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(sK2(X0,X1,X6),X6),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f28,f27,f26])).

fof(f48,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X7,X6),X0)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f67,plain,(
    ! [X6,X0,X7,X1] :
      ( r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X7,X6),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f65,plain,
    ( r2_hidden(sK9,sK5)
    | r2_hidden(sK8,k7_relset_1(sK6,sK4,sK7,sK5)) ),
    inference(cnf_transformation,[],[f41])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK3(X0,X2,X1),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1190,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK3(X0,X2,X1),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1202,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1200,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2692,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | m1_subset_1(X0,X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1202,c_1200])).

cnf(c_4357,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r1_tarski(k1_relat_1(X1),X3) != iProver_top
    | m1_subset_1(sK3(X0,X2,X1),X3) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1190,c_2692])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK3(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1192,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK3(X0,X2,X1),X2) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK3(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1191,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(sK3(X0,X2,X1),X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_21,negated_conjecture,
    ( r2_hidden(k4_tarski(sK9,sK8),sK7)
    | r2_hidden(sK8,k7_relset_1(sK6,sK4,sK7,sK5)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1186,plain,
    ( r2_hidden(k4_tarski(sK9,sK8),sK7) = iProver_top
    | r2_hidden(sK8,k7_relset_1(sK6,sK4,sK7,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_19,negated_conjecture,
    ( ~ r2_hidden(X0,sK5)
    | ~ r2_hidden(k4_tarski(X0,sK8),sK7)
    | ~ r2_hidden(sK8,k7_relset_1(sK6,sK4,sK7,sK5))
    | ~ m1_subset_1(X0,sK6) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1188,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(k4_tarski(X0,sK8),sK7) != iProver_top
    | r2_hidden(sK8,k7_relset_1(sK6,sK4,sK7,sK5)) != iProver_top
    | m1_subset_1(X0,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1485,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(k4_tarski(X0,sK8),sK7) != iProver_top
    | r2_hidden(k4_tarski(sK9,sK8),sK7) = iProver_top
    | m1_subset_1(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1186,c_1188])).

cnf(c_2925,plain,
    ( r2_hidden(sK3(sK8,X0,sK7),sK5) != iProver_top
    | r2_hidden(k4_tarski(sK9,sK8),sK7) = iProver_top
    | r2_hidden(sK8,k9_relat_1(sK7,X0)) != iProver_top
    | m1_subset_1(sK3(sK8,X0,sK7),sK6) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1191,c_1485])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_25,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1371,plain,
    ( r1_tarski(sK7,k2_zfmisc_1(sK6,sK4))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1372,plain,
    ( r1_tarski(sK7,k2_zfmisc_1(sK6,sK4)) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1371])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_200,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_0])).

cnf(c_248,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_3,c_200])).

cnf(c_1470,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_248])).

cnf(c_1551,plain,
    ( ~ r1_tarski(sK7,k2_zfmisc_1(sK6,sK4))
    | ~ v1_relat_1(k2_zfmisc_1(sK6,sK4))
    | v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_1470])).

cnf(c_1552,plain,
    ( r1_tarski(sK7,k2_zfmisc_1(sK6,sK4)) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK6,sK4)) != iProver_top
    | v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1551])).

cnf(c_12,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1566,plain,
    ( v1_relat_1(k2_zfmisc_1(sK6,sK4)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1567,plain,
    ( v1_relat_1(k2_zfmisc_1(sK6,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1566])).

cnf(c_3310,plain,
    ( m1_subset_1(sK3(sK8,X0,sK7),sK6) != iProver_top
    | r2_hidden(sK8,k9_relat_1(sK7,X0)) != iProver_top
    | r2_hidden(k4_tarski(sK9,sK8),sK7) = iProver_top
    | r2_hidden(sK3(sK8,X0,sK7),sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2925,c_25,c_1372,c_1552,c_1567])).

cnf(c_3311,plain,
    ( r2_hidden(sK3(sK8,X0,sK7),sK5) != iProver_top
    | r2_hidden(k4_tarski(sK9,sK8),sK7) = iProver_top
    | r2_hidden(sK8,k9_relat_1(sK7,X0)) != iProver_top
    | m1_subset_1(sK3(sK8,X0,sK7),sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_3310])).

cnf(c_3320,plain,
    ( r2_hidden(k4_tarski(sK9,sK8),sK7) = iProver_top
    | r2_hidden(sK8,k9_relat_1(sK7,sK5)) != iProver_top
    | m1_subset_1(sK3(sK8,sK5,sK7),sK6) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1192,c_3311])).

cnf(c_1183,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1189,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1795,plain,
    ( k7_relset_1(sK6,sK4,sK7,X0) = k9_relat_1(sK7,X0) ),
    inference(superposition,[status(thm)],[c_1183,c_1189])).

cnf(c_2060,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(k4_tarski(X0,sK8),sK7) != iProver_top
    | r2_hidden(sK8,k9_relat_1(sK7,sK5)) != iProver_top
    | m1_subset_1(X0,sK6) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1795,c_1188])).

cnf(c_2924,plain,
    ( r2_hidden(sK3(sK8,X0,sK7),sK5) != iProver_top
    | r2_hidden(sK8,k9_relat_1(sK7,X0)) != iProver_top
    | r2_hidden(sK8,k9_relat_1(sK7,sK5)) != iProver_top
    | m1_subset_1(sK3(sK8,X0,sK7),sK6) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1191,c_2060])).

cnf(c_3419,plain,
    ( m1_subset_1(sK3(sK8,X0,sK7),sK6) != iProver_top
    | r2_hidden(sK8,k9_relat_1(sK7,sK5)) != iProver_top
    | r2_hidden(sK8,k9_relat_1(sK7,X0)) != iProver_top
    | r2_hidden(sK3(sK8,X0,sK7),sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2924,c_25,c_1372,c_1552,c_1567])).

cnf(c_3420,plain,
    ( r2_hidden(sK3(sK8,X0,sK7),sK5) != iProver_top
    | r2_hidden(sK8,k9_relat_1(sK7,X0)) != iProver_top
    | r2_hidden(sK8,k9_relat_1(sK7,sK5)) != iProver_top
    | m1_subset_1(sK3(sK8,X0,sK7),sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_3419])).

cnf(c_3429,plain,
    ( r2_hidden(sK8,k9_relat_1(sK7,sK5)) != iProver_top
    | m1_subset_1(sK3(sK8,sK5,sK7),sK6) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1192,c_3420])).

cnf(c_2057,plain,
    ( r2_hidden(k4_tarski(sK9,sK8),sK7) = iProver_top
    | r2_hidden(sK8,k9_relat_1(sK7,sK5)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1795,c_1186])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k9_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1196,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,k9_relat_1(X3,X1)) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),X3) != iProver_top
    | v1_relat_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3587,plain,
    ( r2_hidden(sK9,X0) != iProver_top
    | r2_hidden(sK8,k9_relat_1(sK7,X0)) = iProver_top
    | r2_hidden(sK8,k9_relat_1(sK7,sK5)) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2057,c_1196])).

cnf(c_4153,plain,
    ( r2_hidden(sK8,k9_relat_1(sK7,sK5)) = iProver_top
    | r2_hidden(sK8,k9_relat_1(sK7,X0)) = iProver_top
    | r2_hidden(sK9,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3587,c_25,c_1372,c_1552,c_1567])).

cnf(c_4154,plain,
    ( r2_hidden(sK9,X0) != iProver_top
    | r2_hidden(sK8,k9_relat_1(sK7,X0)) = iProver_top
    | r2_hidden(sK8,k9_relat_1(sK7,sK5)) = iProver_top ),
    inference(renaming,[status(thm)],[c_4153])).

cnf(c_4162,plain,
    ( r2_hidden(sK9,sK5) != iProver_top
    | r2_hidden(sK8,k9_relat_1(sK7,sK5)) = iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_4154])).

cnf(c_4213,plain,
    ( r2_hidden(sK9,sK5) != iProver_top
    | r2_hidden(sK8,k9_relat_1(sK7,sK5)) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4162])).

cnf(c_20,negated_conjecture,
    ( r2_hidden(sK9,sK5)
    | r2_hidden(sK8,k7_relset_1(sK6,sK4,sK7,sK5)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1187,plain,
    ( r2_hidden(sK9,sK5) = iProver_top
    | r2_hidden(sK8,k7_relset_1(sK6,sK4,sK7,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2058,plain,
    ( r2_hidden(sK9,sK5) = iProver_top
    | r2_hidden(sK8,k9_relat_1(sK7,sK5)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1795,c_1187])).

cnf(c_4215,plain,
    ( r2_hidden(sK8,k9_relat_1(sK7,sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4213,c_2058])).

cnf(c_4722,plain,
    ( m1_subset_1(sK3(sK8,sK5,sK7),sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3320,c_25,c_1372,c_1552,c_1567,c_2058,c_3429,c_4213])).

cnf(c_5640,plain,
    ( r2_hidden(sK8,k9_relat_1(sK7,sK5)) != iProver_top
    | r1_tarski(k1_relat_1(sK7),sK6) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_4357,c_4722])).

cnf(c_17,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_11,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_332,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_17,c_11])).

cnf(c_1181,plain,
    ( r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_332])).

cnf(c_1579,plain,
    ( r1_tarski(k1_relat_1(sK7),sK6) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1183,c_1181])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5640,c_4215,c_1579,c_1567,c_1552,c_1372,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:21:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 2.04/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.01  
% 2.04/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.04/1.01  
% 2.04/1.01  ------  iProver source info
% 2.04/1.01  
% 2.04/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.04/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.04/1.01  git: non_committed_changes: false
% 2.04/1.01  git: last_make_outside_of_git: false
% 2.04/1.01  
% 2.04/1.01  ------ 
% 2.04/1.01  
% 2.04/1.01  ------ Input Options
% 2.04/1.01  
% 2.04/1.01  --out_options                           all
% 2.04/1.01  --tptp_safe_out                         true
% 2.04/1.01  --problem_path                          ""
% 2.04/1.01  --include_path                          ""
% 2.04/1.01  --clausifier                            res/vclausify_rel
% 2.04/1.01  --clausifier_options                    --mode clausify
% 2.04/1.01  --stdin                                 false
% 2.04/1.01  --stats_out                             all
% 2.04/1.01  
% 2.04/1.01  ------ General Options
% 2.04/1.01  
% 2.04/1.01  --fof                                   false
% 2.04/1.01  --time_out_real                         305.
% 2.04/1.01  --time_out_virtual                      -1.
% 2.04/1.01  --symbol_type_check                     false
% 2.04/1.01  --clausify_out                          false
% 2.04/1.01  --sig_cnt_out                           false
% 2.04/1.01  --trig_cnt_out                          false
% 2.04/1.01  --trig_cnt_out_tolerance                1.
% 2.04/1.01  --trig_cnt_out_sk_spl                   false
% 2.04/1.01  --abstr_cl_out                          false
% 2.04/1.01  
% 2.04/1.01  ------ Global Options
% 2.04/1.01  
% 2.04/1.01  --schedule                              default
% 2.04/1.01  --add_important_lit                     false
% 2.04/1.01  --prop_solver_per_cl                    1000
% 2.04/1.01  --min_unsat_core                        false
% 2.04/1.01  --soft_assumptions                      false
% 2.04/1.01  --soft_lemma_size                       3
% 2.04/1.01  --prop_impl_unit_size                   0
% 2.04/1.01  --prop_impl_unit                        []
% 2.04/1.01  --share_sel_clauses                     true
% 2.04/1.01  --reset_solvers                         false
% 2.04/1.01  --bc_imp_inh                            [conj_cone]
% 2.04/1.01  --conj_cone_tolerance                   3.
% 2.04/1.01  --extra_neg_conj                        none
% 2.04/1.01  --large_theory_mode                     true
% 2.04/1.01  --prolific_symb_bound                   200
% 2.04/1.01  --lt_threshold                          2000
% 2.04/1.01  --clause_weak_htbl                      true
% 2.04/1.01  --gc_record_bc_elim                     false
% 2.04/1.01  
% 2.04/1.01  ------ Preprocessing Options
% 2.04/1.01  
% 2.04/1.01  --preprocessing_flag                    true
% 2.04/1.01  --time_out_prep_mult                    0.1
% 2.04/1.01  --splitting_mode                        input
% 2.04/1.01  --splitting_grd                         true
% 2.04/1.01  --splitting_cvd                         false
% 2.04/1.01  --splitting_cvd_svl                     false
% 2.04/1.01  --splitting_nvd                         32
% 2.04/1.01  --sub_typing                            true
% 2.04/1.01  --prep_gs_sim                           true
% 2.04/1.01  --prep_unflatten                        true
% 2.04/1.01  --prep_res_sim                          true
% 2.04/1.01  --prep_upred                            true
% 2.04/1.01  --prep_sem_filter                       exhaustive
% 2.04/1.01  --prep_sem_filter_out                   false
% 2.04/1.01  --pred_elim                             true
% 2.04/1.01  --res_sim_input                         true
% 2.04/1.01  --eq_ax_congr_red                       true
% 2.04/1.01  --pure_diseq_elim                       true
% 2.04/1.01  --brand_transform                       false
% 2.04/1.01  --non_eq_to_eq                          false
% 2.04/1.01  --prep_def_merge                        true
% 2.04/1.01  --prep_def_merge_prop_impl              false
% 2.04/1.02  --prep_def_merge_mbd                    true
% 2.04/1.02  --prep_def_merge_tr_red                 false
% 2.04/1.02  --prep_def_merge_tr_cl                  false
% 2.04/1.02  --smt_preprocessing                     true
% 2.04/1.02  --smt_ac_axioms                         fast
% 2.04/1.02  --preprocessed_out                      false
% 2.04/1.02  --preprocessed_stats                    false
% 2.04/1.02  
% 2.04/1.02  ------ Abstraction refinement Options
% 2.04/1.02  
% 2.04/1.02  --abstr_ref                             []
% 2.04/1.02  --abstr_ref_prep                        false
% 2.04/1.02  --abstr_ref_until_sat                   false
% 2.04/1.02  --abstr_ref_sig_restrict                funpre
% 2.04/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.04/1.02  --abstr_ref_under                       []
% 2.04/1.02  
% 2.04/1.02  ------ SAT Options
% 2.04/1.02  
% 2.04/1.02  --sat_mode                              false
% 2.04/1.02  --sat_fm_restart_options                ""
% 2.04/1.02  --sat_gr_def                            false
% 2.04/1.02  --sat_epr_types                         true
% 2.04/1.02  --sat_non_cyclic_types                  false
% 2.04/1.02  --sat_finite_models                     false
% 2.04/1.02  --sat_fm_lemmas                         false
% 2.04/1.02  --sat_fm_prep                           false
% 2.04/1.02  --sat_fm_uc_incr                        true
% 2.04/1.02  --sat_out_model                         small
% 2.04/1.02  --sat_out_clauses                       false
% 2.04/1.02  
% 2.04/1.02  ------ QBF Options
% 2.04/1.02  
% 2.04/1.02  --qbf_mode                              false
% 2.04/1.02  --qbf_elim_univ                         false
% 2.04/1.02  --qbf_dom_inst                          none
% 2.04/1.02  --qbf_dom_pre_inst                      false
% 2.04/1.02  --qbf_sk_in                             false
% 2.04/1.02  --qbf_pred_elim                         true
% 2.04/1.02  --qbf_split                             512
% 2.04/1.02  
% 2.04/1.02  ------ BMC1 Options
% 2.04/1.02  
% 2.04/1.02  --bmc1_incremental                      false
% 2.04/1.02  --bmc1_axioms                           reachable_all
% 2.04/1.02  --bmc1_min_bound                        0
% 2.04/1.02  --bmc1_max_bound                        -1
% 2.04/1.02  --bmc1_max_bound_default                -1
% 2.04/1.02  --bmc1_symbol_reachability              true
% 2.04/1.02  --bmc1_property_lemmas                  false
% 2.04/1.02  --bmc1_k_induction                      false
% 2.04/1.02  --bmc1_non_equiv_states                 false
% 2.04/1.02  --bmc1_deadlock                         false
% 2.04/1.02  --bmc1_ucm                              false
% 2.04/1.02  --bmc1_add_unsat_core                   none
% 2.04/1.02  --bmc1_unsat_core_children              false
% 2.04/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.04/1.02  --bmc1_out_stat                         full
% 2.04/1.02  --bmc1_ground_init                      false
% 2.04/1.02  --bmc1_pre_inst_next_state              false
% 2.04/1.02  --bmc1_pre_inst_state                   false
% 2.04/1.02  --bmc1_pre_inst_reach_state             false
% 2.04/1.02  --bmc1_out_unsat_core                   false
% 2.04/1.02  --bmc1_aig_witness_out                  false
% 2.04/1.02  --bmc1_verbose                          false
% 2.04/1.02  --bmc1_dump_clauses_tptp                false
% 2.04/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.04/1.02  --bmc1_dump_file                        -
% 2.04/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.04/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.04/1.02  --bmc1_ucm_extend_mode                  1
% 2.04/1.02  --bmc1_ucm_init_mode                    2
% 2.04/1.02  --bmc1_ucm_cone_mode                    none
% 2.04/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.04/1.02  --bmc1_ucm_relax_model                  4
% 2.04/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.04/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.04/1.02  --bmc1_ucm_layered_model                none
% 2.04/1.02  --bmc1_ucm_max_lemma_size               10
% 2.04/1.02  
% 2.04/1.02  ------ AIG Options
% 2.04/1.02  
% 2.04/1.02  --aig_mode                              false
% 2.04/1.02  
% 2.04/1.02  ------ Instantiation Options
% 2.04/1.02  
% 2.04/1.02  --instantiation_flag                    true
% 2.04/1.02  --inst_sos_flag                         false
% 2.04/1.02  --inst_sos_phase                        true
% 2.04/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.04/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.04/1.02  --inst_lit_sel_side                     num_symb
% 2.04/1.02  --inst_solver_per_active                1400
% 2.04/1.02  --inst_solver_calls_frac                1.
% 2.04/1.02  --inst_passive_queue_type               priority_queues
% 2.04/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.04/1.02  --inst_passive_queues_freq              [25;2]
% 2.04/1.02  --inst_dismatching                      true
% 2.04/1.02  --inst_eager_unprocessed_to_passive     true
% 2.04/1.02  --inst_prop_sim_given                   true
% 2.04/1.02  --inst_prop_sim_new                     false
% 2.04/1.02  --inst_subs_new                         false
% 2.04/1.02  --inst_eq_res_simp                      false
% 2.04/1.02  --inst_subs_given                       false
% 2.04/1.02  --inst_orphan_elimination               true
% 2.04/1.02  --inst_learning_loop_flag               true
% 2.04/1.02  --inst_learning_start                   3000
% 2.04/1.02  --inst_learning_factor                  2
% 2.04/1.02  --inst_start_prop_sim_after_learn       3
% 2.04/1.02  --inst_sel_renew                        solver
% 2.04/1.02  --inst_lit_activity_flag                true
% 2.04/1.02  --inst_restr_to_given                   false
% 2.04/1.02  --inst_activity_threshold               500
% 2.04/1.02  --inst_out_proof                        true
% 2.04/1.02  
% 2.04/1.02  ------ Resolution Options
% 2.04/1.02  
% 2.04/1.02  --resolution_flag                       true
% 2.04/1.02  --res_lit_sel                           adaptive
% 2.04/1.02  --res_lit_sel_side                      none
% 2.04/1.02  --res_ordering                          kbo
% 2.04/1.02  --res_to_prop_solver                    active
% 2.04/1.02  --res_prop_simpl_new                    false
% 2.04/1.02  --res_prop_simpl_given                  true
% 2.04/1.02  --res_passive_queue_type                priority_queues
% 2.04/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.04/1.02  --res_passive_queues_freq               [15;5]
% 2.04/1.02  --res_forward_subs                      full
% 2.04/1.02  --res_backward_subs                     full
% 2.04/1.02  --res_forward_subs_resolution           true
% 2.04/1.02  --res_backward_subs_resolution          true
% 2.04/1.02  --res_orphan_elimination                true
% 2.04/1.02  --res_time_limit                        2.
% 2.04/1.02  --res_out_proof                         true
% 2.04/1.02  
% 2.04/1.02  ------ Superposition Options
% 2.04/1.02  
% 2.04/1.02  --superposition_flag                    true
% 2.04/1.02  --sup_passive_queue_type                priority_queues
% 2.04/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.04/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.04/1.02  --demod_completeness_check              fast
% 2.04/1.02  --demod_use_ground                      true
% 2.04/1.02  --sup_to_prop_solver                    passive
% 2.04/1.02  --sup_prop_simpl_new                    true
% 2.04/1.02  --sup_prop_simpl_given                  true
% 2.04/1.02  --sup_fun_splitting                     false
% 2.04/1.02  --sup_smt_interval                      50000
% 2.04/1.02  
% 2.04/1.02  ------ Superposition Simplification Setup
% 2.04/1.02  
% 2.04/1.02  --sup_indices_passive                   []
% 2.04/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.04/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.04/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.04/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.04/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.04/1.02  --sup_full_bw                           [BwDemod]
% 2.04/1.02  --sup_immed_triv                        [TrivRules]
% 2.04/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.04/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.04/1.02  --sup_immed_bw_main                     []
% 2.04/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.04/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.04/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.04/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.04/1.02  
% 2.04/1.02  ------ Combination Options
% 2.04/1.02  
% 2.04/1.02  --comb_res_mult                         3
% 2.04/1.02  --comb_sup_mult                         2
% 2.04/1.02  --comb_inst_mult                        10
% 2.04/1.02  
% 2.04/1.02  ------ Debug Options
% 2.04/1.02  
% 2.04/1.02  --dbg_backtrace                         false
% 2.04/1.02  --dbg_dump_prop_clauses                 false
% 2.04/1.02  --dbg_dump_prop_clauses_file            -
% 2.04/1.02  --dbg_out_stat                          false
% 2.04/1.02  ------ Parsing...
% 2.04/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.04/1.02  
% 2.04/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.04/1.02  
% 2.04/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.04/1.02  
% 2.04/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.04/1.02  ------ Proving...
% 2.04/1.02  ------ Problem Properties 
% 2.04/1.02  
% 2.04/1.02  
% 2.04/1.02  clauses                                 22
% 2.04/1.02  conjectures                             6
% 2.04/1.02  EPR                                     2
% 2.04/1.02  Horn                                    17
% 2.04/1.02  unary                                   3
% 2.04/1.02  binary                                  6
% 2.04/1.02  lits                                    60
% 2.04/1.02  lits eq                                 4
% 2.04/1.02  fd_pure                                 0
% 2.04/1.02  fd_pseudo                               0
% 2.04/1.02  fd_cond                                 0
% 2.04/1.02  fd_pseudo_cond                          3
% 2.04/1.02  AC symbols                              0
% 2.04/1.02  
% 2.04/1.02  ------ Schedule dynamic 5 is on 
% 2.04/1.02  
% 2.04/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.04/1.02  
% 2.04/1.02  
% 2.04/1.02  ------ 
% 2.04/1.02  Current options:
% 2.04/1.02  ------ 
% 2.04/1.02  
% 2.04/1.02  ------ Input Options
% 2.04/1.02  
% 2.04/1.02  --out_options                           all
% 2.04/1.02  --tptp_safe_out                         true
% 2.04/1.02  --problem_path                          ""
% 2.04/1.02  --include_path                          ""
% 2.04/1.02  --clausifier                            res/vclausify_rel
% 2.04/1.02  --clausifier_options                    --mode clausify
% 2.04/1.02  --stdin                                 false
% 2.04/1.02  --stats_out                             all
% 2.04/1.02  
% 2.04/1.02  ------ General Options
% 2.04/1.02  
% 2.04/1.02  --fof                                   false
% 2.04/1.02  --time_out_real                         305.
% 2.04/1.02  --time_out_virtual                      -1.
% 2.04/1.02  --symbol_type_check                     false
% 2.04/1.02  --clausify_out                          false
% 2.04/1.02  --sig_cnt_out                           false
% 2.04/1.02  --trig_cnt_out                          false
% 2.04/1.02  --trig_cnt_out_tolerance                1.
% 2.04/1.02  --trig_cnt_out_sk_spl                   false
% 2.04/1.02  --abstr_cl_out                          false
% 2.04/1.02  
% 2.04/1.02  ------ Global Options
% 2.04/1.02  
% 2.04/1.02  --schedule                              default
% 2.04/1.02  --add_important_lit                     false
% 2.04/1.02  --prop_solver_per_cl                    1000
% 2.04/1.02  --min_unsat_core                        false
% 2.04/1.02  --soft_assumptions                      false
% 2.04/1.02  --soft_lemma_size                       3
% 2.04/1.02  --prop_impl_unit_size                   0
% 2.04/1.02  --prop_impl_unit                        []
% 2.04/1.02  --share_sel_clauses                     true
% 2.04/1.02  --reset_solvers                         false
% 2.04/1.02  --bc_imp_inh                            [conj_cone]
% 2.04/1.02  --conj_cone_tolerance                   3.
% 2.04/1.02  --extra_neg_conj                        none
% 2.04/1.02  --large_theory_mode                     true
% 2.04/1.02  --prolific_symb_bound                   200
% 2.04/1.02  --lt_threshold                          2000
% 2.04/1.02  --clause_weak_htbl                      true
% 2.04/1.02  --gc_record_bc_elim                     false
% 2.04/1.02  
% 2.04/1.02  ------ Preprocessing Options
% 2.04/1.02  
% 2.04/1.02  --preprocessing_flag                    true
% 2.04/1.02  --time_out_prep_mult                    0.1
% 2.04/1.02  --splitting_mode                        input
% 2.04/1.02  --splitting_grd                         true
% 2.04/1.02  --splitting_cvd                         false
% 2.04/1.02  --splitting_cvd_svl                     false
% 2.04/1.02  --splitting_nvd                         32
% 2.04/1.02  --sub_typing                            true
% 2.04/1.02  --prep_gs_sim                           true
% 2.04/1.02  --prep_unflatten                        true
% 2.04/1.02  --prep_res_sim                          true
% 2.04/1.02  --prep_upred                            true
% 2.04/1.02  --prep_sem_filter                       exhaustive
% 2.04/1.02  --prep_sem_filter_out                   false
% 2.04/1.02  --pred_elim                             true
% 2.04/1.02  --res_sim_input                         true
% 2.04/1.02  --eq_ax_congr_red                       true
% 2.04/1.02  --pure_diseq_elim                       true
% 2.04/1.02  --brand_transform                       false
% 2.04/1.02  --non_eq_to_eq                          false
% 2.04/1.02  --prep_def_merge                        true
% 2.04/1.02  --prep_def_merge_prop_impl              false
% 2.04/1.02  --prep_def_merge_mbd                    true
% 2.04/1.02  --prep_def_merge_tr_red                 false
% 2.04/1.02  --prep_def_merge_tr_cl                  false
% 2.04/1.02  --smt_preprocessing                     true
% 2.04/1.02  --smt_ac_axioms                         fast
% 2.04/1.02  --preprocessed_out                      false
% 2.04/1.02  --preprocessed_stats                    false
% 2.04/1.02  
% 2.04/1.02  ------ Abstraction refinement Options
% 2.04/1.02  
% 2.04/1.02  --abstr_ref                             []
% 2.04/1.02  --abstr_ref_prep                        false
% 2.04/1.02  --abstr_ref_until_sat                   false
% 2.04/1.02  --abstr_ref_sig_restrict                funpre
% 2.04/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.04/1.02  --abstr_ref_under                       []
% 2.04/1.02  
% 2.04/1.02  ------ SAT Options
% 2.04/1.02  
% 2.04/1.02  --sat_mode                              false
% 2.04/1.02  --sat_fm_restart_options                ""
% 2.04/1.02  --sat_gr_def                            false
% 2.04/1.02  --sat_epr_types                         true
% 2.04/1.02  --sat_non_cyclic_types                  false
% 2.04/1.02  --sat_finite_models                     false
% 2.04/1.02  --sat_fm_lemmas                         false
% 2.04/1.02  --sat_fm_prep                           false
% 2.04/1.02  --sat_fm_uc_incr                        true
% 2.04/1.02  --sat_out_model                         small
% 2.04/1.02  --sat_out_clauses                       false
% 2.04/1.02  
% 2.04/1.02  ------ QBF Options
% 2.04/1.02  
% 2.04/1.02  --qbf_mode                              false
% 2.04/1.02  --qbf_elim_univ                         false
% 2.04/1.02  --qbf_dom_inst                          none
% 2.04/1.02  --qbf_dom_pre_inst                      false
% 2.04/1.02  --qbf_sk_in                             false
% 2.04/1.02  --qbf_pred_elim                         true
% 2.04/1.02  --qbf_split                             512
% 2.04/1.02  
% 2.04/1.02  ------ BMC1 Options
% 2.04/1.02  
% 2.04/1.02  --bmc1_incremental                      false
% 2.04/1.02  --bmc1_axioms                           reachable_all
% 2.04/1.02  --bmc1_min_bound                        0
% 2.04/1.02  --bmc1_max_bound                        -1
% 2.04/1.02  --bmc1_max_bound_default                -1
% 2.04/1.02  --bmc1_symbol_reachability              true
% 2.04/1.02  --bmc1_property_lemmas                  false
% 2.04/1.02  --bmc1_k_induction                      false
% 2.04/1.02  --bmc1_non_equiv_states                 false
% 2.04/1.02  --bmc1_deadlock                         false
% 2.04/1.02  --bmc1_ucm                              false
% 2.04/1.02  --bmc1_add_unsat_core                   none
% 2.04/1.02  --bmc1_unsat_core_children              false
% 2.04/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.04/1.02  --bmc1_out_stat                         full
% 2.04/1.02  --bmc1_ground_init                      false
% 2.04/1.02  --bmc1_pre_inst_next_state              false
% 2.04/1.02  --bmc1_pre_inst_state                   false
% 2.04/1.02  --bmc1_pre_inst_reach_state             false
% 2.04/1.02  --bmc1_out_unsat_core                   false
% 2.04/1.02  --bmc1_aig_witness_out                  false
% 2.04/1.02  --bmc1_verbose                          false
% 2.04/1.02  --bmc1_dump_clauses_tptp                false
% 2.04/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.04/1.02  --bmc1_dump_file                        -
% 2.04/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.04/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.04/1.02  --bmc1_ucm_extend_mode                  1
% 2.04/1.02  --bmc1_ucm_init_mode                    2
% 2.04/1.02  --bmc1_ucm_cone_mode                    none
% 2.04/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.04/1.02  --bmc1_ucm_relax_model                  4
% 2.04/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.04/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.04/1.02  --bmc1_ucm_layered_model                none
% 2.04/1.02  --bmc1_ucm_max_lemma_size               10
% 2.04/1.02  
% 2.04/1.02  ------ AIG Options
% 2.04/1.02  
% 2.04/1.02  --aig_mode                              false
% 2.04/1.02  
% 2.04/1.02  ------ Instantiation Options
% 2.04/1.02  
% 2.04/1.02  --instantiation_flag                    true
% 2.04/1.02  --inst_sos_flag                         false
% 2.04/1.02  --inst_sos_phase                        true
% 2.04/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.04/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.04/1.02  --inst_lit_sel_side                     none
% 2.04/1.02  --inst_solver_per_active                1400
% 2.04/1.02  --inst_solver_calls_frac                1.
% 2.04/1.02  --inst_passive_queue_type               priority_queues
% 2.04/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.04/1.02  --inst_passive_queues_freq              [25;2]
% 2.04/1.02  --inst_dismatching                      true
% 2.04/1.02  --inst_eager_unprocessed_to_passive     true
% 2.04/1.02  --inst_prop_sim_given                   true
% 2.04/1.02  --inst_prop_sim_new                     false
% 2.04/1.02  --inst_subs_new                         false
% 2.04/1.02  --inst_eq_res_simp                      false
% 2.04/1.02  --inst_subs_given                       false
% 2.04/1.02  --inst_orphan_elimination               true
% 2.04/1.02  --inst_learning_loop_flag               true
% 2.04/1.02  --inst_learning_start                   3000
% 2.04/1.02  --inst_learning_factor                  2
% 2.04/1.02  --inst_start_prop_sim_after_learn       3
% 2.04/1.02  --inst_sel_renew                        solver
% 2.04/1.02  --inst_lit_activity_flag                true
% 2.04/1.02  --inst_restr_to_given                   false
% 2.04/1.02  --inst_activity_threshold               500
% 2.04/1.02  --inst_out_proof                        true
% 2.04/1.02  
% 2.04/1.02  ------ Resolution Options
% 2.04/1.02  
% 2.04/1.02  --resolution_flag                       false
% 2.04/1.02  --res_lit_sel                           adaptive
% 2.04/1.02  --res_lit_sel_side                      none
% 2.04/1.02  --res_ordering                          kbo
% 2.04/1.02  --res_to_prop_solver                    active
% 2.04/1.02  --res_prop_simpl_new                    false
% 2.04/1.02  --res_prop_simpl_given                  true
% 2.04/1.02  --res_passive_queue_type                priority_queues
% 2.04/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.04/1.02  --res_passive_queues_freq               [15;5]
% 2.04/1.02  --res_forward_subs                      full
% 2.04/1.02  --res_backward_subs                     full
% 2.04/1.02  --res_forward_subs_resolution           true
% 2.04/1.02  --res_backward_subs_resolution          true
% 2.04/1.02  --res_orphan_elimination                true
% 2.04/1.02  --res_time_limit                        2.
% 2.04/1.02  --res_out_proof                         true
% 2.04/1.02  
% 2.04/1.02  ------ Superposition Options
% 2.04/1.02  
% 2.04/1.02  --superposition_flag                    true
% 2.04/1.02  --sup_passive_queue_type                priority_queues
% 2.04/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.04/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.04/1.02  --demod_completeness_check              fast
% 2.04/1.02  --demod_use_ground                      true
% 2.04/1.02  --sup_to_prop_solver                    passive
% 2.04/1.02  --sup_prop_simpl_new                    true
% 2.04/1.02  --sup_prop_simpl_given                  true
% 2.04/1.02  --sup_fun_splitting                     false
% 2.04/1.02  --sup_smt_interval                      50000
% 2.04/1.02  
% 2.04/1.02  ------ Superposition Simplification Setup
% 2.04/1.02  
% 2.04/1.02  --sup_indices_passive                   []
% 2.04/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.04/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.04/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.04/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.04/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.04/1.02  --sup_full_bw                           [BwDemod]
% 2.04/1.02  --sup_immed_triv                        [TrivRules]
% 2.04/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.04/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.04/1.02  --sup_immed_bw_main                     []
% 2.04/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.04/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.04/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.04/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.04/1.02  
% 2.04/1.02  ------ Combination Options
% 2.04/1.02  
% 2.04/1.02  --comb_res_mult                         3
% 2.04/1.02  --comb_sup_mult                         2
% 2.04/1.02  --comb_inst_mult                        10
% 2.04/1.02  
% 2.04/1.02  ------ Debug Options
% 2.04/1.02  
% 2.04/1.02  --dbg_backtrace                         false
% 2.04/1.02  --dbg_dump_prop_clauses                 false
% 2.04/1.02  --dbg_dump_prop_clauses_file            -
% 2.04/1.02  --dbg_out_stat                          false
% 2.04/1.02  
% 2.04/1.02  
% 2.04/1.02  
% 2.04/1.02  
% 2.04/1.02  ------ Proving...
% 2.04/1.02  
% 2.04/1.02  
% 2.04/1.02  % SZS status Theorem for theBenchmark.p
% 2.04/1.02  
% 2.04/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 2.04/1.02  
% 2.04/1.02  fof(f7,axiom,(
% 2.04/1.02    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 2.04/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.04/1.02  
% 2.04/1.02  fof(f19,plain,(
% 2.04/1.02    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 2.04/1.02    inference(ennf_transformation,[],[f7])).
% 2.04/1.02  
% 2.04/1.02  fof(f31,plain,(
% 2.04/1.02    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 2.04/1.02    inference(nnf_transformation,[],[f19])).
% 2.04/1.02  
% 2.04/1.02  fof(f32,plain,(
% 2.04/1.02    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 2.04/1.02    inference(rectify,[],[f31])).
% 2.04/1.02  
% 2.04/1.02  fof(f33,plain,(
% 2.04/1.02    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2) & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2))))),
% 2.04/1.02    introduced(choice_axiom,[])).
% 2.04/1.02  
% 2.04/1.02  fof(f34,plain,(
% 2.04/1.02    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2) & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 2.04/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f33])).
% 2.04/1.02  
% 2.04/1.02  fof(f55,plain,(
% 2.04/1.02    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2)) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 2.04/1.02    inference(cnf_transformation,[],[f34])).
% 2.04/1.02  
% 2.04/1.02  fof(f1,axiom,(
% 2.04/1.02    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.04/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.04/1.02  
% 2.04/1.02  fof(f23,plain,(
% 2.04/1.02    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.04/1.02    inference(nnf_transformation,[],[f1])).
% 2.04/1.02  
% 2.04/1.02  fof(f43,plain,(
% 2.04/1.02    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.04/1.02    inference(cnf_transformation,[],[f23])).
% 2.04/1.02  
% 2.04/1.02  fof(f2,axiom,(
% 2.04/1.02    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.04/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.04/1.02  
% 2.04/1.02  fof(f14,plain,(
% 2.04/1.02    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.04/1.02    inference(ennf_transformation,[],[f2])).
% 2.04/1.02  
% 2.04/1.02  fof(f15,plain,(
% 2.04/1.02    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.04/1.02    inference(flattening,[],[f14])).
% 2.04/1.02  
% 2.04/1.02  fof(f44,plain,(
% 2.04/1.02    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.04/1.02    inference(cnf_transformation,[],[f15])).
% 2.04/1.02  
% 2.04/1.02  fof(f57,plain,(
% 2.04/1.02    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 2.04/1.02    inference(cnf_transformation,[],[f34])).
% 2.04/1.02  
% 2.04/1.02  fof(f56,plain,(
% 2.04/1.02    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 2.04/1.02    inference(cnf_transformation,[],[f34])).
% 2.04/1.02  
% 2.04/1.02  fof(f10,conjecture,(
% 2.04/1.02    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))))))))),
% 2.04/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.04/1.02  
% 2.04/1.02  fof(f11,negated_conjecture,(
% 2.04/1.02    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))))))))),
% 2.04/1.02    inference(negated_conjecture,[],[f10])).
% 2.04/1.02  
% 2.04/1.02  fof(f12,plain,(
% 2.04/1.02    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2)))))),
% 2.04/1.02    inference(pure_predicate_removal,[],[f11])).
% 2.04/1.02  
% 2.04/1.02  fof(f22,plain,(
% 2.04/1.02    ? [X0,X1,X2,X3] : (? [X4] : ((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <~> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 2.04/1.02    inference(ennf_transformation,[],[f12])).
% 2.04/1.02  
% 2.04/1.02  fof(f35,plain,(
% 2.04/1.02    ? [X0,X1,X2,X3] : (? [X4] : (((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2)) | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 2.04/1.02    inference(nnf_transformation,[],[f22])).
% 2.04/1.02  
% 2.04/1.02  fof(f36,plain,(
% 2.04/1.02    ? [X0,X1,X2,X3] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2)) | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 2.04/1.02    inference(flattening,[],[f35])).
% 2.04/1.02  
% 2.04/1.02  fof(f37,plain,(
% 2.04/1.02    ? [X0,X1,X2,X3] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 2.04/1.02    inference(rectify,[],[f36])).
% 2.04/1.02  
% 2.04/1.02  fof(f40,plain,(
% 2.04/1.02    ( ! [X4,X2,X3,X1] : (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) => (r2_hidden(sK9,X1) & r2_hidden(k4_tarski(sK9,X4),X3) & m1_subset_1(sK9,X2))) )),
% 2.04/1.02    introduced(choice_axiom,[])).
% 2.04/1.02  
% 2.04/1.02  fof(f39,plain,(
% 2.04/1.02    ( ! [X2,X0,X3,X1] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))) & m1_subset_1(X4,X0)) => ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,sK8),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(sK8,k7_relset_1(X2,X0,X3,X1))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,sK8),X3) & m1_subset_1(X6,X2)) | r2_hidden(sK8,k7_relset_1(X2,X0,X3,X1))) & m1_subset_1(sK8,X0))) )),
% 2.04/1.02    introduced(choice_axiom,[])).
% 2.04/1.02  
% 2.04/1.02  fof(f38,plain,(
% 2.04/1.02    ? [X0,X1,X2,X3] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) => (? [X4] : ((! [X5] : (~r2_hidden(X5,sK5) | ~r2_hidden(k4_tarski(X5,X4),sK7) | ~m1_subset_1(X5,sK6)) | ~r2_hidden(X4,k7_relset_1(sK6,sK4,sK7,sK5))) & (? [X6] : (r2_hidden(X6,sK5) & r2_hidden(k4_tarski(X6,X4),sK7) & m1_subset_1(X6,sK6)) | r2_hidden(X4,k7_relset_1(sK6,sK4,sK7,sK5))) & m1_subset_1(X4,sK4)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))))),
% 2.04/1.02    introduced(choice_axiom,[])).
% 2.04/1.02  
% 2.04/1.02  fof(f41,plain,(
% 2.04/1.02    ((! [X5] : (~r2_hidden(X5,sK5) | ~r2_hidden(k4_tarski(X5,sK8),sK7) | ~m1_subset_1(X5,sK6)) | ~r2_hidden(sK8,k7_relset_1(sK6,sK4,sK7,sK5))) & ((r2_hidden(sK9,sK5) & r2_hidden(k4_tarski(sK9,sK8),sK7) & m1_subset_1(sK9,sK6)) | r2_hidden(sK8,k7_relset_1(sK6,sK4,sK7,sK5))) & m1_subset_1(sK8,sK4)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))),
% 2.04/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9])],[f37,f40,f39,f38])).
% 2.04/1.02  
% 2.04/1.02  fof(f64,plain,(
% 2.04/1.02    r2_hidden(k4_tarski(sK9,sK8),sK7) | r2_hidden(sK8,k7_relset_1(sK6,sK4,sK7,sK5))),
% 2.04/1.02    inference(cnf_transformation,[],[f41])).
% 2.04/1.02  
% 2.04/1.02  fof(f66,plain,(
% 2.04/1.02    ( ! [X5] : (~r2_hidden(X5,sK5) | ~r2_hidden(k4_tarski(X5,sK8),sK7) | ~m1_subset_1(X5,sK6) | ~r2_hidden(sK8,k7_relset_1(sK6,sK4,sK7,sK5))) )),
% 2.04/1.02    inference(cnf_transformation,[],[f41])).
% 2.04/1.02  
% 2.04/1.02  fof(f61,plain,(
% 2.04/1.02    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))),
% 2.04/1.02    inference(cnf_transformation,[],[f41])).
% 2.04/1.02  
% 2.04/1.02  fof(f42,plain,(
% 2.04/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.04/1.02    inference(cnf_transformation,[],[f23])).
% 2.04/1.02  
% 2.04/1.02  fof(f3,axiom,(
% 2.04/1.02    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.04/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.04/1.02  
% 2.04/1.02  fof(f16,plain,(
% 2.04/1.02    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.04/1.02    inference(ennf_transformation,[],[f3])).
% 2.04/1.02  
% 2.04/1.02  fof(f45,plain,(
% 2.04/1.02    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.04/1.02    inference(cnf_transformation,[],[f16])).
% 2.04/1.02  
% 2.04/1.02  fof(f6,axiom,(
% 2.04/1.02    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.04/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.04/1.02  
% 2.04/1.02  fof(f54,plain,(
% 2.04/1.02    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.04/1.02    inference(cnf_transformation,[],[f6])).
% 2.04/1.02  
% 2.04/1.02  fof(f9,axiom,(
% 2.04/1.02    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 2.04/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.04/1.02  
% 2.04/1.02  fof(f21,plain,(
% 2.04/1.02    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.04/1.02    inference(ennf_transformation,[],[f9])).
% 2.04/1.02  
% 2.04/1.02  fof(f60,plain,(
% 2.04/1.02    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.04/1.02    inference(cnf_transformation,[],[f21])).
% 2.04/1.02  
% 2.04/1.02  fof(f4,axiom,(
% 2.04/1.02    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)))))),
% 2.04/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.04/1.02  
% 2.04/1.02  fof(f17,plain,(
% 2.04/1.02    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)))) | ~v1_relat_1(X0))),
% 2.04/1.02    inference(ennf_transformation,[],[f4])).
% 2.04/1.02  
% 2.04/1.02  fof(f24,plain,(
% 2.04/1.02    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2)) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 2.04/1.02    inference(nnf_transformation,[],[f17])).
% 2.04/1.02  
% 2.04/1.02  fof(f25,plain,(
% 2.04/1.02    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X3),X0)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0))) & (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X8,X6),X0)) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 2.04/1.02    inference(rectify,[],[f24])).
% 2.04/1.02  
% 2.04/1.02  fof(f28,plain,(
% 2.04/1.02    ! [X6,X1,X0] : (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X8,X6),X0)) => (r2_hidden(sK2(X0,X1,X6),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X6),X6),X0)))),
% 2.04/1.02    introduced(choice_axiom,[])).
% 2.04/1.02  
% 2.04/1.02  fof(f27,plain,(
% 2.04/1.02    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X3),X0)) => (r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X3),X0)))) )),
% 2.04/1.02    introduced(choice_axiom,[])).
% 2.04/1.02  
% 2.04/1.02  fof(f26,plain,(
% 2.04/1.02    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X3),X0)) | r2_hidden(X3,X2))) => ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,sK0(X0,X1,X2)),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,sK0(X0,X1,X2)),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 2.04/1.02    introduced(choice_axiom,[])).
% 2.04/1.02  
% 2.04/1.02  fof(f29,plain,(
% 2.04/1.02    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,sK0(X0,X1,X2)),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),sK0(X0,X1,X2)),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0))) & ((r2_hidden(sK2(X0,X1,X6),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X6),X6),X0)) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 2.04/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f28,f27,f26])).
% 2.04/1.02  
% 2.04/1.02  fof(f48,plain,(
% 2.04/1.02    ( ! [X6,X2,X0,X7,X1] : (r2_hidden(X6,X2) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0) | k9_relat_1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 2.04/1.02    inference(cnf_transformation,[],[f29])).
% 2.04/1.02  
% 2.04/1.02  fof(f67,plain,(
% 2.04/1.02    ( ! [X6,X0,X7,X1] : (r2_hidden(X6,k9_relat_1(X0,X1)) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0) | ~v1_relat_1(X0)) )),
% 2.04/1.02    inference(equality_resolution,[],[f48])).
% 2.04/1.02  
% 2.04/1.02  fof(f65,plain,(
% 2.04/1.02    r2_hidden(sK9,sK5) | r2_hidden(sK8,k7_relset_1(sK6,sK4,sK7,sK5))),
% 2.04/1.02    inference(cnf_transformation,[],[f41])).
% 2.04/1.02  
% 2.04/1.02  fof(f8,axiom,(
% 2.04/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.04/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.04/1.02  
% 2.04/1.02  fof(f13,plain,(
% 2.04/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.04/1.02    inference(pure_predicate_removal,[],[f8])).
% 2.04/1.02  
% 2.04/1.02  fof(f20,plain,(
% 2.04/1.02    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.04/1.02    inference(ennf_transformation,[],[f13])).
% 2.04/1.02  
% 2.04/1.02  fof(f59,plain,(
% 2.04/1.02    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.04/1.02    inference(cnf_transformation,[],[f20])).
% 2.04/1.02  
% 2.04/1.02  fof(f5,axiom,(
% 2.04/1.02    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.04/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.04/1.02  
% 2.04/1.02  fof(f18,plain,(
% 2.04/1.02    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.04/1.02    inference(ennf_transformation,[],[f5])).
% 2.04/1.02  
% 2.04/1.02  fof(f30,plain,(
% 2.04/1.02    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.04/1.02    inference(nnf_transformation,[],[f18])).
% 2.04/1.02  
% 2.04/1.02  fof(f52,plain,(
% 2.04/1.02    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.04/1.02    inference(cnf_transformation,[],[f30])).
% 2.04/1.02  
% 2.04/1.02  cnf(c_16,plain,
% 2.04/1.02      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 2.04/1.02      | r2_hidden(sK3(X0,X2,X1),k1_relat_1(X1))
% 2.04/1.02      | ~ v1_relat_1(X1) ),
% 2.04/1.02      inference(cnf_transformation,[],[f55]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_1190,plain,
% 2.04/1.02      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 2.04/1.02      | r2_hidden(sK3(X0,X2,X1),k1_relat_1(X1)) = iProver_top
% 2.04/1.02      | v1_relat_1(X1) != iProver_top ),
% 2.04/1.02      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_0,plain,
% 2.04/1.02      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.04/1.02      inference(cnf_transformation,[],[f43]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_1202,plain,
% 2.04/1.02      ( r1_tarski(X0,X1) != iProver_top
% 2.04/1.02      | m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top ),
% 2.04/1.02      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_2,plain,
% 2.04/1.02      ( ~ r2_hidden(X0,X1)
% 2.04/1.02      | m1_subset_1(X0,X2)
% 2.04/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 2.04/1.02      inference(cnf_transformation,[],[f44]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_1200,plain,
% 2.04/1.02      ( r2_hidden(X0,X1) != iProver_top
% 2.04/1.02      | m1_subset_1(X0,X2) = iProver_top
% 2.04/1.02      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 2.04/1.02      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_2692,plain,
% 2.04/1.02      ( r2_hidden(X0,X1) != iProver_top
% 2.04/1.02      | r1_tarski(X1,X2) != iProver_top
% 2.04/1.02      | m1_subset_1(X0,X2) = iProver_top ),
% 2.04/1.02      inference(superposition,[status(thm)],[c_1202,c_1200]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_4357,plain,
% 2.04/1.02      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 2.04/1.02      | r1_tarski(k1_relat_1(X1),X3) != iProver_top
% 2.04/1.02      | m1_subset_1(sK3(X0,X2,X1),X3) = iProver_top
% 2.04/1.02      | v1_relat_1(X1) != iProver_top ),
% 2.04/1.02      inference(superposition,[status(thm)],[c_1190,c_2692]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_14,plain,
% 2.04/1.02      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 2.04/1.02      | r2_hidden(sK3(X0,X2,X1),X2)
% 2.04/1.02      | ~ v1_relat_1(X1) ),
% 2.04/1.02      inference(cnf_transformation,[],[f57]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_1192,plain,
% 2.04/1.02      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 2.04/1.02      | r2_hidden(sK3(X0,X2,X1),X2) = iProver_top
% 2.04/1.02      | v1_relat_1(X1) != iProver_top ),
% 2.04/1.02      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_15,plain,
% 2.04/1.02      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 2.04/1.02      | r2_hidden(k4_tarski(sK3(X0,X2,X1),X0),X1)
% 2.04/1.02      | ~ v1_relat_1(X1) ),
% 2.04/1.02      inference(cnf_transformation,[],[f56]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_1191,plain,
% 2.04/1.02      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 2.04/1.02      | r2_hidden(k4_tarski(sK3(X0,X2,X1),X0),X1) = iProver_top
% 2.04/1.02      | v1_relat_1(X1) != iProver_top ),
% 2.04/1.02      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_21,negated_conjecture,
% 2.04/1.02      ( r2_hidden(k4_tarski(sK9,sK8),sK7)
% 2.04/1.02      | r2_hidden(sK8,k7_relset_1(sK6,sK4,sK7,sK5)) ),
% 2.04/1.02      inference(cnf_transformation,[],[f64]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_1186,plain,
% 2.04/1.02      ( r2_hidden(k4_tarski(sK9,sK8),sK7) = iProver_top
% 2.04/1.02      | r2_hidden(sK8,k7_relset_1(sK6,sK4,sK7,sK5)) = iProver_top ),
% 2.04/1.02      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_19,negated_conjecture,
% 2.04/1.02      ( ~ r2_hidden(X0,sK5)
% 2.04/1.02      | ~ r2_hidden(k4_tarski(X0,sK8),sK7)
% 2.04/1.02      | ~ r2_hidden(sK8,k7_relset_1(sK6,sK4,sK7,sK5))
% 2.04/1.02      | ~ m1_subset_1(X0,sK6) ),
% 2.04/1.02      inference(cnf_transformation,[],[f66]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_1188,plain,
% 2.04/1.02      ( r2_hidden(X0,sK5) != iProver_top
% 2.04/1.02      | r2_hidden(k4_tarski(X0,sK8),sK7) != iProver_top
% 2.04/1.02      | r2_hidden(sK8,k7_relset_1(sK6,sK4,sK7,sK5)) != iProver_top
% 2.04/1.02      | m1_subset_1(X0,sK6) != iProver_top ),
% 2.04/1.02      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_1485,plain,
% 2.04/1.02      ( r2_hidden(X0,sK5) != iProver_top
% 2.04/1.02      | r2_hidden(k4_tarski(X0,sK8),sK7) != iProver_top
% 2.04/1.02      | r2_hidden(k4_tarski(sK9,sK8),sK7) = iProver_top
% 2.04/1.02      | m1_subset_1(X0,sK6) != iProver_top ),
% 2.04/1.02      inference(superposition,[status(thm)],[c_1186,c_1188]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_2925,plain,
% 2.04/1.02      ( r2_hidden(sK3(sK8,X0,sK7),sK5) != iProver_top
% 2.04/1.02      | r2_hidden(k4_tarski(sK9,sK8),sK7) = iProver_top
% 2.04/1.02      | r2_hidden(sK8,k9_relat_1(sK7,X0)) != iProver_top
% 2.04/1.02      | m1_subset_1(sK3(sK8,X0,sK7),sK6) != iProver_top
% 2.04/1.02      | v1_relat_1(sK7) != iProver_top ),
% 2.04/1.02      inference(superposition,[status(thm)],[c_1191,c_1485]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_24,negated_conjecture,
% 2.04/1.02      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) ),
% 2.04/1.02      inference(cnf_transformation,[],[f61]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_25,plain,
% 2.04/1.02      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) = iProver_top ),
% 2.04/1.02      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_1,plain,
% 2.04/1.02      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.04/1.02      inference(cnf_transformation,[],[f42]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_1371,plain,
% 2.04/1.02      ( r1_tarski(sK7,k2_zfmisc_1(sK6,sK4))
% 2.04/1.02      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) ),
% 2.04/1.02      inference(instantiation,[status(thm)],[c_1]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_1372,plain,
% 2.04/1.02      ( r1_tarski(sK7,k2_zfmisc_1(sK6,sK4)) = iProver_top
% 2.04/1.02      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) != iProver_top ),
% 2.04/1.02      inference(predicate_to_equality,[status(thm)],[c_1371]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_3,plain,
% 2.04/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.04/1.02      | ~ v1_relat_1(X1)
% 2.04/1.02      | v1_relat_1(X0) ),
% 2.04/1.02      inference(cnf_transformation,[],[f45]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_200,plain,
% 2.04/1.02      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.04/1.02      inference(prop_impl,[status(thm)],[c_0]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_248,plain,
% 2.04/1.02      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 2.04/1.02      inference(bin_hyper_res,[status(thm)],[c_3,c_200]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_1470,plain,
% 2.04/1.02      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 2.04/1.02      | v1_relat_1(X0)
% 2.04/1.02      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 2.04/1.02      inference(instantiation,[status(thm)],[c_248]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_1551,plain,
% 2.04/1.02      ( ~ r1_tarski(sK7,k2_zfmisc_1(sK6,sK4))
% 2.04/1.02      | ~ v1_relat_1(k2_zfmisc_1(sK6,sK4))
% 2.04/1.02      | v1_relat_1(sK7) ),
% 2.04/1.02      inference(instantiation,[status(thm)],[c_1470]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_1552,plain,
% 2.04/1.02      ( r1_tarski(sK7,k2_zfmisc_1(sK6,sK4)) != iProver_top
% 2.04/1.02      | v1_relat_1(k2_zfmisc_1(sK6,sK4)) != iProver_top
% 2.04/1.02      | v1_relat_1(sK7) = iProver_top ),
% 2.04/1.02      inference(predicate_to_equality,[status(thm)],[c_1551]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_12,plain,
% 2.04/1.02      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.04/1.02      inference(cnf_transformation,[],[f54]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_1566,plain,
% 2.04/1.02      ( v1_relat_1(k2_zfmisc_1(sK6,sK4)) ),
% 2.04/1.02      inference(instantiation,[status(thm)],[c_12]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_1567,plain,
% 2.04/1.02      ( v1_relat_1(k2_zfmisc_1(sK6,sK4)) = iProver_top ),
% 2.04/1.02      inference(predicate_to_equality,[status(thm)],[c_1566]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_3310,plain,
% 2.04/1.02      ( m1_subset_1(sK3(sK8,X0,sK7),sK6) != iProver_top
% 2.04/1.02      | r2_hidden(sK8,k9_relat_1(sK7,X0)) != iProver_top
% 2.04/1.02      | r2_hidden(k4_tarski(sK9,sK8),sK7) = iProver_top
% 2.04/1.02      | r2_hidden(sK3(sK8,X0,sK7),sK5) != iProver_top ),
% 2.04/1.02      inference(global_propositional_subsumption,
% 2.04/1.02                [status(thm)],
% 2.04/1.02                [c_2925,c_25,c_1372,c_1552,c_1567]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_3311,plain,
% 2.04/1.02      ( r2_hidden(sK3(sK8,X0,sK7),sK5) != iProver_top
% 2.04/1.02      | r2_hidden(k4_tarski(sK9,sK8),sK7) = iProver_top
% 2.04/1.02      | r2_hidden(sK8,k9_relat_1(sK7,X0)) != iProver_top
% 2.04/1.02      | m1_subset_1(sK3(sK8,X0,sK7),sK6) != iProver_top ),
% 2.04/1.02      inference(renaming,[status(thm)],[c_3310]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_3320,plain,
% 2.04/1.02      ( r2_hidden(k4_tarski(sK9,sK8),sK7) = iProver_top
% 2.04/1.02      | r2_hidden(sK8,k9_relat_1(sK7,sK5)) != iProver_top
% 2.04/1.02      | m1_subset_1(sK3(sK8,sK5,sK7),sK6) != iProver_top
% 2.04/1.02      | v1_relat_1(sK7) != iProver_top ),
% 2.04/1.02      inference(superposition,[status(thm)],[c_1192,c_3311]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_1183,plain,
% 2.04/1.02      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) = iProver_top ),
% 2.04/1.02      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_18,plain,
% 2.04/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.04/1.02      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 2.04/1.02      inference(cnf_transformation,[],[f60]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_1189,plain,
% 2.04/1.02      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 2.04/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.04/1.02      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_1795,plain,
% 2.04/1.02      ( k7_relset_1(sK6,sK4,sK7,X0) = k9_relat_1(sK7,X0) ),
% 2.04/1.02      inference(superposition,[status(thm)],[c_1183,c_1189]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_2060,plain,
% 2.04/1.02      ( r2_hidden(X0,sK5) != iProver_top
% 2.04/1.02      | r2_hidden(k4_tarski(X0,sK8),sK7) != iProver_top
% 2.04/1.02      | r2_hidden(sK8,k9_relat_1(sK7,sK5)) != iProver_top
% 2.04/1.02      | m1_subset_1(X0,sK6) != iProver_top ),
% 2.04/1.02      inference(demodulation,[status(thm)],[c_1795,c_1188]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_2924,plain,
% 2.04/1.02      ( r2_hidden(sK3(sK8,X0,sK7),sK5) != iProver_top
% 2.04/1.02      | r2_hidden(sK8,k9_relat_1(sK7,X0)) != iProver_top
% 2.04/1.02      | r2_hidden(sK8,k9_relat_1(sK7,sK5)) != iProver_top
% 2.04/1.02      | m1_subset_1(sK3(sK8,X0,sK7),sK6) != iProver_top
% 2.04/1.02      | v1_relat_1(sK7) != iProver_top ),
% 2.04/1.02      inference(superposition,[status(thm)],[c_1191,c_2060]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_3419,plain,
% 2.04/1.02      ( m1_subset_1(sK3(sK8,X0,sK7),sK6) != iProver_top
% 2.04/1.02      | r2_hidden(sK8,k9_relat_1(sK7,sK5)) != iProver_top
% 2.04/1.02      | r2_hidden(sK8,k9_relat_1(sK7,X0)) != iProver_top
% 2.04/1.02      | r2_hidden(sK3(sK8,X0,sK7),sK5) != iProver_top ),
% 2.04/1.02      inference(global_propositional_subsumption,
% 2.04/1.02                [status(thm)],
% 2.04/1.02                [c_2924,c_25,c_1372,c_1552,c_1567]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_3420,plain,
% 2.04/1.02      ( r2_hidden(sK3(sK8,X0,sK7),sK5) != iProver_top
% 2.04/1.02      | r2_hidden(sK8,k9_relat_1(sK7,X0)) != iProver_top
% 2.04/1.02      | r2_hidden(sK8,k9_relat_1(sK7,sK5)) != iProver_top
% 2.04/1.02      | m1_subset_1(sK3(sK8,X0,sK7),sK6) != iProver_top ),
% 2.04/1.02      inference(renaming,[status(thm)],[c_3419]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_3429,plain,
% 2.04/1.02      ( r2_hidden(sK8,k9_relat_1(sK7,sK5)) != iProver_top
% 2.04/1.02      | m1_subset_1(sK3(sK8,sK5,sK7),sK6) != iProver_top
% 2.04/1.02      | v1_relat_1(sK7) != iProver_top ),
% 2.04/1.02      inference(superposition,[status(thm)],[c_1192,c_3420]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_2057,plain,
% 2.04/1.02      ( r2_hidden(k4_tarski(sK9,sK8),sK7) = iProver_top
% 2.04/1.02      | r2_hidden(sK8,k9_relat_1(sK7,sK5)) = iProver_top ),
% 2.04/1.02      inference(demodulation,[status(thm)],[c_1795,c_1186]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_7,plain,
% 2.04/1.02      ( ~ r2_hidden(X0,X1)
% 2.04/1.02      | r2_hidden(X2,k9_relat_1(X3,X1))
% 2.04/1.02      | ~ r2_hidden(k4_tarski(X0,X2),X3)
% 2.04/1.02      | ~ v1_relat_1(X3) ),
% 2.04/1.02      inference(cnf_transformation,[],[f67]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_1196,plain,
% 2.04/1.02      ( r2_hidden(X0,X1) != iProver_top
% 2.04/1.02      | r2_hidden(X2,k9_relat_1(X3,X1)) = iProver_top
% 2.04/1.02      | r2_hidden(k4_tarski(X0,X2),X3) != iProver_top
% 2.04/1.02      | v1_relat_1(X3) != iProver_top ),
% 2.04/1.02      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_3587,plain,
% 2.04/1.02      ( r2_hidden(sK9,X0) != iProver_top
% 2.04/1.02      | r2_hidden(sK8,k9_relat_1(sK7,X0)) = iProver_top
% 2.04/1.02      | r2_hidden(sK8,k9_relat_1(sK7,sK5)) = iProver_top
% 2.04/1.02      | v1_relat_1(sK7) != iProver_top ),
% 2.04/1.02      inference(superposition,[status(thm)],[c_2057,c_1196]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_4153,plain,
% 2.04/1.02      ( r2_hidden(sK8,k9_relat_1(sK7,sK5)) = iProver_top
% 2.04/1.02      | r2_hidden(sK8,k9_relat_1(sK7,X0)) = iProver_top
% 2.04/1.02      | r2_hidden(sK9,X0) != iProver_top ),
% 2.04/1.02      inference(global_propositional_subsumption,
% 2.04/1.02                [status(thm)],
% 2.04/1.02                [c_3587,c_25,c_1372,c_1552,c_1567]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_4154,plain,
% 2.04/1.02      ( r2_hidden(sK9,X0) != iProver_top
% 2.04/1.02      | r2_hidden(sK8,k9_relat_1(sK7,X0)) = iProver_top
% 2.04/1.02      | r2_hidden(sK8,k9_relat_1(sK7,sK5)) = iProver_top ),
% 2.04/1.02      inference(renaming,[status(thm)],[c_4153]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_4162,plain,
% 2.04/1.02      ( r2_hidden(sK9,sK5) != iProver_top
% 2.04/1.02      | r2_hidden(sK8,k9_relat_1(sK7,sK5)) = iProver_top
% 2.04/1.02      | iProver_top != iProver_top ),
% 2.04/1.02      inference(equality_factoring,[status(thm)],[c_4154]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_4213,plain,
% 2.04/1.02      ( r2_hidden(sK9,sK5) != iProver_top
% 2.04/1.02      | r2_hidden(sK8,k9_relat_1(sK7,sK5)) = iProver_top ),
% 2.04/1.02      inference(equality_resolution_simp,[status(thm)],[c_4162]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_20,negated_conjecture,
% 2.04/1.02      ( r2_hidden(sK9,sK5)
% 2.04/1.02      | r2_hidden(sK8,k7_relset_1(sK6,sK4,sK7,sK5)) ),
% 2.04/1.02      inference(cnf_transformation,[],[f65]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_1187,plain,
% 2.04/1.02      ( r2_hidden(sK9,sK5) = iProver_top
% 2.04/1.02      | r2_hidden(sK8,k7_relset_1(sK6,sK4,sK7,sK5)) = iProver_top ),
% 2.04/1.02      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_2058,plain,
% 2.04/1.02      ( r2_hidden(sK9,sK5) = iProver_top
% 2.04/1.02      | r2_hidden(sK8,k9_relat_1(sK7,sK5)) = iProver_top ),
% 2.04/1.02      inference(demodulation,[status(thm)],[c_1795,c_1187]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_4215,plain,
% 2.04/1.02      ( r2_hidden(sK8,k9_relat_1(sK7,sK5)) = iProver_top ),
% 2.04/1.02      inference(global_propositional_subsumption,
% 2.04/1.02                [status(thm)],
% 2.04/1.02                [c_4213,c_2058]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_4722,plain,
% 2.04/1.02      ( m1_subset_1(sK3(sK8,sK5,sK7),sK6) != iProver_top ),
% 2.04/1.02      inference(global_propositional_subsumption,
% 2.04/1.02                [status(thm)],
% 2.04/1.02                [c_3320,c_25,c_1372,c_1552,c_1567,c_2058,c_3429,c_4213]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_5640,plain,
% 2.04/1.02      ( r2_hidden(sK8,k9_relat_1(sK7,sK5)) != iProver_top
% 2.04/1.02      | r1_tarski(k1_relat_1(sK7),sK6) != iProver_top
% 2.04/1.02      | v1_relat_1(sK7) != iProver_top ),
% 2.04/1.02      inference(superposition,[status(thm)],[c_4357,c_4722]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_17,plain,
% 2.04/1.02      ( v4_relat_1(X0,X1)
% 2.04/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.04/1.02      inference(cnf_transformation,[],[f59]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_11,plain,
% 2.04/1.02      ( ~ v4_relat_1(X0,X1)
% 2.04/1.02      | r1_tarski(k1_relat_1(X0),X1)
% 2.04/1.02      | ~ v1_relat_1(X0) ),
% 2.04/1.02      inference(cnf_transformation,[],[f52]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_332,plain,
% 2.04/1.02      ( r1_tarski(k1_relat_1(X0),X1)
% 2.04/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.04/1.02      | ~ v1_relat_1(X0) ),
% 2.04/1.02      inference(resolution,[status(thm)],[c_17,c_11]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_1181,plain,
% 2.04/1.02      ( r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 2.04/1.02      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.04/1.02      | v1_relat_1(X0) != iProver_top ),
% 2.04/1.02      inference(predicate_to_equality,[status(thm)],[c_332]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(c_1579,plain,
% 2.04/1.02      ( r1_tarski(k1_relat_1(sK7),sK6) = iProver_top
% 2.04/1.02      | v1_relat_1(sK7) != iProver_top ),
% 2.04/1.02      inference(superposition,[status(thm)],[c_1183,c_1181]) ).
% 2.04/1.02  
% 2.04/1.02  cnf(contradiction,plain,
% 2.04/1.02      ( $false ),
% 2.04/1.02      inference(minisat,
% 2.04/1.02                [status(thm)],
% 2.04/1.02                [c_5640,c_4215,c_1579,c_1567,c_1552,c_1372,c_25]) ).
% 2.04/1.02  
% 2.04/1.02  
% 2.04/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 2.04/1.02  
% 2.04/1.02  ------                               Statistics
% 2.04/1.02  
% 2.04/1.02  ------ General
% 2.04/1.02  
% 2.04/1.02  abstr_ref_over_cycles:                  0
% 2.04/1.02  abstr_ref_under_cycles:                 0
% 2.04/1.02  gc_basic_clause_elim:                   0
% 2.04/1.02  forced_gc_time:                         0
% 2.04/1.02  parsing_time:                           0.008
% 2.04/1.02  unif_index_cands_time:                  0.
% 2.04/1.02  unif_index_add_time:                    0.
% 2.04/1.02  orderings_time:                         0.
% 2.04/1.02  out_proof_time:                         0.007
% 2.04/1.02  total_time:                             0.197
% 2.04/1.02  num_of_symbols:                         52
% 2.04/1.02  num_of_terms:                           8636
% 2.04/1.02  
% 2.04/1.02  ------ Preprocessing
% 2.04/1.02  
% 2.04/1.02  num_of_splits:                          0
% 2.04/1.02  num_of_split_atoms:                     0
% 2.04/1.02  num_of_reused_defs:                     0
% 2.04/1.02  num_eq_ax_congr_red:                    50
% 2.04/1.02  num_of_sem_filtered_clauses:            1
% 2.04/1.02  num_of_subtypes:                        0
% 2.04/1.02  monotx_restored_types:                  0
% 2.04/1.02  sat_num_of_epr_types:                   0
% 2.04/1.02  sat_num_of_non_cyclic_types:            0
% 2.04/1.02  sat_guarded_non_collapsed_types:        0
% 2.04/1.02  num_pure_diseq_elim:                    0
% 2.04/1.02  simp_replaced_by:                       0
% 2.04/1.02  res_preprocessed:                       111
% 2.04/1.02  prep_upred:                             0
% 2.04/1.02  prep_unflattend:                        8
% 2.04/1.02  smt_new_axioms:                         0
% 2.04/1.02  pred_elim_cands:                        4
% 2.04/1.02  pred_elim:                              1
% 2.04/1.02  pred_elim_cl:                           2
% 2.04/1.02  pred_elim_cycles:                       3
% 2.04/1.02  merged_defs:                            8
% 2.04/1.02  merged_defs_ncl:                        0
% 2.04/1.02  bin_hyper_res:                          9
% 2.04/1.02  prep_cycles:                            4
% 2.04/1.02  pred_elim_time:                         0.003
% 2.04/1.02  splitting_time:                         0.
% 2.04/1.02  sem_filter_time:                        0.
% 2.04/1.02  monotx_time:                            0.001
% 2.04/1.02  subtype_inf_time:                       0.
% 2.04/1.02  
% 2.04/1.02  ------ Problem properties
% 2.04/1.02  
% 2.04/1.02  clauses:                                22
% 2.04/1.02  conjectures:                            6
% 2.04/1.02  epr:                                    2
% 2.04/1.02  horn:                                   17
% 2.04/1.02  ground:                                 5
% 2.04/1.02  unary:                                  3
% 2.04/1.02  binary:                                 6
% 2.04/1.02  lits:                                   60
% 2.04/1.02  lits_eq:                                4
% 2.04/1.02  fd_pure:                                0
% 2.04/1.02  fd_pseudo:                              0
% 2.04/1.02  fd_cond:                                0
% 2.04/1.02  fd_pseudo_cond:                         3
% 2.04/1.02  ac_symbols:                             0
% 2.04/1.02  
% 2.04/1.02  ------ Propositional Solver
% 2.04/1.02  
% 2.04/1.02  prop_solver_calls:                      28
% 2.04/1.02  prop_fast_solver_calls:                 889
% 2.04/1.02  smt_solver_calls:                       0
% 2.04/1.02  smt_fast_solver_calls:                  0
% 2.04/1.02  prop_num_of_clauses:                    2323
% 2.04/1.02  prop_preprocess_simplified:             6926
% 2.04/1.02  prop_fo_subsumed:                       32
% 2.04/1.02  prop_solver_time:                       0.
% 2.04/1.02  smt_solver_time:                        0.
% 2.04/1.02  smt_fast_solver_time:                   0.
% 2.04/1.02  prop_fast_solver_time:                  0.
% 2.04/1.02  prop_unsat_core_time:                   0.
% 2.04/1.02  
% 2.04/1.02  ------ QBF
% 2.04/1.02  
% 2.04/1.02  qbf_q_res:                              0
% 2.04/1.02  qbf_num_tautologies:                    0
% 2.04/1.02  qbf_prep_cycles:                        0
% 2.04/1.02  
% 2.04/1.02  ------ BMC1
% 2.04/1.02  
% 2.04/1.02  bmc1_current_bound:                     -1
% 2.04/1.02  bmc1_last_solved_bound:                 -1
% 2.04/1.02  bmc1_unsat_core_size:                   -1
% 2.04/1.02  bmc1_unsat_core_parents_size:           -1
% 2.04/1.02  bmc1_merge_next_fun:                    0
% 2.04/1.02  bmc1_unsat_core_clauses_time:           0.
% 2.04/1.02  
% 2.04/1.02  ------ Instantiation
% 2.04/1.02  
% 2.04/1.02  inst_num_of_clauses:                    576
% 2.04/1.02  inst_num_in_passive:                    295
% 2.04/1.02  inst_num_in_active:                     272
% 2.04/1.02  inst_num_in_unprocessed:                9
% 2.04/1.02  inst_num_of_loops:                      290
% 2.04/1.02  inst_num_of_learning_restarts:          0
% 2.04/1.02  inst_num_moves_active_passive:          16
% 2.04/1.02  inst_lit_activity:                      0
% 2.04/1.02  inst_lit_activity_moves:                0
% 2.04/1.02  inst_num_tautologies:                   0
% 2.04/1.02  inst_num_prop_implied:                  0
% 2.04/1.02  inst_num_existing_simplified:           0
% 2.04/1.02  inst_num_eq_res_simplified:             0
% 2.04/1.02  inst_num_child_elim:                    0
% 2.04/1.02  inst_num_of_dismatching_blockings:      86
% 2.04/1.02  inst_num_of_non_proper_insts:           407
% 2.04/1.02  inst_num_of_duplicates:                 0
% 2.04/1.02  inst_inst_num_from_inst_to_res:         0
% 2.04/1.02  inst_dismatching_checking_time:         0.
% 2.04/1.02  
% 2.04/1.02  ------ Resolution
% 2.04/1.02  
% 2.04/1.02  res_num_of_clauses:                     0
% 2.04/1.02  res_num_in_passive:                     0
% 2.04/1.02  res_num_in_active:                      0
% 2.04/1.02  res_num_of_loops:                       115
% 2.04/1.02  res_forward_subset_subsumed:            20
% 2.04/1.02  res_backward_subset_subsumed:           0
% 2.04/1.02  res_forward_subsumed:                   0
% 2.04/1.02  res_backward_subsumed:                  0
% 2.04/1.02  res_forward_subsumption_resolution:     0
% 2.04/1.02  res_backward_subsumption_resolution:    0
% 2.04/1.02  res_clause_to_clause_subsumption:       136
% 2.04/1.02  res_orphan_elimination:                 0
% 2.04/1.02  res_tautology_del:                      47
% 2.04/1.02  res_num_eq_res_simplified:              0
% 2.04/1.02  res_num_sel_changes:                    0
% 2.04/1.02  res_moves_from_active_to_pass:          0
% 2.04/1.02  
% 2.04/1.02  ------ Superposition
% 2.04/1.02  
% 2.04/1.02  sup_time_total:                         0.
% 2.04/1.02  sup_time_generating:                    0.
% 2.04/1.02  sup_time_sim_full:                      0.
% 2.04/1.02  sup_time_sim_immed:                     0.
% 2.04/1.02  
% 2.04/1.02  sup_num_of_clauses:                     75
% 2.04/1.02  sup_num_in_active:                      52
% 2.04/1.02  sup_num_in_passive:                     23
% 2.04/1.02  sup_num_of_loops:                       56
% 2.04/1.02  sup_fw_superposition:                   38
% 2.04/1.02  sup_bw_superposition:                   35
% 2.04/1.02  sup_immediate_simplified:               5
% 2.04/1.02  sup_given_eliminated:                   0
% 2.04/1.02  comparisons_done:                       0
% 2.04/1.02  comparisons_avoided:                    0
% 2.04/1.02  
% 2.04/1.02  ------ Simplifications
% 2.04/1.02  
% 2.04/1.02  
% 2.04/1.02  sim_fw_subset_subsumed:                 2
% 2.04/1.02  sim_bw_subset_subsumed:                 2
% 2.04/1.02  sim_fw_subsumed:                        1
% 2.04/1.02  sim_bw_subsumed:                        2
% 2.04/1.02  sim_fw_subsumption_res:                 0
% 2.04/1.02  sim_bw_subsumption_res:                 0
% 2.04/1.02  sim_tautology_del:                      6
% 2.04/1.02  sim_eq_tautology_del:                   0
% 2.04/1.02  sim_eq_res_simp:                        1
% 2.04/1.02  sim_fw_demodulated:                     0
% 2.04/1.02  sim_bw_demodulated:                     4
% 2.04/1.02  sim_light_normalised:                   0
% 2.04/1.02  sim_joinable_taut:                      0
% 2.04/1.02  sim_joinable_simp:                      0
% 2.04/1.02  sim_ac_normalised:                      0
% 2.04/1.02  sim_smt_subsumption:                    0
% 2.04/1.02  
%------------------------------------------------------------------------------
